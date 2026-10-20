#!/usr/bin/env python3
"""Pretraga putovanja: avioni, autobusi, presjedanja i kombinacije.

Python 3.11+; instalacija (jednom):
    python -m pip install fast-flights==3.0 airportsdata==20260905 tzdata typing_extensions certifi

Pokretanje:
    python letovi.py
    python letovi.py --from Podgorica --to Kopenhagen --date 26.11.2026
    python letovi.py --from TGD --to CPH --date 2026-11-26 --sort duration
    python letovi.py --from Podgorica --to Kopenhagen --date 26.11.2026 \
        --via-origin "Tirana,Beograd" --via-destination "Malmo,Hamburg"

Bez API kljuca. Google Flights (fast-flights) i javni FlixBus JSON odgovori.
Rezultati: terminal + rezultati.html + rezultati.json (sve pronadjene opcije).
Pretrazuje jednosmjerno, ekonomsku klasu, odrasle putnike.
Nema rezervisanja/placanja. Sajtovi mogu promijeniti format ili blokirati pristup.

Obuhvat: rezultati oba izvora za trazeni dan, avionska i autobuska presjedanja
koja nude izvori, te autobus+avion ili avion+autobus preko izabranih gradova.
Ne pretrazuje svaki prevoznik/granicni prelaz niti sve moguce kombinacije.
Mijesane rute su kandidati sa odvojenim kartama: lokalni transfer i njegova
cijena nijesu ukljuceni. Rezerva od 4h nije potvrda da transfer postoji.
Provjeri prtljag, stanice, granice, uslove presjedanja i konacnu cijenu na linku.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, asdict
from datetime import date, datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation
from functools import lru_cache
from html import escape
import json
from pathlib import Path
import sys
import ssl
import time
from types import SimpleNamespace
import unicodedata
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError
from zoneinfo import ZoneInfo

UTC = timezone.utc
CATALOG = {
    "Podgorica": ("TGD",), "Tivat": ("TIV",), "Belgrade": ("BEG",),
    "Tirana": ("TIA",), "Dubrovnik": ("DBV",), "Zagreb": ("ZAG",),
    "Sarajevo": ("SJJ",), "Split": ("SPU",), "Ljubljana": ("LJU",),
    "Copenhagen": ("CPH",), "Malmo": ("MMX",), "Hamburg": ("HAM",),
    "Berlin": ("BER",), "Vienna": ("VIE",), "Budapest": ("BUD",),
    "Rome": ("FCO", "CIA"), "Milan": ("MXP", "BGY", "LIN"),
    "Paris": ("CDG", "ORY", "BVA"), "London": ("LHR", "LGW", "STN", "LTN"),
    "Istanbul": ("IST", "SAW"), "Prague": ("PRG",), "Munich": ("MUC",),
    "Frankfurt": ("FRA",), "Zurich": ("ZRH",), "Brussels": ("BRU", "CRL"),
    "Amsterdam": ("AMS",), "Madrid": ("MAD",), "Barcelona": ("BCN",),
    "Athens": ("ATH",), "Warsaw": ("WAW",), "Stockholm": ("ARN", "NYO"),
    "Oslo": ("OSL", "TRF"), "Gothenburg": ("GOT",), "Skopje": ("SKP",),
    "Sofia": ("SOF",), "Bucharest": ("OTP",), "Bratislava": ("BTS",),
    "Bologna": ("BLQ",), "Venice": ("VCE", "TSF"),
}
ALIASES = {
    "beograd": "Belgrade", "kopenhagen": "Copenhagen", "kobenhavn": "Copenhagen",
    "bec": "Vienna", "becs": "Vienna", "rim": "Rome", "milano": "Milan",
    "pariz": "Paris", "minhen": "Munich", "cirih": "Zurich", "atina": "Athens",
    "budimpesta": "Budapest", "prag": "Prague", "varsava": "Warsaw",
    "brisel": "Brussels", "barselona": "Barcelona", "stokholm": "Stockholm",
    "geteborg": "Gothenburg", "skoplje": "Skopje", "sofija": "Sofia",
    "bukurest": "Bucharest", "venecija": "Venice", "bolonja": "Bologna",
}
NEARBY = {
    "Podgorica": ["Tirana", "Belgrade"], "Tivat": ["Dubrovnik", "Podgorica"],
    "Copenhagen": ["Malmo", "Hamburg"], "Belgrade": ["Budapest", "Zagreb"],
    "Tirana": ["Podgorica", "Skopje"], "Dubrovnik": ["Tivat", "Podgorica"],
    "Vienna": ["Bratislava", "Budapest"], "Bratislava": ["Vienna", "Budapest"],
    "Zagreb": ["Ljubljana", "Budapest"], "Ljubljana": ["Zagreb", "Venice"],
    "Malmo": ["Copenhagen", "Gothenburg"], "Hamburg": ["Berlin", "Copenhagen"],
}


def norm(s: str) -> str:
    return "".join(c for c in unicodedata.normalize("NFKD", s.casefold())
                   if not unicodedata.combining(c)).replace("ø", "o").replace("đ", "dj").strip()


@lru_cache(maxsize=1)
def airports() -> dict:
    try:
        import airportsdata
    except ImportError as e:
        raise RuntimeError("Nedostaju zavisnosti. Pokreni instalaciju iz zaglavlja fajla.") from e
    return airportsdata.load("IATA")


@dataclass(frozen=True)
class Place:
    name: str
    codes: tuple[str, ...]


def resolve(text: str) -> Place:
    text = text.strip()
    name = ALIASES.get(norm(text), text)
    for city, codes in CATALOG.items():
        if norm(city) == norm(name):
            return Place(city, codes)
    if len(text) == 3 and text.upper() in airports():
        code = text.upper()
        city = next((n for n, cs in CATALOG.items() if code in cs), airports()[code]["city"])
        return Place(city, (code,))
    # City without an airport is valid for bus searches.
    codes = tuple(sorted(k for k, a in airports().items() if norm(a["city"]) == norm(name)))
    return Place(name, codes)


def parse_date(s: str) -> date:
    for fmt in ("%Y-%m-%d", "%d.%m.%Y", "%d.%m.%Y.", "%d/%m/%Y", "%d-%m-%Y"):
        try:
            return datetime.strptime(s.strip(), fmt).date()
        except ValueError:
            continue
    raise ValueError("Neispravan datum. Primjer: 26.11.2026 ili 2026-11-26.")


def instant(dt: datetime) -> datetime:
    if dt.tzinfo is None:
        raise ValueError("Vrijeme mora imati vremensku zonu.")
    return dt.astimezone(UTC)


def minutes(a: datetime, b: datetime) -> int:
    return int((instant(b) - instant(a)).total_seconds() // 60)


def money(value) -> Decimal | None:
    if value is None:
        return None
    try:
        v = Decimal(str(value))
        return v.quantize(Decimal("0.01")) if v.is_finite() and v >= 0 else None
    except InvalidOperation:
        return None


def message_texts(value):
    """The bus API uses both a string list and a from/to message dictionary."""
    if isinstance(value, str):
        return [value] if value.strip() else []
    if isinstance(value, dict):
        value = list(value.values())
    if isinstance(value, list):
        return [text for item in value for text in message_texts(item)]
    return []


@dataclass(frozen=True)
class Leg:
    mode: str
    origin: str
    destination: str
    departure: datetime
    arrival: datetime
    carrier: str
    origin_city: str = ""
    destination_city: str = ""

    def __post_init__(self):
        if minutes(self.departure, self.arrival) < 0:
            raise ValueError("Dolazak prije polaska: neispravan odgovor izvora.")


@dataclass
class Option:
    legs: list[Leg]
    price: Decimal | None
    sources: list[str]
    links: list[str]
    notes: list[str]
    mixed: bool = False

    def __post_init__(self):
        if not self.legs:
            raise ValueError("Prazna ruta.")
        for a, b in zip(self.legs, self.legs[1:]):
            if instant(a.arrival) > instant(b.departure):
                raise ValueError("Dionice se vremenski preklapaju.")

    @property
    def duration(self) -> int:
        return minutes(self.legs[0].departure, self.legs[-1].arrival)

    @property
    def label(self) -> str:
        if self.mixed:
            return "AUTOBUS + AVION · odvojene karte"
        return "AVION" if self.legs[0].mode == "flight" else "AUTOBUS / KOPNENI PREVOZ"

    def key(self):
        return tuple((x.mode, x.origin, x.destination, x.departure.isoformat(),
                      x.arrival.isoformat(), x.carrier) for x in self.legs)


@lru_cache(maxsize=1)
def ssl_context():
    # Keep system/SSL_CERT_FILE trust and add Mozilla roots for Python installs
    # whose default CA store is empty. Certificate verification stays enabled.
    context = ssl.create_default_context()
    try:
        import certifi
    except ImportError as e:
        raise RuntimeError("Instaliraj sertifikate: python -m pip install --upgrade certifi") from e
    context.load_verify_locations(cafile=certifi.where())
    return context


def json_get(url: str, params: dict, timeout: float) -> object:
    req = Request(url + "?" + urlencode(params), headers={
        "User-Agent": "Mozilla/5.0", "Accept": "application/json"})
    try:
        with urlopen(req, timeout=timeout, context=ssl_context()) as response:
            return json.load(response)
    except HTTPError as e:
        raise RuntimeError(f"Izvor je vratio HTTP {e.code}.") from e
    except (URLError, TimeoutError) as e:
        raise RuntimeError(f"Izvor nije dostupan: {e}") from e


class FlixBus:
    name = "FlixBus"

    def __init__(self, adults=1, timeout=30):
        self.adults, self.timeout = adults, timeout
        self.cities = {}

    def city(self, place: Place) -> dict:
        if place.name in self.cities:
            return self.cities[place.name]
        data = json_get("https://global.api.flixbus.com/search/autocomplete/cities",
                        {"q": place.name, "lang": "en"}, self.timeout)
        if not isinstance(data, list):
            raise RuntimeError("Promijenjen format FlixBus pretrage gradova.")
        exact = [x for x in data if norm(x.get("name", "")) == norm(place.name)
                 and x.get("is_flixbus_city")]
        if len(exact) != 1:
            names = ", ".join(f"{x.get('name')} ({x.get('country')})" for x in data[:8])
            raise RuntimeError(f"Grad '{place.name}' nije jednoznacno pronadjen. "
                               f"Upisi tacan naziv sa sajta. Kandidati: {names or 'nema'}")
        self.cities[place.name] = exact[0]
        return exact[0]

    def search(self, origin: Place, dest: Place, day: date) -> list[Option]:
        o, d = self.city(origin), self.city(dest)
        params = {"from_city_id": o["id"], "to_city_id": d["id"],
                  "departure_date": day.strftime("%d.%m.%Y"),
                  "products": json.dumps({"adult": self.adults}), "currency": "EUR",
                  "locale": "en_US", "search_by": "cities", "include_after_midnight_rides": "0"}
        data = json_get("https://global.api.flixbus.com/search/service/v4/search", params, self.timeout)
        link = "https://shop.flixbus.com/search?" + urlencode({
            "departureCity": o["id"], "arrivalCity": d["id"],
            "rideDate": day.strftime("%d.%m.%Y"), "adult": self.adults, "currency": "EUR"})
        return self.parse(data, day, link)

    @staticmethod
    def parse(data, day: date, link: str) -> list[Option]:
        if not isinstance(data, dict) or not isinstance(data.get("trips"), list):
            raise RuntimeError("Promijenjen format FlixBus odgovora; rezultat nije pouzdan.")
        cities, stations, operators = (data.get(k, {}) for k in ("cities", "stations", "operators"))

        def stop(s: dict):
            t = datetime.fromisoformat(s["date"].replace("Z", "+00:00"))
            instant(t)  # reject naive times rather than invent a timezone
            city = cities.get(s.get("city_id"), {}).get("name", "")
            station = stations.get(s.get("station_id"), {}).get("name", city or s.get("station_id", "?"))
            return t, station, city

        out = []
        for trip in data["trips"]:
            results = trip.get("results", {})
            if not isinstance(results, dict):
                raise RuntimeError("Promijenjen format FlixBus rezultata.")
            for r in results.values():
                if r.get("status") != "available" or (r.get("restrictions") or {}).get("sale_restriction"):
                    continue
                if stop(r["departure"])[0].date() != day:
                    continue
                rawlegs = r.get("legs") or []
                if not rawlegs:
                    raise RuntimeError("FlixBus nije poslao detalje dionica; ne prikazujem nepotpunu rutu.")
                legs = []
                for raw in rawlegs:
                    dep, os, oc = stop(raw["departure"])
                    arr, ds, dc = stop(raw["arrival"])
                    carrier = operators.get(raw.get("operator_id"), {}).get("label", "FlixBus partner")
                    legs.append(Leg(raw.get("means_of_transport", "bus"), os, ds, dep, arr, carrier, oc, dc))
                p = r.get("price") or {}
                fare = money(p.get("total_with_platform_fee") if data.get("platform_fee_in_price_required")
                             else p.get("total"))
                notes = message_texts(r.get("messages", []))
                if fare is None:
                    notes.append("Ukupna cijena sa obaveznim naknadama nije dostupna.")
                notes.append("Provjeri navedene doplate vozacu/stanici i pravila prtljaga.")
                out.append(Option(legs, fare, ["FlixBus"], [link], notes))
        return out


class GoogleFlights:
    name = "Google Flights"

    def __init__(self, adults=1, timeout=30, max_stops=2):
        self.adults, self.timeout, self.max_stops = adults, timeout, max_stops

    def search(self, origin: Place, dest: Place, day: date) -> list[Option]:
        if not origin.codes or not dest.codes:
            raise RuntimeError("Nije pronadjen aerodrom. Za avione unesi IATA kod ili grad iz kataloga.")
        # Catch per airport pair in Planner, preserving working airport results.
        if len(origin.codes) != 1 or len(dest.codes) != 1:
            raise ValueError("Interno: potrebno je pretraziti pojedinacni par aerodroma.")
        try:
            from fast_flights import FlightQuery, Passengers, create_query
            from fast_flights.integrations.base import FetchIntegration
            from primp import Client
        except ImportError as e:
            raise RuntimeError("Instaliraj zavisnosti iz zaglavlja programa (fast-flights==3.0).") from e
        timeout = self.timeout

        class Fetch(FetchIntegration):
            def fetch_html(self, q, /):
                client = Client(impersonate="chrome_145", timeout=timeout, connect_timeout=timeout)
                res = client.get("https://www.google.com/travel/flights", params=q.params())
                if res.status_code != 200:
                    raise RuntimeError(f"Google Flights HTTP {res.status_code}.")
                return res.text

        q = create_query(flights=[FlightQuery(date=day.isoformat(), from_airport=origin.codes[0],
                                             to_airport=dest.codes[0])],
                         trip="one-way", seat="economy", passengers=Passengers(adults=self.adults),
                         language="en-US", currency="EUR", max_stops=self.max_stops)
        results = self.decode_html(Fetch().fetch_html(q))
        return self.parse(results, day, origin.codes[0], dest.codes[0], q.url())

    @staticmethod
    def decode_html(html):
        """Read both Google result groups, retaining unpriced itineraries.

        Wire positions are also documented by the fast-flights parser:
        https://github.com/AWeirdDev/flights/blob/dev/fast_flights/parser.py
        Only schedule and fare fields are required, not carbon/alliance metadata.
        """
        from selectolax.lexbor import LexborHTMLParser
        script = LexborHTMLParser(html).css_first(r"script.ds\:1")
        message = ("Google nije poslao citljiv rezultat: moguca blokada ili promjena formata. "
                   "Ovo ne potvrdjuje da nema letova.")
        if script is None or "data:" not in script.text():
            raise RuntimeError(message)
        try:
            payload, _ = json.JSONDecoder().raw_decode(script.text().split("data:", 1)[1].lstrip())
            if not isinstance(payload, list) or len(payload) < 8:
                raise ValueError("Nepoznata struktura.")
            results, skipped = [], 0
            for section in payload[2:4]:
                if section is None:
                    continue
                entries = section[0] or []
                if not isinstance(entries, list):
                    raise ValueError("Nepoznata grupa rezultata.")
                for record in entries:
                    try:
                        offer = record[0]
                        fare = record[1][0] if len(record) > 1 and record[1] else []
                        amount = fare[1] if isinstance(fare, list) and len(fare) > 1 else None
                        legs = []
                        for leg in offer[2]:
                            detail = leg[22] if len(leg) > 22 and leg[22] else []
                            carrier = str(detail[3]) if len(detail) > 3 and detail[3] else " / ".join(offer[1])
                            number = "".join(str(v) for v in detail[:2] if v is not None)
                            legs.append(SimpleNamespace(
                                from_airport=SimpleNamespace(code=leg[3]),
                                to_airport=SimpleNamespace(code=leg[6]),
                                departure=SimpleNamespace(date=leg[20], time=leg[8] or []),
                                arrival=SimpleNamespace(date=leg[21], time=leg[10] or []),
                                carrier=(carrier + " " + number).strip()))
                        if not legs:
                            raise ValueError("Nedostaju dionice.")
                        results.append(SimpleNamespace(flights=legs, airlines=offer[1], price=amount))
                    except (TypeError, IndexError, ValueError):
                        skipped += 1
            if skipped and not results:
                raise ValueError("Nijedan rezultat nije citljiv.")
            if skipped:
                for result in results:
                    result.parser_note = f"Izvor je poslao i {skipped} necitljivih ponuda koje nijesu prikazane."
            return results
        except (TypeError, IndexError, ValueError) as e:
            raise RuntimeError(message) from e

    @staticmethod
    def parse(results, day, origin, dest, link):
        out = []

        def dt(value, code):
            a = airports().get(code)
            if not a or not a.get("tz"):
                raise ValueError(f"Nepoznata vremenska zona aerodroma {code}.")
            # Google omits zero minutes, e.g. time=[16] means 16:00.
            clock = list(value.time or []) + [0, 0]
            # The wire format uses null for zero, including midnight [null, 15].
            clock[0] = 0 if clock[0] is None else clock[0]
            clock[1] = 0 if clock[1] is None else clock[1]
            return datetime(*value.date, clock[0], clock[1], tzinfo=ZoneInfo(a["tz"]))

        for r in results:
            legs = []
            for f in r.flights:
                o, d = f.from_airport.code, f.to_airport.code
                legs.append(Leg("flight", o, d, dt(f.departure, o), dt(f.arrival, d),
                                getattr(f, "carrier", " / ".join(r.airlines)),
                                airports()[o]["city"], airports()[d]["city"]))
            if not legs or legs[0].origin != origin or legs[-1].destination != dest:
                continue
            if legs[0].departure.date() != day:
                continue
            notes = ["Provjeri prtljag, konacnu cijenu i da li su svi letovi na istoj karti."]
            if r.price is None:
                notes.append("Red letenja je dostupan, ali cijena nije objavljena u ovom rezultatu.")
            if getattr(r, "parser_note", ""):
                notes.append(r.parser_note)
            for a, b in zip(legs, legs[1:]):
                if a.destination != b.origin:
                    notes.append(f"Promjena aerodroma {a.destination} → {b.origin}: provjeri lokalni transfer.")
            out.append(Option(legs, money(r.price), ["Google Flights"], [link], notes))
        return out


def combine(a: Option, b: Option, min_minutes=240, max_wait=1440) -> Option | None:
    """Combine separately bookable offers. The station-airport transfer is NOT sold."""
    last, first = a.legs[-1], b.legs[0]
    if norm(last.destination_city) != norm(first.origin_city) or not last.destination_city:
        return None
    gap = minutes(last.arrival, first.departure)
    if not min_minutes <= gap <= max_wait:
        return None
    # A transfer may cross midnight or a timezone boundary; all comparisons use UTC.
    price = a.price + b.price if a.price is not None and b.price is not None else None
    note = (f"ODVOJENE KARTE: {last.destination} → {first.origin}; rezerva {duration_text(gap)}. "
            "Lokalni transfer nije provjeren niti ukljucen u cijenu/trajanje dionica. "
            "Provjeri da je ovaj transfer izvodljiv; propustena veza nije zasticena.")
    return Option(a.legs + b.legs, price, a.sources + b.sources, a.links + b.links,
                  list(dict.fromkeys(a.notes + b.notes + [note])), True)


def duration_text(n: int) -> str:
    return f"{n // 60}h {n % 60:02d}min"


def dedupe(options):
    found = {}
    for x in options:
        k = x.key()
        old = found.get(k)
        if old is None or (x.price is not None and (old.price is None or x.price < old.price)):
            found[k] = x
    return list(found.values())


class Planner:
    def __init__(self, args):
        self.args = args
        self.bus = FlixBus(args.adults, args.timeout)
        self.flights = GoogleFlights(args.adults, args.timeout, args.max_stops)
        self.cache, self.status = {}, []

    def search(self, mode, origin, dest, day):
        key = (mode, origin, dest, day)
        if key in self.cache:
            return self.cache[key]
        if mode == "flight" and (len(origin.codes) != 1 or len(dest.codes) != 1):
            options = []
            if not origin.codes or not dest.codes:
                self.status.append({"source": "Google Flights", "route": f"{origin.name} → {dest.name}",
                                    "date": day.isoformat(), "status": "error", "detail": "Nema IATA kodova."})
            for o in origin.codes:
                for d in dest.codes:
                    options.extend(self.search(mode, Place(origin.name, (o,)), Place(dest.name, (d,)), day))
            self.cache[key] = dedupe(options)
            return self.cache[key]
        provider = self.flights if mode == "flight" else self.bus
        print(f"  {provider.name}: {origin.name} → {dest.name}, {day:%d.%m.%Y}", flush=True)
        row = {"source": provider.name, "route": f"{origin.name} → {dest.name}",
               "date": day.isoformat(), "status": "ok"}
        try:
            out = provider.search(origin, dest, day)
            row["count"] = len(out)
        except Exception as e:
            out = []
            row.update(status="error", detail=f"{type(e).__name__}: {str(e)[:400]}")
            print(f"    NEDOSTUPNO: {row['detail']}", flush=True)
        self.status.append(row)
        self.cache[key] = out
        # Small sequential pause; no mass parallel scraping or browser/CAPTCHA bypass.
        time.sleep(0.2)
        return out

    def run(self, origin, dest, day):
        a = self.args
        options = []
        if a.mode in ("all", "flights"):
            options.extend(self.search("flight", origin, dest, day))
        if a.mode in ("all", "bus"):
            options.extend(self.search("bus", origin, dest, day))
        if a.mode == "all" and not a.no_mixed:
            # At most one separately purchased bus offer, before OR after the flight offer.
            for hub in hubs(origin, a.via_origin):
                if norm(hub.name) in (norm(origin.name), norm(dest.name)):
                    continue
                buses = self.search("bus", origin, hub, day)
                self.extend_connections(options, buses, "flight", hub, dest, day)
            for hub in hubs(dest, a.via_destination):
                if norm(hub.name) in (norm(origin.name), norm(dest.name)):
                    continue
                planes = self.search("flight", origin, hub, day)
                self.extend_connections(options, planes, "bus", hub, dest, day)
        options = [x for x in dedupe(options) if x.duration <= a.max_hours * 60]
        if a.sort == "duration":
            options.sort(key=lambda x: (x.duration, x.price if x.price is not None else Decimal("Infinity")))
        elif a.sort == "departure":
            options.sort(key=lambda x: instant(x.legs[0].departure))
        else:
            options.sort(key=lambda x: (x.price if x.price is not None else Decimal("Infinity"), x.duration))
        return options

    def extend_connections(self, output, first_offers, second_mode, hub, dest, start_day):
        # Dates depend on actual arrival, not on the initial departure date.
        # Search each relevant date once through the request cache.
        days = set()
        for x in first_offers:
            local = x.legs[-1].arrival
            begin = local + timedelta(minutes=self.args.min_transfer)
            end = local + timedelta(hours=self.args.max_wait_hours)
            d = begin.date()
            while d <= end.date():
                if 0 <= (d - start_day).days <= self.args.connection_days:
                    days.add(d)
                d += timedelta(days=1)
        for d in sorted(days):
            second_offers = self.search(second_mode, hub, dest, d)
            for a in first_offers:
                for b in second_offers:
                    route = combine(a, b, self.args.min_transfer, self.args.max_wait_hours * 60)
                    if route and route.duration <= self.args.max_hours * 60:
                        output.append(route)


def hubs(place, override):
    names = override.split(",") if override is not None else NEARBY.get(place.name, [])
    return list(dict.fromkeys(resolve(n) for n in names if n.strip()))


def serialize(value):
    if isinstance(value, (datetime, date)):
        return value.isoformat()
    if isinstance(value, Decimal):
        return str(value)
    raise TypeError(type(value).__name__)


def price_text(option):
    if option.price is None:
        return "Cijena nije dostupna"
    return f"{option.price:.2f} EUR" + (" + lokalni transfer i moguce doplate" if option.mixed else " + moguce doplate")


def show(options, limit):
    for i, x in enumerate(options[:limit], 1):
        print(f"\n{i}. {x.label} | {price_text(x)} | ukupno {duration_text(x.duration)}")
        for j, leg in enumerate(x.legs):
            if j:
                prev = x.legs[j - 1]
                print(f"   Cekanje/transfer: {duration_text(minutes(prev.arrival, leg.departure))}")
            print(f"   {leg.mode}: {leg.origin} → {leg.destination} | "
                  f"{leg.departure:%d.%m. %H:%M %z} → {leg.arrival:%d.%m. %H:%M %z} | {leg.carrier}")
        for note in x.notes:
            print(f"   Napomena: {note}")
        for link in dict.fromkeys(x.links):
            print(f"   Provjera/kupovina: {link}")


def save_report(options, status, origin, dest, day, args):
    base = Path(args.output)
    base.parent.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(UTC).isoformat()
    payload = {"checked_at": stamp, "origin": origin.name, "destination": dest.name,
               "date": day.isoformat(), "adults": args.adults, "currency": "EUR",
               "coverage": "Google Flights + FlixBus; nije potpuna lista svih mogucih putovanja.",
               "scope": {"via_origin": [x.name for x in hubs(origin, args.via_origin)],
                         "via_destination": [x.name for x in hubs(dest, args.via_destination)],
                         "max_flight_stops": args.max_stops, "max_hours": args.max_hours,
                         "min_mixed_transfer_minutes": args.min_transfer,
                         "max_mixed_wait_hours": args.max_wait_hours,
                         "connection_days": args.connection_days},
               "status": status, "options": [asdict(x) for x in options]}
    json_path, html_path = Path(str(base) + ".json"), Path(str(base) + ".html")
    json_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, default=serialize), encoding="utf-8")
    cards = []
    for i, x in enumerate(options, 1):
        rows = []
        for j, leg in enumerate(x.legs):
            if j:
                prev = x.legs[j - 1]
                rows.append(f'<p class="wait">Cekanje / transfer: {duration_text(minutes(prev.arrival, leg.departure))}</p>')
            rows.append(f'<div class="leg"><b>{escape(leg.mode.upper())} · {escape(leg.origin)} → '
                        f'{escape(leg.destination)}</b><br>{leg.departure:%d.%m.%Y %H:%M %z} → '
                        f'{leg.arrival:%d.%m.%Y %H:%M %z}<br>{escape(leg.carrier)}</div>')
        notes = "".join(f"<li>{escape(n)}</li>" for n in x.notes)
        links = " ".join(f'<a target="_blank" rel="noopener noreferrer" href="{escape(u, quote=True)}">'
                         f'Provjeri ponudu {j}</a>' for j, u in enumerate(dict.fromkeys(x.links), 1))
        cards.append(f'<article data-kind="{"mixed" if x.mixed else x.legs[0].mode}">'
                     f'<h2>{i}. {escape(x.label)}</h2><p class="price">{escape(price_text(x))}</p>'
                     f'<p>Ukupno {duration_text(x.duration)} · {len(x.legs)-1} presjedanja</p>'
                     f'{"".join(rows)}<details><summary>Napomene i doplate</summary><ul>{notes}</ul>'
                     f'</details><p>{links}</p></article>')
    statuses = "".join(f'<li>{escape(s["source"])} · {escape(s["route"])} · {s["date"]}: '
                       f'{escape(s.get("detail", str(s.get("count", 0)) + " rezultata"))}</li>' for s in status)
    html = '''<!doctype html><html lang="sr-Latn"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Putovanja</title>
<style>body{font:16px system-ui;background:#f0f4f8;color:#172637;margin:0}main{max-width:960px;margin:auto;padding:28px}
h1{font-size:30px}article{background:white;border:1px solid #dce5ed;border-radius:16px;padding:24px;margin:20px 0}
h2{font-size:19px}.price{font-size:25px;font-weight:700;color:#087564}.leg{padding:14px;background:#f4f7fb;border-radius:9px;margin:8px 0}
.wait{color:#795600;margin:10px}.notice{padding:18px;background:#fff4d9;border-radius:12px}a{color:#145aa1;display:inline-block;margin:8px 18px 0 0}
select{padding:10px;font:inherit}summary{cursor:pointer}li{margin:8px 0}small{color:#526579}</style><main>'''
    html += (f'<h1>{escape(origin.name)} → {escape(dest.name)}</h1><p>{day:%d.%m.%Y} · '
             f'{args.adults} odraslih · {len(options)} opcija</p><p class="notice">'
             'Cijene su za izabrani broj putnika, prema izvorima u trenutku provjere. '
             'Prtljag i navedene doplate mogu se dodatno placati. Kombinacije imaju odvojene karte; '
             'lokalni transfer nije provjeren ni ukljucen. Provjeri sve dionice prije kupovine. '
             'Obuhvat: Google Flights i FlixBus, uz ogranicenja pretrage. Nije garantovana potpuna lista.</p>'
             f'<small>Provjereno (UTC): {stamp}</small><p><label>Prikazi: <select id="filter">'
             '<option value="all">Sve</option><option value="flight">Avioni</option>'
             '<option value="bus">Autobusi</option><option value="mixed">Kombinacije</option></select></label></p>')
    html += "".join(cards) if cards else (
        '<p>Pretraga nije dala prikazive opcije. Neki izvori nijesu uspjesno provjereni; '
        'ovo ne znaci da nema putovanja. Detalji su u statusu ispod.</p>'
        if any(s['status'] == 'error' for s in status) else
        '<p>Nema pronadjenih opcija u izabranim izvorima i ogranicenjima pretrage.</p>')
    html += f'<details><summary>Status svih pretraga</summary><ul>{statuses}</ul></details></main>'
    html += '''<script>document.getElementById('filter').onchange=function(){document.querySelectorAll('article').forEach(x=>{x.hidden=this.value!=='all'&&x.dataset.kind!==this.value})}</script></html>'''
    html_path.write_text(html, encoding="utf-8")
    return html_path, json_path


def parser():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--from", dest="origin")
    p.add_argument("--to", dest="destination")
    p.add_argument("--date", dest="day")
    p.add_argument("--adults", type=int, default=1)
    p.add_argument("--mode", choices=["all", "flights", "bus"], default="all")
    p.add_argument("--no-mixed", action="store_true", help="Samo rezultati izvora, bez spajanja odvojenih karata")
    p.add_argument("--via-origin", help="Gradovi za autobus→avion, razdvojeni zarezom; prazno iskljucuje")
    p.add_argument("--via-destination", help="Gradovi za avion→autobus, razdvojeni zarezom; prazno iskljucuje")
    p.add_argument("--max-stops", type=int, default=2, help="Najvise avionskih presjedanja (0–5)")
    p.add_argument("--min-transfer", type=int, default=240, help="Minimalna rezerva autobus/aerodrom, minuti")
    p.add_argument("--max-wait-hours", type=int, default=24)
    p.add_argument("--connection-days", type=int, default=3, help="Najkasniji dan polaska druge ponude: pocetni datum + N")
    p.add_argument("--max-hours", type=int, default=96, help="Najduze ukupno putovanje")
    p.add_argument("--timeout", type=float, default=30)
    p.add_argument("--sort", choices=["price", "duration", "departure"], default="price")
    p.add_argument("--limit", type=int, default=15, help="Broj opcija u terminalu; fajlovi sadrze sve")
    p.add_argument("--output", default="rezultati", help="Putanja bez ekstenzije za HTML i JSON")
    return p


def main(argv=None):
    p = parser()
    args = p.parse_args(argv)
    try:
        if not 1 <= args.adults <= 9:
            raise ValueError("Broj odraslih mora biti izmedju 1 i 9.")
        if not 0 <= args.max_stops <= 5 or not 0 <= args.connection_days <= 7:
            raise ValueError("Presjedanja: 0–5; dodatni dani: 0–7.")
        if (args.min_transfer < 1 or args.max_wait_hours * 60 < args.min_transfer
                or args.max_hours < 1 or not 0 < args.timeout <= 120 or args.limit < 1):
            raise ValueError("Neispravna ogranicenja vremena, trajanja ili prikaza.")
        origin = resolve(args.origin or input("Odakle (grad ili IATA, npr. Podgorica): "))
        dest = resolve(args.destination or input("Gdje (grad ili IATA, npr. Kopenhagen): "))
        day = parse_date(args.day or input("Datum polaska (npr. 26.11.2026): "))
        if not origin.name or not dest.name or norm(origin.name) == norm(dest.name):
            raise ValueError("Unesi dva razlicita grada.")
        # Use the origin city's date when known, otherwise the user's regional default.
        tz = airports().get(origin.codes[0], {}).get("tz", "Europe/Podgorica") if origin.codes else "Europe/Podgorica"
        if day < datetime.now(ZoneInfo(tz)).date():
            raise ValueError("Datum polaska je u proslosti.")
        print(f"\n{origin.name} → {dest.name} | {day:%d.%m.%Y} | {args.adults} odraslih | EUR")
        print("Pretraga: Google Flights + FlixBus. Cijene i dostupnost mogu se promijeniti.")
        if args.mode == "all" and not args.no_mixed:
            print("Autobus→avion preko:", ", ".join(x.name for x in hubs(origin, args.via_origin)) or "nema")
            print("Avion→autobus preko:", ", ".join(x.name for x in hubs(dest, args.via_destination)) or "nema")
        planner = Planner(args)
        options = planner.run(origin, dest, day)
        show(options, args.limit)
        html_path, json_path = save_report(options, planner.status, origin, dest, day, args)
        errors = sum(s["status"] == "error" for s in planner.status)
        print(f"\nPronadjeno {len(options)} opcija. Neuspjelih pretraga: {errors}.")
        print(f"Sve opcije i status izvora: {html_path.resolve()}\nPodaci: {json_path.resolve()}")
        return 2 if not options and errors else 0
    except (ValueError, RuntimeError, EOFError) as e:
        print(f"GRESKA: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nPretraga prekinuta.", file=sys.stderr)
        sys.exit(130)
