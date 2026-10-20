#!/usr/bin/env python3
"""Pretraga putovanja: avioni, autobusi, presjedanja i kombinacije.

Python 3.11+; instalacija (jednom):
    python -m pip install fast-flights==3.0 airportsdata==20260905 tzdata typing_extensions certifi

Pokretanje:
    python letovi.py                 # forma u browseru: gradovi + kalendar
    python letovi.py --cli           # unos u terminalu
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
import secrets
import threading
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
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
    def __init__(self, args, on_progress=None):
        self.args = args
        self.on_progress = on_progress
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
        progress = f"{provider.name}: {origin.name} → {dest.name}, {day:%d.%m.%Y}"
        print(f"  {progress}", flush=True)
        if self.on_progress:
            self.on_progress(progress)
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
        kind = "mixed" if x.mixed else ("flight" if x.legs[0].mode == "flight" else "bus")
        cards.append(f'<article data-kind="{kind}" data-duration="{x.duration}" '
                     f'data-price="{x.price if x.price is not None else ""}" '
                     f'data-departure="{instant(x.legs[0].departure).timestamp()}">'
                     f'<h2><span class="rank">{i}</span>. {escape(x.label)}</h2><p class="price">{escape(price_text(x))}</p>'
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
select{padding:10px;font:inherit;max-width:100%}.controls{display:flex;gap:16px;flex-wrap:wrap;align-items:end}
.controls label{display:grid;gap:6px}summary{cursor:pointer}li{margin:8px 0}small{color:#526579}</style><main>'''
    html += (f'<h1>{escape(origin.name)} → {escape(dest.name)}</h1><p>{day:%d.%m.%Y} · '
             f'{args.adults} odraslih · {len(options)} opcija</p><p class="notice">'
             'Cijene su za izabrani broj putnika, prema izvorima u trenutku provjere. '
             'Prtljag i navedene doplate mogu se dodatno placati. Kombinacije imaju odvojene karte; '
             'lokalni transfer nije provjeren ni ukljucen. Provjeri sve dionice prije kupovine. '
             'Obuhvat: Google Flights i FlixBus, uz ogranicenja pretrage. Nije garantovana potpuna lista.</p>'
             f'<small>Provjereno (UTC): {stamp}</small><p id="visible-count" aria-live="polite"></p>'
             '<div class="controls"><label>Prikaži <select id="filter">'
             '<option value="all">Sve</option><option value="flight">Avioni</option>'
             '<option value="bus">Autobusi</option><option value="mixed">Kombinacije</option></select></label>'
             '<label>Sortiraj <select id="sort">'
             f'<option value="duration" {"selected" if args.sort == "duration" else ""}>Trajanje: najkraće prvo</option>'
             f'<option value="price" {"selected" if args.sort == "price" else ""}>Cijena: najniža prvo</option>'
             f'<option value="departure" {"selected" if args.sort == "departure" else ""}>Polazak: najranije prvo</option>'
             '</select></label></div><p><small>Trajanje uključuje čekanja i presjedanja. '
             'Ponude bez cijene su na kraju pri sortiranju po cijeni.</small></p>')
    html += '<section id="options">'
    html += "".join(cards) if cards else (
        '<p>Pretraga nije dala prikazive opcije. Neki izvori nijesu uspjesno provjereni; '
        'ovo ne znaci da nema putovanja. Detalji su u statusu ispod.</p>'
        if any(s['status'] == 'error' for s in status) else
        '<p>Nema pronadjenih opcija u izabranim izvorima i ogranicenjima pretrage.</p>')
    html += '</section><p id="empty-filter" hidden>Nema opcija za ovaj tip prevoza. Izaberi „Sve“.</p>'
    html += f'<details><summary>Status svih pretraga</summary><ul>{statuses}</ul></details></main>'
    html += '''<script>
const container=document.getElementById('options'),filter=document.getElementById('filter'),sort=document.getElementById('sort');
function value(card,key){const raw=card.dataset[key];return raw===''||raw===undefined?Infinity:Number(raw)}
function update(){
 const cards=Array.from(container.querySelectorAll('article'));
 cards.sort((a,b)=>{const x=value(a,sort.value),y=value(b,sort.value);
  return (x<y?-1:x>y?1:0)||value(a,'duration')-value(b,'duration')||value(a,'departure')-value(b,'departure')});
 let visible=0;
 cards.forEach(card=>{container.appendChild(card);card.hidden=filter.value!=='all'&&card.dataset.kind!==filter.value;
  if(!card.hidden){visible++;card.querySelector('.rank').textContent=visible}});
 document.getElementById('visible-count').textContent=`Prikazano ${visible} od ${cards.length} opcija`;
 document.getElementById('empty-filter').hidden=visible!==0||cards.length===0;
}
filter.addEventListener('change',update);sort.addEventListener('change',update);update();
</script></html>'''
    html_path.write_text(html, encoding="utf-8")
    return html_path, json_path


def parser():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--from", dest="origin")
    p.add_argument("--gui", action="store_true", help="Forma sa kalendarom i prijedlozima gradova u browseru")
    p.add_argument("--cli", action="store_true", help="Unos u terminalu umjesto forme")
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


def validate_trip(args):
    if not 1 <= args.adults <= 9:
        raise ValueError("Broj odraslih mora biti između 1 i 9.")
    if args.mode not in ("all", "flights", "bus") or args.sort not in ("price", "duration", "departure"):
        raise ValueError("Nepoznat tip prevoza ili sortiranja.")
    if not 0 <= args.max_stops <= 5 or not 0 <= args.connection_days <= 7:
        raise ValueError("Presjedanja: 0–5; dodatni dani: 0–7.")
    if (args.min_transfer < 1 or args.max_wait_hours * 60 < args.min_transfer
            or args.max_hours < 1 or not 0 < args.timeout <= 120 or args.limit < 1):
        raise ValueError("Neispravna ograničenja vremena, trajanja ili prikaza.")
    if not args.origin or not args.destination or not args.day:
        raise ValueError("Unesi polazište, odredište i datum.")
    if len(args.origin) > 100 or len(args.destination) > 100:
        raise ValueError("Naziv grada je predugačak.")
    origin, dest, day = resolve(args.origin), resolve(args.destination), parse_date(args.day)
    if not origin.name or not dest.name or norm(origin.name) == norm(dest.name):
        raise ValueError("Unesi dva različita grada.")
    tz = airports().get(origin.codes[0], {}).get("tz", "Europe/Podgorica") if origin.codes else "Europe/Podgorica"
    if day < datetime.now(ZoneInfo(tz)).date():
        raise ValueError("Datum polaska je u prošlosti.")
    return origin, dest, day


def form_html(args, token):
    today = datetime.now(ZoneInfo("Europe/Podgorica")).date()
    tomorrow = today + timedelta(days=1)
    local_names = {"Belgrade": "Beograd", "Copenhagen": "Kopenhagen", "Vienna": "Beč",
                   "Budapest": "Budimpešta", "Rome": "Rim", "Paris": "Pariz", "Munich": "Minhen",
                   "Zurich": "Cirih", "Prague": "Prag", "Warsaw": "Varšava", "Brussels": "Brisel",
                   "Athens": "Atina", "Barcelona": "Barselona", "Stockholm": "Stokholm"}
    suggestions = []
    for city, codes in CATALOG.items():
        label = local_names.get(city, city)
        suggestions.append(f'<option value="{escape(label, quote=True)}">{escape(city)} · {", ".join(codes)}</option>')
        if label != city:
            suggestions.append(f'<option value="{escape(city, quote=True)}">{escape(label)} · {", ".join(codes)}</option>')
        for code in codes:
            suggestions.append(f'<option value="{code}">{escape(label)}</option>')
    selected_day = parse_date(args.day).isoformat() if args.day else tomorrow.isoformat()
    page = r'''<!doctype html><html lang="sr-Latn"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Pronađi putovanje</title>
<style>body{font:16px system-ui;margin:0;background:#f0f4f8;color:#172637}main{max-width:960px;margin:auto;padding:30px 20px}
h1{font-size:34px;margin-bottom:8px}.intro{color:#526579;margin:0 0 24px}form{background:white;padding:26px;border:1px solid #dce5ed;border-radius:18px}
.route{display:grid;grid-template-columns:1fr 44px 1fr;gap:14px;align-items:end}.grid{display:grid;grid-template-columns:1fr 1fr;gap:18px;margin-top:20px}
label.field{display:grid;gap:8px;font-weight:600}input,select,button{font:inherit;box-sizing:border-box}input,select{border:1px solid #b9c8d7;border-radius:9px;padding:12px;width:100%;background:white;color:#172637}
input:focus,select:focus{outline:3px solid #b9e4df;border-color:#087564}button{cursor:pointer;border:0;border-radius:9px;padding:13px;background:#e7eef5;color:#172637}
button.primary{background:#087564;color:white;padding:14px 24px;font-weight:700}button:disabled{opacity:.55;cursor:wait}.quick{display:flex;gap:10px;margin-top:10px}.quick button{padding:7px 12px;font-size:14px}
.check{display:flex;gap:10px;align-items:center;margin:22px 0}.check input{width:auto}.actions{display:flex;gap:16px;align-items:center;flex-wrap:wrap}
.help{font-size:14px;color:#526579}.status{background:white;border-radius:12px;padding:18px;margin:22px 0;white-space:pre-wrap}a{color:#075f51;font-weight:600}
#results{width:100%;min-height:1000px;border:0;border-radius:12px;background:white;margin-top:18px}[hidden]{display:none!important}
@media(max-width:600px){.route{grid-template-columns:1fr}.route button{justify-self:center}.grid{grid-template-columns:1fr}form{padding:18px}h1{font-size:28px}}</style>
<main><h1>Gdje putujemo?</h1><p class="intro">Avioni, autobusi i veze sa presjedanjem — jedna pretraga.</p>
<form id="search-form"><div class="route">
<label class="field">Odakle<input id="origin" name="origin" list="cities" required maxlength="100" autocomplete="off" placeholder="npr. Podgorica" value="__ORIGIN__"></label>
<button id="swap" type="button" aria-label="Zamijeni polazište i odredište" title="Zamijeni gradove">⇄</button>
<label class="field">Gdje<input id="destination" name="destination" list="cities" required maxlength="100" autocomplete="off" placeholder="npr. Beograd ili Kopenhagen" value="__DEST__"></label>
</div><datalist id="cities">__CITIES__</datalist>
<p class="help">Počni da kucaš grad i izaberi prijedlog. Možeš unijeti i aerodromski kod, npr. TGD.</p>
<div class="grid"><div><label class="field">Datum polaska<input id="day" name="day" type="date" required min="__TODAY__" value="__DAY__"></label>
<div class="quick"><button type="button" data-day="__TODAY__">Danas</button><button type="button" data-day="__TOMORROW__">Sjutra</button></div></div>
<label class="field">Broj odraslih<select id="adults" name="adults">__ADULTS__</select></label>
<label class="field">Prevoz<select id="mode" name="mode"><option value="all">Avioni i autobusi</option><option value="flights">Samo avioni</option><option value="bus">Samo autobusi</option></select></label>
<label class="field">Prvo prikaži<select id="initial-sort" name="sort"><option value="duration">Najkraće putovanje</option><option value="price">Najnižu cijenu</option><option value="departure">Najraniji polazak</option></select></label></div>
<label class="check"><input id="mixed" type="checkbox" __CHECKED__> Uključi i kombinacije autobusa i aviona</label>
<div class="actions"><button class="primary" id="submit" type="submit">Pronađi putovanja</button><span class="help">U rezultatima možeš promijeniti redosljed bez nove pretrage.</span></div></form>
<div id="status" class="status" role="status" aria-live="polite" hidden></div>
<p id="result-links" hidden><a id="open-results" target="_blank" rel="noopener">Otvori rezultate u novom prozoru ↗</a></p>
<iframe id="results" title="Rezultati putovanja" hidden></iframe>
<p class="help">Prozor Python programa treba da ostane otvoren dok koristiš pretragu.</p></main>
<script>
const token=__TOKEN__,form=document.getElementById('search-form'),button=document.getElementById('submit'),statusBox=document.getElementById('status');
let polling=false;
document.getElementById('mode').value=__MODE__;
document.getElementById('initial-sort').value=__SORT__;
function syncMixed(){document.getElementById('mixed').disabled=document.getElementById('mode').value!=='all'}
document.getElementById('mode').onchange=syncMixed;syncMixed();
document.getElementById('swap').onclick=()=>{const a=document.getElementById('origin'),b=document.getElementById('destination');[a.value,b.value]=[b.value,a.value]};
document.querySelectorAll('[data-day]').forEach(b=>b.onclick=()=>{document.getElementById('day').value=b.dataset.day});
function message(text){statusBox.hidden=false;statusBox.textContent=text}
function busy(value){button.disabled=value;button.textContent=value?'Pretraga je u toku…':'Pronađi putovanja'}
async function api(path,options={}){const res=await fetch(path,{...options,headers:{'Content-Type':'application/json','X-Search-Token':token}});
 const data=await res.json();if(!res.ok)throw new Error(data.error||'Zahtjev nije uspio.');return data}
function poll(){
 if(polling)return;polling=true;
 const tick=async()=>{try{const s=await api('/api/status');
  if(s.state==='running'){busy(true);message('Tražim putovanja…\n'+s.progress);setTimeout(tick,1000);return}
  busy(false);polling=false;
  if(s.state==='error'){message(s.error);return}
  if(s.state==='done'){message(`Pronađeno ${s.count} opcija. Neuspjelih pretraga: ${s.errors}.`);
   const url='/results?token='+encodeURIComponent(token)+'&job='+s.job;
   document.getElementById('results').src=url;document.getElementById('results').hidden=false;
   document.getElementById('open-results').href=url;document.getElementById('result-links').hidden=false}
 }catch(e){polling=false;busy(false);message('Veza sa programom je prekinuta. Provjeri da li je Python program i dalje otvoren.')}};
 tick();
}
form.onsubmit=async event=>{event.preventDefault();busy(true);document.getElementById('results').hidden=true;document.getElementById('result-links').hidden=true;
 try{const payload=Object.fromEntries(new FormData(form));payload.no_mixed=!document.getElementById('mixed').checked;
  await api('/api/search',{method:'POST',body:JSON.stringify(payload)});message('Pretraga je pokrenuta…');poll();
 }catch(e){busy(false);message(e.message)}};
poll();
</script></html>'''
    replacements = {
        "__ORIGIN__": escape(args.origin or "Podgorica", quote=True),
        "__DEST__": escape(args.destination or "", quote=True), "__CITIES__": "".join(suggestions),
        "__TODAY__": today.isoformat(), "__TOMORROW__": tomorrow.isoformat(), "__DAY__": selected_day,
        "__ADULTS__": "".join(f'<option value="{n}" {"selected" if n == args.adults else ""}>{n}</option>' for n in range(1, 10)),
        "__CHECKED__": "" if args.no_mixed else "checked", "__TOKEN__": json.dumps(token),
        "__MODE__": json.dumps(args.mode), "__SORT__": json.dumps(args.sort),
    }
    # Substitute once, so user-entered text cannot accidentally become a template token.
    import re
    return re.sub(r"__[A-Z_]+__", lambda match: replacements[match.group()], page)


class LocalSearch:
    def __init__(self, args):
        self.args, self.lock = args, threading.Lock()
        self.token = secrets.token_urlsafe(32)
        self.data = {"state": "idle", "progress": ""}
        self.result_path = None

    def snapshot(self):
        with self.lock:
            return dict(self.data)

    def progress(self, text):
        with self.lock:
            self.data["progress"] = text

    def start(self, payload):
        if not isinstance(payload, dict):
            raise ValueError("Neispravan unos.")
        args = argparse.Namespace(**vars(self.args))
        for key in ("origin", "destination", "day", "mode", "sort"):
            value = payload.get(key)
            if not isinstance(value, str):
                raise ValueError("Popuni gradove, datum i tip pretrage.")
            setattr(args, key, value.strip())
        args.adults = int(payload.get("adults", 1))
        args.no_mixed = payload.get("no_mixed", False) is True
        origin, dest, day = validate_trip(args)
        with self.lock:
            if self.data["state"] == "running":
                raise ValueError("Jedna pretraga je već u toku. Sačekaj rezultate.")
            self.data = {"state": "running", "progress": "Pripremam pretragu…", "job": secrets.token_hex(8)}
            self.result_path = None
        threading.Thread(target=self.run, args=(args, origin, dest, day), daemon=True).start()

    def run(self, args, origin, dest, day):
        try:
            planner = Planner(args, on_progress=self.progress)
            options = planner.run(origin, dest, day)
            html_path, _ = save_report(options, planner.status, origin, dest, day, args)
            with self.lock:
                self.result_path = html_path
                self.data.update(state="done", count=len(options),
                                 errors=sum(s["status"] == "error" for s in planner.status))
        except Exception as e:
            with self.lock:
                self.data.update(state="error", error=f"Pretraga nije završena: {e}")


def make_local_server(args):
    app = LocalSearch(args)

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def reply(self, code, content, content_type="application/json; charset=utf-8"):
            if isinstance(content, dict):
                content = json.dumps(content, ensure_ascii=False)
            data = content.encode("utf-8") if isinstance(content, str) else content
            self.send_response(code)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.end_headers()
            self.wfile.write(data)

        def allowed(self):
            return self.headers.get("Host") == f"127.0.0.1:{self.server.server_port}"

        def do_GET(self):
            from urllib.parse import urlsplit, parse_qs
            if not self.allowed():
                return self.reply(403, {"error": "Pristup nije dozvoljen."})
            url = urlsplit(self.path)
            if url.path == "/":
                return self.reply(200, form_html(args, app.token), "text/html; charset=utf-8")
            if url.path == "/api/status" and self.headers.get("X-Search-Token") == app.token:
                return self.reply(200, app.snapshot())
            if url.path == "/results" and parse_qs(url.query).get("token") == [app.token]:
                with app.lock:
                    path = app.result_path
                if path is not None:
                    return self.reply(200, path.read_bytes(), "text/html; charset=utf-8")
            self.reply(404, {"error": "Stranica nije dostupna."})

        def do_POST(self):
            if (not self.allowed() or self.path != "/api/search"
                    or self.headers.get("X-Search-Token") != app.token):
                return self.reply(403, {"error": "Zahtjev nije dozvoljen."})
            try:
                size = int(self.headers.get("Content-Length", "0"))
                if not 0 < size <= 8192:
                    raise ValueError("Neispravan unos.")
                app.start(json.loads(self.rfile.read(size)))
                self.reply(202, {"status": "started"})
            except (ValueError, TypeError, RuntimeError) as e:
                self.reply(400, {"error": str(e)})

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    return server, app


def launch_form(args):
    server, _ = make_local_server(args)
    url = f"http://127.0.0.1:{server.server_port}/"
    print(f"\nForma za putovanja: {url}\nZa izlaz pritisni Ctrl+C u ovom prozoru.", flush=True)
    threading.Timer(0.3, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    finally:
        server.server_close()
    return 0


def main(argv=None):
    p = parser()
    argv = sys.argv[1:] if argv is None else argv
    args = p.parse_args(argv)
    try:
        if args.gui or (not argv and not args.cli):
            return launch_form(args)
        args.origin = args.origin or input("Odakle (grad ili IATA, npr. Podgorica): ")
        args.destination = args.destination or input("Gdje (grad ili IATA, npr. Kopenhagen): ")
        args.day = args.day or input("Datum polaska (npr. 26.11.2026): ")
        origin, dest, day = validate_trip(args)
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
