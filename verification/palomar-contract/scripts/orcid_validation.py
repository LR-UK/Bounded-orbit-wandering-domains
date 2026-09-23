"""Bounded validation of ORCID iDs declared in repository metadata.

This checks that an identifier names a current record in the ORCID Registry.
It does not authenticate the record holder and must never be described as an
authorship or identity proof.
"""

from __future__ import annotations

import datetime as dt
import json
import re
from collections.abc import Callable, Iterable
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

from scripts.verification_errors import VerificationError

ORCID_API_BASE = "https://pub.orcid.org/v3.0"
ORCID_PUBLIC_BASE = "https://orcid.org"
ORCID_RESPONSE_LIMIT = 1024 * 1024
ORCID_TIMEOUT_SECONDS = 15
MAX_DISTINCT_ORCIDS = 100
ORCID_IDENTIFIER_PATTERN = r"[0-9]{4}-[0-9]{4}-[0-9]{4}-[0-9]{3}[0-9X]"
ORCID_RE = re.compile(rf"{ORCID_IDENTIFIER_PATTERN}\Z")
ORCID_URL_RE = re.compile(
    rf"{re.escape(ORCID_PUBLIC_BASE)}/"
    rf"(?P<identifier>{ORCID_IDENTIFIER_PATTERN})/?\Z"
)
ORCID_IN_TEXT_RE = re.compile(
    r"(?<![0-9])(?:https?://(?:www\.)?orcid\.org/)?"
    r"[0-9]{4}-[0-9]{4}-[0-9]{4}-[0-9]{3}[0-9X](?![0-9A-Za-z])",
    re.IGNORECASE,
)


def canonical_identifier(value: str) -> str | None:
    """Return the bare iD for an accepted bare iD or canonical ORCID URL."""
    if ORCID_RE.fullmatch(value):
        return value
    match = ORCID_URL_RE.fullmatch(value)
    return match.group("identifier") if match is not None else None


def contains_identifier(value: str) -> bool:
    """Return whether free text contains something shaped like an ORCID iD."""
    return ORCID_IN_TEXT_RE.search(value) is not None


def valid_checksum(identifier: str) -> bool:
    """Return whether a canonical ORCID iD has its ISO 7064 check digit."""
    if not ORCID_RE.fullmatch(identifier):
        return False
    compact = identifier.replace("-", "")
    total = 0
    for character in compact[:15]:
        total = (total + int(character)) * 2
    result = (12 - total % 11) % 11
    expected = "X" if result == 10 else str(result)
    return compact[-1] == expected


def _unavailable(message: str, *, detail: str | None = None) -> VerificationError:
    return VerificationError(
        message,
        code="orcid.registry_unavailable",
        owner="palomar",
        retryable=True,
        next_action=(
            "Do not change the repository. Palomar should retry once the ORCID Registry "
            "is available."
        ),
        detail=detail,
    )


def _not_found(identifier: str) -> VerificationError:
    return VerificationError(
        f"formalization.yaml ORCID iD {identifier} does not name a current ORCID record",
        code="formalization.orcid_not_found",
        field="orcid",
        next_action=(
            "Correct or remove that ORCID iD, commit the metadata change, then make a new "
            "submission using the new commit SHA."
        ),
    )


def validate_record(
    identifier: str,
    *,
    open_url: Callable[..., Any] = urlopen,
) -> None:
    """Require one canonical iD to resolve to the same current ORCID record."""
    request = Request(
        f"{ORCID_API_BASE}/{identifier}/record",
        headers={
            "Accept": "application/vnd.orcid+json",
            "User-Agent": "palomar-submission/1",
        },
        method="GET",
    )
    try:
        response = open_url(request, timeout=ORCID_TIMEOUT_SECONDS)
    except HTTPError as error:
        status = error.code
        error.close()
        if status in {400, 404, 410}:
            raise _not_found(identifier) from None
        raise _unavailable(
            f"the ORCID Registry could not validate {identifier}",
            detail=f"ORCID returned HTTP {status}.",
        ) from None
    except (TimeoutError, URLError, OSError) as error:
        raise _unavailable(
            f"the ORCID Registry could not be reached while validating {identifier}",
            detail=str(error),
        ) from None

    try:
        with response:
            status = getattr(response, "status", 200)
            if status != 200:
                raise _unavailable(
                    f"the ORCID Registry returned an unexpected response for {identifier}",
                    detail=f"ORCID returned HTTP {status}.",
                )
            raw = response.read(ORCID_RESPONSE_LIMIT + 1)
    except (TimeoutError, URLError, OSError) as error:
        raise _unavailable(
            f"the ORCID Registry response ended while validating {identifier}",
            detail=str(error),
        ) from None
    if len(raw) > ORCID_RESPONSE_LIMIT:
        raise _unavailable(
            f"the ORCID Registry returned an oversized record for {identifier}"
        )
    try:
        record = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise _unavailable(
            f"the ORCID Registry returned an unreadable record for {identifier}",
            detail=str(error),
        ) from None
    returned = record.get("orcid-identifier") if isinstance(record, dict) else None
    returned_id = returned.get("path") if isinstance(returned, dict) else None
    if returned_id != identifier:
        if isinstance(returned_id, str):
            raise VerificationError(
                f"formalization.yaml ORCID iD {identifier} resolves to {returned_id}; "
                "use the current identifier",
                code="formalization.orcid_superseded",
                field="orcid",
                next_action=(
                    f"Replace {identifier} with {returned_id}, commit the metadata change, "
                    "then make a new submission using the new commit SHA."
                ),
            )
        raise _unavailable(
            f"the ORCID Registry response did not identify the record for {identifier}"
        )
    history = record.get("history") if isinstance(record, dict) else None
    if not isinstance(history, dict):
        raise _unavailable(
            f"the ORCID Registry response did not describe the status of {identifier}"
        )
    if history.get("deactivation-date") is not None:
        raise _not_found(identifier)


def validate_records(
    identifiers: Iterable[str],
    *,
    checked_at: str | None = None,
    open_url: Callable[..., Any] = urlopen,
) -> dict[str, Any]:
    """Validate each distinct iD once and return public, data-minimal receipts."""
    unique = sorted(set(identifiers))
    if len(unique) > MAX_DISTINCT_ORCIDS:
        raise VerificationError(
            "formalization.yaml declares more than 100 distinct ORCID iDs",
            code="formalization.too_many_orcids",
            field="orcid",
            next_action=(
                "Reduce the metadata to at most 100 distinct ORCID iDs, commit the change, "
                "then make a new submission using the new commit SHA."
            ),
        )
    for identifier in unique:
        validate_record(identifier, open_url=open_url)
    if checked_at is None:
        checked_at = (
            dt.datetime.now(dt.UTC)
            .replace(microsecond=0)
            .isoformat()
            .replace("+00:00", "Z")
        )
    return {
        "schema_version": 1,
        "checked_at": checked_at,
        "registry": ORCID_PUBLIC_BASE,
        "records": [
            {"orcid": identifier, "record_url": f"{ORCID_PUBLIC_BASE}/{identifier}"}
            for identifier in unique
        ],
    }
