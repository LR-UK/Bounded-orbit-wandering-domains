"""Validate dispatch intake and the submitted formalization metadata contract."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import yaml

from scripts.orcid_validation import (
    ORCID_RE,
    canonical_identifier,
    contains_identifier,
    valid_checksum,
)
from scripts.verification_errors import FormalizationValidationError, VerificationError

__all__ = (
    "ARXIV_CATEGORIES",
    "ARXIV_CATEGORY_NAMES",
    "AUTHORIZATION_RELATIONSHIPS",
    "CLASSIFICATION_CARDINALITY",
    "GITHUB_LOGIN_RE",
    "GITHUB_RE",
    "FORMALIZATION_PROFILE_VERSION",
    "MAX_FORMALIZATION_BYTES",
    "MSC2020_CODES",
    "MSC2020_NAMES",
    "OPTIONAL_FIELDS",
    "ORCID_RE",
    "ORIGINAL_PROOF_TYPE",
    "PALOMAR_ID_RE",
    "PROJECT_NAME_MAXIMUM",
    "REPOSITORY_RE",
    "REPOSITORY_ROLES",
    "REPAIRABLE_FORMALIZATION_FIELDS",
    "SHA_RE",
    "SOURCE_RELATIONSHIP_CATEGORIES",
    "SUBSTANTIVE_SOURCE_RELATIONSHIPS",
    "SUBMISSION_ID_RE",
    "UniqueKeySafeLoader",
    "declared_orcids",
    "load_formalization_metadata",
    "normalize_repository",
    "normalized_provenance",
    "registry_correction",
    "submission_request",
)

ROOT = Path(__file__).resolve().parent.parent
MAX_FORMALIZATION_BYTES = 256 * 1024
FORMALIZATION_PROFILE_VERSION = 4
PROJECT_NAME_MAXIMUM = 300
REPAIRABLE_FORMALIZATION_FIELDS = frozenset(
    {
        "project.name",
        "project.description",
        "project.authors",
        "project.license",
        "project.responsible_maintainers",
        "classification.arxiv",
        "classification.msc2020",
        "sources",
        "automation.methods",
        "review.status",
        "repository.substantive_formalization",
    }
)

ARXIV_CATEGORY_NAMES = json.loads(
    (ROOT / "taxonomies" / "arxiv-categories.json").read_text(encoding="utf-8")
)
MSC2020_NAMES = json.loads(
    (ROOT / "taxonomies" / "msc2020-codes.json").read_text(encoding="utf-8")
)
ARXIV_CATEGORIES = frozenset(ARXIV_CATEGORY_NAMES)
MSC2020_CODES = frozenset(MSC2020_NAMES)
# What load_formalization_metadata requires and what a repair draft may carry
# are the same bounds; browser-preflight-policy.json publishes them so the
# intake page can apply them before a submission reaches the verifier.
CLASSIFICATION_CARDINALITY = {"arxiv": (1, 8), "msc2020": (0, 8)}

# Every dispatch input is visible on the run page of this public repository, so
# a submitter's private prose stays private only by the server never sending it.
# `context` carried the submission form's free-text notes until the server
# stopped sending it. Dropping the key here cannot unmake a disclosure that has
# already happened by the time this runs; what it does is turn a stale or
# regressed caller into a failed run rather than a silently accepted field.
OPTIONAL_FIELDS = frozenset(
    {
        "existing_id",
        "authorization_relationship",
        "authorization_evidence",
        "project_path",
        "comparator_config_path",
        "formalization_metadata_path",
        "registry_correction",
    }
)
SUBMISSION_ID_RE = re.compile(r"^[0-9a-z]{12}$")
REPOSITORY_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
GITHUB_RE = re.compile(
    r"^https://github\.com/(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+?)(?:\.git)?/?$"
)
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
PALOMAR_ID_RE = re.compile(r"^PALOMAR-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{6}$")
GITHUB_LOGIN_RE = re.compile(
    r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?$"
)
AUTHORIZATION_RELATIONSHIPS = {
    "I am a responsible author or maintainer": "maintainer",
    "I have approval from a responsible author or maintainer": "approved",
    "I am a Palomar Technical Maintainer testing the workflow": "technical-test",
    "Palomar is making an exceptional registry metadata correction": "palomar-maintainer",
}
ORIGINAL_PROOF_TYPE = "original-proof"
REPOSITORY_ROLES = {"substantive-development", "thin-wrapper"}
SUBSTANTIVE_SOURCE_RELATIONSHIPS = frozenset({
    "formalizes",
    "adapts",
    "independently-proves",
})
SOURCE_RELATIONSHIP_CATEGORIES = frozenset({
    *SUBSTANTIVE_SOURCE_RELATIONSHIPS,
    "background",
    "other",
})
REGISTRY_CORRECTION_FIELDS = (
    "title",
    "abstract",
    "authors",
    "classification.arxiv",
    "classification.msc2020",
    "provenance.responsible_maintainers",
    "provenance.mathematical_sources",
    "provenance.related_formalizations",
)
_CORRECTION_CONTROL_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")


class UniqueKeySafeLoader(yaml.SafeLoader):
    """Safe YAML loader that rejects ambiguous duplicate mapping keys."""


def _construct_unique_mapping(
    loader: UniqueKeySafeLoader,
    node: yaml.nodes.MappingNode,
    deep: bool = False,
) -> dict[Any, Any]:
    mapping: dict[Any, Any] = {}
    for key_node, value_node in node.value:
        if key_node.tag == "tag:yaml.org,2002:merge":
            raise VerificationError(
                "formalization.yaml must not use YAML merge keys",
                code="formalization.invalid_yaml",
            )
        key = loader.construct_object(key_node, deep=deep)
        try:
            duplicate = key in mapping
        except TypeError as error:
            raise VerificationError(
                "formalization.yaml contains an invalid mapping key"
            ) from error
        if duplicate:
            raise VerificationError(
                f"formalization.yaml contains a duplicate key: {key!r}",
                code="formalization.invalid_yaml",
            )
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


UniqueKeySafeLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
    _construct_unique_mapping,
)


def _correction_text(value: Any, field: str, maximum: int) -> str:
    if (
        not isinstance(value, str)
        or not value.strip()
        or len(value.strip()) > maximum
        or _CORRECTION_CONTROL_RE.search(value.strip())
    ):
        raise VerificationError(f"Registry correction {field} is malformed")
    return value.strip()


def _correction_value(metadata: dict[str, Any], field: str) -> Any:
    value: Any = metadata
    for part in field.split("."):
        if not isinstance(value, dict) or part not in value:
            raise VerificationError(f"Registry correction has no {field}")
        value = value[part]
    return value


def registry_correction(raw: str) -> dict[str, Any] | None:
    """Validate the closed public correction payload dispatched by the Server."""
    if not raw:
        return None
    if len(raw.encode("utf-8")) > 48_000:
        raise VerificationError("Registry correction exceeds the 48,000-byte dispatch bound")
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as error:
        raise VerificationError("Registry correction is not valid JSON") from error
    expected = {
        "schema_version", "kind", "based_on", "explanation", "metadata",
        "changed_fields", "edits", "baseline",
    }
    if not isinstance(value, dict) or set(value) != expected:
        raise VerificationError("Registry correction has an unsupported shape")
    if value.get("schema_version") != 1 or value.get("kind") != "palomar-maintainer":
        raise VerificationError("Registry correction contract is unsupported")
    based_on = value.get("based_on")
    baseline = value.get("baseline")
    if (
        not isinstance(based_on, dict)
        or set(based_on) != {"id", "version"}
        or not PALOMAR_ID_RE.fullmatch(str(based_on.get("id", "")))
        or type(based_on.get("version")) is not int
        or based_on["version"] < 1
        or not isinstance(baseline, dict)
        or set(baseline) != {"id", "version", "path", "sha256"}
        or baseline.get("id") != based_on["id"]
        or baseline.get("version") != based_on["version"]
        or baseline.get("path") != f"entries/{based_on['id']}-v{based_on['version']}.json"
        or not re.fullmatch(r"[0-9a-f]{64}", str(baseline.get("sha256", "")))
    ):
        raise VerificationError("Registry correction baseline is malformed")
    value["explanation"] = _correction_text(value.get("explanation"), "explanation", 4_000)
    metadata = value.get("metadata")
    if (
        not isinstance(metadata, dict)
        or set(metadata) != {"title", "abstract", "authors", "classification", "provenance"}
        or not isinstance(metadata.get("classification"), dict)
        or set(metadata["classification"]) != {"arxiv", "msc2020"}
        or not isinstance(metadata.get("provenance"), dict)
        or set(metadata["provenance"]) != {
            "responsible_maintainers", "mathematical_sources", "related_formalizations"
        }
    ):
        raise VerificationError("Registry correction metadata is malformed")
    _correction_text(metadata.get("title"), "title", 300)
    _correction_text(metadata.get("abstract"), "abstract", 10_000)
    # The Server owns detailed field validation; this independent boundary
    # still closes recursive size and scalar types before publishing the report.
    def safe(node: Any, depth: int = 0) -> bool:
        if depth > 8:
            return False
        if node is None or isinstance(node, (bool, int)):
            return True
        if isinstance(node, str):
            return len(node) <= 10_000 and _CORRECTION_CONTROL_RE.search(node) is None
        if isinstance(node, list):
            return len(node) <= 100 and all(safe(item, depth + 1) for item in node)
        if isinstance(node, dict):
            return len(node) <= 20 and all(
                isinstance(key, str) and safe(item, depth + 1)
                for key, item in node.items()
            )
        return False
    if not safe(metadata):
        raise VerificationError("Registry correction metadata exceeds its structural bounds")
    _person_records(
        metadata["authors"],
        "registry_correction.metadata.authors",
        required=True,
    )
    _person_records(
        metadata["provenance"]["responsible_maintainers"],
        "registry_correction.metadata.provenance.responsible_maintainers",
        required=True,
    )
    correction_sources = metadata["provenance"]["mathematical_sources"]
    if not isinstance(correction_sources, list):
        raise VerificationError("Registry correction mathematical sources are malformed")
    for index, source in enumerate(correction_sources):
        if not isinstance(source, dict):
            raise VerificationError("Registry correction mathematical sources are malformed")
        _person_records(
            source.get("authors"),
            f"registry_correction.metadata.provenance.mathematical_sources[{index}].authors",
            required=False,
        )
    changed = value.get("changed_fields")
    if (
        not isinstance(changed, list)
        or not changed
        or any(field not in REGISTRY_CORRECTION_FIELDS for field in changed)
        or changed != sorted(set(changed), key=REGISTRY_CORRECTION_FIELDS.index)
    ):
        raise VerificationError("Registry correction changed_fields is malformed")
    edits = value.get("edits")
    if not isinstance(edits, list) or len(edits) != len(changed):
        raise VerificationError("Registry correction edits are malformed")
    for field, edit in zip(changed, edits, strict=True):
        if (
            not isinstance(edit, dict)
            or set(edit) != {"field", "value"}
            or edit.get("field") != field
            or edit.get("value") != _correction_value(metadata, field)
        ):
            raise VerificationError("Registry correction edits disagree with effective metadata")
    return value


def submission_request(event: dict[str, Any]) -> tuple[dict[str, str], str]:
    """Read the submission out of the dispatch that started this run.

    Submissions arrive through the submission server, which keeps the
    submitter's identity private, so a submission is identified by an opaque
    id and nothing else. Inputs are validated as strictly as a form would be:
    an intake that trusts whoever can dispatch is the wrong place to relax.
    """
    inputs = event.get("inputs")
    if not isinstance(inputs, dict):
        raise VerificationError("workflow dispatch carried no submission inputs")

    submission_id = str(inputs.get("request_id", "")).strip()
    if not SUBMISSION_ID_RE.fullmatch(submission_id):
        raise VerificationError(
            "Submission id must be twelve lowercase alphanumeric characters"
        )

    repository = str(inputs.get("repository", "")).strip()
    if not REPOSITORY_RE.fullmatch(repository):
        raise VerificationError("Repository must be given as owner/name")

    values = {
        "repository_url": f"https://github.com/{repository}",
        "commit_sha": str(inputs.get("commit", "")).strip(),
    }
    # The optional source fields retain one closed JSON-object contract.
    # Execution-profile and attempt inputs are separate trusted workflow fields.
    # A field missing from the allowlist would be dropped rather than
    # refused, so unknown keys are an error.
    raw_options = str(inputs.get("options", "")).strip()
    if raw_options:
        try:
            options = json.loads(raw_options)
        except json.JSONDecodeError as error:
            raise VerificationError(
                f"Submission options are not valid JSON: {error}"
            ) from error
        if not isinstance(options, dict):
            raise VerificationError("Submission options must be a JSON object")
        unknown = sorted(set(options) - OPTIONAL_FIELDS)
        if unknown:
            raise VerificationError(
                f"Unrecognized submission options: {', '.join(unknown)}"
            )
        for key, value in options.items():
            if not isinstance(value, str):
                raise VerificationError(f"Submission option {key} must be a string")
            values[key] = value

    if not values.get("comparator_config_path", "").strip():
        raise VerificationError(
            "Comparator configuration path must be supplied explicitly for this submission",
            code="comparator.path_missing",
            next_action=(
                "Choose the repository-relative Comparator configuration for this submission, "
                "then submit the same commit again."
            ),
        )

    return values, submission_id


def normalize_repository(url: str) -> tuple[str, str]:
    """Return the canonical owner/name and credential-free GitHub URL."""
    match = GITHUB_RE.fullmatch(url.strip())
    if not match:
        raise VerificationError("Repository URL must be https://github.com/owner/repo")
    owner = match.group("owner")
    repo = match.group("repo")
    if owner in {".", ".."} or repo in {".", ".."}:
        raise VerificationError("invalid GitHub repository path")
    return f"{owner}/{repo}", f"https://github.com/{owner}/{repo}"


def _required_mapping(value: Any, path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise VerificationError(f"formalization.yaml field {path} must be a mapping")
    return value


def _required_text(value: Any, path: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise VerificationError(
            f"formalization.yaml field {path} must be a nonempty string"
        )
    return value.strip()


def _required_bounded_text(value: Any, path: str, *, maximum: int) -> str:
    text = _required_text(value, path)
    if len(text) > maximum:
        raise VerificationError(
            f"formalization.yaml field {path} exceeds {maximum} characters"
        )
    return text


def _required_people(
    value: Any, path: str, *, allow_legacy_orcid_names: bool = False
) -> list[Any]:
    if not isinstance(value, list) or not value:
        raise VerificationError(
            f"formalization.yaml field {path} must be a nonempty list"
        )
    for index, person in enumerate(value):
        item_path = f"{path}[{index}]"
        if isinstance(person, str):
            _person_name(
                person,
                item_path,
                allow_legacy_orcid_names=allow_legacy_orcid_names,
            )
        elif isinstance(person, dict):
            _person_name(
                person.get("name"),
                f"{item_path}.name",
                allow_legacy_orcid_names=allow_legacy_orcid_names,
            )
        else:
            raise VerificationError(
                f"formalization.yaml field {item_path} must be a name or a mapping with a name"
            )
    return value


def _person_name(
    value: Any, path: str, *, allow_legacy_orcid_names: bool = False
) -> str:
    name = _required_text(value, path).strip()
    if not allow_legacy_orcid_names and contains_identifier(name):
        raise VerificationError(
            f"formalization.yaml field {path} contains an ORCID iD in the name; "
            "move it to that person's separate orcid field",
            code="formalization.orcid_in_name",
            field=path,
            next_action=(
                "Remove the ORCID iD from the person's name and put it in the same "
                "person mapping, for example `{name: Ada Lovelace, orcid: "
                "0000-0002-1825-0097}`. Commit the metadata change, then make a new "
                "submission using the new commit SHA."
            ),
        )
    return name


def _person_records(
    value: Any,
    path: str,
    *,
    required: bool,
    allow_legacy_orcid_names: bool = False,
) -> list[dict[str, str]]:
    if value in (None, []) and not required:
        return []
    people = _required_people(
        value, path, allow_legacy_orcid_names=allow_legacy_orcid_names
    )
    records: list[dict[str, str]] = []
    for index, person in enumerate(people):
        item_path = f"{path}[{index}]"
        if isinstance(person, str):
            records.append({
                "name": _person_name(
                    person,
                    item_path,
                    allow_legacy_orcid_names=allow_legacy_orcid_names,
                )
            })
            continue
        record = {
            "name": _person_name(
                person.get("name"),
                f"{item_path}.name",
                allow_legacy_orcid_names=allow_legacy_orcid_names,
            )
        }
        github = person.get("github")
        if github is not None:
            login = _required_text(github, f"{item_path}.github").strip().removeprefix("@")
            if not GITHUB_LOGIN_RE.fullmatch(login):
                raise VerificationError(
                    f"formalization.yaml field {item_path}.github must be a GitHub login"
                )
            record["github"] = login
        orcid = person.get("orcid")
        if orcid is not None:
            submitted_identifier = _required_text(
                orcid, f"{item_path}.orcid"
            ).strip()
            identifier = canonical_identifier(submitted_identifier)
            if identifier is None or not valid_checksum(identifier):
                raise VerificationError(
                    f"formalization.yaml field {item_path}.orcid must be a valid bare "
                    "ORCID iD or an https://orcid.org URL"
                )
            record["orcid"] = identifier
        records.append(record)
    return records


def declared_orcids(
    data: dict[str, Any],
    provenance: dict[str, Any],
    *,
    allow_legacy_orcid_names: bool = False,
) -> list[str]:
    """Return every canonical ORCID iD from the supported person positions."""
    project = _required_mapping(data.get("project"), "project")
    groups = [
        _person_records(
            project.get("authors"),
            "project.authors",
            required=True,
            allow_legacy_orcid_names=allow_legacy_orcid_names,
        ),
        provenance.get("responsible_maintainers", []),
    ]
    for source in provenance.get("mathematical_sources", []):
        if isinstance(source, dict):
            groups.append(source.get("authors", []))
    return sorted({
        person["orcid"]
        for people in groups
        for person in people
        if isinstance(person, dict) and "orcid" in person
    })


def _optional_text(value: Any, path: str, *, maximum: int = 10_000) -> str | None:
    if value is None or value == "":
        return None
    text = _required_text(value, path).strip()
    if len(text) > maximum:
        raise VerificationError(
            f"formalization.yaml field {path} exceeds {maximum} characters"
        )
    return text


def _person_records_with_singular_alias(
    mapping: dict[str, Any],
    plural: str,
    singular: str,
    path: str,
    *,
    required: bool,
    allow_legacy_orcid_names: bool = False,
) -> list[dict[str, str]]:
    """Read the canonical people list, falling back to a legacy singular key."""
    if plural in mapping:
        return _person_records(
            mapping.get(plural),
            f"{path}.{plural}",
            required=required,
            allow_legacy_orcid_names=allow_legacy_orcid_names,
        )
    if singular not in mapping:
        return _person_records(
            None,
            f"{path}.{plural}",
            required=required,
            allow_legacy_orcid_names=allow_legacy_orcid_names,
        )

    value = mapping.get(singular)
    if value is None:
        value = []
    elif not isinstance(value, list):
        value = [value]
    return _person_records(
        value,
        f"{path}.{singular}",
        required=required,
        allow_legacy_orcid_names=allow_legacy_orcid_names,
    )


def _source_contributor_records(value: Any, path: str) -> list[dict[str, str]]:
    if value in (None, []):
        return []
    if not isinstance(value, list):
        raise VerificationError(
            f"formalization.yaml field {path} must be a list"
        )
    records: list[dict[str, str]] = []
    for index, contributor in enumerate(value):
        item_path = f"{path}[{index}]"
        if not isinstance(contributor, dict):
            raise VerificationError(
                f"formalization.yaml field {item_path} must be a mapping with a name and role"
            )
        name = _required_text(contributor.get("name"), f"{item_path}.name").strip()
        role = _required_text(contributor.get("role"), f"{item_path}.role").strip()
        if len(role) > 200:
            raise VerificationError(
                f"formalization.yaml field {item_path}.role exceeds 200 characters"
            )
        records.append({"name": name, "role": role})
    return records


def normalized_provenance(
    data: dict[str, Any], *, allow_legacy_orcid_names: bool = False
) -> dict[str, Any]:
    """Validate and canonicalize the current Palomar provenance contract."""
    project = _required_mapping(data.get("project"), "project")
    maintainers = _person_records_with_singular_alias(
        project,
        "responsible_maintainers",
        "responsible_maintainer",
        "project",
        required=True,
        allow_legacy_orcid_names=allow_legacy_orcid_names,
    )

    raw_repository = data.get("repository")
    if raw_repository is None:
        repository: dict[str, Any] = {}
    else:
        repository = _required_mapping(raw_repository, "repository")
    raw_repository_role = repository.get("role")
    if raw_repository_role is None or raw_repository_role == "":
        repository_role = (
            "thin-wrapper"
            if "substantive_formalization" in repository
            else "substantive-development"
        )
    else:
        repository_role = _required_text(
            raw_repository_role, "repository.role"
        ).strip()
        if repository_role not in REPOSITORY_ROLES:
            allowed = ", ".join(sorted(REPOSITORY_ROLES))
            raise VerificationError(
                f"formalization.yaml field repository.role must be one of: {allowed}"
            )
    substantive: dict[str, str] | None = None
    if (
        repository_role == "substantive-development"
        and "substantive_formalization" in repository
    ):
        raise VerificationError(
            "formalization.yaml field repository.substantive_formalization is valid only "
            "for a thin wrapper; remove it when the submitted repository contains the "
            "substantive development"
        )
    if repository_role == "thin-wrapper":
        if not isinstance(repository.get("substantive_formalization"), dict):
            raise VerificationError(
                "formalization.yaml field repository.substantive_formalization is a required "
                "mapping when repository.role is thin-wrapper"
            )
        item = repository["substantive_formalization"]
        repository_id = _required_text(
            item.get("id"), "repository.substantive_formalization.id"
        )
        if not repository_id.startswith("https://"):
            repository_id = f"https://github.com/{repository_id}"
        repo, url = normalize_repository(repository_id)
        revision = _required_text(
            item.get("revision"), "repository.substantive_formalization.revision"
        ).strip().lower()
        if not SHA_RE.fullmatch(revision):
            raise VerificationError(
                "formalization.yaml field repository.substantive_formalization.revision "
                "must be a full lowercase commit"
            )
        substantive = {
            "repository": repo,
            "repository_url": url,
            "commit": revision,
            "tree_url": f"{url}/tree/{revision}",
        }

    raw_sources = data.get("sources")
    if not isinstance(raw_sources, list) or not raw_sources:
        raise VerificationError(
            "formalization.yaml field sources must be a nonempty list; use an entry with "
            "type: original-proof when the formalization first presents the result"
        )
    sources: list[dict[str, Any]] = []
    for index, source in enumerate(raw_sources):
        path = f"sources[{index}]"
        item = _required_mapping(source, path)
        raw_relationship = item.get("relationship")
        if not isinstance(raw_relationship, str) or not raw_relationship.strip():
            raise VerificationError(
                f"formalization.yaml field {path}.relationship must be a nonempty string; "
                "every source needs a relationship, including original-proof entries, which "
                "must use other"
            )
        relationship_text = raw_relationship.strip()
        if len(relationship_text) > 500:
            raise VerificationError(
                f"formalization.yaml field {path}.relationship exceeds 500 characters"
            )
        # The submitted description remains free-form. The public provenance
        # contract has five semantic categories, so an unfamiliar description
        # has the same provenance meaning as an explicit `other`.
        relationship = (
            relationship_text
            if relationship_text in SOURCE_RELATIONSHIP_CATEGORIES
            else "other"
        )
        source_type = _optional_text(item.get("type"), f"{path}.type", maximum=200)
        record: dict[str, Any] = {
            "title": _required_text(item.get("title"), f"{path}.title").strip(),
            "authors": _person_records_with_singular_alias(
                item,
                "authors",
                "author",
                path,
                required=False,
                allow_legacy_orcid_names=allow_legacy_orcid_names,
            ),
            "relationship": relationship,
        }
        contributors = _source_contributor_records(
            item.get("contributors"), f"{path}.contributors"
        )
        if contributors:
            record["contributors"] = contributors
        for source_key, record_key, maximum in (
            ("id", "identifier", 2_048),
            ("location", "location", 1_000),
            ("note", "note", 10_000),
            ("license", "license", 500),
            ("author_endorsement", "author_endorsement", 100),
        ):
            raw_value = item.get(source_key)
            value = _optional_text(
                raw_value, f"{path}.{source_key}", maximum=maximum
            )
            if value is not None:
                record[record_key] = value
        if source_type is not None:
            record["type"] = source_type
        sources.append(record)

    has_original_proof = any(
        source.get("type") == ORIGINAL_PROOF_TYPE for source in sources
    )
    if has_original_proof:
        result_origin = "original"
    else:
        result_origin = "source-based"
    if result_origin == "source-based" and not any(
        source["relationship"] in SUBSTANTIVE_SOURCE_RELATIONSHIPS for source in sources
    ):
        raise VerificationError(
            "formalization.yaml sources for a source-based result must include a "
            "formalizes, adapts, or independently-proves relationship"
        )
    if result_origin == "original" and any(
        source.get("type") == ORIGINAL_PROOF_TYPE and source["relationship"] != "other"
        for source in sources
    ):
        raise VerificationError(
            "formalization.yaml type: original-proof declares that this formalization first "
            "presents the result and must use relationship: other. If the source is a prior "
            "publication of the result, use its actual type (such as paper or book) and keep "
            "the substantive relationship instead"
        )
    if result_origin == "original" and any(
        source["relationship"] in SUBSTANTIVE_SOURCE_RELATIONSHIPS for source in sources
    ):
        raise VerificationError(
            "formalization.yaml declares an original-proof, so every source must use "
            "relationship background or other; formalizes, adapts, and independently-proves "
            "declare a source-based result. Remove type: original-proof when the named source "
            "is a prior presentation of the result"
        )

    raw_related = data.get("related_formalizations", [])
    if not isinstance(raw_related, list):
        raise VerificationError(
            "formalization.yaml field related_formalizations must be a list when present"
        )
    related: list[dict[str, str]] = []
    for index, related_item in enumerate(raw_related):
        path = f"related_formalizations[{index}]"
        item = _required_mapping(related_item, path)
        relationship = _required_text(
            item.get("relationship"), f"{path}.relationship"
        ).strip()
        if len(relationship) > 500:
            raise VerificationError(
                f"formalization.yaml field {path}.relationship exceeds 500 characters"
            )
        record = {
            "identifier": _required_text(item.get("id"), f"{path}.id").strip(),
            "relationship": relationship,
        }
        note = _optional_text(item.get("note"), f"{path}.note")
        if note is not None:
            record["note"] = note
        related.append(record)

    result: dict[str, Any] = {
        "result_origin": result_origin,
        "repository_role": repository_role,
        "responsible_maintainers": maintainers,
        "mathematical_sources": sources,
        "related_formalizations": related,
    }
    if substantive is not None:
        result["substantive_formalization"] = substantive
    return result


def _required_classifications(
    value: Any,
    path: str,
    *,
    allowed: frozenset[str],
    minimum: int,
    maximum: int | None,
) -> list[str]:
    too_short = not isinstance(value, list) or len(value) < minimum
    too_long = isinstance(value, list) and maximum is not None and len(value) > maximum
    if too_short or too_long:
        if maximum is None:
            count = f"at least {minimum}"
        else:
            count = (
                f"{minimum} or {maximum}"
                if minimum + 1 == maximum
                else f"{minimum}–{maximum}"
            )
        raise VerificationError(
            f"formalization.yaml field {path} must contain {count} classification codes"
        )
    for index, code in enumerate(value):
        if not isinstance(code, str) or code not in allowed:
            raise VerificationError(
                f"formalization.yaml field {path}[{index}] is not a recognized classification code"
            )
    if len(value) != len(set(value)):
        raise VerificationError(
            f"formalization.yaml field {path} must not contain duplicates"
        )
    return value


def _safe_people(value: Any) -> list[str] | None:
    if not isinstance(value, list) or not value:
        return None
    names: list[str] = []
    for person in value:
        name = person if isinstance(person, str) else person.get("name") if isinstance(person, dict) else None
        if not isinstance(name, str) or not name.strip():
            return None
        names.append(name.strip())
    return names


def _safe_string_list(value: Any) -> list[str] | None:
    if not isinstance(value, list) or not value or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        return None
    return [item.strip() for item in value]


def _canonicalize_classification_keys(data: dict[str, Any]) -> None:
    """Accept classification scheme names without making their casing significant."""
    classification = data.get("classification")
    if not isinstance(classification, dict):
        return
    for canonical in ("arxiv", "msc2020"):
        matches = [
            key
            for key in classification
            if isinstance(key, str) and key.casefold() == canonical
        ]
        if len(matches) > 1:
            raise VerificationError(
                "formalization.yaml contains duplicate classification keys "
                f"differing only by case: {canonical!r}",
                code="formalization.invalid_yaml",
            )
        if matches and matches[0] != canonical:
            classification[canonical] = classification.pop(matches[0])


def _safe_source(value: Any) -> dict[str, Any] | None:
    if not isinstance(value, dict):
        return {}
    title = value.get("title")
    result: dict[str, Any] = {}
    if isinstance(title, str) and title.strip():
        result["title"] = title.strip()
    authors = _safe_people(value.get("authors"))
    if authors is None and "author" in value:
        authors = _safe_people(
            value["author"] if isinstance(value["author"], list) else [value["author"]]
        )
    if authors:
        result["authors"] = authors
    contributors = value.get("contributors")
    if isinstance(contributors, list):
        safe_contributors = []
        for contributor in contributors:
            if not isinstance(contributor, dict):
                continue
            name = contributor.get("name")
            role = contributor.get("role")
            if (
                isinstance(name, str) and name.strip()
                and isinstance(role, str) and role.strip()
                and len(role.strip()) <= 200
            ):
                safe_contributors.append({"name": name.strip(), "role": role.strip()})
        if safe_contributors:
            result["contributors"] = safe_contributors
    for field in ("id", "location", "license"):
        item = value.get(field)
        if isinstance(item, str) and item.strip():
            result[field] = item.strip()
    for field, maximum in (
        ("type", 200), ("relationship", 500), ("note", 10_000),
        ("author_endorsement", 100),
    ):
        item = value.get(field)
        if isinstance(item, str) and item.strip() and len(item.strip()) <= maximum:
            result[field] = item.strip()
    return result


def formalization_repair_draft(data: dict[str, Any]) -> dict[str, Any]:
    """Carry only exact legacy equivalents into a submitter-confirmed repair."""
    values: dict[str, Any] = {}
    origins: dict[str, str] = {}

    project = data.get("project") if isinstance(data.get("project"), dict) else {}
    artifact = data.get("artifact") if isinstance(data.get("artifact"), dict) else {}
    for field, current, legacy in (
        ("project.name", project.get("name"), artifact.get("name")),
        ("project.license", project.get("license"), artifact.get("license")),
    ):
        value = current if isinstance(current, str) and current.strip() else legacy
        if isinstance(value, str) and value.strip():
            values[field] = value.strip()
            origins[field] = field if value is current else f"artifact.{field.split('.')[-1]}"
    description_candidates = (
        (project.get("description"), "project.description"),
        (project.get("short_description"), "project.short_description"),
        (
            data.get("result", {}).get("statement")
            if isinstance(data.get("result"), dict)
            else None,
            "result.statement",
        ),
        (project.get("name"), "project.name"),
    )
    for candidate, origin in description_candidates:
        if isinstance(candidate, str) and candidate.strip():
            values["project.description"] = candidate.strip()[:10_000]
            origins["project.description"] = origin
            break
    for field, current, legacy in (
        ("project.authors", project.get("authors"), artifact.get("authors")),
        (
            "project.responsible_maintainers",
            project.get("responsible_maintainers"),
            project.get("responsible_maintainer"),
        ),
    ):
        legacy_people = legacy if isinstance(legacy, list) else [legacy] if legacy is not None else None
        people = _safe_people(current) or _safe_people(legacy_people)
        if people:
            values[field] = people
            origins[field] = field if _safe_people(current) else (
                "project.responsible_maintainer"
                if field == "project.responsible_maintainers"
                else f"artifact.{field.split('.')[-1]}"
            )

    classification = data.get("classification")
    if isinstance(classification, dict):
        for name in ("arxiv", "msc2020"):
            items = _safe_string_list(classification.get(name))
            if items:
                field = f"classification.{name}"
                values[field] = items[: CLASSIFICATION_CARDINALITY[name][1]]
                origins[field] = field

    raw_sources = data.get("sources")
    source_origin = "sources"
    if not isinstance(raw_sources, list) or not raw_sources:
        legacy_source = data.get("source")
        raw_sources = [legacy_source] if isinstance(legacy_source, dict) else []
        source_origin = "source"
    sources = [item for raw in raw_sources if (item := _safe_source(raw)) is not None]
    if sources:
        values["sources"] = sources
        origins["sources"] = source_origin

    automation = data.get("automation")
    if isinstance(automation, dict):
        raw_methods = automation.get("methods")
        method_origin = "automation.methods"
        if not isinstance(raw_methods, list) or not raw_methods:
            raw_methods = [automation] if isinstance(automation.get("method"), str) else []
            method_origin = "automation.method"
        methods: list[dict[str, Any]] = []
        for raw in raw_methods:
            if (
                not isinstance(raw, dict)
                or not isinstance(raw.get("method"), str)
                or not raw["method"].strip()
            ):
                continue
            method: dict[str, Any] = {"method": raw["method"].strip()}
            if isinstance(raw.get("framework"), str) and raw["framework"].strip():
                method["framework"] = raw["framework"].strip()
            models = _safe_string_list(raw.get("models"))
            if models:
                method["models"] = models
            methods.append(method)
        if methods:
            values["automation.methods"] = methods
            origins["automation.methods"] = method_origin

    review = data.get("review")
    if isinstance(review, dict) and isinstance(review.get("status"), str) and review["status"].strip():
        values["review.status"] = review["status"].strip()
        origins["review.status"] = "review.status"
    repository = data.get("repository")
    if isinstance(repository, dict) and isinstance(repository.get("substantive_formalization"), dict):
        item = repository["substantive_formalization"]
        identifier, revision = item.get("id"), item.get("revision")
        if (
            isinstance(identifier, str)
            and identifier.strip()
            and isinstance(revision, str)
            and revision.strip()
        ):
            values["repository.substantive_formalization"] = {
                "id": identifier.strip(), "revision": revision.strip()
            }
            origins["repository.substantive_formalization"] = "repository.substantive_formalization"
    return {"values": values, "origins": origins}


def load_formalization_metadata(
    path: Path, *, allow_legacy_orcid_names: bool = False
) -> dict[str, Any]:
    """Parse and enforce Palomar's mechanical minimum for formalization.yaml."""
    if path.stat().st_size > MAX_FORMALIZATION_BYTES:
        raise VerificationError(
            "formalization.yaml exceeds the 256 KiB hard cap",
            code="formalization.too_large",
            path=path.name,
            next_action="Reduce formalization.yaml below 256 KiB, commit it, and submit again.",
        )
    try:
        data = yaml.load(path.read_text(encoding="utf-8"), Loader=UniqueKeySafeLoader)
    except (UnicodeDecodeError, yaml.YAMLError) as error:
        detail = str(error).splitlines()[0] if str(error) else type(error).__name__
        mark = getattr(error, "problem_mark", None)
        raise VerificationError(
            f"formalization.yaml is not valid YAML: {detail}",
            code="formalization.invalid_yaml",
            path=path.name,
            line=getattr(mark, "line", -1) + 1 if mark is not None else None,
            column=getattr(mark, "column", -1) + 1 if mark is not None else None,
            next_action=(
                "Correct the YAML syntax at the reported location in your repository, "
                "commit the change, and make a new submission."
            ),
        ) from error
    if not isinstance(data, dict):
        raise VerificationError(
            "formalization.yaml must contain one top-level mapping",
            code="formalization.wrong_root_type",
            path=path.name,
        )
    _canonicalize_classification_keys(data)

    issues: list[VerificationError] = []

    def check(action: Any, field: str | None = None) -> None:
        try:
            action()
        except VerificationError as error:
            message = str(error)
            match = re.search(r"formalization\.yaml field ([^ ]+)", message)
            detected = match.group(1).rstrip(";:,.") if match else error.field
            canonical = field or detected
            if canonical and canonical.startswith("sources"):
                canonical = "sources"
            elif canonical and canonical.startswith("automation.methods"):
                canonical = "automation.methods"
            issues.append(
                VerificationError(
                    message,
                    code=error.code if error.code != "submission.invalid" else "formalization.invalid_field",
                    owner=error.owner,
                    retryable=error.retryable,
                    path=path.name,
                    line=error.line,
                    column=error.column,
                    field=canonical,
                    repairable=bool(canonical in REPAIRABLE_FORMALIZATION_FIELDS),
                    next_action=(
                        "Complete the guided metadata form and let Palomar prepare a pull request."
                        if canonical in REPAIRABLE_FORMALIZATION_FIELDS
                        else error.next_action
                    ),
                )
            )

    project = data.get("project") if isinstance(data.get("project"), dict) else {}
    check(
        lambda: _required_bounded_text(
            project.get("name"), "project.name", maximum=PROJECT_NAME_MAXIMUM
        )
    )
    check(
        lambda: _required_bounded_text(
            project.get("description"), "project.description", maximum=10_000
        )
    )
    check(
        lambda: _person_records(
            project.get("authors"),
            "project.authors",
            required=True,
            allow_legacy_orcid_names=allow_legacy_orcid_names,
        )
    )
    check(lambda: _required_text(project.get("license"), "project.license"))
    maintainers = project.get("responsible_maintainers")
    if "responsible_maintainers" not in project and "responsible_maintainer" in project:
        maintainers = project.get("responsible_maintainer")
        if not isinstance(maintainers, list):
            maintainers = [maintainers]
    check(
        lambda: _person_records(
            maintainers,
            "project.responsible_maintainers",
            required=True,
            allow_legacy_orcid_names=allow_legacy_orcid_names,
        )
    )

    classification = (
        data.get("classification") if isinstance(data.get("classification"), dict) else {}
    )
    arxiv_minimum, arxiv_maximum = CLASSIFICATION_CARDINALITY["arxiv"]
    msc2020_minimum, msc2020_maximum = CLASSIFICATION_CARDINALITY["msc2020"]
    check(
        lambda: _required_classifications(
            classification.get("arxiv"),
            "classification.arxiv",
            allowed=ARXIV_CATEGORIES,
            minimum=arxiv_minimum,
            maximum=arxiv_maximum,
        )
    )
    check(
        lambda: _required_classifications(
            classification.get("msc2020", []),
            "classification.msc2020",
            allowed=MSC2020_CODES,
            minimum=msc2020_minimum,
            maximum=msc2020_maximum,
        )
    )

    # Validate source provenance independently of maintainers and repository so
    # one old section cannot hide the other fields the guided form must collect.
    source_document = {
        **data,
        "project": {**project, "responsible_maintainers": ["Palomar validation placeholder"]},
    }
    source_document.pop("repository", None)
    check(
        lambda: normalized_provenance(
            source_document,
            allow_legacy_orcid_names=allow_legacy_orcid_names,
        ),
        "sources",
    )

    # Ordinary repositories need no repository edit. Only an explicitly
    # declared thin wrapper may ask the guided form for its pinned target.
    if "repository" in data:
        repository_document = {
            **data,
            "project": {**project, "responsible_maintainers": ["Palomar validation placeholder"]},
            "sources": [{
                "title": "Palomar validation placeholder",
                "type": "original-proof",
                "relationship": "other",
            }],
        }
        repository = data.get("repository")
        explicit_missing_target = (
            isinstance(repository, dict)
            and repository.get("role") == "thin-wrapper"
            and not isinstance(repository.get("substantive_formalization"), dict)
        )
        check(
            lambda: normalized_provenance(
                repository_document,
                allow_legacy_orcid_names=allow_legacy_orcid_names,
            ),
            "repository.substantive_formalization" if explicit_missing_target else None,
        )

    automation = data.get("automation") if isinstance(data.get("automation"), dict) else {}

    def check_automation() -> None:
        methods = automation.get("methods")
        if not isinstance(methods, list) or not methods:
            raise VerificationError(
                "formalization.yaml field automation.methods must be a nonempty list"
            )
        for index, method in enumerate(methods):
            item = _required_mapping(method, f"automation.methods[{index}]")
            method_name = _required_text(
                item.get("method"), f"automation.methods[{index}].method"
            )
            if len(method_name) > 500:
                raise VerificationError(
                    f"formalization.yaml field automation.methods[{index}].method "
                    "exceeds 500 characters"
                )

    check(check_automation)

    review = data.get("review") if isinstance(data.get("review"), dict) else {}
    check(lambda: _required_text(review.get("status"), "review.status"))
    if issues:
        raise FormalizationValidationError(
            issues,
            repair_draft=formalization_repair_draft(data),
        )
    return data
