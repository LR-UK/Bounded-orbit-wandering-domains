"""Run the pinned Palomar metadata contract; requires PyYAML."""
from pathlib import Path
import hashlib
import json
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification/palomar-contract"))
metadata = ROOT / "formalization.yaml"
report_path = ROOT / "verification/metadata.json"
report_path.unlink(missing_ok=True)  # Do not leave a stale success after a failed recheck.
try:
    from scripts.submission_contract import load_formalization_metadata, normalized_provenance
except ModuleNotFoundError as error:
    if error.name != "yaml":
        raise
    report_path.write_text(json.dumps({
        "result": "not-run",
        "metadata_sha256": hashlib.sha256(metadata.read_bytes()).hexdigest(),
        "reason": "PyYAML is not installed in this Python environment.",
        "next_step": "Install PyYAML and rerun python scripts/verify_metadata.py; Linux CI also runs it.",
    }, indent=2) + "\n", encoding="utf-8")
    raise SystemExit("Metadata validation not run: install PyYAML, then rerun this script.") from error
data = load_formalization_metadata(metadata)
report = {
    "result": "passed",
    "validator_repository": "https://github.com/PalomarRegistry/PalomarSubmission",
    "validator_commit": "e48a86d0495356b5131a92c9406aa6e27cf99e56",
    "metadata_sha256": hashlib.sha256(metadata.read_bytes()).hexdigest(),
    "provenance": normalized_provenance(data),
    "scope": "Mechanical metadata contract only; no independent policy review or registry acceptance",
}
report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"result": report["result"], "validator_commit": report["validator_commit"]}))
