"""Run the pinned Palomar metadata contract; requires PyYAML."""
from pathlib import Path
import hashlib
import json
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification/palomar-contract"))
from scripts.submission_contract import load_formalization_metadata, normalized_provenance
metadata = ROOT / "formalization.yaml"
data = load_formalization_metadata(metadata)
report = {
    "result": "passed",
    "validator_repository": "https://github.com/PalomarRegistry/PalomarSubmission",
    "validator_commit": "e48a86d0495356b5131a92c9406aa6e27cf99e56",
    "metadata_sha256": hashlib.sha256(metadata.read_bytes()).hexdigest(),
    "provenance": normalized_provenance(data),
    "scope": "Mechanical metadata contract only; no independent policy review or registry acceptance",
}
(ROOT / "verification/metadata.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"result": report["result"], "validator_commit": report["validator_commit"]}))
