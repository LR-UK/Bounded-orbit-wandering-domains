"""Backward-compatible entry point for the strict version 1.2 audit."""
from pathlib import Path
import runpy

runpy.run_path(str(Path(__file__).with_name("verify_submission.py")), run_name="__main__")
