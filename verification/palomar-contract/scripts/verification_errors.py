"""Shared failures raised by Palomar's verification boundaries."""

from __future__ import annotations

from typing import Any


class VerificationError(RuntimeError):
    """A bounded failure with enough context to tell a submitter what to do."""

    def __init__(
        self,
        message: str,
        *,
        code: str = "submission.invalid",
        owner: str = "submitter",
        next_action: str = (
            "Update the repository, commit the correction, then make a new submission "
            "using the new commit SHA."
        ),
        retryable: bool = False,
        path: str | None = None,
        line: int | None = None,
        column: int | None = None,
        field: str | None = None,
        repairable: bool = False,
        detail: str | None = None,
    ) -> None:
        super().__init__(message)
        self.detail = detail
        self.code = code
        self.owner = owner
        self.next_action = next_action
        self.retryable = retryable
        self.path = path
        self.line = line
        self.column = column
        self.field = field
        self.repairable = repairable

    def diagnostic(self, stage: str) -> dict[str, Any]:
        # The reader is shown `explanation` only where it says more than
        # `summary`, so evidence belongs here rather than in a longer sentence.
        explanation = str(self)
        if self.detail:
            explanation = f"{explanation}\n\n{self.detail[:1_500]}"
        result: dict[str, Any] = {
            "code": self.code,
            "stage": stage,
            "owner": self.owner,
            "summary": str(self)[:500],
            "explanation": explanation[:2_000],
            "next_action": self.next_action[:1_000],
            "retryable": self.retryable,
            "repairable": self.repairable,
        }
        if self.path:
            location: dict[str, Any] = {"path": self.path[:400]}
            if self.line is not None:
                location["line"] = self.line
            if self.column is not None:
                location["column"] = self.column
            result["location"] = location
        if self.field:
            result["field"] = self.field[:400]
        return result


class FormalizationValidationError(VerificationError):
    """Several independent formalization.yaml checks failed together."""

    def __init__(
        self,
        issues: list[VerificationError],
        *,
        repair_draft: dict[str, Any] | None = None,
    ) -> None:
        if not issues:
            raise ValueError("formalization validation needs at least one issue")
        super().__init__(str(issues[0]), code=issues[0].code)
        self.issues = tuple(issues)
        self.repair_draft = repair_draft
