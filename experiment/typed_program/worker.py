#!/usr/bin/env python3
"""Stateless finite producer for the typed-program protocol.

The training invocation never receives a probe.  A measurement invocation
receives an input but no target and has no update operation.  Program formation
is computed from the supplied corpus by one rank-free frontier rule.
"""

from __future__ import annotations

import json
import sys
from typing import Any, NoReturn


class WorkerError(Exception):
    pass


def fail(message: str) -> NoReturn:
    raise WorkerError(message)


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def formation_depth(formation: dict[str, Any]) -> int:
    tag = formation.get("tag")
    if tag in {"identity", "negate", "duplicate", "first"}:
        return 1
    if tag == "compose" and set(formation) == {"tag", "left", "right"}:
        return max(formation_depth(formation["left"]), formation_depth(formation["right"])) + 1
    fail("ill-formed program formation")


def formation_key(formation: dict[str, Any]) -> str:
    formation_depth(formation)
    return canonical(formation)


def frontier(corpus: list[dict[str, Any]]) -> dict[str, Any] | None:
    present = {formation_key(entry["formation"]) for entry in corpus}
    for left in corpus:
        for right in corpus:
            if left["target"] != right["source"]:
                continue
            candidate = {
                "tag": "compose",
                "left": left["formation"],
                "right": right["formation"],
            }
            if formation_key(candidate) not in present:
                return candidate
    return None


def evaluate(formation: dict[str, Any], value: bool) -> bool:
    tag = formation["tag"]
    if tag == "identity":
        return value
    if tag == "negate":
        return not value
    if tag == "compose":
        return evaluate(formation["right"], evaluate(formation["left"], value))
    fail("probe evaluator only accepts bit-to-bit formations")


def train(request: dict[str, Any]) -> dict[str, Any]:
    required = {"operation", "incoming_capacity", "increment", "training_view", "public_bounds"}
    if set(request) != required:
        fail("training request schema mismatch")
    if request["operation"] != "train":
        fail("invalid training operation")
    forbidden = {"probe", "target", "expected", "future_formation", "future_ast"}
    if forbidden.intersection(request) or forbidden.intersection(request["training_view"]):
        fail("future probe or target leaked into training")
    incoming = int(request["incoming_capacity"])
    increment = int(request["increment"])
    if increment != 1:
        fail("undeclared capacity increment")
    return {
        "operation": "train-result",
        "incoming_capacity": incoming,
        "acquired_capacity": incoming + increment,
        "evidence": "single-constructive-increment",
    }


def measure(request: dict[str, Any]) -> dict[str, Any]:
    required = {"operation", "capacity", "corpus", "probe_input", "allow_update"}
    if set(request) != required:
        fail("measurement request schema mismatch")
    if request["operation"] != "measure" or request["allow_update"] is not False:
        fail("measurement must be read-only")
    if "target" in request or "expected" in request:
        fail("measurement target leaked")
    candidate = frontier(request["corpus"])
    capacity = int(request["capacity"])
    proposal = candidate if candidate is not None and formation_depth(candidate) <= capacity else None
    behavior = None
    if proposal is not None:
        behavior = [evaluate(proposal, bool(value)) for value in request["probe_input"]]
    return {
        "operation": "measure-result",
        "predicted": proposal,
        "consumed_prediction": proposal,
        "proposal": proposal,
        "probe_behavior": behavior,
    }


def main() -> int:
    try:
        request = json.load(sys.stdin)
        if not isinstance(request, dict):
            fail("request root must be an object")
        operation = request.get("operation")
        result = train(request) if operation == "train" else measure(request)
        json.dump(result, sys.stdout, sort_keys=True, separators=(",", ":"))
        return 0
    except (WorkerError, KeyError, TypeError, ValueError) as error:
        json.dump({"error": str(error)}, sys.stdout, sort_keys=True)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
