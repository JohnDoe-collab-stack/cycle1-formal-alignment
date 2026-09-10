#!/usr/bin/env python3
"""Read-only verifier for the frozen constitutive-transformer result."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, NoReturn


EXPECTED_PROTOCOL = "constitutive-transformer-v1"
EXPECTED_SEEDS = [11, 29, 47]
EXPECTED_SCRIPT_SHA256 = (
    "ab27a54ae7cf62a5c5f9dbb4d6ef3f6db6eb214db606498884d976df780eb04d"
)
EXPECTED_CONFIG_SHA256 = (
    "008993ba6a21e5e9731869e1dbf4f16edc1ffa29c380486e738e9b26516241c0"
)
EXPECTED_DATA_SHA256 = (
    "3ae9c050758295f2f56bd3e216d48241f51b3ee48544b50eb4f18b1c9f003f08"
)
EXPECTED_TRAINING_SHA256 = (
    "4a2a43bd7888355d26c888f795c6719bd7d5553e1c15ab4372ff19d7bc8f8ae0"
)
EXPECTED_PROBE_POLICY_SHA256 = (
    "28822c4762958997f8da6c5d18121b896f6fac650e1030e39b23ea7d4343fd57"
)
EXPECTED_RESULT_SHA256 = (
    "e483c0e0a046e2f81b03b043be956ad575f972e9ffb1b756c53eda3b9896928c"
)
EXPECTED_COMMITMENT = "fixed-held-out-probe-policy"
EXPECTED_PROBE_ID = "confirmatory-0"
EXPECTED_PROBE_ORDINAL = 1
EXPECTED_CYCLES = [
    "parent",
    "learned-cycle-1",
    "learned-cycle-2",
    "intercycle-ablation",
    "active-relation-control",
    "inert-original",
    "inert-flipped",
    "address-renamed",
]
EXPECTED_TRACE_FIELDS = {
    "seed",
    "cycle",
    "probe_role",
    "probe_id",
    "probe_ordinal",
    "view",
    "parameters",
    "neural",
    "consumed_prediction",
    "proposal",
    "candidate",
    "regime_admitted",
    "norm_satisfied",
    "error_position",
    "error_reason",
    "certificate_issued",
    "governed_effect",
}


class ValidationError(Exception):
    """A frozen artifact or constitutive-boundary check failed."""


def fail(message: str) -> NoReturn:
    raise ValidationError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def load_json(path: Path) -> tuple[bytes, dict[str, Any]]:
    payload = path.read_bytes()
    parsed = json.loads(payload)
    require(isinstance(parsed, dict), f"{path}: root must be an object")
    return payload, parsed


def case_signature(case: dict[str, Any]) -> tuple[Any, ...]:
    return (
        tuple(case["tokens"]),
        case["cache"],
        case["initial_relation"],
        case["budget"],
    )


def validate_config(config: dict[str, Any]) -> None:
    require(config["protocol"] == EXPECTED_PROTOCOL, "configuration protocol mismatch")
    require(config["seeds"] == EXPECTED_SEEDS, "configuration seed mismatch")
    training = config["data"]["training_cases"]
    policy = config["data"]["probe_policy"]
    training_ids = [str(case["case_id"]) for case in training]
    probe_ids = [str(probe["probe_id"]) for probe in policy["probes"]]
    require(bool(training), "training set is empty")
    require(len(training_ids) == len(set(training_ids)), "duplicate training id")
    require(len(probe_ids) == len(set(probe_ids)), "duplicate probe id")
    require(not set(training_ids).intersection(probe_ids), "split id collision")
    require(policy["training_case_ids"] == training_ids, "training binding mismatch")
    require(policy["commitment_id"] == EXPECTED_COMMITMENT, "commitment mismatch")
    require(policy["smoke_ordinal"] != policy["confirmatory_ordinal"], "probe roles collide")
    require(
        policy["confirmatory_ordinal"] == EXPECTED_PROBE_ORDINAL,
        "confirmatory ordinal mismatch",
    )
    require(
        policy["probes"][EXPECTED_PROBE_ORDINAL]["probe_id"] == EXPECTED_PROBE_ID,
        "confirmatory probe mismatch",
    )
    training_views = {case_signature(case) for case in training}
    probe_views = [case_signature(probe) for probe in policy["probes"]]
    require(len(probe_views) == len(set(probe_views)), "duplicate probe view")
    require(not training_views.intersection(probe_views), "probe leaks training view")


def validate_trace(
    trace: dict[str, Any], expected_seed: int, proposal_threshold: float
) -> None:
    require(set(trace) == EXPECTED_TRACE_FIELDS, "primary trace schema mismatch")
    require(trace["seed"] == expected_seed, "trace seed mismatch")
    require(trace["probe_role"] == "confirmatory", "non-confirmatory trace")
    require(trace["probe_id"] == EXPECTED_PROBE_ID, "probe substitution")
    require(trace["probe_ordinal"] == EXPECTED_PROBE_ORDINAL, "ordinal substitution")
    require(trace["proposal"] in (0, 1), "proposal must be discrete")
    require(
        trace["consumed_prediction"] == trace["neural"]["probability"],
        "produced prediction was not consumed exactly",
    )
    require(
        trace["proposal"]
        == int(trace["consumed_prediction"] >= proposal_threshold),
        "proposal is not the declared discretization",
    )

    candidate = "admitted" if trace["proposal"] == 1 else "outside"
    admitted = candidate == "admitted"
    normative = candidate == "admitted"
    certificate = admitted and normative
    require(trace["candidate"] == candidate, "candidate was rewritten")
    require(trace["regime_admitted"] is admitted, "regime verdict mismatch")
    require(trace["norm_satisfied"] is normative, "norm verdict mismatch")
    require(trace["certificate_issued"] is certificate, "certificate mismatch")
    require(
        trace["governed_effect"]
        == ("relation-incorporated" if certificate else None),
        "governed effect is not confined",
    )
    if admitted:
        require(trace["error_position"] is None, "accepted trace has an error")
        require(trace["error_reason"] is None, "accepted trace has a reason")
    else:
        require(trace["error_position"] == 0, "rejection position mismatch")
        require(
            trace["error_reason"] == "outside-regime-and-norm",
            "rejection reason mismatch",
        )

    view = trace["view"]
    require(
        set(view) == {"tokens", "cache", "memory", "relation", "budget"},
        "authorized-view schema mismatch",
    )
    require(view["relation"] in (0, 1), "relation must be discrete")
    require(
        set(view["memory"]) == {"keys", "values", "address_polarity"},
        "attention-memory schema mismatch",
    )


def validate_run(
    run: dict[str, Any], config: dict[str, Any], tolerance: float
) -> None:
    seed = run["seed"]
    require(seed in EXPECTED_SEEDS, "unexpected seed")
    require(run["probe_role"] == "confirmatory", "run role mismatch")
    require(run["selected_probe_id"] == EXPECTED_PROBE_ID, "run probe mismatch")
    require(
        run["selected_probe_ordinal"] == EXPECTED_PROBE_ORDINAL,
        "run ordinal mismatch",
    )
    training_ids = [
        str(case["case_id"]) for case in config["data"]["training_cases"]
    ]
    require(run["training_case_ids"] == training_ids, "run training binding mismatch")
    require(run["probe_commitment_id"] == EXPECTED_COMMITMENT, "run commitment mismatch")
    require(
        run["training_views_sha256"]
        == "b9522be46ba717683c4064596ad7e8c0311a2c0ef8ebe0903f2c8442d5c6e9d2",
        "training-view hash mismatch",
    )
    require(
        run["probe_view_sha256"]
        == "2eecfe1b1f90c346511a19a3c52ac4a46c9d4d3cd12103c43e5e3ac00220233b",
        "confirmatory-view hash mismatch",
    )

    traces = run["traces"]
    require(len(traces) == len(EXPECTED_CYCLES), "primary trace count mismatch")
    require([trace["cycle"] for trace in traces] == EXPECTED_CYCLES, "trace order mismatch")
    threshold = float(config["architecture"]["proposal_threshold"])
    for trace in traces:
        validate_trace(trace, seed, threshold)

    parent, learned, second, ablated, active, inert_a, inert_b, renamed = traces
    require(parent["proposal"] == 0, "parent proposal mismatch")
    require(learned["proposal"] == 1, "learned proposal mismatch")
    require(second["proposal"] == 0, "second proposal mismatch")
    require(ablated["proposal"] == 1, "ablated proposal mismatch")
    require(parent["view"] == learned["view"], "parent/learned probe mismatch")
    require(second["view"]["relation"] == learned["proposal"], "missing intercycle link")
    require(second["parameters"] == learned["parameters"], "learned weights changed")
    require(second["proposal"] != ablated["proposal"], "ablation is inert")
    require(
        abs(learned["neural"]["probability"] - active["neural"]["probability"])
        > tolerance,
        "active relation did not change prediction",
    )
    require(
        abs(inert_a["neural"]["probability"] - inert_b["neural"]["probability"])
        <= tolerance,
        "inert relation control changed prediction",
    )
    require(
        abs(learned["neural"]["probability"] - renamed["neural"]["probability"])
        <= tolerance,
        "address renaming changed prediction",
    )
    sealed_hash = sha256_bytes(canonical_bytes(traces))
    require(sealed_hash == run["sealed_primary_trace_sha256"], "trace seal mismatch")
    audit = run["deferred_audit"]
    require(audit["checked_after_seal"] is True, "audit was not deferred")
    require(audit["primary_trace_unchanged"] is True, "audit changed primary trace")
    require(audit["all_passed"] is True, "recorded audit failed")
    require(all(audit["checks"].values()), "a recorded audit check is false")


def validate_report(
    report: dict[str, Any],
    config: dict[str, Any],
    *,
    script_hash: str,
    config_hash: str,
    result_hash: str,
) -> None:
    validate_config(config)
    require(report["protocol"] == EXPECTED_PROTOCOL, "protocol mismatch")
    require(report["mode"] == "confirmatory", "result is not confirmatory")
    require(report["precommitted_seeds"] == EXPECTED_SEEDS, "seed list mismatch")
    require(result_hash == EXPECTED_RESULT_SHA256, "reference result hash mismatch")
    require(script_hash == EXPECTED_SCRIPT_SHA256, "frozen script hash mismatch")
    require(config_hash == EXPECTED_CONFIG_SHA256, "frozen config hash mismatch")
    require(
        sha256_bytes(canonical_bytes(config["data"])) == EXPECTED_DATA_SHA256,
        "frozen data hash mismatch",
    )
    provenance = report["provenance"]
    expected_provenance = {
        "script_sha256": script_hash,
        "config_sha256": config_hash,
        "data_sha256": EXPECTED_DATA_SHA256,
        "training_sha256": EXPECTED_TRAINING_SHA256,
        "probe_policy_sha256": EXPECTED_PROBE_POLICY_SHA256,
    }
    for field, expected in expected_provenance.items():
        require(provenance[field] == expected, f"recorded {field} mismatch")
    runs = report["facts"]["runs"]
    require([run["seed"] for run in runs] == EXPECTED_SEEDS, "run seed order mismatch")
    tolerance = float(config["criteria"]["float_tolerance"])
    for run in runs:
        validate_run(run, config, tolerance)
    require(report["facts"]["every_seed_passed"] is True, "aggregate result failed")


def negative_self_tests(
    report: dict[str, Any],
    config: dict[str, Any],
    script_hash: str,
    config_hash: str,
    result_hash: str,
) -> dict[str, bool]:
    mutations: dict[str, dict[str, Any]] = {}
    for name, path, value in (
        ("candidate_rewrite_rejected", ("candidate",), "admitted"),
        ("uncertified_effect_rejected", ("governed_effect",), "relation-incorporated"),
        ("prediction_substitution_rejected", ("consumed_prediction",), 0.0),
        ("probe_role_substitution_rejected", ("probe_role",), "smoke"),
        ("probe_identity_substitution_rejected", ("probe_id",), "smoke-0"),
    ):
        mutation = copy.deepcopy(report)
        trace = mutation["facts"]["runs"][0]["traces"][0]
        trace[path[0]] = value
        mutations[name] = mutation

    broken_link = copy.deepcopy(report)
    broken_link["facts"]["runs"][0]["traces"][2]["view"]["relation"] = 0
    mutations["missing_intercycle_link_rejected"] = broken_link
    missing_field = copy.deepcopy(report)
    del missing_field["facts"]["runs"][0]["traces"][0]["proposal"]
    mutations["missing_primary_field_rejected"] = missing_field

    outcomes: dict[str, bool] = {}
    for name, mutation in mutations.items():
        try:
            validate_report(
                mutation,
                config,
                script_hash=script_hash,
                config_hash=config_hash,
                result_hash=result_hash,
            )
        except (ValidationError, KeyError, TypeError):
            outcomes[name] = True
        else:
            outcomes[name] = False

    try:
        validate_report(
            report,
            config,
            script_hash="0" * 64,
            config_hash=config_hash,
            result_hash=result_hash,
        )
    except ValidationError:
        outcomes["provenance_substitution_rejected"] = True
    else:
        outcomes["provenance_substitution_rejected"] = False
    return outcomes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--script", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--result", type=Path, required=True)
    args = parser.parse_args()
    try:
        config_bytes, config = load_json(args.config)
        result_bytes, report = load_json(args.result)
        script_hash = sha256_bytes(args.script.read_bytes())
        config_hash = sha256_bytes(config_bytes)
        result_hash = sha256_bytes(result_bytes)
        validate_report(
            report,
            config,
            script_hash=script_hash,
            config_hash=config_hash,
            result_hash=result_hash,
        )
        negative = negative_self_tests(
            report, config, script_hash, config_hash, result_hash
        )
        require(all(negative.values()), "a negative self-test was accepted")
    except (ValidationError, KeyError, TypeError, ValueError, OSError) as error:
        print(f"refinement verification failed: {error}", file=sys.stderr)
        return 1

    summary = {
        "protocol": EXPECTED_PROTOCOL,
        "reference_result_sha256": result_hash,
        "runs_verified": len(report["facts"]["runs"]),
        "primary_traces_verified": sum(
            len(run["traces"]) for run in report["facts"]["runs"]
        ),
        "negative_self_tests": negative,
        "status": "verified",
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
