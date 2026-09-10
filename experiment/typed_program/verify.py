#!/usr/bin/env python3
"""Read-only verifier for a typed-program primary journal."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Callable, NoReturn


ROOT = Path(__file__).resolve().parent
SOURCE_NAMES = ("protocol.json", "run.py", "worker.py", "verify.py")


class ValidationError(Exception):
    pass


def fail(message: str) -> NoReturn:
    raise ValidationError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: normalize(item) for key, item in sorted(value.items()) if key != "address"}
    if isinstance(value, list):
        return [normalize(item) for item in value]
    return value


def walk_keys(value: Any) -> set[str]:
    if isinstance(value, dict):
        return set(value).union(*(walk_keys(item) for item in value.values()))
    if isinstance(value, list):
        return set().union(*(walk_keys(item) for item in value)) if value else set()
    return set()


def formation_depth(formation: dict[str, Any]) -> int:
    tag = formation.get("tag")
    if tag in {"identity", "negate", "duplicate", "first"}:
        return 1
    if tag == "compose" and set(formation) == {"tag", "left", "right"}:
        return max(formation_depth(formation["left"]), formation_depth(formation["right"])) + 1
    fail("ill-formed formation")


def formation_key(formation: dict[str, Any]) -> str:
    formation_depth(formation)
    return json.dumps(formation, sort_keys=True, separators=(",", ":"))


def validate_corpus(corpus: Any) -> list[dict[str, Any]]:
    require(isinstance(corpus, list) and corpus, "corpus must be a positive list")
    addresses: list[int] = []
    for entry in corpus:
        require(set(entry) == {"address", "source", "target", "formation"}, "corpus schema mismatch")
        require(entry["source"] == "bit" and entry["target"] == "bit", "published witness must be bit-to-bit")
        require(isinstance(entry["address"], int), "technical address must be integral")
        formation_depth(entry["formation"])
        addresses.append(entry["address"])
    require(len(addresses) == len(set(addresses)), "duplicate technical address")
    return corpus


def frontier(corpus: list[dict[str, Any]]) -> dict[str, Any] | None:
    present = {formation_key(entry["formation"]) for entry in corpus}
    for left in corpus:
        for right in corpus:
            if left["target"] == right["source"]:
                candidate = {"tag": "compose", "left": left["formation"], "right": right["formation"]}
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
    fail("non-bit formation in evaluation")


def generated_bits(descriptor: dict[str, Any], seed: str, width: int) -> list[bool]:
    key = canonical_bytes({"descriptor": normalize(descriptor), "seed": seed})
    values: list[bool] = []
    counter = 0
    while len(values) < width:
        block = hashlib.sha256(key + counter.to_bytes(4, "big")).digest()
        for byte in block:
            for shift in range(8):
                values.append(bool((byte >> shift) & 1))
                if len(values) == width:
                    return values
        counter += 1
    return values


def expected_measure(request: dict[str, Any]) -> dict[str, Any]:
    required = {"operation", "capacity", "corpus", "probe_input", "allow_update"}
    require(set(request) == required, "measurement request schema mismatch")
    require(request["operation"] == "measure" and request["allow_update"] is False, "measurement is not read-only")
    require(not {"target", "expected"}.intersection(request), "target leaked to measurement")
    corpus = validate_corpus(request["corpus"])
    candidate = frontier(corpus)
    proposal = candidate if candidate is not None and formation_depth(candidate) <= request["capacity"] else None
    behavior = None if proposal is None else [evaluate(proposal, bool(value)) for value in request["probe_input"]]
    return {
        "operation": "measure-result", "predicted": proposal,
        "consumed_prediction": proposal, "proposal": proposal,
        "probe_behavior": behavior,
    }


def validate_training(request: dict[str, Any], response: dict[str, Any]) -> None:
    required = {"operation", "incoming_capacity", "increment", "training_view", "public_bounds"}
    require(set(request) == required, "training request schema mismatch")
    forbidden = {"probe", "probe_input", "target", "expected", "future_formation", "future_ast"}
    require(not forbidden.intersection(walk_keys(request)), "probe or target leaked to training")
    require(request["operation"] == "train" and request["increment"] == 1, "training rule mismatch")
    expected = {
        "operation": "train-result",
        "incoming_capacity": request["incoming_capacity"],
        "acquired_capacity": request["incoming_capacity"] + 1,
        "evidence": "single-constructive-increment",
    }
    require(response == expected, "training response mismatch")


def validate_result(result: dict[str, Any], protocol: dict[str, Any]) -> None:
    require(result["protocol"] == protocol["protocol"], "protocol identifier mismatch")
    require(result["mode"] in {"smoke", "confirmatory"}, "unknown run mode")
    if result["mode"] == "confirmatory":
        require(result["source_was_clean"] is True, "confirmatory source was not frozen cleanly")
    require(result["protocol_sha256"] == file_digest(ROOT / "protocol.json"), "protocol hash mismatch")
    require(result["source_sha256"] == {name: file_digest(ROOT / name) for name in SOURCE_NAMES}, "source hash mismatch")
    seed = protocol["generator"][f"{result['mode']}_seed"]
    require(result["seed_commitment"] == digest(seed), "seed commitment mismatch")
    require(protocol["frontier"]["cycle_ordinal_input"] is False, "rank-indexed frontier enabled")
    forbidden_protocol = {"first_ast", "second_ast", "expected_ast", "delta1_ast", "candidate_catalogue"}
    require(not forbidden_protocol.intersection(walk_keys(protocol)), "expected program catalogue in protocol")

    stages = result["stages"]
    require(len(stages) == protocol["criteria"]["required_transitions"] == 2, "transition count mismatch")
    expected_events: list[str] = []
    ledger_expected: list[dict[str, Any]] = []
    previous_target = None
    width = protocol["language"]["probe_width"]

    for ordinal, stage in enumerate(stages):
        require(stage["stage"] == ordinal, "stage journal order mismatch")
        source = validate_corpus(stage["source_corpus"])
        if previous_target is not None:
            require(source == previous_target, "second call did not consume the produced first corpus")
        obligation = frontier(source)
        require(stage["frontier"] == obligation and obligation is not None, "frontier mismatch")
        require(stage["sealed_descriptor"]["sha256"] == digest(stage["sealed_descriptor"]["descriptor"]), "descriptor seal mismatch")
        descriptor = stage["sealed_descriptor"]["descriptor"]
        require(descriptor["source_corpus"] == normalize(source), "descriptor source mismatch")
        require(descriptor["obligation_depth"] == formation_depth(obligation), "descriptor obligation mismatch")
        probe = generated_bits(descriptor, seed, width)
        require(stage["generated_probe"] == probe, "generated probe mismatch")

        parent_expected = expected_measure(stage["parent_worker_request"])
        require(stage["parent_worker_response"] == parent_expected, "incoming parent response mismatch")
        expected_incoming_probe = generated_bits(
            {"incoming_source": normalize(source)}, "public-incoming-view", width
        )
        require(
            stage["parent_worker_request"]["probe_input"] == expected_incoming_probe,
            "incoming exposed input mismatch",
        )
        evaluation_parent_expected = expected_measure(stage["evaluation_parent_worker_request"])
        require(stage["evaluation_parent_worker_response"] == evaluation_parent_expected, "same-probe parent response mismatch")
        require(stage["evaluation_parent_worker_request"]["probe_input"] == probe, "parent measured a substituted probe")
        validate_training(stage["training_worker_request"], stage["training_worker_response"])
        require(stage["training_worker_request"]["incoming_capacity"] == stage["incoming_capacity"], "training consumed wrong weights")
        require(stage["acquired_capacity"] == stage["training_worker_response"]["acquired_capacity"], "acquired weights mismatch")
        require(stage["learned_worker_request"]["capacity"] == stage["acquired_capacity"], "dynamics did not consume acquired weights")
        require(stage["learned_worker_request"]["probe_input"] == probe, "learned path measured a substituted probe")
        learned_expected = expected_measure(stage["learned_worker_request"])
        require(stage["learned_worker_response"] == learned_expected, "learned response mismatch")
        require(learned_expected["predicted"] == learned_expected["consumed_prediction"] == learned_expected["proposal"], "prediction was not consumed exactly")
        require(learned_expected["proposal"] == obligation, "learned proposal is not the frontier")

        certified = stage["certified_abstraction"]
        require(certified["formation"] == obligation, "candidate was rewritten after proposal")
        require(certified["source"] == "bit" and certified["target"] == "bit", "certified interface mismatch")
        target = validate_corpus(stage["target_corpus"])
        require(target == source + [certified], "target corpus is not exact incorporation")
        require(formation_key(certified["formation"]) in {formation_key(entry["formation"]) for entry in target}, "regime admission failed")
        require(all(isinstance(evaluate(certified["formation"], bit), bool) for bit in (False, True)), "total semantic norm failed")

        training_values = stage["training_worker_request"]["training_view"]["exposure"]
        incoming_values = stage["parent_worker_request"]["probe_input"]
        incoming_signature = digest({"carrier": "bit-sequence", "values": incoming_values})
        training_signature = digest({"carrier": "bit-sequence", "values": training_values})
        probe_signature = digest({"carrier": "bit-sequence", "values": probe})
        require(stage["incoming_signature"] == incoming_signature, "incoming ledger signature mismatch")
        require(stage["training_signature"] == training_signature, "training ledger signature mismatch")
        require(stage["probe_signature"] == probe_signature, "probe ledger signature mismatch")
        ledger_expected.extend([
            {"role": f"stage-{ordinal}-incoming", "signature": incoming_signature},
            {"role": f"stage-{ordinal}-training", "signature": training_signature},
            {"role": f"stage-{ordinal}-probe", "signature": probe_signature},
        ])
        previous_target = target
        expected_events.extend([
            f"stage-{ordinal}:incoming-proposition", f"stage-{ordinal}:elaboration",
            f"stage-{ordinal}:descriptor-sealed", f"stage-{ordinal}:training-exposure-recorded",
            f"stage-{ordinal}:seed-revealed", f"stage-{ordinal}:probe-reserved",
            f"stage-{ordinal}:learning-complete", f"stage-{ordinal}:same-probe-parent-learned-measurement",
            f"stage-{ordinal}:successor-published",
        ])

    require(result["events"] == expected_events, "causal event order mismatch")
    require(result["ledger"] == ledger_expected, "cumulative ledger mismatch")
    signatures = [entry["signature"] for entry in result["ledger"]]
    require(len(signatures) == len(set(signatures)), "cumulative exposure collision")
    require(result["final_corpus"] == stages[-1]["target_corpus"], "final corpus mismatch")
    require(result["final_capacity"] == stages[-1]["acquired_capacity"], "final weights mismatch")

    no_incorporation = result["counterfactuals"]["without_first_incorporation"]
    restored = result["counterfactuals"]["restored_prior_weights"]
    require(no_incorporation["response"] == expected_measure(no_incorporation["request"]), "incorporation counterfactual response mismatch")
    require(restored["response"] == expected_measure(restored["request"]), "learning counterfactual response mismatch")
    require(no_incorporation["request"]["corpus"] == stages[0]["source_corpus"], "incorporation counterfactual changed extra data")
    require(no_incorporation["request"]["capacity"] == stages[0]["acquired_capacity"], "incorporation counterfactual changed weights")
    require(no_incorporation["request"]["capacity"] == stages[1]["incoming_capacity"], "counterfactual and factual frontier used different incoming weights")
    require(no_incorporation["computed_frontier"] == frontier(no_incorporation["request"]["corpus"]), "incorporation counterfactual frontier mismatch")
    require(no_incorporation["computed_frontier"] != stages[1]["frontier"], "incorporation counterfactual did not change the obligation")
    require(restored["request"]["corpus"] == stages[1]["source_corpus"], "learning counterfactual changed corpus")
    require(restored["request"]["capacity"] == stages[1]["incoming_capacity"], "prior weights not restored")
    require(restored["response"]["proposal"] != stages[1]["learned_worker_response"]["proposal"], "learning counterfactual did not diverge")

    renamed = result["address_renaming"]
    require(renamed["normalized_equal"] is True and renamed["probe_transport_exact"] is True, "renaming certificate absent")
    require(normalize(renamed["renamed_corpus"]) == normalize(stages[1]["source_corpus"]), "address renaming altered constitution")
    renamed_descriptor = {**stages[1]["sealed_descriptor"]["descriptor"], "source_corpus": normalize(renamed["renamed_corpus"])}
    require(generated_bits(renamed_descriptor, seed, width) == stages[1]["generated_probe"], "renaming changed generated probe")


def mutation_tests(result: dict[str, Any], protocol: dict[str, Any]) -> None:
    mutations: list[Callable[[dict[str, Any]], None]] = [
        lambda value: value["stages"][0]["training_worker_request"].update({"probe": [True]}),
        lambda value: value["stages"][1].update({"source_corpus": value["stages"][0]["source_corpus"]}),
        lambda value: value["stages"][0]["target_corpus"].pop(),
        lambda value: value["stages"][1]["learned_worker_request"].update({"capacity": 99}),
        lambda value: value["stages"][1]["learned_worker_response"].update({"proposal": {"tag": "identity"}}),
        lambda value: value["stages"][1].update({"generated_probe": value["stages"][0]["generated_probe"]}),
        lambda value: value["ledger"].__setitem__(1, copy.deepcopy(value["ledger"][0])),
        lambda value: value["events"].reverse(),
        lambda value: value["counterfactuals"]["without_first_incorporation"]["request"].update({"capacity": 77}),
        lambda value: value["counterfactuals"]["restored_prior_weights"]["request"].update({"corpus": value["stages"][0]["source_corpus"]}),
        lambda value: value["address_renaming"].update({"normalized_equal": False}),
        lambda value: value.update({"final_capacity": 100}),
    ]
    for index, mutate in enumerate(mutations):
        candidate = copy.deepcopy(result)
        mutate(candidate)
        try:
            validate_result(candidate, protocol)
        except ValidationError:
            continue
        fail(f"negative mutation {index} was accepted")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("result", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        protocol = json.loads((ROOT / "protocol.json").read_text(encoding="utf-8"))
        result = json.loads(args.result.read_text(encoding="utf-8"))
        validate_result(result, protocol)
        if args.self_test:
            mutation_tests(result, protocol)
        print("typed-program journal verified")
        return 0
    except (ValidationError, KeyError, TypeError, ValueError, OSError) as error:
        print(f"verification error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
