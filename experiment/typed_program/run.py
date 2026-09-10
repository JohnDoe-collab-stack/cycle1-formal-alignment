#!/usr/bin/env python3
"""Run the finite typed-program self-extension protocol."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, NoReturn


ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[1]
SOURCE_NAMES = ("protocol.json", "run.py", "worker.py", "verify.py")


class ProtocolError(Exception):
    pass


def fail(message: str) -> NoReturn:
    raise ProtocolError(message)


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


def formation_depth(formation: dict[str, Any]) -> int:
    if formation["tag"] in {"identity", "negate", "duplicate", "first"}:
        return 1
    if formation["tag"] == "compose":
        return max(formation_depth(formation["left"]), formation_depth(formation["right"])) + 1
    fail("unknown formation")


def formation_key(formation: dict[str, Any]) -> str:
    formation_depth(formation)
    return json.dumps(formation, sort_keys=True, separators=(",", ":"))


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
    fail("non-bit formation in probe")


def invoke_worker(request: dict[str, Any]) -> dict[str, Any]:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "worker.py")],
        input=canonical_bytes(request),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        fail(f"worker rejected request: {completed.stdout.decode(errors='replace')}")
    response = json.loads(completed.stdout)
    if not isinstance(response, dict) or "error" in response:
        fail("invalid worker response")
    return response


def generated_bits(sealed_descriptor: dict[str, Any], seed: str, width: int) -> list[bool]:
    key = canonical_bytes({"descriptor": normalize(sealed_descriptor), "seed": seed})
    bits: list[bool] = []
    counter = 0
    while len(bits) < width:
        block = hashlib.sha256(key + counter.to_bytes(4, "big")).digest()
        for byte in block:
            for shift in range(8):
                bits.append(bool((byte >> shift) & 1))
                if len(bits) == width:
                    return bits
        counter += 1
    return bits


def reserve(ledger: list[dict[str, Any]], role: str, values: list[bool]) -> str:
    signature = digest({"carrier": "bit-sequence", "values": values})
    if any(entry["signature"] == signature for entry in ledger):
        fail(f"cumulative exposure collision for {role}")
    ledger.append({"role": role, "signature": signature})
    return signature


def training_bits(descriptor: dict[str, Any], width: int) -> list[bool]:
    return generated_bits(descriptor, "training-view-not-probe", width)


def git_state() -> tuple[str, bool]:
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPOSITORY, check=True,
        stdout=subprocess.PIPE, text=True,
    ).stdout.strip()
    dirty = bool(subprocess.run(
        ["git", "status", "--porcelain"], cwd=REPOSITORY, check=True,
        stdout=subprocess.PIPE, text=True,
    ).stdout.strip())
    return commit, dirty


def run(mode: str) -> dict[str, Any]:
    protocol = json.loads((ROOT / "protocol.json").read_text(encoding="utf-8"))
    commit, dirty = git_state()
    if mode == "confirmatory" and dirty:
        fail("confirmatory run requires a clean source-freeze commit")
    seed = protocol["generator"][f"{mode}_seed"]
    width = int(protocol["language"]["probe_width"])
    increment = int(protocol["language"]["capacity_increment"])
    capacity = int(protocol["language"]["initial_capacity"])
    corpus = [{"address": 0, "source": "bit", "target": "bit", "formation": {"tag": "negate"}}]
    ledger: list[dict[str, Any]] = []
    stages: list[dict[str, Any]] = []
    events: list[str] = []
    first_source = json.loads(json.dumps(corpus))
    first_acquired = None

    for stage_number in range(2):
        source = json.loads(json.dumps(corpus))
        incoming_capacity = capacity
        obligation = frontier(source)
        if obligation is None:
            fail("unexpected finite saturation")

        parent_probe = generated_bits(
            {"incoming_source": normalize(source)}, "public-incoming-view", width
        )
        incoming_signature = reserve(
            ledger, f"stage-{stage_number}-incoming", parent_probe
        )

        descriptor = {
            "source_corpus": normalize(source),
            "source_interface": "bit->bit",
            "frontier_rule": protocol["frontier"]["rule"],
            "obligation_depth": formation_depth(obligation),
        }
        parent_request = {
            "operation": "measure", "capacity": incoming_capacity,
            "corpus": source, "probe_input": parent_probe, "allow_update": False,
        }
        parent_response = invoke_worker(parent_request)
        events.extend([f"stage-{stage_number}:incoming-proposition", f"stage-{stage_number}:elaboration"])

        sealed = {"descriptor": descriptor, "sha256": digest(descriptor)}
        events.append(f"stage-{stage_number}:descriptor-sealed")
        exposure = training_bits({"training": descriptor}, width)
        training_signature = reserve(ledger, f"stage-{stage_number}-training", exposure)
        events.append(f"stage-{stage_number}:training-exposure-recorded")

        events.append(f"stage-{stage_number}:seed-revealed")
        probe = generated_bits(descriptor, seed, width)
        probe_signature = reserve(ledger, f"stage-{stage_number}-probe", probe)
        events.append(f"stage-{stage_number}:probe-reserved")

        evaluation_parent_request = {
            "operation": "measure", "capacity": incoming_capacity,
            "corpus": source, "probe_input": probe, "allow_update": False,
        }
        evaluation_parent_response = invoke_worker(evaluation_parent_request)

        training_request = {
            "operation": "train",
            "incoming_capacity": incoming_capacity,
            "increment": increment,
            "training_view": {
                "source_corpus_sha256": digest(normalize(source)),
                "parent_proposal": parent_response["proposal"],
                "exposure": exposure,
            },
            "public_bounds": {"maximum_depth": protocol["language"]["maximum_composition_depth"]},
        }
        training_response = invoke_worker(training_request)
        acquired_capacity = int(training_response["acquired_capacity"])
        events.append(f"stage-{stage_number}:learning-complete")

        learned_request = {
            "operation": "measure", "capacity": acquired_capacity,
            "corpus": source, "probe_input": probe, "allow_update": False,
        }
        learned_response = invoke_worker(learned_request)
        events.append(f"stage-{stage_number}:same-probe-parent-learned-measurement")
        proposal = learned_response["proposal"]
        if proposal != obligation:
            fail("learned proposal is not the runtime frontier")
        expected_behavior = [evaluate(obligation, value) for value in probe]
        if learned_response["probe_behavior"] != expected_behavior:
            fail("worker behavior disagrees with total semantics")

        certified = {
            "address": max(entry["address"] for entry in source) + 1,
            "source": "bit", "target": "bit", "formation": proposal,
        }
        corpus = source + [certified]
        capacity = acquired_capacity
        events.append(f"stage-{stage_number}:successor-published")
        stages.append({
            "stage": stage_number,
            "source_corpus": source,
            "incoming_capacity": incoming_capacity,
            "frontier": obligation,
            "parent_worker_request": parent_request,
            "parent_worker_response": parent_response,
            "sealed_descriptor": sealed,
            "incoming_signature": incoming_signature,
            "training_signature": training_signature,
            "probe_signature": probe_signature,
            "generated_probe": probe,
            "evaluation_parent_worker_request": evaluation_parent_request,
            "evaluation_parent_worker_response": evaluation_parent_response,
            "training_worker_request": training_request,
            "training_worker_response": training_response,
            "learned_worker_request": learned_request,
            "learned_worker_response": learned_response,
            "certified_abstraction": certified,
            "target_corpus": corpus,
            "acquired_capacity": acquired_capacity,
        })
        if stage_number == 0:
            first_acquired = acquired_capacity

    if stages[1]["source_corpus"] != stages[0]["target_corpus"]:
        fail("second transition did not consume the produced first corpus")

    counterfactual_probe = stages[1]["generated_probe"]
    no_incorporation_request = {
        "operation": "measure", "capacity": first_acquired,
        "corpus": first_source, "probe_input": counterfactual_probe, "allow_update": False,
    }
    no_incorporation_response = invoke_worker(no_incorporation_request)
    no_incorporation_frontier = frontier(first_source)
    restored_weights_request = {
        "operation": "measure", "capacity": stages[1]["incoming_capacity"],
        "corpus": stages[1]["source_corpus"], "probe_input": counterfactual_probe,
        "allow_update": False,
    }
    restored_weights_response = invoke_worker(restored_weights_request)
    if no_incorporation_frontier == stages[1]["frontier"]:
        fail("incorporation counterfactual did not change the second obligation")
    if restored_weights_response["proposal"] == stages[1]["learned_worker_response"]["proposal"]:
        fail("learning counterfactual did not change the second proposal")

    renamed = [{**entry, "address": entry["address"] + 1000} for entry in stages[1]["source_corpus"]]
    renamed_descriptor = {**stages[1]["sealed_descriptor"]["descriptor"], "source_corpus": normalize(renamed)}
    if digest(normalize(renamed)) != digest(normalize(stages[1]["source_corpus"])):
        fail("address normalizer changed semantic corpus")
    if generated_bits(renamed_descriptor, seed, width) != stages[1]["generated_probe"]:
        fail("address renaming changed generated probe")

    return {
        "protocol": protocol["protocol"],
        "mode": mode,
        "source_freeze_commit": commit,
        "source_was_clean": not dirty,
        "protocol_sha256": file_digest(ROOT / "protocol.json"),
        "source_sha256": {name: file_digest(ROOT / name) for name in SOURCE_NAMES},
        "seed_commitment": digest(seed),
        "events": events,
        "ledger": ledger,
        "stages": stages,
        "counterfactuals": {
            "without_first_incorporation": {
                "request": no_incorporation_request,
                "response": no_incorporation_response,
                "computed_frontier": no_incorporation_frontier,
            },
            "restored_prior_weights": {
                "request": restored_weights_request, "response": restored_weights_response,
            },
        },
        "address_renaming": {
            "renamed_corpus": renamed,
            "normalized_equal": normalize(renamed) == normalize(stages[1]["source_corpus"]),
            "probe_transport_exact": True,
        },
        "final_corpus": corpus,
        "final_capacity": capacity,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("smoke", "confirmatory"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.output.exists():
            fail("output path already exists")
        if args.mode == "confirmatory" and args.output.parent.resolve() != (ROOT / "results").resolve():
            fail("confirmatory output must be a new file in results/")
        result = run(args.mode)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(canonical_bytes(result) + b"\n")
        print(args.output)
        return 0
    except (ProtocolError, KeyError, TypeError, ValueError, subprocess.SubprocessError) as error:
        print(f"protocol error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
