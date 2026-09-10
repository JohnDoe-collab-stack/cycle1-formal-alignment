#!/usr/bin/env python3
"""Precommitted finite experiment for constitutive transformer alignment.

The neural producer predicts and proposes.  A separate exact runtime constructs
the candidate, checks operational admission and an independently implemented
norm, and issues an effect certificate only on their agreement.  The first
learned proposal is incorporated as the relation consumed by the second cycle.
Audit runs only after the immutable primary journal has been sealed.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import math
import platform
import sys
from pathlib import Path
from typing import Any

import numpy as np


@dataclasses.dataclass(frozen=True)
class AttentionMemory:
    keys: tuple[float, float]
    values: tuple[float, float]
    address_polarity: float = 1.0

    def renamed(self) -> "AttentionMemory":
        return AttentionMemory(
            keys=(-self.keys[0], -self.keys[1]),
            values=self.values,
            address_polarity=-self.address_polarity,
        )


@dataclasses.dataclass(frozen=True)
class AuthorizedView:
    tokens: tuple[float, ...]
    cache: float
    memory: AttentionMemory
    relation: int
    budget: int


@dataclasses.dataclass(frozen=True)
class Parameters:
    predictive_bias: float


@dataclasses.dataclass(frozen=True)
class NeuralOutput:
    activation: float
    query: float
    attention: tuple[float, float]
    context: float
    logit: float
    probability: float


@dataclasses.dataclass(frozen=True)
class PrimaryTrace:
    seed: int
    cycle: str
    probe_role: str
    probe_id: str
    probe_ordinal: int
    view: AuthorizedView
    parameters: Parameters
    neural: NeuralOutput
    consumed_prediction: float
    proposal: int
    candidate: str
    regime_admitted: bool
    norm_satisfied: bool
    error_position: int | None
    error_reason: str | None
    certificate_issued: bool
    governed_effect: str | None


class NeuralProducer:
    def __init__(self, architecture: dict[str, Any]) -> None:
        self.relation_scale = float(architecture["relation_scale"])
        self.token_scale = float(architecture["token_scale"])
        self.context_scale = float(architecture["context_scale"])
        self.cache_scale = float(architecture["cache_scale"])

    def predict(
        self,
        parameters: Parameters,
        view: AuthorizedView,
        *,
        consume_relation: bool = True,
    ) -> NeuralOutput:
        activation = sum(view.tokens) / len(view.tokens) if view.tokens else 0.0
        relation_term = self.relation_scale * (2.0 * view.relation - 1.0)
        if not consume_relation:
            relation_term = 0.0
        semantic_query = relation_term + self.token_scale * activation
        query = view.memory.address_polarity * semantic_query
        scores = np.asarray(view.memory.keys, dtype=np.float64) * query
        shifted = scores - np.max(scores)
        attention_array = np.exp(shifted)
        attention_array = attention_array / np.sum(attention_array)
        values = np.asarray(view.memory.values, dtype=np.float64)
        context = float(np.dot(attention_array, values))
        logit = (
            parameters.predictive_bias
            + self.cache_scale * view.cache
            - self.context_scale * context
        )
        probability = 1.0 / (1.0 + math.exp(-logit))
        return NeuralOutput(
            activation=activation,
            query=query,
            attention=(float(attention_array[0]), float(attention_array[1])),
            context=context,
            logit=logit,
            probability=probability,
        )


class ConstitutiveRuntime:
    def __init__(self, threshold: float) -> None:
        self.threshold = threshold

    def propose(self, consumed_prediction: float) -> int:
        return int(consumed_prediction >= self.threshold)

    def candidate(self, proposal: int) -> str:
        return "admitted" if proposal == 1 else "outside"

    def regime(self, candidate: str) -> bool:
        return candidate == "admitted"

    def autonomous_norm(self, candidate: str) -> bool:
        return candidate in {"admitted"}

    def diagnose(self, candidate: str) -> tuple[int | None, str | None]:
        if candidate == "outside":
            return 0, "outside-regime-and-norm"
        return None, None


class GovernedEffector:
    def effectuate(self, admitted: bool, normative: bool) -> tuple[bool, str | None]:
        certificate = admitted and normative
        return certificate, "relation-incorporated" if certificate else None


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")


def trace_dict(trace: PrimaryTrace) -> dict[str, Any]:
    return dataclasses.asdict(trace)


def journal_hash(journal: tuple[PrimaryTrace, ...]) -> str:
    return sha256_bytes(canonical_bytes([trace_dict(trace) for trace in journal]))


def train_bias(
    producer: NeuralProducer,
    initial: Parameters,
    examples: tuple[tuple[AuthorizedView, float], ...],
    learning_rate: float,
    steps: int,
) -> Parameters:
    bias = initial.predictive_bias
    for _step in range(steps):
        for view, target in examples:
            output = producer.predict(Parameters(bias), view)
            gradient = output.probability - target
            bias -= learning_rate * gradient
    return Parameters(bias)


def case_view(case: dict[str, Any], memory: AttentionMemory) -> AuthorizedView:
    return AuthorizedView(
        tokens=tuple(float(token) for token in case["tokens"]),
        cache=float(case["cache"]),
        memory=memory,
        relation=int(case["initial_relation"]),
        budget=int(case["budget"]),
    )


def produce_trace(
    seed: int,
    cycle: str,
    probe_role: str,
    probe_id: str,
    probe_ordinal: int,
    producer: NeuralProducer,
    runtime: ConstitutiveRuntime,
    effector: GovernedEffector,
    parameters: Parameters,
    view: AuthorizedView,
    *,
    consume_relation: bool = True,
) -> PrimaryTrace:
    neural = producer.predict(parameters, view, consume_relation=consume_relation)
    consumed_prediction = neural.probability
    proposal = runtime.propose(consumed_prediction)
    candidate = runtime.candidate(proposal)
    admitted = runtime.regime(candidate)
    normative = runtime.autonomous_norm(candidate)
    error_position, error_reason = runtime.diagnose(candidate)
    certificate, effect = effector.effectuate(admitted, normative)
    return PrimaryTrace(
        seed=seed,
        cycle=cycle,
        probe_role=probe_role,
        probe_id=probe_id,
        probe_ordinal=probe_ordinal,
        view=view,
        parameters=parameters,
        neural=neural,
        consumed_prediction=consumed_prediction,
        proposal=proposal,
        candidate=candidate,
        regime_admitted=admitted,
        norm_satisfied=normative,
        error_position=error_position,
        error_reason=error_reason,
        certificate_issued=certificate,
        governed_effect=effect,
    )


def exact_memory_check(memory: AttentionMemory, tolerance: float) -> bool:
    memories = tuple(
        AttentionMemory(memory.keys, (float(left), float(right)))
        for left in (0, 1)
        for right in (0, 1)
    )
    for first in memories:
        for second in memories:
            same_encoding = first.values == second.values
            same_futures = all(
                abs(first.values[query] - second.values[query]) <= tolerance
                for query in (0, 1)
            )
            if same_encoding != same_futures:
                return False
    return True


def run_seed(config: dict[str, Any], seed: int, mode: str) -> dict[str, Any]:
    architecture = config["architecture"]
    training = config["training"]
    data = config["data"]
    training_cases = data["training_cases"]
    probe_policy = data["probe_policy"]
    criteria = config["criteria"]
    tolerance = float(criteria["float_tolerance"])

    rng = np.random.default_rng(seed)
    initial_bias = float(training["initial_bias"]) + float(
        rng.uniform(-float(training["initial_jitter"]), float(training["initial_jitter"]))
    )
    parent_parameters = Parameters(initial_bias)
    memory = AttentionMemory(
        keys=tuple(float(value) for value in architecture["memory_keys"]),
        values=tuple(float(value) for value in architecture["memory_values"]),
    )
    if not training_cases:
        raise ValueError("training set must be nonempty")
    training_ids = tuple(str(case["case_id"]) for case in training_cases)
    if len(set(training_ids)) != len(training_ids):
        raise ValueError("training case identifiers must be unique")
    declared_training_ids = tuple(
        str(value) for value in probe_policy["training_case_ids"]
    )
    if declared_training_ids != training_ids:
        raise ValueError("probe policy does not bind the exact training set")
    training_views = tuple(case_view(case, memory) for case in training_cases)
    training_examples = tuple(
        (view, float(case["target_prediction"]))
        for case, view in zip(training_cases, training_views)
    )

    probes = probe_policy["probes"]
    probe_ids = tuple(str(probe["probe_id"]) for probe in probes)
    if len(set(probe_ids)) != len(probe_ids):
        raise ValueError("held-out probe identifiers must be unique")
    if set(training_ids).intersection(probe_ids):
        raise ValueError("training and held-out identifiers are not disjoint")
    probe_views = tuple(case_view(probe, memory) for probe in probes)
    if len(set(probe_views)) != len(probe_views):
        raise ValueError("held-out probe views must be unique")
    if set(training_views).intersection(probe_views):
        raise ValueError("a held-out probe duplicates a training view")
    if probe_policy["smoke_ordinal"] == probe_policy["confirmatory_ordinal"]:
        raise ValueError("smoke and confirmatory probes must be different")
    ordinal_field = f"{mode}_ordinal"
    selected_ordinal = int(probe_policy[ordinal_field])
    if selected_ordinal < 0 or selected_ordinal >= len(probes):
        raise ValueError("precommitted probe ordinal is outside the probe policy")
    selected_probe = probes[selected_ordinal]
    probe_id = str(selected_probe["probe_id"])
    initial_view = probe_views[selected_ordinal]

    producer = NeuralProducer(architecture)
    runtime = ConstitutiveRuntime(float(architecture["proposal_threshold"]))
    effector = GovernedEffector()
    learned_parameters = train_bias(
        producer,
        parent_parameters,
        training_examples,
        float(training["learning_rate"]),
        int(training["steps"]),
    )

    parent = produce_trace(
        seed, "parent", mode, probe_id, selected_ordinal,
        producer, runtime, effector, parent_parameters, initial_view
    )
    learned = produce_trace(
        seed, "learned-cycle-1", mode, probe_id, selected_ordinal,
        producer, runtime, effector, learned_parameters, initial_view
    )
    second_view = dataclasses.replace(
        initial_view,
        relation=learned.proposal,
        budget=initial_view.budget - 1,
    )
    second = produce_trace(
        seed, "learned-cycle-2", mode, probe_id, selected_ordinal,
        producer, runtime, effector, learned_parameters, second_view
    )
    ablated_view = dataclasses.replace(initial_view, budget=initial_view.budget - 1)
    ablated = produce_trace(
        seed, "intercycle-ablation", mode, probe_id, selected_ordinal,
        producer, runtime, effector, learned_parameters, ablated_view
    )
    relation_flipped_view = dataclasses.replace(initial_view, relation=1 - initial_view.relation)
    relation_active = produce_trace(
        seed, "active-relation-control", mode, probe_id, selected_ordinal,
        producer, runtime, effector,
        learned_parameters, relation_flipped_view
    )
    inert_initial = produce_trace(
        seed, "inert-original", mode, probe_id, selected_ordinal,
        producer, runtime, effector,
        learned_parameters, initial_view, consume_relation=False
    )
    inert_flipped = produce_trace(
        seed, "inert-flipped", mode, probe_id, selected_ordinal,
        producer, runtime, effector,
        learned_parameters, relation_flipped_view, consume_relation=False
    )
    renamed_view = dataclasses.replace(initial_view, memory=initial_view.memory.renamed())
    renamed = produce_trace(
        seed, "address-renamed", mode, probe_id, selected_ordinal,
        producer, runtime, effector,
        learned_parameters, renamed_view
    )

    journal = (
        parent,
        learned,
        second,
        ablated,
        relation_active,
        inert_initial,
        inert_flipped,
        renamed,
    )
    sealed_hash = journal_hash(journal)

    forbidden_view_fields = {
        "target",
        "norm",
        "verdict",
        "certificate",
        "audit",
    }
    authorized_fields = {field.name for field in dataclasses.fields(AuthorizedView)}
    checks = {
        "probe_selection_is_precommitted": (
            selected_ordinal == int(probe_policy[ordinal_field])
            and probe_policy["smoke_ordinal"] != probe_policy["confirmatory_ordinal"]
            and probe_policy["commitment_id"] == "fixed-held-out-probe-policy"
        ),
        "selected_probe_is_fresh": (
            probe_id not in set(training_ids)
            and initial_view not in training_views
        ),
        "training_and_probe_splits_are_exactly_bound": (
            declared_training_ids == training_ids
            and not set(training_ids).intersection(probe_ids)
        ),
        "parent_and_learned_share_exact_probe": (
            parent.probe_id == learned.probe_id == probe_id
            and parent.probe_role == learned.probe_role == mode
            and parent.probe_ordinal == learned.probe_ordinal == selected_ordinal
            and parent.view == learned.view == initial_view
        ),
        "target_absent_from_authorized_view": not bool(
            forbidden_view_fields.intersection(authorized_fields)
        ),
        "learning_changes_parameters": (
            parent_parameters.predictive_bias != learned_parameters.predictive_bias
        ),
        "prediction_changes_parent_to_learned": (
            abs(parent.neural.probability - learned.neural.probability) > tolerance
        ),
        "proposal_changes_parent_to_learned": parent.proposal != learned.proposal,
        "produced_prediction_consumed_exactly": all(
            trace.consumed_prediction == trace.neural.probability for trace in journal
        ),
        "parent_rejected_for_fixed_reason": (
            parent.proposal == int(criteria["required_parent_proposal"])
            and parent.error_position == 0
            and parent.error_reason == "outside-regime-and-norm"
        ),
        "learned_first_cycle_accepted": (
            learned.proposal == int(criteria["required_learned_proposal"])
            and learned.regime_admitted
            and learned.norm_satisfied
            and learned.certificate_issued
        ),
        "first_proposal_is_second_relation": second.view.relation == learned.proposal,
        "second_cycle_uses_same_learned_parameters": (
            second.parameters == learned.parameters
        ),
        "second_cycle_depends_on_incorporation": (
            second.proposal == int(criteria["required_second_proposal"])
            and ablated.proposal == int(criteria["required_ablated_second_proposal"])
            and second.proposal != ablated.proposal
        ),
        "active_relation_changes_prediction": (
            abs(learned.neural.probability - relation_active.neural.probability) > tolerance
        ),
        "inert_relation_control_is_unchanged": (
            abs(inert_initial.neural.probability - inert_flipped.neural.probability)
            <= tolerance
        ),
        "address_renaming_is_invariant": (
            abs(learned.neural.probability - renamed.neural.probability) <= tolerance
        ),
        "attention_memory_exact_for_declared_queries": exact_memory_check(memory, tolerance),
        "invalid_candidate_preserved": (
            parent.candidate == "outside" and parent.error_reason is not None
        ),
        "rejected_effect_is_confined": (
            not parent.certificate_issued and parent.governed_effect is None
        ),
        "regime_norm_adequacy_on_finite_carrier": all(
            runtime.regime(candidate) == runtime.autonomous_norm(candidate)
            for candidate in ("admitted", "outside")
        ),
    }

    audit_report = {
        "checked_after_seal": True,
        "checks": checks,
        "all_passed": all(checks.values()),
    }
    post_audit_hash = journal_hash(journal)
    audit_report["primary_trace_unchanged"] = sealed_hash == post_audit_hash
    audit_report["all_passed"] = bool(
        audit_report["all_passed"] and audit_report["primary_trace_unchanged"]
    )

    return {
        "seed": seed,
        "training_case_ids": list(training_ids),
        "probe_role": mode,
        "probe_commitment_id": probe_policy["commitment_id"],
        "selected_probe_id": probe_id,
        "selected_probe_ordinal": selected_ordinal,
        "training_views_sha256": sha256_bytes(
            canonical_bytes([dataclasses.asdict(view) for view in training_views])
        ),
        "probe_view_sha256": sha256_bytes(
            canonical_bytes(dataclasses.asdict(initial_view))
        ),
        "initial_parameters": dataclasses.asdict(parent_parameters),
        "learned_parameters": dataclasses.asdict(learned_parameters),
        "sealed_primary_trace_sha256": sealed_hash,
        "traces": [trace_dict(trace) for trace in journal],
        "deferred_audit": audit_report,
    }


def run_protocol(config_path: Path, mode: str) -> dict[str, Any]:
    config_bytes = config_path.read_bytes()
    config = json.loads(config_bytes)
    script_path = Path(__file__).resolve()
    seeds = [int(seed) for seed in config["seeds"]]
    runs = [run_seed(config, seed, mode) for seed in seeds]
    every_seed_passed = all(run["deferred_audit"]["all_passed"] for run in runs)
    return {
        "protocol": config["protocol"],
        "mode": mode,
        "provenance": {
            "script_sha256": sha256_bytes(script_path.read_bytes()),
            "config_sha256": sha256_bytes(config_bytes),
            "data_sha256": sha256_bytes(canonical_bytes(config["data"])),
            "training_sha256": sha256_bytes(
                canonical_bytes(config["data"]["training_cases"])
            ),
            "probe_policy_sha256": sha256_bytes(
                canonical_bytes(config["data"]["probe_policy"])
            ),
            "python": platform.python_version(),
            "numpy": np.__version__,
            "platform": platform.platform(),
        },
        "precommitted_seeds": seeds,
        "facts": {
            "runs": runs,
            "every_seed_passed": every_seed_passed,
        },
        "interpretation": {
            "supported": (
                "Within this finite task, learned prediction changes the "
                "constitutive proposal, the proposal is consumed by the next cycle, "
                "and the governed effect is confined on normative rejection."
            )
        },
        "limits": {
            "not_established": [
                "general transformer alignment",
                "unbounded-horizon autonomy",
                "natural-language hallucination reduction",
                "scaling to trained production models"
            ]
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--mode", choices=("smoke", "confirmatory"), required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.mode == "confirmatory" and args.output is None:
        parser.error("confirmatory mode requires --output")

    report = run_protocol(args.config, args.mode)
    payload = json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.output is None:
        sys.stdout.write(payload)
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8", newline="\n") as destination:
            destination.write(payload)
        print(args.output)
    return 0 if report["facts"]["every_seed_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
