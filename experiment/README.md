# Finite constitutive-transformer experiment

**English** | [Français](README_fr.md)

This directory contains the first numerical prototype corresponding to Gate K.
The protocol keeps the neural producer, exact constitutive runtime, governed
effector, immutable primary journal, and deferred auditor separate.

The single canonical protocol is `protocol_v1.json`; `protocol_v1.py` is its
only executable implementation. Its training set, smoke probe, and
precommitted confirmatory probe are separate and are checked for identifier and
authorized-view disjointness before training. Parent and learned paths consume
the exact same probe selected for their mode. A smoke run never executes the
confirmatory probe.

Install the pinned dependency in an isolated Python environment:

```text
python -m pip install -r experiment/requirements-v1.txt
```

Run a non-confirmatory smoke test:

```text
python experiment/protocol_v1.py --mode smoke --config experiment/protocol_v1.json
```

After the script and configuration have been frozen by a source commit, run
the confirmatory protocol once:

```text
python experiment/protocol_v1.py --mode confirmatory --config experiment/protocol_v1.json --output experiment/results/confirmatory_v1.json
```

The program refuses to overwrite an existing result. Every result records the
script, configuration, complete data, training-set, and probe-policy hashes;
all primary traces are sealed before the deferred audit.

The protocol was frozen in commit `a4b9a44` before the confirmatory probe was
executed. Its immutable result and bilingual report are available as
[`results/confirmatory_v1.json`](results/confirmatory_v1.json) and
[`RESULTS_v1.md`](RESULTS_v1.md).

Verify the frozen artifacts without rerunning training or modifying them:

```text
python experiment/verify_refinement_v1.py --script experiment/protocol_v1.py --config experiment/protocol_v1.json --result experiment/results/confirmatory_v1.json
```

The read-only verifier checks all frozen hashes, the exact confirmatory probe,
24 primary traces, the discrete constitutive boundary, intercycle consumption,
effect confinement, and eight negative mutations. Lean separately proves the
canonical discrete refinement relation; it does not parse the JSON result.

This finite experiment is not a proof of general transformer alignment,
unbounded-horizon autonomy, production-scale training, or natural-language
hallucination reduction.

## Authorship

> **Intellectual-design and AI-generation disclosure.** The project lead
> states that the essential ideas and the research direction of this project
> are their own. This document and the experimental implementation were written
> from A to Z by models in OpenAI's ChatGPT series, under human direction and
> through successive interactions. See the
> [full bilingual disclosure](../AI_AUTHORSHIP.md).
