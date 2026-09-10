# Finite constitutive-transformer experiment

**English** | [Français](README_fr.md)

This directory contains the first numerical prototype corresponding to Gate K.
The protocol keeps the neural producer, exact constitutive runtime, governed
effector, immutable primary journal, and deferred auditor separate.

The frozen protocol is `protocol_v1.json`; `protocol_v1.py` is its only
executable implementation. The reference result must never be overwritten.

Install the pinned dependency in an isolated Python environment:

```text
python -m pip install -r experiment/requirements-v1.txt
```

Run a non-confirmatory smoke test:

```text
python experiment/protocol_v1.py --mode smoke --config experiment/protocol_v1.json
```

Run the frozen confirmatory protocol once, choosing a new output path:

```text
python experiment/protocol_v1.py --mode confirmatory --config experiment/protocol_v1.json --output experiment/results/confirmatory_v1.json
```

The program refuses to overwrite an existing result. Every result records the
script, configuration, and data hashes; all primary traces are sealed before
the deferred audit. The report separates facts, interpretation, and limits.

The immutable reference run and its human-readable report are available as
[`results/confirmatory_v1.json`](results/confirmatory_v1.json) and
[`RESULTS_v1.md`](RESULTS_v1.md).

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
