# Confirmatory result v1

**English** | [Français](RESULTATS_v1.md)

## Status

The canonical protocol was frozen in commit `a4b9a44` before the confirmatory
probe was executed. The unique confirmatory run completed with exit code 0;
all precommitted criteria passed for seeds `11`, `29`, and `47`.

Reference result:
[`results/confirmatory_v1.json`](results/confirmatory_v1.json)

Reference-result SHA-256:
`e483c0e0a046e2f81b03b043be956ad575f972e9ffb1b756c53eda3b9896928c`

## Frozen provenance

| Item | Value |
| --- | --- |
| protocol | `constitutive-transformer-v1` |
| source-freeze commit | `a4b9a44` |
| seeds | `11`, `29`, `47` |
| selected probe | `confirmatory-0`, ordinal `1` |
| script SHA-256 | `ab27a54ae7cf62a5c5f9dbb4d6ef3f6db6eb214db606498884d976df780eb04d` |
| configuration SHA-256 | `008993ba6a21e5e9731869e1dbf4f16edc1ffa29c380486e738e9b26516241c0` |
| complete-data SHA-256 | `3ae9c050758295f2f56bd3e216d48241f51b3ee48544b50eb4f18b1c9f003f08` |
| training-set SHA-256 | `4a2a43bd7888355d26c888f795c6719bd7d5553e1c15ab4372ff19d7bc8f8ae0` |
| probe-policy SHA-256 | `28822c4762958997f8da6c5d18121b896f6fac650e1030e39b23ea7d4343fd57` |
| training-view SHA-256 | `b9522be46ba717683c4064596ad7e8c0311a2c0ef8ebe0903f2c8442d5c6e9d2` |
| confirmatory-view SHA-256 | `2eecfe1b1f90c346511a19a3c52ac4a46c9d4d3cd12103c43e5e3ac00220233b` |
| Python | `3.12.14` |
| NumPy | `2.3.5` |
| platform | `Windows-11-10.0.26200-SP0` |

The training case, smoke probe, and confirmatory probe have distinct
identifiers and distinct authorized views. The smoke run selected ordinal `0`;
the confirmatory run selected ordinal `1`. Every confirmatory trace records role
`confirmatory`, identifier `confirmatory-0`, and ordinal `1`.

## Facts

Each seed produced eight primary traces: parent, learned first cycle, learned
second cycle, intercycle ablation, active-relation control, two inert controls,
and coherent address renaming. The journal was sealed before deferred audit.

| Seed | Parent probability | Learned cycle 1 | Learned cycle 2 | Ablated cycle 2 | All checks |
| ---: | ---: | ---: | ---: | ---: | :---: |
| 11 | 0.1761 | 0.7314 | 0.2713 | 0.7314 | yes |
| 29 | 0.1750 | 0.7309 | 0.2708 | 0.7309 | yes |
| 47 | 0.1852 | 0.7354 | 0.2753 | 0.7354 | yes |

For every seed:

- training and probe splits are exactly bound and disjoint;
- parent and learned paths consume the same confirmatory probe;
- learning changes the predictive parameter, prediction, and proposal;
- produced prediction and constitutively consumed value are identical;
- the parent proposal is retained and rejected at position 0 for the fixed
  regime-and-norm reason;
- the learned first proposal is admitted, normative, certified, and effected;
- that proposal is exactly the relation consumed by the second cycle;
- the second cycle reuses the same learned parameters;
- omitting only intercycle incorporation changes the second proposal;
- the active relation changes prediction, while its inert control does not;
- coherent address renaming preserves prediction;
- attention memory is exact for the two declared queries;
- the rejected governed effect remains confined;
- regime and independently implemented norm agree on the finite carrier;
- deferred audit leaves the sealed primary journal unchanged.

## Read-only verification

```text
python experiment/verify_refinement_v1.py --script experiment/protocol_v1.py --config experiment/protocol_v1.json --result experiment/results/confirmatory_v1.json
```

The verifier accepted 3/3 runs and 24/24 primary traces, matched every frozen
hash, and rejected eight mutations: candidate rewriting, uncertified effect,
missing intercycle linkage, prediction substitution, probe-role substitution,
probe-identity substitution, a missing primary field, and provenance
substitution. It does not rerun training or modify an artifact.

## Interpretation

Within this frozen finite task, a parameter learned only from the training set
changes the proposal on the distinct precommitted confirmatory probe. That
proposal is consumed by the next cycle, and a normatively rejected candidate
remains auditable while its governed external effect is confined.

## Limits

This is one finite numerical observation. It is not a Lean theorem, a general
transformer-alignment result, an unbounded-horizon result, a natural-language
hallucination benchmark, or a production-scale training claim.

## Authorship

> **Intellectual-design and AI-generation disclosure.** The project lead
> states that the essential ideas and research direction are their own. This
> report was written from A to Z by models in OpenAI's ChatGPT series, under
> human direction and through successive interactions. See the
> [full bilingual disclosure](../AI_AUTHORSHIP.md).
