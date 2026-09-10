# Confirmatory result v1

**English** | [Français](RESULTATS_v1.md)

## Status

The confirmatory run was executed after the protocol had been frozen in commit
`7aba368`. It completed with exit code 0. All precommitted criteria passed for
all three precommitted seeds.

Reference result:
[`results/confirmatory_v1.json`](results/confirmatory_v1.json)

SHA-256 of the reference result:
`397c7bf5b39dd5f08ab565588314a9466538a5aaebb836d43b202ce6925c5648`

## Frozen provenance

| Item | Value |
| --- | --- |
| protocol | `constitutive-transformer-v1` |
| seeds | `11`, `29`, `47` |
| script SHA-256 | `e9fa57cf9859d3373adb63a466aa37aad99ee3f85ca5fd492e5244f364253493` |
| configuration SHA-256 | `149ab76af8db75f9ee79af24188ecefa7aad434bb26ecc735f414df7921d96f9` |
| data SHA-256 | `5a46f24b76e81eead471980e85733d3ec8eaa40312446f4a98334a0dd2caeb94` |
| Python | `3.12.14` |
| NumPy | `2.3.5` |
| platform | `Windows-11-10.0.26200-SP0` |

## Facts

Each seed produced eight complete primary traces: parent, learned first cycle,
learned second cycle, intercycle ablation, active-relation control, two inert
controls, and coherent address renaming. The auditor ran only after the journal
had been sealed, and the journal SHA-256 remained identical after audit.

| Seed | Parent probability | Learned cycle 1 | Learned cycle 2 | Ablated cycle 2 | All checks |
| ---: | ---: | ---: | ---: | ---: | :---: |
| 11 | 0.1762 | 0.7316 | 0.2714 | 0.7316 | yes |
| 29 | 0.1751 | 0.7311 | 0.2709 | 0.7311 | yes |
| 47 | 0.1853 | 0.7355 | 0.2754 | 0.7355 | yes |

For every seed, the observed facts include:

- the target is absent from the authorized neural view;
- learning changes the predictive parameter, prediction, and proposal;
- the produced prediction is exactly the value consumed by proposition;
- the parent proposal is retained and rejected at position 0 for the fixed
  regime-and-norm reason;
- the learned first proposal is admitted, normative, certified, and effected;
- that proposal is exactly the relation consumed by the second cycle;
- the second cycle reuses the same learned parameters;
- omitting only the intercycle incorporation changes the second prediction and
  proposal;
- the active relation changes prediction, while the inert control does not;
- coherent technical address renaming preserves prediction;
- memory is exact for the two declared attention queries;
- the rejected governed effect remains impossible;
- regime and independently implemented norm agree on the finite carrier;
- deferred audit leaves every primary trace unchanged.

## Interpretation

Within this frozen finite task, learned prediction causally changes the
constitutive proposal; the proposal is consumed by the next cycle; and a
normatively rejected candidate remains auditable while its governed external
effect is confined. The numerical experiment realizes the same separations as
the Lean architecture without turning neural output into identity, norm, or
admission.

## Limits

This result does not establish general transformer alignment, unbounded-horizon
autonomy, natural-language hallucination reduction, or scaling to trained
production models. It is one finite confirmatory observation, not a Lean
theorem and not a benchmark claim.

## Authorship

> **Intellectual-design and AI-generation disclosure.** The project lead
> states that the essential ideas and the research direction of this project
> are their own. This report was written from A to Z by models in OpenAI's
> ChatGPT series, under human direction and through successive interactions.
> See the [full bilingual disclosure](../AI_AUTHORSHIP.md).
