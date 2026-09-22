# Lower-bound attempt: proved bound and applicability check

Base commit: `0bdf5ef428124ca330a6b3b2882dbde206b93965`.
The audited files are unchanged. Read `CoreFactorization.lean`, then
`QueryBound.lean`, then `Regression.lean`.

## Question

Can the audited `2^n` reference width be strengthened to an exponential
necessary cost for every competing procedure without dynamic reconstruction?

**Not for the same output-normalization task in this family.** This extension
constructs a direct one-pass normalizer and proves that it gives exactly the
same output as the audited executor on every structural input. Separately,
it proves the suggested adversarial query lower bound, but identifies the
additional independent-answer assumption that prevents applying it to this
family's branch viability.

## 1. Direct normalization, same outputs

`directNormalize` only recurses on the input tail. At each cell it leaves a
true decision unchanged, or replaces a false decision by true and copies core
to payload. It calls no table discovery and threads no output guard.

Theorems, valid for every input `cells`:

```text
executed_output_eq_direct:
  (execute cells).output = (directNormalize cells).output

direct_visits:
  (directNormalize cells).cellVisits = cells.length

direct_preserves_acceptance:
  Accepted G true cells -> Accepted G true (directNormalize cells).output
```

`directTransport` closes the original total continuation-transport interface.
The direct algorithm has a fixed, statically written update. Its correctness
is proved separately. It does not reconstruct a table at runtime.

This is equality of outputs, NOT identity of constitutive formation. It does
not refute the audited executor's causal data path. It does show that runtime
discovery and feedback are not necessary to obtain these same outputs.

`cellVisits` counts cells visited, not machine instructions. It is a different
counter from the audited `work`; no 60-fold runtime speedup is claimed.

## 2. An actual adversarial exponential lower bound

`QueryTree` is a finite deterministic adaptive query algorithm. Each query
returns one Boolean branch answer. `Correct tree domain` requires correct
existential/disjunctive answers for every independent answer table on the
domain. Queries may repeat or occur outside the domain.

`missed_singleton` proves indistinguishability: if a coordinate is not queried
on the all-false run, making just that coordinate true cannot change its result.
`correct_covers_zero` therefore forces a correct algorithm to query every
coordinate. Distinctness then gives the exact counting lower bound:

```text
independent_exponential_lower_bound:
  Correct tree (branches n) ->
  2^n <= (tree.trace zero).length
```

This is not an exhaustive strategy's runtime alone: it quantifies over ALL
finite deterministic query trees satisfying that independent-input contract.
`scan_correct` and `independent_bound_is_tight` supply a concrete algorithm
attaining the bound on the all-false input. The premise is not left uninstantiated.

## 3. Why that lower bound does not transfer to the audited family

`CoreViable n G` means that G has an accepted core valuation of length n.
For every FULL history h of length n, the original semantics yield:

```text
branch_viable_iff_core:
  Viable h <-> CoreViable n G
```

The converse uses the existing explicit `branchWitness`, not `execute` or
`normalizingTransport`. Thus all full histories have identical viability.
`one_branch_determines_all` further proves that agreement between two cores on
one full history forces their agreement on every full history. The proposed
adversarial instances differing only at an unqueried branch cannot occur here.

`ModelsChain` restricts oracle answers to exactly that actual viability promise.
Under it, `oneQuery` decides reference viability with exactly one branch query.
Both uniform answer cases are inhabited: `trueCore_models` and
`falseCore_models` instantiate G by True and False. No-query algorithms cannot
distinguish those two cases. Consequently:

```text
chain_query_optimum_one: exact optimal branch-query count = 1
no_exponential_query_necessity:
  not (forall correct promised trees, count >= 2^(n+1))
```

One oracle query is not a free decision of G: the oracle cost model hides the
cost of answering that query. This result measures needed branch information;
it is not a machine-time theorem. The direct normalizer likewise preserves G
and does not decide it.

## Outcome

The independent-answer lower bound is true and proved. Its application to the
audited family is false in the defined branch-query model. The same-output
normalization also admits the explicit direct one-pass implementation above.
The original `2^n / 1 / 60n` theorem remains unchanged, but cannot be strengthened
into exponential necessity for every alternative normalizer by this argument.
A restriction that expressly excludes the direct algorithm would be an
additional baseline definition, not a consequence of counting branches.

## Reproduction

```bash
bash scripts/verify-historical-lower-bound.sh
```

The script reruns the original verification, checks the supplemental source
manifest, compiles all three new modules to `.olean` and C, independently audits
all new public declarations, checks the direct function's generated C, and runs
the regressions. Tests exhaust all 4,681 chains of lengths 0 through 4, check
larger chains through 1,024 cells, and exercise both query contracts. Theorems
are quantified over all sizes; tests are not used as their proofs.

## Resume francais

La tentative demandee a ete poussee jusqu'a des preuves Lean compilees.
La borne exponentielle est prouvee quand les reponses des branches peuvent
varier independamment. Dans la famille auditee, elles ne le peuvent pas :
toutes les histoires completes sont viables exactement lorsque le meme noyau
G l'est. Un seul renseignement de viabilite suffit donc dans ce modele de
requetes. En outre, une normalisation directe donne les memes sorties en un
passage, sans recherche de tables ni transmission de garde entre etapes.
Ce sont des faits sur les memes definitions, pas une modification du resultat
precedent ni une identification des deux processus constitutifs.
