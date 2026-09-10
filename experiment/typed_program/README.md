# Typed-program self-extension experiment

[Français](README_fr.md)

This directory contains the separate executable witness for Gate N. It does
not modify or version the frozen `experiment/protocol_v1.*` experiment.

The protocol uses one rank-free frontier rule on a finite typed corpus. A first
certified composition is incorporated into the actual successor corpus; the
same rule is then invoked again on that produced corpus. The journal records
the exact stateless worker requests, acquired capacities, generated probes,
cumulative exposure ledger, exact incorporation, and the incorporation and
learning counterfactuals.

The worker never receives a probe or future target while training. Measurement
receives the probe input but no target and cannot update state. Expected probe
behavior is computed independently from the total program semantics.

Development smoke run:

```powershell
py run.py --mode smoke --output "$env:TEMP\typed-program-smoke.json"
py verify.py "$env:TEMP\typed-program-smoke.json" --self-test
```

A confirmatory run is deliberately blocked while the worktree is dirty. After
the scientific sources and protocol have been frozen by commit, use a new path
inside `results/`; existing outputs are never overwritten.

This finite witness does not establish general program synthesis, unbounded
autonomy, or general transformer alignment.
