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

## Confirmatory result

The scientific sources were frozen in commit `16219a6`. One confirmatory run
then wrote [`results/confirmatory_v1.json`](results/confirmatory_v1.json) without
overwriting any prior output. Its SHA-256 is
`5fc922dfc3af2a05469fff52208e92acdf6b792ca6852b87473cb7c809835fc6`.

The read-only verifier accepts both linked transitions, all 18 causal events,
the six unique cumulative-ledger entries, both counterfactuals, and the address
renaming control. Its twelve negative mutations are all rejected.

Further confirmatory execution is not part of this protocol version. Existing
outputs are never overwritten.

This finite witness does not establish general program synthesis, unbounded
autonomy, or general transformer alignment.
