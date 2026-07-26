# StepB1RawProducer

## Target-first assembly

`MetricCompactBase.exists_b1_raw` is stated at the exact final
`StepB1RawInput` interface. This keeps the target theorem visible while its
radius diagonal, stage-map geometry, and metric-error producers are assembled.

## Live result

`MetricCompactBase.exists_b1_raw` has a complete source proof body with no
`sorry` or `admit`. It extracts one strict master subsequence `psi` and
constructs the unchanged `StepB1RawInput` for `X.subseq psi`. The record closes
all five requested fields for the same global finite-stage comparison map:

1. local diffeomorphism on the larger open ball;
2. injectivity there;
3. exact basepoint preservation;
4. the forward arbitrary-order `PreApproxIsoDataOn` carrier;
5. the reverse carrier for the exact `Function.invFunOn`.

The radius master diagonal, pair-index shift, and final casts are part of the
source proof. This file contains no fixed-center normal-chart or radius API;
it only consumes the stage-master and metric-carrier outputs. No
endpoint-radius assumption, whole-cage target containment, pointwise chart
selector, or glued limit-weight family was added. Focused verification and the
exact module refresh both pass against the complete canonical framed producer
chain.

## Next consumer

`stepB1_of_raw` turns this checked raw package into the
book's partial approximate-isometry maps on the extracted sequence, and
`compactness_of_b1` produces the Step-D compactness conclusion for that
sequence. The subsequent assembly seam is subsequence bookkeeping: lift the
resulting nested-subsequence conclusion back to the original sequence and use
it to discharge the conditional Chapter-4 endpoint.

## Accounting

- `MetricCompactBase.exists_b1_raw`: theorem 100% and canonical framed
  focused/exact-green.
- Concrete `StepB1RawInput` field closure: 5/5 checked on one global stage map.
- The selected B/C-to-raw-B1 producer chain: 100% checked.  This is machinery
  for the later textbook-facing result, not that result itself.
- Dedicated B1 machinery: approximately 95%; the older full textbook Step-C
  recurrence route remains separate and incomplete.
- A separately named combined textbook-B1 endpoint is not yet stated, so it is
  still recorded as theorem-level 0% despite the producer and conditional
  consumer proof bodies already being present.
- Conditional compactness endpoint: theorem-level 0% until the nested
  subsequence lift and final assembly are checked. Chapter-4 machinery remains
  approximately 87%; whole-HCG machinery approximately 60%.
