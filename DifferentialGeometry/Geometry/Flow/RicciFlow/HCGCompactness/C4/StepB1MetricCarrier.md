# StepB1MetricCarrier

## Status

`preapprox_pair` is the generic final carrier assembly for Step B1.  It keeps
the existing `PreApproxIsoDataOn` interface and introduces no new input.  A
compact source collar and the image collar are extended to genuine smooth
pullback metrics using `exists_pullbackField`.  The reverse carrier uses the
exact `Function.invFunOn` of the forward map.

`HasStageJetData.preapprox_tail` is the stage-specific capstone.  It takes one
maximum of the forward intrinsic, exact-inverse intrinsic, local-diffeomorphism,
and injectivity thresholds, then instantiates `preapprox_pair` on nested closed
source balls.  The output already has the exact two fields required by
`StepB1RawInput`; no auxiliary carrier record is introduced.

The source contains no fixed-center raw normal-coordinate or raw-radius API:
it only consumes the intrinsic forward/reverse tails and the exact
`Function.invFunOn`.  Focused verification and the exact module refresh now
pass against the refreshed canonical framed intrinsic stack.  No theorem
statement, endpoint assumption, or carrier interface changed.

## Next consumer

The forward and reverse intrinsic norm tails feed this stage-specific capstone,
and `StepB1RawProducer` consumes it on the master subsequence.  The remaining
ordered validation gate is the raw producer itself.

## Accounting

- `preapprox_pair` and `HasStageJetData.preapprox_tail`: complete source proof
  bodies and post-framed focused/exact-green.
- Concrete `StepB1RawInput` fields: 5/5 closed in the live source proof, but not
  yet framed-checked.
- `MetricCompactBase.exists_b1_raw`: source implementation complete with no
  `sorry`/`admit`; framed validation pending. A separately named combined
  textbook-B1 endpoint remains unstated (0%).
- Dedicated B1 machinery: approximately 95%; Chapter 4 machinery:
  approximately 87%; whole-HCG machinery: approximately 60%.
