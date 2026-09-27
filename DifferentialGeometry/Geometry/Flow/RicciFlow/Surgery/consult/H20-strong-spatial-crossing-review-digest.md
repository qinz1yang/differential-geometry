# Review H20 (single statement: `StrongSpatialCrossingContinuation`, the strong form of SX — young non-cap-window witness, neck ⇒ cross-event strong neck), digested

Date: 2026-09-27. Reviewer: GPT, on `codex/pc-consult-t` @ 9e218c15a, not compiled.
Overall: **statement may stand, leaning TRUE; proof closure is FIX.** SX's spatial conclusion cannot be upgraded to
the strong one; one must REUSE the spacetime X-core in a form that does NOT depend on "the bad point has no
spatial witness".

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (1) does B8 really give time jets? | yes; but the young-point public interface is insufficient | `CanonicalWitness`'s neck branch carries a genuine `StrongNeck`: cylinder comparison on normalized `[−1, 0]`, controlling mixed space–time orders `a + 2b ≤ ⌈ε⁻¹⌉`, not slice-wise spatial comparison; so it can be cut to `[−1/5, 0]`. BUT B8's young-point proof internally does `obtain ⟨K, -⟩ := …` and then exports only scalar-derivative and gradient bounds: `K` must be EXPORTED together with the cap-tube condition; the existing derivative conclusions cannot replace it. |
| (2) accuracy and quantifiers | current order suffices; no forced fixed ratio | Cheapest: take B8's OUTPUT accuracy `α := ε`; its internal `δ₀(ε)` already reserves the approximate-transport margin via the buffered witness. Exact rescaling and survivor maps add no error; then `ε ≤ ε₁` shortens the tube / lowers the order; cutting the window loses no accuracy. So no extra `εbar ≤ c·ε₁`. But any ADDITIONAL approximate transport cannot be absorbed by `ε ≤ ε₁` alone — pick a finer internal accuracy there. |
| (3) whole-window carry-back and events | conditionally OK; "B5 tracing" alone is not a citation | B5 needs curvature control along ALL existing partial trajectories of EVERY point of the ball, then the non-cap-window exclusion gives whole-ball survival. B8's construction consumes depth `δ₀(ε)⁻¹` and a spatial buffer, far more than `1/5`: infinite depth must supply it. A neck witness's compact domain is only the image of `S² × [−10, 10]`; capturing it ≠ capturing the whole `±ε₁⁻¹` tube; PRODUCE `K` DIRECTLY ON THE COMMON FLOW so whole-tube containment is built in. Events inside the window: handle via exact metric splicing on the survivor domain + `IsSolutionOn`, never by splicing approximate strong necks event by event with accumulated error. |
| (4) cap witnesses make it vacuous? | intended alternative, not general vacuity | It strengthens only the CHOSEN `W`. Take `W := K.toSpatial` and keep the branch label. B8 giving a neck does NOT mean no other cap witness exists (witnesses are not mutually exclusive); but a cap must have a real core, tube and depth data — no arbitrary labels. To FORCE the neck branch the consumer must prove SC1-c-type whole-witness-domain capture + non-neck exclusion, not merely "the limit base looks cylindrical". |
| (5) counterexamples | refute shortcuts, not H20 | Newborn points with `R(t − T) < 1/5`: the current slab is too short and earlier slabs have no survivor preimage, so no history strong neck; a retained base tube touching newborn material cannot be carried back whole. "Base point survives + spatial neck" is insufficient; whole-tube survival or a legitimate cap branch must be completed. No complete H20 counterexample found. |

Consumer substitution correct: `Cs = 1`, `θ = τmin`, `t₀ = t`, `η₃ = slab end − t`; the whole-slab hypotheses do
supply the needed `Before/On`. But the source proves `hcross → StrongNecksOfCutoffClass`, not `hcross` itself.
Minimal completion: EXPORT B8's full witness on the young common flow, and prove it exactly compatible with the
whole-survivor-domain flow `HistoryStrongNeck` requires, carried back.

Decision (lead): the strong-SX proof lane must (a) add a B8-young variant that exports `K` (the `CanonicalWitness`)
with the cap-tube condition, as a NEW file (never edit `AncientLimitCanonicalWitness.lean`); (b) produce `K` on
the traced common flow of the WHOLE ball (B5/B13 data at infinite depth), take `W := K.toSpatial` keeping the
label; (c) neck branch: cut the `StrongNeck` `[−1, 0]` comparison to `[−1/5, 0]` (`TruncatedNeck.ofStrongNeck`)
and identify the common flow with the survivor-domain flow by exact splicing (SC3's
`metricScalarAt_backwardSurvivor_eq_stageMetric`-style identification, `IsSolutionOn`), then `restrictOpen`;
(d) accuracy: `α := ε` from B8, no second approximate transport.
