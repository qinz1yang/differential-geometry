# X1 — Crossing room lemma (2026-09-26)

New file `Topology/CrossingRoom.lean` (compiles clean read-only against current oleans incl. the
margin `CapWindowPoint`; `#lint` clean except docBlameThm; axioms propext/choice/Quot.sound).

Proved:
- `MetricCutCapEvent.RegularCrossing.rmNormSq_eq`: |Rm|² of terminal metric = output metric at a
  regular crossing.
- `RetainedCoreHistory.sqrt_rmNormSq_stageMetric_le_of_pinched` (pinching → |Rm| ≤ K·max(R,1)).
- `isRmControlled_of_backwardPointTrace_of_derivative_bounds`: along any backward trace from u to t,
  R(t) ≤ M, 1 ≤ M, Ctime·M·(t−u) ≤ 1/2, r⁴(8√3 K M)² ≤ 1 ⇒ `A.isRmControlled r` (both clauses).
- `capWindowPoint_of_isEmpty_backwardPointTrace` / `nonempty_backwardPointTrace_of_not_capWindowPoint`:
  y itself untraceable to activeStage u ⇒ CapWindowPoint, given hscale (cap scalar ≥ scale/2),
  transitionEnd < Dcap+1, 4M(t−u) ≤ θcap.
- `isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace` (+ `_of_gradient_bound`,
  event slab, r = c/√R, Cgrad c ≤ 1/4, 8 Ctime c² ≤ 1, 3072 K² c⁴ ≤ 1, 1 ≤ 4R, qcan ≤ R).

Open (not proved, stated in report): trace existence for x ≠ y in B(y, c/√R) from ¬CapWindowPoint y
(needs distance distortion along traces + ball sandwich of the cap window).
