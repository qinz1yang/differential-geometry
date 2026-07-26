import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.NablaRicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

/-!
# The per-direction tension-field curvature IBP: refutation record

This module formerly stated the **per-direction frame-summed tension-field curvature-divergence
nullity** (for a fixed smooth Parseval frame family `V a` and each fixed slot-`0` direction `b`,
`∑_a ∫_M ⟨R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S, slot0_{V b}(∇S)⟩_g dvol_g = 0`), and was
afterwards re-pointed at a per-`b` IBP *difference* restatement.  Both are now refuted
(`PROVE_REFUTED.md`):

* **The per-`b` nullity is FALSE** (2026-06-12, "Kernel (rank-0 Bochner) — the per-b TENSION-FIELD
  NULLITY family").  Mechanism: under a point-dependent gauge rotation of the Parseval family the
  tension-field carrier reads the family's pure gauge freedom (the rotation generator
  `τ = dφ(V₁)V₂ − dφ(V₂)V₁`) while `0` is gauge-invariant, so the per-`b` nullity equates a
  gauge-variant quantity to an invariant one; an explicit `S²` endpoint evaluates the left side to a
  nonzero value.

* **The per-group value-assignment family containing the difference restatement is FALSE in dim ≥ 3**
  (2026-06-12, "Kernel per-group VALUE-ASSIGNMENT family").  An `S³` rotation family evaluates the
  former per-group Bochner folds (`G₃ = ⟨ricTraceSection, ∇S⟩`, `G₂ + G₄ = operator residue`) with a
  common nonzero error `N(t) = −0.115184482·t` (three independent computations in 9-digit agreement),
  and an ellipsoid refutes the formerly posited `D = group2 − group1` (`D = +6.125 ≠ 0`).  The dim-`2`
  fibre algebra degenerates (`X_{UW} ≡ 0` pointwise), so every counterexample/variance probe for this
  family must run in dim ≥ 3 — the earlier `S²`-only audits were structurally blind to it.

The single surviving (posited) kernel primitive is the `b`-summed difference-of-engine identity
`D = −(G₁ + I₂)` — `parsevalFrameSum_diffCurvTrace_doubleSum_eq_neg_group1_add_crossPairing`
(`ParsevalSevenTermBochnerFold`), the genuine integrated `∇R`-vs-`∇S` covariant integration by parts,
numerically confirmed twice in dim `3`.

This file intentionally retains its import closure (the differentiated-Ricci carriers, the
frame-summed covariant-IBP engine `MovingFrameIntegratedNullity`, Theorem A and the contracted second
Bianchi) and no declarations; it is the import seam through which the seven-term fold reaches that
infrastructure.
-/
