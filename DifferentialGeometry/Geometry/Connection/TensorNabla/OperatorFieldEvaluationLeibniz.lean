import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle

/-! # The order-`0` fibrewise-curvature fingerprint and its operator-field Cauchy–Schwarz

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file records the *order-`0` fibrewise-curvature fingerprint*
(`IsOrderZeroCurvFactor`) shared by the two concrete recursively-differentiated curvature towers and the
two *proved* value-level lemmas it supports — the order-`0` homogeneity bridge `op_zero_value_homogeneous`
and the fibrewise Cauchy–Schwarz `riemannianFiberNormSq_clm_apply_le`. Both are honest, sorry-free
building blocks: the fingerprint pins the order-`0` base of a recursive operator family to a *value-local*,
`ℝ`-linear fibrewise operator (the structural shape of a bundled curvature operator), and the
Cauchy–Schwarz bound is the per-point step that converts a fibrewise continuous-linear operator into a
section-proportional fibre bound.

## Why there is NO abstract per-order factorisation node (the deleted `op_perOrder_factorisation_continuous`)

An earlier version of this file carried a *posited* abstract node
`op_perOrder_factorisation_continuous`: from the order-`0` fingerprint `IsOrderZeroCurvFactor` plus the
single-step covariant Leibniz remainder identity `hcovGrad_op`
(`∇(op p r W) = op (p+1) r W + (rank-cast) op p (r+1)(∇W)`), it claimed a per-`(p, r)` factorisation
`op p r W (x) = Lᵖ x (W x)` through a fibrewise operator field with a *continuous* fibre bound. **This
node is FALSE as stated** (Lean-refuted at `(p, r) = (1, 0)`): the fingerprint `IsOrderZeroCurvFactor`
constrains `op 0 r` only *per-rank* (`ℝ`-linear and value-local at order `0`), with **no inter-rank
relation**, while the recursion `hcovGrad_op` *mixes ranks* (`op (p+1) r` is defined through
`op p (r+1)`). A concrete counterexample: take `op 0 0 := 0` and `op 0 1 := id` (each value-local and
linear at order `0`, so the fingerprint holds); the recursion then forces
`op 1 0 W = − (rank-cast) op 0 1 (covGrad g 0 0 W) = − (rank-cast)(covGrad g 0 0 W)`, which reads the
*one-jet* of `W` — it is **not value-local**, so *no* fibrewise factorising operator field `L` exists,
and the operator is unbounded relative to `rfns(W (x))`. Hence the abstract telescoping cannot be sound
under the order-`0`-only fingerprint: the value-locality of the Leibniz remainder at order `p ≥ 1` is
*genuinely new* analytic content (smoothness of the iterated curvature coefficient `∇ᵖ L₀ = ∇ᵖ(g, R)`),
which an abstract `op` knowing only its order-`0` value-locality cannot supply.

The deep content — the per-order section-proportional fibre boundedness of the iterated curvature
operator — is therefore **localized to each concrete tower** (where the smooth `L₀ = g, R` coefficient
is available): each tower carries ONE precise *posited* high-order envelope about *its own* operator
(`exists_proportional_pureRGenuineDiffOp_highOrder`,
`exists_proportional_diffCurvOp_highOrder`), and the genuinely-abstract *combination* of the order-`0`
proportional bound with the high-order envelope is the sorry-free shared lemma
`exists_proportional_recCurvDiffOp` (`Analysis/Spectral/Tensor/CovGrad/IteratedDiffOpProportionalBound`).
This file's `sorry`-free contribution is the order-`0` fingerprint and the two value-level lemmas above.

## The pieces

* `IsOrderZeroCurvFactor` — the order-`0` fibrewise-curvature fingerprint (`ℝ`-linear + value-local at
  order `0`), the honest structural shape of a bundled curvature operator, proved on disk for both
  concrete towers. It does **not** by itself force any inter-rank coherence, which is exactly why the
  abstract telescoping node above is false; it remains the shared order-`0` fingerprint documenting the
  non-vacuity of the towers' high-order posits.
* **P1** `op_zero_value_homogeneous` (**proved**) — the value-level homogeneity bridge upgrading the
  pointwise `ℝ`-linearity of the order-`0` base to `C^∞(M, ℝ)`-linearity (a smooth scalar contributes
  only its value at the point, by value-locality); the bridge that makes the order-`0` operator field
  extraction (`ofLinearMapSection`) applicable.
* **P4** `riemannianFiberNormSq_clm_apply_le` (**proved**) — the fibrewise Cauchy–Schwarz
  `rfns(φ v) ≤ Cφ · rfns(v)` for a fibrewise continuous-linear operator `φ` between tensor fibres,
  via the proved intrinsic-fibre-norm/`g`-bundle-norm bridge `riemannianFiberNormSq_eq_bundle_norm_sq`
  (`riemannianFiberNormSq = ‖·‖²` under the `(r, s)`-tensor Riemannian bundle instance) and the
  continuous-linear-map operator-norm bound.

Both `op_zero_value_homogeneous` and `riemannianFiberNormSq_clm_apply_le` are *proved*; this file
introduces no `sorry`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- **The order-`0` fibrewise-curvature-operator factorisation hypothesis.** For a recursive operator
family `op`, this records the two structural facts that fix the order-`0` base `op 0 r` to a *fibrewise*
operator — one reading only the *value* of its section (no derivative), the structural fingerprint of a
bundled curvature operator:

* `linear` — the order-`0` base is `ℝ`-linear in the section: `op 0 r (c₁ • W₁ + c₂ • W₂) =
  c₁ • op 0 r W₁ + c₂ • op 0 r W₂`;
* `local'` — the order-`0` base is *value-local*: its fibre value at `x` depends only on the section
  value `W (x)` (if two sections agree at `x`, the operator's values at `x` agree).

Together these force `op 0 r` to factor, fibrewise, through a continuous-`ℝ`-linear operator on the
fibre applied to `W (x)` — the carrier of the genuine curvature setting. Both facts are *proved* on disk
for the two concrete towers (at order `0` each reads only its section's value, linearly). This is the
honest, instance-plumbing-free fingerprint of the fibrewise curvature operator; it is what fixes the
family away from a pathological free `covGrad_op`-family (whose high-order layer can be unbounded). -/
structure IsOrderZeroCurvFactor (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)) : Prop where

  linear : ∀ (r : ℕ) (c₁ c₂ : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    (op 0 r (c₁ • W₁ + c₂ • W₂)).toSection x =
      c₁ • (op 0 r W₁).toSection x + c₂ • (op 0 r W₂).toSection x

  local' : ∀ (r : ℕ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    W₁.toSection x = W₂.toSection x → (op 0 r W₁).toSection x = (op 0 r W₂).toSection x

set_option linter.unusedSectionVars false in
/-- **P1 — the value-level homogeneity of the order-`0` base** (proved). From the
`IsOrderZeroCurvFactor` fingerprint (pointwise `ℝ`-linearity + value-locality), the order-`0` base
commutes, *at each point* `x`, with multiplication of the section value by any scalar: if
`W₂.toSection x = c • W₁.toSection x` then `(op 0 r W₂).toSection x = c • (op 0 r W₁).toSection x`.

This is the value-level fingerprint that upgrades the pointwise `ℝ`-linearity of the order-`0` base to
`C^∞(M, ℝ)`-linearity (a smooth scalar `f` contributes, at `x`, only its value `f x`, by
value-locality: `op 0 r (f • W) (x) = op 0 r (any section with value f(x) • W(x)) (x) =
f(x) • op 0 r W (x)`), the bridge that makes the order-`0` operator-field extraction
(`ofLinearMapSection`) applicable. It is *false* for a non-`ℝ`-linear or non-value-local family, so it
genuinely uses both fingerprint fields. -/
theorem op_zero_value_homogeneous
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op)
    (c : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M)
    (hval : W₂.toSection x = c • W₁.toSection x) :
    (op 0 r W₂).toSection x = c • (op 0 r W₁).toSection x := by
  have hcW : (c • W₁).toSection x = c • W₁.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [hbase.local' r W₂ (c • W₁) x (by rw [hval, hcW])]
  have hlin := hbase.linear r c 0 W₁ W₁ x
  rw [show (c • W₁) = c • W₁ + (0 : ℝ) • W₁ from by rw [zero_smul, add_zero]]
  rw [hlin]
  simp only [zero_smul, add_zero]

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The intrinsic-fibre-norm/`g`-bundle-norm bridge** (proved). Under the `(r, s)`-tensor
Riemannian bundle instance `tensorRS_riemannianBundle g r s`, the intrinsic squared Riemannian fibre
norm `riemannianFiberNormSq g r s x z` coincides with the squared bundle-fibre norm `‖z‖²`. The proof
runs entirely through the *proved* fibre-norm bridge `riemannianFiberNormSq = tensorInnerPointwise`
(`riemannianFiberNormSq_eq_tensorInnerPointwise`), the bundle-fibre inner product
`tensorRSRiemannianInnerCLM` and its `tensorInnerPointwise` apply formula, and
`real_inner_self_eq_norm_sq`; the ambient model-induced fibre norm is removed (`attribute [-instance]`)
so that `‖·‖` resolves to the Riemannian bundle norm. -/
private lemma riemannianFiberNormSq_eq_bundle_norm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    riemannianFiberNormSq (I := I) (M := M) g r s x z = ‖z‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s x z z : ℝ) =
        riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x z).symm
  have hself : (inner ℝ z z : ℝ) =
      riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **P4 — the fibrewise Cauchy–Schwarz for an operator-field evaluation** (proved). For a fibrewise
continuous-linear operator `φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x` between tensor
fibres at a point `x`, the intrinsic squared Riemannian fibre norm of the evaluation `φ v` is
controlled by a nonnegative fibre-operator constant `Cφ` (the squared `g`-fibre operator norm of `φ`)
times the intrinsic squared fibre norm of `v`:
```
rfns(φ v) ≤ Cφ · rfns(v).
```

**Proof.** Install the source- and target-fibre `(0, r)`/`(0, s)`-tensor Riemannian bundle instances;
under them each fibre is a finite-dimensional inner-product space whose squared norm is
`riemannianFiberNormSq` (the *proved* bridge `riemannianFiberNormSq_eq_bundle_norm_sq`). Repackage `φ`
as a continuous-linear map `φg` for the `g`-fibre norm topologies (`LinearMap.toContinuousLinearMap` on
the finite-dimensional domain; same underlying map, hence `φg v = φ v`); take `Cφ := ‖φg‖²` and square
the operator bound `‖φg v‖ ≤ ‖φg‖ · ‖v‖` (`ContinuousLinearMap.le_opNorm`). The bridge converts both
sides to `riemannianFiberNormSq`.

**Trap screen.** Reads only the *value* `v` (no jet); a single fibrewise operator `φ` at one point `x`
(no free `(p, r)` family); the witness `Cφ = ‖φg‖²` genuinely uses `φ` and rejects `Cφ ≡ 0` whenever
`φ ≠ 0` (then `‖φg‖ > 0`, so `rfns(φ v) > 0 = 0 · rfns(v)` for a suitable `v`); no free binders escape
`x`. -/
theorem riemannianFiberNormSq_clm_apply_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ v : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  let φg : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap (φ.toLinearMap)
  have hφg_apply : ∀ v, φg v = φ v := fun v => by
    change (LinearMap.toContinuousLinearMap (φ.toLinearMap)) v = φ v
    rw [LinearMap.coe_toContinuousLinearMap']; rfl
  refine ⟨‖φg‖ ^ 2, sq_nonneg _, fun v => ?_⟩
  rw [riemannianFiberNormSq_eq_bundle_norm_sq (I := I) (M := M) g 0 s x (φ v),
      riemannianFiberNormSq_eq_bundle_norm_sq (I := I) (M := M) g 0 r x v, ← hφg_apply v]
  calc ‖φg v‖ ^ 2 ≤ (‖φg‖ * ‖v‖) ^ 2 := by
          apply sq_le_sq'
          · nlinarith [φg.le_opNorm v, norm_nonneg (φg v), norm_nonneg v, norm_nonneg φg]
          · exact φg.le_opNorm v
    _ = ‖φg‖ ^ 2 * ‖v‖ ^ 2 := by ring

end Connection
end Integral
end DifferentialGeometry

end
