import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightApproximation

/-!
# Consumers of the `C²` collar height smoothing (E8, Z contract)

* `CuspEmbedding.exists_smooth_height_C1`: exactly BDY-FILL's interface `Z_smooth_height_C1`
  (`build-logs/scratch/BDY-FILL/BoundaryInterfaces.lean`), now a theorem.
* `CuspEmbedding.exists_smooth_height_hessian_vertical`: the vertical Hessian error
  `|Hess_g(η - ζ)(de ∂_z, de ∂_z)| ≤ ε` (`|∂_z|_H = 1`).
* `NearlyCuspidalBoundary.exists_smooth_height_C2`: the Z contract in the `i`-th collar of a nearly
  cuspidal boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- BDY-FILL's `Z_smooth_height_C1`. -/
theorem CuspEmbedding.exists_smooth_height_C1 (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : W.Carrier → ℝ,
      ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ η
        (e.toFun '' {p : CuspHalfSpace | 1 < p.2.val 0 ∧ p.2.val 0 < 99}) ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < ε ∧
        ∀ v : TangentSpace halfCollarModel p,
          |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
              (show ℝ from v.2 0)| ≤
            ε * Real.sqrt (e.cusp.metric.inner p v v) := by
  obtain ⟨η, -, hη, hb⟩ := e.exists_smooth_height_C2 hK hε
  exact ⟨η, hη, fun p hp h2 h98 => ⟨(hb p hp h2 h98).1, (hb p hp h2 h98).2.1⟩⟩

/-- The vertical Hessian error: along the unit vertical vector `∂_z` of the model the Hessian of
`η - ζ` is at most `ε`. -/
theorem CuspEmbedding.exists_smooth_height_hessian_vertical (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        ∀ v : TangentSpace halfCollarModel p, v.1 = 0 → v.2 0 = 1 →
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
              (mfderiv halfCollarModel W.model e.toFun p v)
              (mfderiv halfCollarModel W.model e.toFun p v)| ≤ ε := by
  obtain ⟨η, hη, -, hb⟩ := e.exists_smooth_height_C2 hK hε
  refine ⟨η, hη, fun p hp h2 h98 v hv1 hv2 => ?_⟩
  have hH : e.cusp.metric.inner p v v = 1 := by
    rw [cusp_inner_vertical e.cusp p v hv1, hv2, one_pow]
  have h := (hb p hp h2 h98).2.2 v v
  rw [hH, Real.sqrt_one, mul_one, mul_one] at h
  exact h

/-- The Z contract (E8) in each collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.exists_smooth_height_C2 (B : NearlyCuspidalBoundary W g K δ)
    (i : Fin B.count) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η ((B.collar i).toFun p) - p.2.val 0| < ε ∧
        (∀ v : TangentSpace halfCollarModel p,
          |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ (B.collar i).toFun) p v) -
              (show ℝ from v.2 0)| ≤
            ε * Real.sqrt ((B.collar i).cusp.metric.inner p v v)) ∧
        ∀ v w : TangentSpace halfCollarModel p,
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn (B.collar i).toFun cuspDomain y).2.val 0)
              ((B.collar i).toFun p)
              (mfderiv halfCollarModel W.model (B.collar i).toFun p v)
              (mfderiv halfCollarModel W.model (B.collar i).toFun p w)| ≤
            ε * Real.sqrt ((B.collar i).cusp.metric.inner p v v) *
              Real.sqrt ((B.collar i).cusp.metric.inner p w w) := by
  obtain ⟨η, hη, -, hb⟩ := (B.collar i).exists_smooth_height_C2 hK hε
  exact ⟨η, hη, hb⟩

end DifferentialGeometry.Geometry.Collapse
