import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightGeometry

/-!
# Consumers of the BCP01 analytic clauses in `g`-norms

* `CuspEmbedding.exists_smooth_height_bcp01_differential`: for `0 ≤ δ ≤ 1/1000` and every
  `0 < ε ≤ 1/1000` one smooth `η` (row E8) satisfies on the band `2 ≤ z ≤ 98`: BCP01.a in
  `g`-norms (`|η − ζ| < ε`, `|d(η − ζ)(u)| ≤ ε(1 − δ)^{-1}|u|_g`,
  `|Hess_g(η − ζ)(u, w)| ≤ ε(1 − δ)^{-1}|u|_g|w|_g`) and the first and third clauses of BCP01.b
  (`.99 < ‖dη‖_g < 1.01`, `.99 < ∂_z η < 1.01`).
* `NearlyCuspidalBoundary.exists_smooth_height_bcp01_differential`: the same in the `i`-th collar.
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

/-- BCP01.a in `g`-norms and BCP01.b (first and third clauses) for one smooth `η`. -/
theorem CuspEmbedding.exists_smooth_height_bcp01_differential (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < ε ∧
        (∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
              (e.toFun p) u| ≤ ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u)) ∧
        (∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u w| ≤
            ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) *
              Real.sqrt (g.inner (e.toFun p) w w)) ∧
        (∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model η (e.toFun p) u| ≤
            (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u)) ∧
        (∃ u : TangentSpace W.model (e.toFun p), 0 < mvfderiv W.model η (e.toFun p) u ∧
          199 / 200 * Real.sqrt (g.inner (e.toFun p) u u) ≤ mvfderiv W.model η (e.toFun p) u) ∧
        99 / 100 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
            ((0, 0), EuclideanSpace.single 0 1)) ∧
          (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
            ((0, 0), EuclideanSpace.single 0 1)) < 101 / 100 := by
  obtain ⟨η, hη, -, hb⟩ := e.exists_smooth_height_C2 hK hε
  refine ⟨η, hη, fun p hp h2 h98 => ?_⟩
  obtain ⟨h0, h1, h2'⟩ := hb p hp h2 h98
  obtain ⟨ha1, ha2⟩ := e.bcp01a_of_contract hδ0 (by linarith) hη hε.le hp h1 h2'
  obtain ⟨hb1, hb2, hb3⟩ := e.bcp01b_differential_of_contract hδ hη hε.le hε1 hp h1
  exact ⟨h0, ha1, ha2, hb1, hb2, hb3⟩

/-- The same in the `i`-th collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.exists_smooth_height_bcp01_differential
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η ((B.collar i).toFun p) - p.2.val 0| < ε ∧
        (∀ u : TangentSpace W.model ((B.collar i).toFun p),
          |mvfderiv W.model η ((B.collar i).toFun p) u| ≤
            (1 + 1 / 200) * Real.sqrt (g.inner ((B.collar i).toFun p) u u)) ∧
        ∃ u : TangentSpace W.model ((B.collar i).toFun p),
          0 < mvfderiv W.model η ((B.collar i).toFun p) u ∧
          199 / 200 * Real.sqrt (g.inner ((B.collar i).toFun p) u u) ≤
            mvfderiv W.model η ((B.collar i).toFun p) u := by
  obtain ⟨η, hη, hb⟩ := (B.collar i).exists_smooth_height_bcp01_differential hK hδ0 hδ hε hε1
  exact ⟨η, hη, fun p hp h2 h98 =>
    ⟨(hb p hp h2 h98).1, (hb p hp h2 h98).2.2.2.1, (hb p hp h2 h98).2.2.2.2.1⟩⟩

end DifferentialGeometry.Geometry.Collapse
