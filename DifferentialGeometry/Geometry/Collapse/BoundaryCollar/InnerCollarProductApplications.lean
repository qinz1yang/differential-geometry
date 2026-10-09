import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarProduct

/-!
# Consumers of the E6 kernel (inner collars of nearly cuspidal boundaries)

* `NearlyCuspidalBoundary.exists_sublevel_diffeomorph_torus_Icc`: for every component `∂_i W` of
  a nearly cuspidal boundary, a smooth `F` regular on `{F ≤ r}`, equal to `a < r` on `∂_i W` and
  meeting `∂W` inside `{F ≤ r}` only in `∂_i W`, has sublevel `≅ T² × [a, r]` as a pair.
* `NearlyCuspidalBoundary.isBoundaryPoint_sublevel_iff_of_diffeomorph`: in that product the
  boundary of the sublevel is exactly the image of `T² × {a, r}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- E6 kernel for each component of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.exists_sublevel_diffeomorph_torus_Icc {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {F : W.Carrier → ℝ} {a r : ℝ}
    (har : a < r) (hF : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F)
    (hreg : ∀ x, F x ≤ r → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) (hr : ∃ x, F x = r)
    (hXa : ∀ x ∈ B.component i, F x = a)
    (hbd : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r → x ∈ B.component i) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ r},
      letI := cs
      IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ r} ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // F x ≤ r} => x.1) ∧
      (∀ y : {x : W.Carrier // F x ≤ r},
        (𝓡∂ 3).IsBoundaryPoint y ↔ (y.1 ∈ B.component i ∨ F y.1 = r)) ∧
      haveI : Fact (a < r) := ⟨har⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a r)
          {x : W.Carrier // F x ≤ r} ∞,
        (∀ p, F (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ B.component i ↔ p.2.1 = a :=
  (B.collar i).exists_sublevel_diffeomorph_torus_Icc har hF hreg hr hXa hbd

/-- In the product of the E6 kernel, a point of the sublevel is a boundary point exactly when it
is the image of a point of `T² × {a, r}`. -/
theorem NearlyCuspidalBoundary.isBoundaryPoint_sublevel_iff_of_diffeomorph
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {F : W.Carrier → ℝ} {a r : ℝ}
    (har : a < r) (hF : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F)
    (hreg : ∀ x, F x ≤ r → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) (hr : ∃ x, F x = r)
    (hXa : ∀ x ∈ B.component i, F x = a)
    (hbd : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r → x ∈ B.component i) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ r},
      letI := cs
      haveI : Fact (a < r) := ⟨har⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a r)
          {x : W.Carrier // F x ≤ r} ∞,
        ∀ p, (𝓡∂ 3).IsBoundaryPoint (D p) ↔ (p.2.1 = a ∨ p.2.1 = r) := by
  obtain ⟨cs, -, -, hiff, D, hDF, hDX⟩ :=
    B.exists_sublevel_diffeomorph_torus_Icc i har hF hreg hr hXa hbd
  exact ⟨cs, D, fun p => (hiff (D p)).trans (or_congr (hDX p) (by rw [hDF p]))⟩

end DifferentialGeometry.Geometry.Collapse
