import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarSublevel

/-!
# Consumers of the inner collar product (E6)

* `CuspEmbedding.exists_innerCollar_height_between`: the sublevel `{F ≤ 90}` of E6(i) contains the
  collar `e (z ≤ 2)` and lies in `e (z < 91)`; `X` is its bottom level.
* `NearlyCuspidalBoundary.exists_innerCollar_diffeomorph_torus_Icc`: E6 in the `i`-th collar of a
  nearly cuspidal boundary.
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

/-- The inner collar of E6(i) lies between `e (z ≤ 2)` and `e (z < 91)`. -/
theorem CuspEmbedding.exists_innerCollar_height_between (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) :
    ∃ (F : W.Carrier → ℝ) (a : ℝ), a < 90 ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x ∈ X, F x = a) ∧ (∀ p ∈ cuspDomain, p.2.val 0 ≤ 2 → F (e.toFun p) ≤ 90) ∧
      (∀ y, F y ≤ 90 → ∃ p ∈ cuspDomain, p.2.val 0 < 91 ∧ e.toFun p = y) ∧
      ∀ x, F x ≤ 90 → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0 := by
  obtain ⟨η, F, a, har, -, hF, hZ, hXa, -, hchar, hreg, -, -⟩ :=
    e.exists_innerCollar_height hK (ε := 1) one_pos
  refine ⟨F, a, har, hF, hXa, fun p hp h2 => (hchar _).mpr ⟨p, hp, rfl, Or.inl h2⟩,
    fun y hy => ?_, hreg⟩
  obtain ⟨p, hp, rfl, h⟩ := (hchar y).mp hy
  refine ⟨p, hp, ?_, rfl⟩
  rcases h with h2 | ⟨h98, hη⟩
  · linarith
  · by_contra h91
    have h1 := (abs_lt.mp (hZ p hp (by linarith) h98).1).1
    linarith

/-- E6 in each collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.exists_innerCollar_diffeomorph_torus_Icc
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) (hK : 1 ≤ K) :
    ∃ (F : W.Carrier → ℝ) (a : ℝ) (har : a < 90), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ 90},
        letI := cs
        IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ 90} ∧
        ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // F x ≤ 90} => x.1) ∧
        (∀ y : {x : W.Carrier // F x ≤ 90}, (𝓡∂ 3).IsBoundaryPoint y ↔
          (y.1 ∈ B.component i ∨ F y.1 = 90)) ∧
        haveI : Fact (a < 90) := ⟨har⟩
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a 90)
            {x : W.Carrier // F x ≤ 90} ∞,
          (∀ p, F (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ B.component i ↔ p.2.1 = a := by
  obtain ⟨-, F, a, har, -, hF, -, -, -, hprod⟩ :=
    (B.collar i).exists_innerCollar_diffeomorph_torus_Icc hK (ε := 1) one_pos
  exact ⟨F, a, har, hF, hprod⟩

end DifferentialGeometry.Geometry.Collapse
