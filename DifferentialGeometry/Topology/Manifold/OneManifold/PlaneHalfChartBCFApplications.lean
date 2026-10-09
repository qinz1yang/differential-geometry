import DifferentialGeometry.Topology.Manifold.OneManifold.PlaneHalfChartBCF

/-!
# Consumer of the plane half chart lemmas: the axes of the plane (lane S-BCF03)

`σ = id : ℝ² → ℝ²`, `u = x₀`, `w = x₁`: the closed ray `{x₀ = 0, x₁ ≤ 0}` has a corner half chart at
`0` (coordinate `0`) and the axis `{x₀ = 0}` an interior half chart (positive coordinate).
-/

set_option autoImplicit false

open Set Function
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem coordinates_independent_BCF :
    Injective fun v : E2 =>
      (fderiv ℝ (fun x : E2 => x 0) 0 v, fderiv ℝ (fun x : E2 => x 1) 0 v) := by
  intro v v' h
  have h0 : ∀ y : E2, fderiv ℝ (fun x : E2 => x 0) 0 y = y 0 := fun y => by
    have := (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt (x := (0 : E2))
    exact congrArg (fun L => L y) this.fderiv
  have h1 : ∀ y : E2, fderiv ℝ (fun x : E2 => x 1) 0 y = y 1 := fun y => by
    have := (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt (x := (0 : E2))
    exact congrArg (fun L => L y) this.fderiv
  have hh := Prod.mk.inj h
  rw [h0, h0] at hh
  rw [h1, h1] at hh
  ext i
  fin_cases i
  · exact hh.1
  · exact hh.2

theorem exists_halfChart_axis_corner_BCF :
    ∃ (B : Set E2) (d : HalfChart_BCF B {x : E2 | x 0 = 0 ∧ x 1 ≤ 0}),
      (id (0 : E2)) ∈ d.O ∧ d.L (id (0 : E2)) + d.κ = 0 := by
  have hu : ContDiff ℝ ∞ (fun x : E2 => x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).contDiff
  have hw : ContDiff ℝ ∞ (fun x : E2 => x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).contDiff
  exact exists_halfChart_of_plane_corner_BCF (σ := (id : E2 → E2)) contDiff_id
    Topology.IsEmbedding.id (fun x => by
      have : fderiv ℝ (id : E2 → E2) x = ContinuousLinearMap.id ℝ E2 := fderiv_id
      rw [this]
      exact fun a b h => h)
    (Bs₀ := univ) (Oσ := univ) isOpen_univ (by simp) (subset_univ _) isOpen_univ (mem_univ _)
    hu.contDiffOn hw.contDiffOn rfl rfl coordinates_independent_BCF (fun x _ => Iff.rfl)

theorem exists_halfChart_axis_interior_BCF :
    ∃ (B : Set E2) (d : HalfChart_BCF B {x : E2 | x 0 = 0}),
      (id (0 : E2)) ∈ d.O ∧ 0 < d.L (id (0 : E2)) + d.κ := by
  have hu : ContDiff ℝ ∞ (fun x : E2 => x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).contDiff
  have hw : ContDiff ℝ ∞ (fun x : E2 => x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).contDiff
  exact exists_halfChart_of_plane_interior_BCF (σ := (id : E2 → E2)) contDiff_id
    Topology.IsEmbedding.id (fun x => by
      have : fderiv ℝ (id : E2 → E2) x = ContinuousLinearMap.id ℝ E2 := fderiv_id
      rw [this]
      exact fun a b h => h)
    (Bs₀ := univ) (Oσ := univ) isOpen_univ (by simp) (subset_univ _) isOpen_univ (mem_univ _)
    hu.contDiffOn hw.contDiffOn rfl rfl coordinates_independent_BCF (fun x _ => Iff.rfl)

end DifferentialGeometry.Topology
