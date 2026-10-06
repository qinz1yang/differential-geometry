import DifferentialGeometry.Topology.Manifold.OneManifold.PlaneCurveBCF

/-!
# Consumer of `exists_curve_of_independent_BCF`: the coordinate axes of the plane (lane S-BCF03)

`exists_curve_coordinates_BCF`: for `u = x₀`, `w = x₁` (independent differentials at `0`) the lemma
applies with `P = ℝ²` and gives a smooth curve `c` with `x₀ ∘ c = 0`, `x₁ ∘ c = id` (the axis).
-/

set_option autoImplicit false

open Set Function
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem exists_curve_coordinates_BCF :
    ∃ (ε : ℝ) (N : Set E2) (c : ℝ → E2), 0 < ε ∧ IsOpen N ∧ (0 : E2) ∈ N ∧
      ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧ c 0 = 0 ∧
      (∀ s ∈ Ioo (-ε) ε, c s ∈ N ∧ c s 0 = 0 ∧ c s 1 = s) ∧
      (∀ x ∈ N, x 0 = 0 → x 1 ∈ Ioo (-ε) ε ∧ c (x 1) = x) ∧
      (∀ s ∈ Ioo (-ε) ε, deriv c s ≠ 0) := by
  have hu : ContDiff ℝ ∞ (fun x : E2 => x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).contDiff
  have hw : ContDiff ℝ ∞ (fun x : E2 => x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).contDiff
  obtain ⟨ε, N, c, hε, hN, h0N, -, hc, hc0, h1, h2, h3⟩ := exists_curve_of_independent_BCF
    (u := fun x : E2 => x 0) (w := fun x : E2 => x 1) (P := univ) isOpen_univ (mem_univ _)
    hu.contDiffOn hw.contDiffOn rfl rfl (by
      intro v v' h
      have h0 : fderiv ℝ (fun x : E2 => x 0) 0 v = v 0 := by
        have := (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt (x := (0 : E2))
        exact congrArg (fun L => L v) this.fderiv
      have h1 : fderiv ℝ (fun x : E2 => x 1) 0 v = v 1 := by
        have := (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt (x := (0 : E2))
        exact congrArg (fun L => L v) this.fderiv
      have h0' : fderiv ℝ (fun x : E2 => x 0) 0 v' = v' 0 := by
        have := (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt (x := (0 : E2))
        exact congrArg (fun L => L v') this.fderiv
      have h1' : fderiv ℝ (fun x : E2 => x 1) 0 v' = v' 1 := by
        have := (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt (x := (0 : E2))
        exact congrArg (fun L => L v') this.fderiv
      have hh := Prod.mk.inj h
      rw [h0, h0'] at hh
      rw [h1, h1'] at hh
      ext i
      fin_cases i
      · exact hh.1
      · exact hh.2.symm.symm)
  exact ⟨ε, N, c, hε, hN, h0N, hc, hc0, fun s hs => h1 s hs, h2, h3⟩

end DifferentialGeometry.Topology
