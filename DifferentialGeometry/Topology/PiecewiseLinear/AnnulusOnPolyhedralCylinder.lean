import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.Simplex.NormedBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Nonempty ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ A)) :
    ∃ A₀ A₁ : Set X, IsAnnulusOn A A₀ A₁ := by
  obtain ⟨φ⟩ := h
  have hβ : ∀ z : stdSimplexBoundary 2, (⟨z.1, z.2.1⟩ : stdSimplex ℝ (Fin 3)) ∈
      DifferentialGeometry.Simplex.boundary (Fin 3) := fun z => z.2.2
  have hβ' : ∀ z : DifferentialGeometry.Simplex.boundary (Fin 3),
      (z.1.1 : Fin 3 → ℝ) ∈ stdSimplexBoundary 2 := fun z => ⟨z.1.2, z.2⟩
  let β : stdSimplexBoundary 2 ≃ₜ DifferentialGeometry.Simplex.boundary (Fin 3) :=
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, hβ z⟩
      invFun := fun z => ⟨z.1.1, hβ' z⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk fun z => z.2.1).subtype_mk hβ
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hβ' }
  let γ : stdSimplexBoundary 2 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    β.trans (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  let ψ := ((γ.symm.prodCongr (Homeomorph.refl (Icc (0 : ℝ) 1))).trans
    (Homeomorph.Set.prod (stdSimplexBoundary 2) (Icc (0 : ℝ) 1)).symm).trans φ
  exact ⟨Subtype.val '' (ψ '' {p | (p.2 : ℝ) = 0}),
    Subtype.val '' (ψ '' {p | (p.2 : ℝ) = 1}), ψ, rfl, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
