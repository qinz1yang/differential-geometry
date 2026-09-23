import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.symm {X : Type*} [TopologicalSpace X] {A A₀ A₁ : Set X}
    (h : IsAnnulusOn A A₀ A₁) : IsAnnulusOn A A₁ A₀ := by
  obtain ⟨φ, h₀, h₁⟩ := h
  let e := (Homeomorph.refl (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).prodCongr
    unitInterval.symmHomeomorph
  let ψ := e.trans φ
  have key (s : ℝ) : Subtype.val '' (φ '' {p | (p.2 : ℝ) = s}) =
      Subtype.val '' (ψ '' {p | (p.2 : ℝ) = 1 - s}) := by
    apply congrArg (image Subtype.val)
    apply Subset.antisymm
    · rintro y ⟨p, hp, rfl⟩
      refine ⟨e.symm p, ?_, congrArg φ (e.apply_symm_apply p)⟩
      change 1 - (p.2 : ℝ) = 1 - s
      rw [hp]
    · rintro y ⟨p, hp, rfl⟩
      refine ⟨e p, ?_, rfl⟩
      change 1 - (p.2 : ℝ) = s
      change (p.2 : ℝ) = 1 - s at hp
      linarith
  exact ⟨ψ, by simpa only [sub_self] using h₁.trans (key 1),
    by simpa only [sub_zero] using h₀.trans (key 0)⟩

theorem isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (φ : (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ A) :
    IsAnnulusOn A (Subtype.val '' (φ '' {p | p.1.2 = 0}))
      (Subtype.val '' (φ '' {p | p.1.2 = 1})) := by
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
  let e := (γ.symm.prodCongr (Homeomorph.refl (Icc (0 : ℝ) 1))).trans
    (Homeomorph.Set.prod (stdSimplexBoundary 2) (Icc (0 : ℝ) 1)).symm
  let ψ := e.trans φ
  have key (t : ℝ) : Subtype.val '' (φ '' {p | p.1.2 = t}) =
      Subtype.val '' (ψ '' {p | (p.2 : ℝ) = t}) := by
    apply congrArg (image Subtype.val)
    apply Subset.antisymm
    · rintro y ⟨p, hp, rfl⟩
      refine ⟨e.symm p, hp, ?_⟩
      exact congrArg φ (e.apply_symm_apply p)
    · rintro y ⟨p, hp, rfl⟩
      exact ⟨e p, hp, rfl⟩
  exact ⟨ψ, key 0, key 1⟩

theorem annulus_level_subset_sdiff_ends
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (φ : (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ A) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Subtype.val '' (φ '' {p | p.1.2 = t}) ⊆ A \
      (Subtype.val '' (φ '' {p | p.1.2 = 0}) ∪
        Subtype.val '' (φ '' {p | p.1.2 = 1})) := by
  have hdis {r s : ℝ} (hrs : r ≠ s) :
      Disjoint (Subtype.val '' (φ '' {p | p.1.2 = r}))
        (Subtype.val '' (φ '' {p | p.1.2 = s})) := by
    apply disjoint_image_of_injective Subtype.val_injective
    apply disjoint_image_of_injective φ.injective
    exact disjoint_left.mpr fun p hp hq => hrs (hp.symm.trans hq)
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y.2, ?_⟩
  rintro (h₀ | h₁)
  · exact disjoint_left.mp (hdis ht.1.ne') ⟨y, hy, rfl⟩ h₀
  · exact disjoint_left.mp (hdis ht.2.ne) ⟨y, hy, rfl⟩ h₁

theorem exists_isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Nonempty ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ A)) :
    ∃ A₀ A₁ : Set X, IsAnnulusOn A A₀ A₁ := by
  obtain ⟨φ⟩ := h
  exact ⟨_, _, isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod φ⟩

open Classical in
theorem IsPLHomeomorphOn.boundaryComplex_eq_annulus_ends
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : Set E} (hJ : IsPLSphere 1 J) {a b : ℝ} (hab : a < b)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces] {ρ : E × ℝ → F}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc a b) K.space) :
    (boundaryComplex 2 K).space = ρ '' (J ×ˢ {a, b}) := by
  obtain ⟨A, hAfin, hA, -, hAspace, hAbd⟩ := hρ.exists_annulus_complex hJ hab
  have : Finite A.faces := hAfin.to_subtype
  have hid : IsPLHomeomorphOn id A.space K.space := by
    rw [hAspace]
    exact (isPolyhedron_space K).isPLHomeomorphOn_id
  rw [boundaryComplex_space_of_isPLHomeomorphOn A K hA hid, image_id, hAbd]

end DifferentialGeometry.Topology.PiecewiseLinear
