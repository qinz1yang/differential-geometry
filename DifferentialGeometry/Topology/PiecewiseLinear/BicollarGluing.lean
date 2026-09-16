import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_prod_Icc_of_collars {S A B : Set E} (hS : IsPolyhedron S)
    {ρ₀ ρ₁ : E × ℝ → E}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (S ×ˢ Icc (0 : ℝ) 1) A)
    (hρ₁ : IsPLHomeomorphOn ρ₁ (S ×ˢ Icc (0 : ℝ) 1) B)
    (h₀ : ∀ x ∈ S, ρ₀ (x, 0) = x) (h₁ : ∀ x ∈ S, ρ₁ (x, 0) = x)
    (hAB : A ∩ B = S) :
    ∃ ρ : E × ℝ → E, IsPLHomeomorphOn ρ (S ×ˢ Icc (-1 : ℝ) 1) (A ∪ B) ∧
      (∀ x ∈ S, ρ (x, 0) = x) ∧ MapsTo ρ (S ×ˢ Ico (-1 : ℝ) 0) (A \ S) ∧
      MapsTo ρ (S ×ˢ Ioc (0 : ℝ) 1) (B \ S) := by
  have hnegpoly : IsPolyhedron (Icc (-1 : ℝ) 0) :=
    isHPolytope_Icc.isPolyhedron
  have hpospoly : IsPolyhedron (Icc (0 : ℝ) 1) :=
    isHPolytope_Icc.isPolyhedron
  have hneg : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (-1 : ℝ) 0) (Icc (0 : ℝ) 1) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hnegpoly
      ((isPiecewiseAffineOn_of_affine ((-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap)
        isOpen_univ).mono_of_isPolyhedron hnegpoly (subset_univ _))
    refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
    · intro t ht
      change 0 ≤ -t ∧ -t ≤ 1
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro t ht
      exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩
  have hleft := (hS.isPLHomeomorphOn_id.prodMap hneg).trans hρ₀
  have hagree : EqOn (ρ₀ ∘ Prod.map id (fun t : ℝ => -t)) ρ₁
      ((S ×ˢ Icc (-1 : ℝ) 0) ∩ (S ×ˢ Icc (0 : ℝ) 1)) := by
    rintro ⟨x, t⟩ ht
    have ht0 : t = 0 := le_antisymm ht.1.2.2 ht.2.2.1
    subst t
    simpa using (h₀ x ht.1.1).trans (h₁ x ht.1.1).symm
  have hsurj : SurjOn (ρ₀ ∘ Prod.map id (fun t : ℝ => -t))
      ((S ×ˢ Icc (-1 : ℝ) 0) ∩ (S ×ˢ Icc (0 : ℝ) 1)) (A ∩ B) := by
    intro x hx
    have hxS := hAB.subset hx
    exact ⟨(x, 0), ⟨⟨hxS, by norm_num, by norm_num⟩,
      ⟨hxS, by norm_num, by norm_num⟩⟩, by simpa using h₀ x hxS⟩
  obtain ⟨ρ, hρ, hρleft, hρright⟩ := exists_isPLHomeomorphOn_union
    (hS.prod hnegpoly) (hS.prod hpospoly) hleft hρ₁ hagree hsurj
  have hunion : (S ×ˢ Icc (-1 : ℝ) 0) ∪ (S ×ˢ Icc (0 : ℝ) 1) =
      S ×ˢ Icc (-1 : ℝ) 1 := by
    ext z
    constructor
    · rintro (⟨hx, ha, hb⟩ | ⟨hx, ha, hb⟩) <;> exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, ha, hb⟩
      by_cases hz : z.2 ≤ 0
      · exact Or.inl ⟨hx, ha, hz⟩
      · exact Or.inr ⟨hx, by linarith, hb⟩
  rw [hunion] at hρ
  have hbottom : ∀ x ∈ S, ρ (x, 0) = x := fun x hx =>
    (hρright ⟨hx, by norm_num, by norm_num⟩).trans (h₁ x hx)
  have hnonS (z : E × ℝ) (hz : z ∈ S ×ˢ Icc (-1 : ℝ) 1) (ht : z.2 ≠ 0) : ρ z ∉ S := by
    intro hzS
    have heq := hρ.bijOn.injOn hz ⟨hzS, by norm_num, by norm_num⟩ (hbottom (ρ z) hzS).symm
    exact ht (congrArg Prod.snd heq)
  refine ⟨ρ, hρ, hbottom, ?_, ?_⟩
  · intro z hz
    have hzleft : z ∈ S ×ˢ Icc (-1 : ℝ) 0 := ⟨hz.1, hz.2.1, hz.2.2.le⟩
    refine ⟨?_, hnonS z ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩ hz.2.2.ne⟩
    rw [hρleft hzleft]
    exact hleft.bijOn.mapsTo hzleft
  · intro z hz
    have hzright : z ∈ S ×ˢ Icc (0 : ℝ) 1 := ⟨hz.1, hz.2.1.le, hz.2.2⟩
    refine ⟨?_, hnonS z ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩ hz.2.1.ne'⟩
    rw [hρright hzright]
    exact hρ₁.bijOn.mapsTo hzright

end DifferentialGeometry.Topology.PiecewiseLinear
