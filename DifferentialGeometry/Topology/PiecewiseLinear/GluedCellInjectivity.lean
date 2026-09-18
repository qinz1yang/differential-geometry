import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingPrecomp

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem mem_seam_of_image_mem_of_injOn
    {Q S B : Set (EuclideanSpace ℝ (Fin 2))}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hinj : InjOn f Q) (hSQ : S ⊆ Q) (hB : f '' S = B)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Q) (hmem : f x ∈ B) : x ∈ S := by
  rw [← hB] at hmem
  obtain ⟨x', hx', hxx'⟩ := hmem
  exact (hinj (hSQ hx') hx hxx') ▸ hx'

theorem fiber_le_two_of_glue_boundary_arc {D D₁ D₂ : SingularTwoCell M}
    {P Q B : Set (EuclideanSpace ℝ (Fin 2))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf₁ : IsPLHomeomorphOn f₁ P D₁.domain) (hf₂ : IsPLHomeomorphOn f₂ Q D₂.domain)
    (hDP : EqOn D (D₁ ∘ f₁) P) (hDQ : EqOn D (D₂ ∘ f₂) Q)
    (hdom : D.domain = P ∪ Q) (hB : f₂ '' (P ∩ Q) = B)
    (hD₁fib : ∀ y, (D₁.domain ∩ D₁ ⁻¹' {y}).encard ≤ 2)
    (hD₂inj : InjOn D₂ D₂.domain)
    (hD₂disj : ∀ x ∈ D₂.domain, x ∉ B → ∀ z ∈ D₁.domain, D₂ x ≠ D₁ z) :
    ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2 := by
  intro y
  rcases Classical.em (∃ x, x ∈ Q ∧ D x = y ∧ f₂ x ∉ B) with ⟨x₀, hx₀Q, hx₀y, hx₀B⟩ | hcase
  · have hx₀val : D₂ (f₂ x₀) = y := (hDQ hx₀Q).symm.trans hx₀y
    have hsub : D.domain ∩ D ⁻¹' {y} ⊆ Q := by
      intro z hz
      have hzd := hz.1
      rw [hdom] at hzd
      rcases hzd with hzP | hzQ
      · exact absurd ((hDP hzP).symm.trans hz.2)
          (fun h => hD₂disj (f₂ x₀) (hf₂.bijOn.mapsTo hx₀Q) hx₀B (f₁ z)
            (hf₁.bijOn.mapsTo hzP) (hx₀val.trans h.symm))
      · exact hzQ
    refine le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
    intro a b ha hb
    have haQ : a ∈ Q := hsub ha
    have hbQ : b ∈ Q := hsub hb
    have h1 : D₂ (f₂ a) = y := (hDQ haQ).symm.trans ha.2
    have h2 : D₂ (f₂ b) = y := (hDQ hbQ).symm.trans hb.2
    have hval : D₂ (f₂ a) = D₂ (f₂ b) := h1.trans h2.symm
    exact hf₂.bijOn.injOn haQ hbQ
      (hD₂inj (hf₂.bijOn.mapsTo haQ) (hf₂.bijOn.mapsTo hbQ) hval)
  · have hall : ∀ x ∈ Q, D x = y → f₂ x ∈ B := by
      intro x hxQ hxy
      by_contra hb
      exact hcase ⟨x, hxQ, hxy, hb⟩
    have hsub : D.domain ∩ D ⁻¹' {y} ⊆ P := by
      intro z hz
      have hzd := hz.1
      rw [hdom] at hzd
      rcases hzd with hzP | hzQ
      · exact hzP
      · exact (mem_seam_of_image_mem_of_injOn hf₂.bijOn.injOn inter_subset_right hB hzQ
          (hall z hzQ hz.2)).1
    have himg : f₁ '' (D.domain ∩ D ⁻¹' {y}) = D₁.domain ∩ D₁ ⁻¹' {y} := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact ⟨hf₁.bijOn.mapsTo (hsub hz), (hDP (hsub hz)).symm.trans hz.2⟩
      · rintro w ⟨hwd, hwy⟩
        obtain ⟨z, hzP, rfl⟩ := hf₁.bijOn.surjOn hwd
        refine ⟨z, ⟨?_, ?_⟩, rfl⟩
        · rw [hdom]
          exact Or.inl hzP
        · exact (hDP hzP).trans hwy
    have hcard : (D.domain ∩ D ⁻¹' {y}).encard = (D₁.domain ∩ D₁ ⁻¹' {y}).encard := by
      rw [← himg, (hf₁.bijOn.injOn.mono hsub).encard_image]
    rw [hcard]
    exact hD₁fib y

theorem injOn_of_subset_second_piece {D D₂ : SingularTwoCell M}
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    {f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf₂ : IsPLHomeomorphOn f₂ Q D₂.domain) (hDQ : EqOn D (D₂ ∘ f₂) Q)
    (hD₂inj : InjOn D₂ D₂.domain) {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : U ⊆ Q) :
    InjOn D U := by
  intro a ha b hb hab
  have haQ : a ∈ Q := hU ha
  have hbQ : b ∈ Q := hU hb
  have hval : D₂ (f₂ a) = D₂ (f₂ b) := ((hDQ haQ).symm.trans hab).trans (hDQ hbQ)
  exact hf₂.bijOn.injOn haQ hbQ
    (hD₂inj (hf₂.bijOn.mapsTo haQ) (hf₂.bijOn.mapsTo hbQ) hval)

theorem locallyInjective_of_glue_boundary_arc {D D₁ D₂ : SingularTwoCell M}
    {P Q B : Set (EuclideanSpace ℝ (Fin 2))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hPball : IsPLBall 2 P)
    (hf₁ : IsPLHomeomorphOn f₁ P D₁.domain) (hf₂ : IsPLHomeomorphOn f₂ Q D₂.domain)
    (hDP : EqOn D (D₁ ∘ f₁) P) (hDQ : EqOn D (D₂ ∘ f₂) Q)
    (hdom : D.domain = P ∪ Q) (hB : f₂ '' (P ∩ Q) = B)
    (hD₁loc : ∀ x ∈ D₁.domain, ∃ V ∈ 𝓝[D₁.domain] x, InjOn D₁ V)
    (hD₂inj : InjOn D₂ D₂.domain)
    (hD₂disj : ∀ x ∈ D₂.domain, x ∉ B → ∀ z ∈ D₁.domain, D₂ x ≠ D₁ z) :
    ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn D U := by
  have hPclosed : IsClosed P := hPball.isPolyhedron.isCompact.isClosed
  have hcross : ∀ a ∈ P, ∀ b ∈ Q, b ∉ P → D a ≠ D b := by
    intro a haP b hbQ hbP hab
    have hbB : f₂ b ∉ B := fun hmem =>
      hbP (mem_seam_of_image_mem_of_injOn hf₂.bijOn.injOn inter_subset_right hB hbQ hmem).1
    refine hD₂disj (f₂ b) (hf₂.bijOn.mapsTo hbQ) hbB (f₁ a) (hf₁.bijOn.mapsTo haP) ?_
    exact ((hDQ hbQ).symm.trans hab.symm).trans (hDP haP)
  intro x hx
  rw [hdom] at hx
  rcases hx with hxP | hxQ
  · obtain ⟨V, hV, hVinj⟩ := hD₁loc (f₁ x) (hf₁.bijOn.mapsTo hxP)
    have hU₁ : P ∩ f₁ ⁻¹' V ∈ 𝓝[P] x := by
      have h := mem_nhdsWithin_inter_preimage hf₁ (hf₁.bijOn.mapsTo hxP) hV
      rwa [hf₁.bijOn.invOn_invFunOn.1 hxP] at h
    obtain ⟨W, hWopen, hxW, hWsub⟩ := mem_nhdsWithin.mp hU₁
    refine ⟨(P ∩ W) ∪ (Q \ P), ?_, ?_⟩
    · rw [hdom]
      refine mem_nhdsWithin.mpr ⟨W, hWopen, hxW, ?_⟩
      rintro z ⟨hzW, hzP | hzQ⟩
      · exact Or.inl ⟨hzP, hzW⟩
      · by_cases hzP : z ∈ P
        · exact Or.inl ⟨hzP, hzW⟩
        · exact Or.inr ⟨hzQ, hzP⟩
    · rintro a (⟨haP, haW⟩ | ⟨haQ, haP⟩) b (⟨hbP, hbW⟩ | ⟨hbQ, hbP⟩) hab
      · have hfa : f₁ a ∈ V := (hWsub ⟨haW, haP⟩).2
        have hfb : f₁ b ∈ V := (hWsub ⟨hbW, hbP⟩).2
        refine hf₁.bijOn.injOn haP hbP (hVinj hfa hfb ?_)
        exact ((hDP haP).symm.trans hab).trans (hDP hbP)
      · exact absurd hab (hcross a haP b hbQ hbP)
      · exact absurd hab.symm (hcross b hbP a haQ haP)
      · exact injOn_of_subset_second_piece (U := Q \ P) hf₂ hDQ hD₂inj
          (fun z hz => hz.1) ⟨haQ, haP⟩ ⟨hbQ, hbP⟩ hab
  · by_cases hxP : x ∈ P
    · obtain ⟨V, hV, hVinj⟩ := hD₁loc (f₁ x) (hf₁.bijOn.mapsTo hxP)
      have hU₁ : P ∩ f₁ ⁻¹' V ∈ 𝓝[P] x := by
        have h := mem_nhdsWithin_inter_preimage hf₁ (hf₁.bijOn.mapsTo hxP) hV
        rwa [hf₁.bijOn.invOn_invFunOn.1 hxP] at h
      obtain ⟨W, hWopen, hxW, hWsub⟩ := mem_nhdsWithin.mp hU₁
      refine ⟨(P ∩ W) ∪ (Q \ P), ?_, ?_⟩
      · rw [hdom]
        refine mem_nhdsWithin.mpr ⟨W, hWopen, hxW, ?_⟩
        rintro z ⟨hzW, hzP | hzQ⟩
        · exact Or.inl ⟨hzP, hzW⟩
        · by_cases hzP : z ∈ P
          · exact Or.inl ⟨hzP, hzW⟩
          · exact Or.inr ⟨hzQ, hzP⟩
      · rintro a (⟨haP, haW⟩ | ⟨haQ, haP⟩) b (⟨hbP, hbW⟩ | ⟨hbQ, hbP⟩) hab
        · have hfa : f₁ a ∈ V := (hWsub ⟨haW, haP⟩).2
          have hfb : f₁ b ∈ V := (hWsub ⟨hbW, hbP⟩).2
          refine hf₁.bijOn.injOn haP hbP (hVinj hfa hfb ?_)
          exact ((hDP haP).symm.trans hab).trans (hDP hbP)
        · exact absurd hab (hcross a haP b hbQ hbP)
        · exact absurd hab.symm (hcross b hbP a haQ haP)
        · exact injOn_of_subset_second_piece (U := Q \ P) hf₂ hDQ hD₂inj
            (fun z hz => hz.1) ⟨haQ, haP⟩ ⟨hbQ, hbP⟩ hab
    · refine ⟨Q \ P, ?_, injOn_of_subset_second_piece (U := Q \ P) hf₂ hDQ hD₂inj (fun z hz => hz.1)⟩
      rw [hdom]
      refine mem_nhdsWithin.mpr ⟨Pᶜ, hPclosed.isOpen_compl, hxP, ?_⟩
      rintro z ⟨hzP, hzPQ | hzQ⟩
      · exact absurd hzPQ hzP
      · exact ⟨hzQ, hzP⟩

end DifferentialGeometry.Topology.PiecewiseLinear
