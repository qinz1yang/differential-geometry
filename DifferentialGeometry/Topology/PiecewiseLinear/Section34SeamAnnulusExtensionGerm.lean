import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamAnnulusExtensionMatching

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_annulus_map_matching_short_core_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A W₀ W₁ : Set E} {φ ρ₀ ρ₁ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) A)
    {d : ℝ} (hd : 0 < d)
    (hρ₀ : IsPLHomeomorphOn ρ₀ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d) W₀)
    (hρ₁ : IsPLHomeomorphOn ρ₁ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d) W₁)
    (hzero₀ : ∀ x ∈ stdSimplexBoundary 2, ρ₀ (x, 0) = φ (x, 0))
    (hzero₁ : ∀ x ∈ stdSimplexBoundary 2, ρ₁ (x, 0) = φ (x, 0))
    (hW₀A : W₀ ⊆ A) (hW₁A : W₁ ⊆ A) :
    ∃ (e : ℝ) (F : E → E), 0 < e ∧ e ≤ d ∧ IsPLHomeomorphOn F A A ∧
      EqOn F id (φ '' (stdSimplexBoundary 2 ×ˢ {0})) ∧
      F '' (φ '' (stdSimplexBoundary 2 ×ˢ {1})) = φ '' (stdSimplexBoundary 2 ×ˢ {1}) ∧
      ∀ x ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (0 : ℝ) e, F (ρ₀ (x, t)) = ρ₁ (x, t) := by
  let S := stdSimplexBoundary 2
  let J₀ := φ '' (S ×ˢ {(0 : ℝ)})
  let J₁ := φ '' (S ×ˢ {(1 : ℝ)})
  have hS : IsPolyhedron S := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  have hsub (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : S ×ˢ {t} ⊆ S ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.symm ▸ ht⟩
  have hJ₁cl : IsClosed J₁ :=
    ((hS.prod (isHPolytope_singleton (1 : ℝ)).isPolyhedron).image_of_isPiecewiseAffineOn
      (hφ.isPiecewiseAffineOn.mono_of_isPolyhedron
        (hS.prod (isHPolytope_singleton _).isPolyhedron) (hsub 1 (by norm_num)))
      (hφ.bijOn.injOn.mono (hsub 1 (by norm_num)))).isClosed
  have hdis : Disjoint J₀ J₁ := by
    apply disjoint_left.mpr
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have heq := hφ.bijOn.injOn (hsub 0 (by norm_num) hx) (hsub 1 (by norm_num) hy)
      (hxz.trans hyz.symm)
    exact zero_ne_one (hx.2.symm.trans ((congrArg Prod.snd heq).trans hy.2))
  have hO : J₁ᶜ ∈ 𝓝ˢ[A] J₀ := mem_nhdsSetWithin.mpr
    ⟨J₁ᶜ, hJ₁cl.isOpen_compl,
      fun z hz => fun hz' => disjoint_left.mp hdis hz hz', inter_subset_left⟩
  have hshort {ρ : (Fin 3 → ℝ) × ℝ → E} {W : Set E}
      (hρ : IsPLHomeomorphOn ρ (S ×ˢ Icc (0 : ℝ) d) W)
      (hzero : ∀ x ∈ S, ρ (x, 0) = φ (x, 0)) (hWA : W ⊆ A) :
      ∃ e : ℝ, 0 < e ∧ e ≤ d ∧ ρ '' (S ×ˢ Icc (0 : ℝ) e) ⊆ J₁ᶜ := by
    apply exists_short_product_image_subset_of_compact hS.isCompact hd
      hρ.isPiecewiseAffineOn.continuousOn (hρ.bijOn.mapsTo.mono_right hWA) _ hO
    intro x hx
    rw [hzero x hx]
    exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  obtain ⟨e₀, he₀, he₀d, he₀O⟩ := hshort hρ₀ hzero₀ hW₀A
  obtain ⟨e₁, he₁, he₁d, he₁O⟩ := hshort hρ₁ hzero₁ hW₁A
  let e := min e₀ e₁
  have he : 0 < e := lt_min he₀ he₁
  have hed : e ≤ d := (min_le_left _ _).trans he₀d
  let κ : (Fin 3 → ℝ) → E := fun x => φ (x, 0)
  have hκ : IsPLHomeomorphOn κ S J₀ :=
    (hS.isPLHomeomorphOn_prod_const 0).trans
      (hφ.restrict (hS.prod (isHPolytope_singleton _).isPolyhedron) (hsub 0 (by norm_num)))
  let ν := Function.invFunOn κ S
  let δ₀ := ρ₀ ∘ Prod.map ν id
  let δ₁ := ρ₁ ∘ Prod.map ν id
  have hsmall : S ×ˢ Icc (0 : ℝ) e ⊆ S ×ˢ Icc (0 : ℝ) d :=
    prod_mono_right (Icc_subset_Icc le_rfl hed)
  have hρ₀' := hρ₀.restrict (hS.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hρ₁' := hρ₁.restrict (hS.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hνprod := hκ.symm.prodMap
    (isHPolytope_Icc (a := (0 : ℝ)) (b := e)).isPolyhedron.isPLHomeomorphOn_id
  have hδ₀ : IsPLHomeomorphOn δ₀ (J₀ ×ˢ Icc (0 : ℝ) e)
      (ρ₀ '' (S ×ˢ Icc (0 : ℝ) e)) := hνprod.trans hρ₀'
  have hδ₁ : IsPLHomeomorphOn δ₁ (J₀ ×ˢ Icc (0 : ℝ) e)
      (ρ₁ '' (S ×ˢ Icc (0 : ℝ) e)) := hνprod.trans hρ₁'
  have hz₀ (z : E) (hz : z ∈ J₀) : δ₀ (z, 0) = z := by
    change ρ₀ (ν z, 0) = z
    rw [hzero₀ (ν z) (hκ.symm.bijOn.mapsTo hz)]
    exact hκ.bijOn.invOn_invFunOn.2 hz
  have hz₁ (z : E) (hz : z ∈ J₀) : δ₁ (z, 0) = z := by
    change ρ₁ (ν z, 0) = z
    rw [hzero₁ (ν z) (hκ.symm.bijOn.mapsTo hz)]
    exact hκ.bijOn.invOn_invFunOn.2 hz
  have hsmall₀ : ρ₀ '' (S ×ˢ Icc (0 : ℝ) e) ⊆ ρ₀ '' (S ×ˢ Icc (0 : ℝ) e₀) :=
    image_mono (prod_mono_right (Icc_subset_Icc le_rfl (min_le_left e₀ e₁)))
  have hsmall₁ : ρ₁ '' (S ×ˢ Icc (0 : ℝ) e) ⊆ ρ₁ '' (S ×ˢ Icc (0 : ℝ) e₁) :=
    image_mono (prod_mono_right (Icc_subset_Icc le_rfl (min_le_right e₀ e₁)))
  obtain ⟨F, hF, hFzero, hFtop, hFmatch⟩ :=
    hφ.exists_annulus_map_matching_rim_collars he hδ₀ hδ₁ hz₀ hz₁
      ((image_mono hsmall).trans hρ₀.image_eq.subset |>.trans hW₀A)
      ((image_mono hsmall).trans hρ₁.image_eq.subset |>.trans hW₁A)
      (disjoint_left.mpr fun z hz hz' => he₀O (hsmall₀ hz) hz')
      (disjoint_left.mpr fun z hz hz' => he₁O (hsmall₁ hz) hz')
  refine ⟨e, F, he, hed, hF, hFzero, hFtop, ?_⟩
  intro x hx t ht
  have h := hFmatch (κ x) (hκ.bijOn.mapsTo hx) t ht
  change F (ρ₀ (ν (κ x), t)) = ρ₁ (ν (κ x), t) at h
  rwa [show ν (κ x) = x from hκ.bijOn.invOn_invFunOn.1 hx] at h

end DifferentialGeometry.Topology.PiecewiseLinear
