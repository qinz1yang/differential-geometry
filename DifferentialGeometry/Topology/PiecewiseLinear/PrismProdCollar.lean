import DifferentialGeometry.Topology.PiecewiseLinear.PrismArc

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def heightRescaleProd (h : ℝ) : (E × ℝ) →ᵃ[ℝ] (E × ℝ) :=
  (LinearMap.prod (LinearMap.fst ℝ E ℝ) (h⁻¹ • LinearMap.snd ℝ E ℝ)).toAffineMap

theorem heightRescaleProd_apply (h : ℝ) (z : E × ℝ) :
    heightRescaleProd h z = (z.1, z.2 / h) := by
  simp [heightRescaleProd, div_eq_inv_mul]

theorem preimage_heightRescaleProd {h : ℝ} (hh : 0 < h) (P : Set E) :
    heightRescaleProd h ⁻¹' (P ×ˢ Icc (0 : ℝ) 1) = P ×ˢ Icc (0 : ℝ) h := by
  ext z
  rw [mem_preimage, heightRescaleProd_apply]
  simp only [Set.mem_prod, mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [le_div_iff₀ hh] at h2
    rw [div_le_one hh] at h3
    exact ⟨h1, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [le_div_iff₀ hh]; linarith
    · rw [div_le_one hh]; linarith

theorem exists_isPiecewiseAffineOn_prism_of_arcs_height (L : Geometry.SimplicialComplex ℝ F)
    {J A B : Set E} {γ κ : ℝ → E} {p q : E}
    (hγ : IsPLHomeomorphOn γ (Icc (0 : ℝ) 1) A) (hκ : IsPLHomeomorphOn κ (Icc (0 : ℝ) 1) B)
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = q) (hκ0 : κ 0 = p) (hκ1 : κ 1 = q)
    (hunion : A ∪ B = J) (hinter : A ∩ B = {p, q})
    {f g : E → F} (hf : IsPiecewiseAffineOn f J) (hg : IsPiecewiseAffineOn g J)
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hfaceγ : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (γ a), f (γ b), g (γ a), g (γ b)} : Set F) ⊆ convexHull ℝ (u : Set F))
    (hfaceκ : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (κ a), f (κ b), g (κ a), g (κ b)} : Set F) ⊆ convexHull ℝ (u : Set F))
    {h : ℝ} (hh : 0 < h) :
    ∃ Φ : E × ℝ → F, IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) h) ∧
      MapsTo Φ (J ×ˢ Icc (0 : ℝ) h) L.space ∧
      (∀ y ∈ J, Φ (y, 0) = f y) ∧ (∀ y ∈ J, Φ (y, h) = g y) := by
  obtain ⟨Φ₀, hPA, hmaps, hbot, htop⟩ :=
    exists_isPiecewiseAffineOn_prism_of_arcs_mapsTo_space L hγ hκ hγ0 hγ1 hκ0 hκ1 hunion hinter
      hf hg hδ T hT hfaceγ hfaceκ
  refine ⟨Φ₀ ∘ heightRescaleProd h, ?_, ?_, ?_, ?_⟩
  · have hc := hPA.comp (isPiecewiseAffineOn_of_affine (heightRescaleProd h) isOpen_univ)
    rwa [univ_inter, preimage_heightRescaleProd hh J] at hc
  · intro z hz
    refine hmaps ?_
    rw [← preimage_heightRescaleProd hh J] at hz
    exact hz
  · intro y hy
    have hz : heightRescaleProd h ((y, (0 : ℝ)) : E × ℝ) = (y, 0) := by
      rw [heightRescaleProd_apply]
      simp
    rw [Function.comp_apply, hz]
    exact hbot y hy
  · intro y hy
    have hz : heightRescaleProd h ((y, h) : E × ℝ) = (y, 1) := by
      rw [heightRescaleProd_apply]
      simp [div_self (ne_of_gt hh)]
    rw [Function.comp_apply, hz]
    exact htop y hy

open Classical in
theorem exists_isPiecewiseAffineOn_glue_collar_prod (L : Geometry.SimplicialComplex ℝ F)
    {P : Set E} (hP : IsPolyhedron P)
    {G : E × ℝ → F} (hG : IsPiecewiseAffineOn G (P ×ˢ Icc (0 : ℝ) 1))
    (hGL : MapsTo G (P ×ˢ Icc (0 : ℝ) 1) L.space)
    {f : E → F} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {Φ : E × ℝ → F} (hΦ : IsPiecewiseAffineOn Φ (P ×ˢ Icc (0 : ℝ) ε))
    (hΦL : MapsTo Φ (P ×ˢ Icc (0 : ℝ) ε) L.space)
    (hΦbot : ∀ y ∈ P, Φ (y, 0) = f y) (hΦtop : ∀ y ∈ P, Φ (y, ε) = G (y, ε)) :
    ∃ g : E × ℝ → F, IsPiecewiseAffineOn g (P ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo g (P ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ y ∈ P, g (y, 0) = f y) ∧ (∀ z ∈ P ×ˢ Icc ε 1, g z = G z) := by
  classical
  have hGupper : IsPiecewiseAffineOn G (P ×ˢ Icc ε 1) :=
    hG.mono_of_isPolyhedron (hP.prod isHPolytope_Icc.isPolyhedron)
      (prod_mono_right (Icc_subset_Icc hε.le le_rfl))
  have hunion : P ×ˢ Icc (0 : ℝ) ε ∪ P ×ˢ Icc ε 1 = P ×ˢ Icc (0 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc hε.le hε1]
  have heq : EqOn Φ G (P ×ˢ Icc (0 : ℝ) ε ∩ P ×ˢ Icc ε 1) := by
    rintro ⟨y, t⟩ ⟨⟨hy, -, ht2⟩, -, ht3, -⟩
    have hte : t = ε := le_antisymm ht2 ht3
    subst hte
    exact hΦtop y hy
  set g : E × ℝ → F :=
    @Set.piecewise (E × ℝ) (fun _ => F) (P ×ˢ Icc (0 : ℝ) ε) Φ G
      (fun j => Classical.propDecidable _) with hgdef
  have hgmem : ∀ z ∈ P ×ˢ Icc (0 : ℝ) ε, g z = Φ z := by
    intro z hz
    rw [hgdef]
    exact if_pos hz
  have hgnot : ∀ z ∉ P ×ˢ Icc (0 : ℝ) ε, g z = G z := by
    intro z hz
    rw [hgdef]
    exact if_neg hz
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [← hunion]
    exact hΦ.piecewise_of_isClosed hGupper (hP.isClosed.prod isClosed_Icc)
      (hP.isClosed.prod isClosed_Icc) heq
  · intro z hz
    by_cases hzc : z ∈ P ×ˢ Icc (0 : ℝ) ε
    · rw [hgmem _ hzc]
      exact hΦL hzc
    · rw [hgnot _ hzc]
      exact hGL hz
  · intro y hy
    rw [hgmem _ ⟨hy, le_rfl, hε.le⟩]
    exact hΦbot y hy
  · rintro ⟨y, t⟩ ⟨hy, ht1, ht2⟩
    by_cases hzc : ((y, t) : E × ℝ) ∈ P ×ˢ Icc (0 : ℝ) ε
    · rw [hgmem _ hzc]
      have hte : t = ε := le_antisymm hzc.2.2 ht1
      subst hte
      exact hΦtop y hy
    · rw [hgnot _ hzc]

end DifferentialGeometry.Topology.PiecewiseLinear
