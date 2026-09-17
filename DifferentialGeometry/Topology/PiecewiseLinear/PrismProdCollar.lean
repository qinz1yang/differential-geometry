import DifferentialGeometry.Topology.PiecewiseLinear.PrismArc
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSquareApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

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

theorem exists_isPiecewiseAffineOn_prod_eqOn_bottom_of_arcs [FiniteDimensional ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {J A B : Set E} {γ κ : ℝ → E} {p q : E}
    (hγ : IsPLHomeomorphOn γ (Icc (0 : ℝ) 1) A) (hκ : IsPLHomeomorphOn κ (Icc (0 : ℝ) 1) B)
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = q) (hκ0 : κ 0 = p) (hκ1 : κ 1 = q)
    (hunion : A ∪ B = J) (hinter : A ∩ B = {p, q})
    {f : E × ℝ → F} (hf : ContinuousOn f (J ×ˢ Icc (0 : ℝ) 1))
    (hfL : MapsTo f (J ×ˢ Icc (0 : ℝ) 1) L.space)
    (hbot : IsPiecewiseAffineOn (fun y : E => f (y, 0)) J)
    {n : ℕ} {s : ℕ → ℝ} (hs0 : s 0 = 0) (hsn : s n = 1) (hn : 0 < n)
    (hmono : ∀ i < n, s i < s (i + 1))
    (hcellγ : ∀ i < n, ∃ u ∈ L.faces, ∀ x ∈ Icc (s i) (s (i + 1)),
      f (γ x, 0) ∈ convexHull ℝ (u : Set F))
    (hcellκ : ∀ i < n, ∃ u ∈ L.faces, ∀ x ∈ Icc (s i) (s (i + 1)),
      f (κ x, 0) ∈ convexHull ℝ (u : Set F)) :
    ∃ g : E × ℝ → F, IsPiecewiseAffineOn g (J ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo g (J ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ y ∈ J, g (y, 0) = f (y, 0)) := by
  classical
  have hone : (0 : ℝ) < 1 := by norm_num
  have hApoly : IsPolyhedron A := ((isPLBall_Icc hone).of_isPLHomeomorphOn hγ).isPolyhedron
  have hBpoly : IsPolyhedron B := ((isPLBall_Icc hone).of_isPLHomeomorphOn hκ).isPolyhedron
  have hJ : IsPolyhedron J := hunion ▸ hApoly.union hBpoly
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 : ℝ) / 2 < 1 := by norm_num
  set ρ : E × ℝ → E × ℝ := fun z => (z.1, collarReparam (1 / 2) z.2) with hρdef
  have hρcont : Continuous ρ :=
    continuous_fst.prodMk ((continuous_collarReparam _).comp continuous_snd)
  have hρmaps : MapsTo ρ (J ×ˢ Icc (0 : ℝ) 1) (J ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hz.1, collarReparam_mem hε1 hz.2.2⟩
  have hf' : ContinuousOn (f ∘ ρ) (J ×ˢ Icc (0 : ℝ) 1) := hf.comp hρcont.continuousOn hρmaps
  have hf'L : MapsTo (f ∘ ρ) (J ×ˢ Icc (0 : ℝ) 1) L.space := fun z hz => hfL (hρmaps hz)
  obtain ⟨K, hKfin, hKspace⟩ :=
    IsPolyhedron.exists_simplicialComplex (hJ.prod isHPolytope_Icc.isPolyhedron)
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨K', φ, hK', hK'fin, hφ, hclose⟩ :=
    exists_isSubdivision_simplicialApproximation K L (by rw [hKspace]; exact hf')
      (by rw [hKspace]; exact hf'L)
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = J ×ˢ Icc (0 : ℝ) 1 := by rw [hK'.space_eq, hKspace]
  have hG : IsPiecewiseAffineOn (simplicialMap K' φ) (J ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hK'space]
    exact isPiecewiseAffineOn_simplicialMap K' φ
  have hGL : MapsTo (simplicialMap K' φ) (J ×ˢ Icc (0 : ℝ) 1) L.space := by
    rw [← hK'space]
    exact simplicialMap_mapsTo K' L φ hφ
  have hslice : ∀ y : E, (f ∘ ρ) (y, 1 / 2) = f (y, 0) := by
    intro y
    rw [Function.comp_apply, hρdef]
    simp only
    rw [collarReparam_eq_zero hε1 le_rfl]
  have hGslice : IsPiecewiseAffineOn (fun y : E => simplicialMap K' φ (y, 1 / 2)) J := by
    have haff : IsPiecewiseAffineOn (fun y : E => ((y, (1 : ℝ) / 2) : E × ℝ)) (univ : Set E) :=
      (isPiecewiseAffineOn_of_affine
        (AffineMap.const ℝ E ((0 : E), (1 : ℝ) / 2) +
          ((LinearMap.id).prod 0).toAffineMap) isOpen_univ).congr (fun y _ => by simp)
    have hc := hG.comp haff
    have hset : (univ : Set E) ∩ (fun y : E => ((y, (1 : ℝ) / 2) : E × ℝ)) ⁻¹'
        (J ×ˢ Icc (0 : ℝ) 1) = J := by
      ext y
      simp only [univ_inter, mem_preimage, Set.mem_prod, mem_Icc]
      exact ⟨fun h => h.1, fun h => ⟨h, hε.le, hε1.le⟩⟩
    rwa [hset] at hc
  have hcarrier : ∀ y : E, ∀ u ∈ L.faces, y ∈ J → f (y, 0) ∈ convexHull ℝ (u : Set F) →
      simplicialMap K' φ (y, 1 / 2) ∈ convexHull ℝ (u : Set F) := by
    intro y u hu hyJ hfy
    have hyK : ((y, (1 : ℝ) / 2) : E × ℝ) ∈ K.space := by
      rw [hKspace]
      exact ⟨hyJ, hε.le, hε1.le⟩
    have h1 := hclose _ hyK
    rw [hslice y] at h1
    exact convexHull_mono (Finset.coe_subset.mpr
      (carrierFace_subset (L.convexHull_subset_space hu hfy) hu hfy)) h1
  have hface : ∀ (θ : ℝ → E), MapsTo θ (Icc (0 : ℝ) 1) J →
      (∀ i < n, ∃ u ∈ L.faces, ∀ x ∈ Icc (s i) (s (i + 1)),
        f (θ x, 0) ∈ convexHull ℝ (u : Set F)) →
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < 1 →
      (∀ x ∈ (Finset.range (n + 1)).image s, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (θ a, 0), f (θ b, 0), simplicialMap K' φ (θ a, 1 / 2),
        simplicialMap K' φ (θ b, 1 / 2)} : Set F) ⊆ convexHull ℝ (u : Set F) := by
    intro θ hθ hcell a ha b hb hle _ hgap
    obtain ⟨u, hu, hsub⟩ :=
      exists_face_of_no_partition_point_between L hs0 hsn hn hmono hcell ha hb hle
        (fun i hi hcon => hgap (s i)
          (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩) hcon)
    refine ⟨u, hu, ?_⟩
    rintro y (rfl | rfl | rfl | rfl)
    · exact hsub (mem_insert _ _)
    · exact hsub (mem_insert_of_mem _ rfl)
    · exact hcarrier _ u hu (hθ ha) (hsub (mem_insert _ _))
    · exact hcarrier _ u hu (hθ hb) (hsub (mem_insert_of_mem _ rfl))
  have hTmem : ∀ x ∈ (Finset.range (n + 1)).image s, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact mem_Icc_of_forall_lt_succ hmono hs0 hsn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  obtain ⟨Φ, hPAΦ, hmapsΦ, hbotΦ, htopΦ⟩ :=
    exists_isPiecewiseAffineOn_prism_of_arcs_height L hγ hκ hγ0 hγ1 hκ0 hκ1 hunion hinter
      hbot hGslice one_pos ((Finset.range (n + 1)).image s) hTmem
      (hface γ (fun x hx => hunion ▸ Or.inl (hγ.bijOn.mapsTo hx)) hcellγ)
      (hface κ (fun x hx => hunion ▸ Or.inr (hκ.bijOn.mapsTo hx)) hcellκ) hε
  obtain ⟨g, hgPA, hgL, hgbot, -⟩ :=
    exists_isPiecewiseAffineOn_glue_collar_prod L hJ hG hGL hε hε1.le hPAΦ hmapsΦ hbotΦ htopΦ
  exact ⟨g, hgPA, hgL, hgbot⟩

end DifferentialGeometry.Topology.PiecewiseLinear
