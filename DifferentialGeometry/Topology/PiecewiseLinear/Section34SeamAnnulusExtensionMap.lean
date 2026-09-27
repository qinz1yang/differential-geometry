import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamAnnulusExtensionComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_lateral_map_matching_rim_collars
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {W₀ W₁ : Set (E × ℝ)} {ρ₀ ρ₁ : (E × ℝ) × ℝ → E × ℝ}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (((r '' stdSimplexBoundary 2) ×ˢ {a}) ×ˢ Icc c d) W₀)
    (hρ₁ : IsPLHomeomorphOn ρ₁ (((r '' stdSimplexBoundary 2) ×ˢ {a}) ×ˢ Icc c d) W₁)
    (hzero₀ : ∀ z ∈ (r '' stdSimplexBoundary 2) ×ˢ {a}, ρ₀ (z, c) = z)
    (hzero₁ : ∀ z ∈ (r '' stdSimplexBoundary 2) ×ˢ {a}, ρ₁ (z, c) = z)
    (hW₀A : W₀ ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hW₁A : W₁ ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hdis₀ : Disjoint W₀ ((r '' stdSimplexBoundary 2) ×ˢ {b}))
    (hdis₁ : Disjoint W₁ ((r '' stdSimplexBoundary 2) ×ˢ {b})) :
    ∃ F : E × ℝ → E × ℝ,
      IsPLHomeomorphOn F ((r '' stdSimplexBoundary 2) ×ˢ Icc a b)
        ((r '' stdSimplexBoundary 2) ×ˢ Icc a b) ∧
      EqOn F id ((r '' stdSimplexBoundary 2) ×ˢ {a}) ∧
      F '' ((r '' stdSimplexBoundary 2) ×ˢ {b}) = (r '' stdSimplexBoundary 2) ×ˢ {b} ∧
      ∀ z ∈ (r '' stdSimplexBoundary 2) ×ˢ {a}, ∀ t ∈ Icc c d,
        F (ρ₀ (z, t)) = ρ₁ (z, t) := by
  classical
  let J := r '' stdSimplexBoundary 2
  let A := J ×ˢ Icc a b
  let D₀ := P ×ˢ {a}
  let D₁ := P ×ˢ {b}
  let J₀ := J ×ˢ {a}
  let J₁ := J ×ˢ {b}
  let S := P ×ˢ {a, b} ∪ A
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJP : J ⊆ P := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hS : IsPLSphere 2 S := hr.isPLSphere_prism_boundary hab
  have hA : IsPolyhedron A := hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hAS : A ⊆ S := subset_union_right
  have hr₀ := hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hr₁ := hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const b)
  have hb₀ : ((fun x : E => (x, a)) ∘ r) '' stdSimplexBoundary 2 = J₀ := by
    rw [image_comp, ← prod_singleton]
  have hD₀ : IsPLBall 2 D₀ := ⟨_, hr₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨_, hr₁⟩
  have hD₀S : D₀ ⊆ S := fun z hz => Or.inl ⟨hz.1, Or.inl hz.2⟩
  have hD₁S : D₁ ⊆ S := fun z hz => Or.inl ⟨hz.1, Or.inr hz.2⟩
  have hcap {W : Set (E × ℝ)} {ρ : (E × ℝ) × ℝ → E × ℝ}
      (hρ : IsPLHomeomorphOn ρ (J₀ ×ˢ Icc c d) W)
      (hzero : ∀ z ∈ J₀, ρ (z, c) = z) (hWA : W ⊆ A)
      (hdis : Disjoint W J₁) :
      IsPolyhedron W ∧ W ∩ D₀ = J₀ ∧ IsPLBall 2 (D₀ ∪ W) ∧
        Disjoint (D₀ ∪ W) D₁ := by
    have hW : IsPolyhedron W := by
      rw [← hρ.image_eq]
      exact (((hJ.isPolyhedron.prod (isHPolytope_singleton a).isPolyhedron).prod
        isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
          hρ.isPiecewiseAffineOn hρ.bijOn.injOn)
    have hWD : W ∩ D₀ = J₀ := by
      apply Subset.antisymm
      · exact fun z hz => ⟨(hWA hz.1).1, hz.2.2⟩
      · intro z hz
        exact ⟨hzero z hz ▸ hρ.bijOn.mapsTo ⟨hz, le_rfl, hcd.le⟩, hJP hz.1, hz.2⟩
    obtain ⟨q, hq, -, -⟩ := hr₀.exists_isPLHomeomorphOn_union_collar hcd
      (by rwa [hb₀]) (by simpa only [hb₀] using hzero) (by rwa [hb₀])
    refine ⟨hW, hWD, ⟨q, hq⟩, disjoint_left.mpr ?_⟩
    intro z hz hz₁
    rcases hz with hz | hz
    · exact hab.ne (hz.2.symm.trans hz₁.2)
    · exact disjoint_left.mp hdis hz ⟨(hWA hz).1, hz₁.2⟩
  obtain ⟨hW₀, hmeet₀, hcap₀, hcapdis₀⟩ := hcap hρ₀ hzero₀ hW₀A hdis₀
  obtain ⟨hW₁, hmeet₁, hcap₁, hcapdis₁⟩ := hcap hρ₁ hzero₁ hW₁A hdis₁
  let g := ρ₁ ∘ Function.invFunOn ρ₀ (J₀ ×ˢ Icc c d)
  have hg : IsPLHomeomorphOn g W₀ W₁ := hρ₀.symm.trans hρ₁
  have hgfix : EqOn g id J₀ := by
    intro z hz
    have hi := hρ₀.bijOn.invOn_invFunOn.1 (show (z, c) ∈ J₀ ×ˢ Icc c d from
      ⟨hz, le_rfl, hcd.le⟩)
    rw [hzero₀ z hz] at hi
    change ρ₁ (Function.invFunOn ρ₀ (J₀ ×ˢ Icc c d) z) = z
    rw [hi, hzero₁ z hz]
  have hsurj : SurjOn id (D₀ ∩ W₀) (D₀ ∩ W₁) := by
    intro z hz
    have hzJ := hmeet₁.subset ⟨hz.2, hz.1⟩
    exact ⟨z, ⟨hz.1, (hmeet₀.symm.subset hzJ).1⟩, rfl⟩
  obtain ⟨G, hG, hGbase, hGside⟩ := exists_isPLHomeomorphOn_union hD₀.isPolyhedron hW₀
    hD₀.isPolyhedron.isPLHomeomorphOn_id hg
    (fun z hz => (hgfix (hmeet₀.subset ⟨hz.2, hz.1⟩)).symm) hsurj
  have hcap₀S := union_subset hD₀S (hW₀A.trans hAS)
  have hcap₁S := union_subset hD₀S (hW₁A.trans hAS)
  obtain ⟨F, hF, hFG, hFD₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    hS hS hcap₀ hcap₀S hD₁ hD₁S hcapdis₀ hD₁ hD₁S hcapdis₁ hG hcap₁S
  have hFbase : EqOn F id D₀ :=
    (hFG.mono subset_union_left).trans hGbase
  have hFD₀ : F '' D₀ = D₀ := hFbase.image_eq.trans (image_id _)
  have hdiff : S \ (D₀ ∪ D₁) = J ×ˢ Ioo a b := by
    ext z
    constructor
    · rintro ⟨hz | hz, hn⟩
      · rcases hz with ⟨hzP, hza | hzb⟩
        · exact (hn (Or.inl ⟨hzP, hza⟩)).elim
        · exact (hn (Or.inr ⟨hzP, hzb⟩)).elim
      · exact ⟨hz.1, lt_of_le_of_ne hz.2.1
          (fun h => hn (Or.inl ⟨hJP hz.1, h.symm⟩)),
          lt_of_le_of_ne hz.2.2 (fun h => hn (Or.inr ⟨hJP hz.1, h⟩))⟩
    · intro hz
      refine ⟨Or.inr ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, ?_⟩
      rintro (hz₀ | hz₁)
      · exact hz.2.1.ne' hz₀.2
      · exact hz.2.2.ne hz₁.2
  have hcl : closure (S \ (D₀ ∪ D₁)) = A := by
    rw [hdiff, closure_prod_eq, hJ.isPolyhedron.isClosed.closure_eq, closure_Ioo hab.ne]
  have hFA : F '' A = A := by
    have hC := image_closure_of_isCompact (hcl.symm ▸ hA.isCompact)
      (hF.isPiecewiseAffineOn.continuousOn.mono (hcl ▸ hAS))
    rw [hcl, hF.bijOn.injOn.image_sdiff_subset (union_subset hD₀S hD₁S),
      hF.image_eq, image_union, hFD₀, hFD₁, hcl] at hC
    exact hC
  have htop : A ∩ D₁ = J₁ := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2.2⟩
    · intro hz
      exact ⟨⟨hz.1, hz.2.symm ▸ ⟨hab.le, le_rfl⟩⟩, hJP hz.1, hz.2⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · simpa only [hFA] using hF.restrict hA hAS
  · apply hFbase.mono
    intro z hz
    exact ⟨hJP hz.1, hz.2⟩
  · change F '' J₁ = J₁
    rw [← htop, hF.bijOn.injOn.image_inter hAS hD₁S, hFA, hFD₁]
  · intro z hz t ht
    have hzt : (z, t) ∈ J₀ ×ˢ Icc c d := ⟨hz, ht⟩
    have hw := hρ₀.bijOn.mapsTo hzt
    rw [hFG (Or.inr hw), hGside hw]
    exact congrArg ρ₁ (hρ₀.bijOn.invOn_invFunOn.1 hzt)

end DifferentialGeometry.Topology.PiecewiseLinear
