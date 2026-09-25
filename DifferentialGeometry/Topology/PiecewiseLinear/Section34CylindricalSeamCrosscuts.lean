import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalStripCrosscuts

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.mem_image_upper_strip_iff_height
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) {a : ℝ} (ha : 0 < a)
    {x : E × ℝ} (hx : x ∈ P ×ˢ Ioc (0 : ℝ) 1) :
    f x ∈ f '' (P ×ˢ Icc a 1) ↔ a ≤ x.2 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rcases hf.eq_or_endpoints y ⟨hy.1, ha.le.trans hy.2.1, hy.2.2⟩ x
      ⟨hx.1, hx.2.1.le, hx.2.2⟩ hyx with h | h | h
    · exact h ▸ hy.2.1
    · exfalso
      linarith [hy.2.1, h.1]
    · exact (hx.2.1.ne' h.2).elim
  · intro ht
    exact ⟨x, ⟨hx.1, ht, hx.2.2⟩, rfl⟩

theorem IsCylindricalDiagram.inter_closure_compl_upper_strip_subset_rims
    [FiniteDimensional ℝ E] {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsCompact P)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (f '' (P ×ˢ Icc a 1)) ∩ closure (S \ f '' (P ×ˢ Icc a 1)) ⊆
      f '' (P ×ˢ ({a, 1} : Set ℝ)) := by
  have hclosed : IsClosed (f '' (P ×ˢ Icc 0 a)) :=
    ((hP.prod isCompact_Icc).image_of_continuousOn
      (hf.isPiecewiseAffineOn.continuousOn.mono
        (prod_mono_right (Icc_subset_Icc le_rfl ha.2.le)))).isClosed
  have hcompl : S \ f '' (P ×ˢ Icc a 1) ⊆ f '' (P ×ˢ Icc 0 a) := by
    rintro x ⟨hxS, hxn⟩
    exact ((hf.image_strip_union ⟨ha.1.le, ha.2.le⟩).symm.subset hxS).resolve_right hxn
  rintro x ⟨hxD, hxcl⟩
  have hxR := closure_minimal hcompl hclosed hxcl
  have hxends := (hf.image_strip_inter ha).subset ⟨hxR, hxD⟩
  rcases hxends with h | h
  · rw [← hf.image_top_eq_bottom] at h
    exact image_mono (show P ×ˢ ({1} : Set ℝ) ⊆ P ×ˢ {a, 1} from
      fun _ hz => ⟨hz.1, Or.inr hz.2⟩) h
  · exact image_mono (show P ×ˢ ({a} : Set ℝ) ⊆ P ×ˢ {a, 1} from
      fun _ hz => ⟨hz.1, Or.inl hz.2⟩) h

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.exists_finite_crosscut_partition_of_regular_upper_strip
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite L.faces]
    {c a d : ℝ} (hc : 0 ≤ c) (hca : c < a) (had : a < d) (hd : d ≤ 1)
    (hL : L.space = (P ×ˢ Icc c d) ∩ f ⁻¹' J)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) (ha : a ∉ Prod.snd '' L.vertices)
    (hseam : ∀ y ∈ J ∩ f '' (P ×ˢ ({1} : Set ℝ)),
      y ∈ closure (J ∩ f '' (P ×ˢ Ioo a 1)) ∧
      y ∈ closure (J \ f '' (P ×ˢ Icc a 1)))
    (hmeet : (J ∩ f '' (P ×ˢ ({1} : Set ℝ))).Nonempty) :
    ∃ C : Set (Set F), C.Finite ∧ C.PairwiseDisjoint id ∧
      ⋃₀ C = J ∩ f '' (P ×ˢ Icc a 1) ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → F,
        IsPLHomeomorphOn q (stdSimplex ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ f '' (P ×ˢ ({a, 1} : Set ℝ)) := by
  let D : Set F := f '' (P ×ˢ Icc a 1)
  let W : Set F := f '' (P ×ˢ ({a, 1} : Set ℝ))
  have ha0 : 0 < a := hc.trans_lt hca
  have ha1 : a < 1 := had.trans_le hd
  have hfstrip := hf.isPLHomeomorphOn_strip hP ha0.le le_rfl (Or.inl ha0)
  have hprod : IsPolyhedron (P ×ˢ Icc a 1) := hP.prod isHPolytope_Icc.isPolyhedron
  have hD : IsPolyhedron D := hprod.image_of_isPiecewiseAffineOn
    hfstrip.isPiecewiseAffineOn hfstrip.bijOn.injOn
  have hLfull : L.space ⊆ P ×ˢ Icc (0 : ℝ) 1 := by
    rw [hL]
    exact fun _ h => ⟨h.1.1, hc.trans h.1.2.1, h.1.2.2.trans hd⟩
  have hLJ : MapsTo f L.space J := by rw [hL]; exact fun _ h => h.2
  have hopenstrip : f '' (P ×ˢ Ioo a 1) ⊆ D \ W := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨x, ⟨hx.1, hx.2.1.le, hx.2.2.le⟩, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    have hzD : z ∈ P ×ˢ Icc a 1 := by
      rcases hz.2 with h | h
      · exact ⟨hz.1, by rw [h]; exact ⟨le_rfl, ha1.le⟩⟩
      · exact ⟨hz.1, by rw [h]; exact ⟨ha1.le, le_rfl⟩⟩
    have hzx' := hfstrip.bijOn.injOn hzD ⟨hx.1, hx.2.1.le, hx.2.2.le⟩ hzx
    have ht : x.2 = a ∨ x.2 = 1 := hzx' ▸ hz.2
    exact ht.elim hx.2.1.ne' hx.2.2.ne
  have hinside : MapsTo f (L.space ∩ {x | a < x.2 ∧ x.2 < 1}) (J ∩ (D \ W)) := by
    rintro x ⟨hxL, hxa, hx1⟩
    exact ⟨hLJ hxL, hopenstrip ⟨x, ⟨(hLfull hxL).1, hxa, hx1⟩, rfl⟩⟩
  have houtside : MapsTo f (L.space ∩ {x | 0 < x.2 ∧ x.2 < a}) (J \ D) := by
    rintro x ⟨hxL, hx0, hxa⟩
    exact ⟨hLJ hxL, fun h => hxa.not_ge
      ((hf.mem_image_upper_strip_iff_height ha0
        ⟨(hLfull hxL).1, hx0, (hLfull hxL).2.2⟩).mp h)⟩
  have hsides : ∀ y ∈ J ∩ W,
      y ∈ closure (J ∩ (D \ W)) ∧ y ∈ closure (J \ D) := by
    rintro y ⟨hyJ, x, ⟨hxP, hxt⟩, rfl⟩
    rcases hxt with hxa | hx1
    · have hxL : x ∈ L.space := by
        rw [hL]
        exact ⟨⟨hxP, by rw [hxa]; exact ⟨hca.le, had.le⟩⟩, hyJ⟩
      obtain ⟨hlow, hhigh⟩ := mem_closure_height_sides_of_notMem_vertex_image L hcard
        (LinearMap.snd ℝ E ℝ) ha ⟨hxL, hxa⟩
      have hcont := hf.isPiecewiseAffineOn.continuousOn (x := x) (hLfull hxL)
      have hopenhi : IsOpen {z : E × ℝ | z.2 < 1} :=
        isOpen_lt continuous_snd continuous_const
      have hopenlo : IsOpen {z : E × ℝ | 0 < z.2} :=
        isOpen_lt continuous_const continuous_snd
      have hin := hopenhi.closure_inter ⟨hhigh, by change x.2 < 1; rw [hxa]; exact ha1⟩
      have hout := hopenlo.closure_inter ⟨hlow, by change 0 < x.2; rw [hxa]; exact ha0⟩
      constructor
      · apply (hcont.mono (show L.space ∩ {z | a < z.2 ∧ z.2 < 1} ⊆ _ from
          inter_subset_left.trans hLfull)).mem_closure _ hinside
        exact closure_mono (by rintro z ⟨⟨hzL, hza⟩, hz1⟩; exact ⟨hzL, hza, hz1⟩) hin
      · apply (hcont.mono (show L.space ∩ {z | 0 < z.2 ∧ z.2 < a} ⊆ _ from
          inter_subset_left.trans hLfull)).mem_closure _ houtside
        exact closure_mono (by rintro z ⟨⟨hzL, hza⟩, hz0⟩; exact ⟨hzL, hz0, hza⟩) hout
    · obtain ⟨hin, hout⟩ := hseam (f x) ⟨hyJ, x, ⟨hxP, hx1⟩, rfl⟩
      exact ⟨closure_mono (inter_subset_inter_right _ hopenstrip) hin, hout⟩
  have hproper : J ∩ D ⊂ J := by
    refine ⟨inter_subset_left, ?_⟩
    intro hsub
    obtain ⟨y, hy⟩ := hmeet
    have hyout := (hseam y hy).2
    have hempty : J \ D = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
      hx.2 (hsub hx.1).2
    rw [hempty, closure_empty] at hyout
    exact hyout
  exact hJ.exists_finite_crosscut_partition_in_region hJS hD
    (hf.inter_closure_compl_upper_strip_subset_rims hP.isCompact ⟨ha0, ha1⟩) hproper
    (fun y hy => (hsides y hy).1) (fun y hy => (hsides y hy).2)

theorem IsCylindricalDiagram.exists_source_crosscut_partition_of_regular_upper_strip
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite L.faces]
    {c a d : ℝ} (hc : 0 ≤ c) (hca : c < a) (had : a < d) (hd : d ≤ 1)
    (hL : L.space = (P ×ˢ Icc c d) ∩ f ⁻¹' J)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) (ha : a ∉ Prod.snd '' L.vertices)
    (hseam : ∀ y ∈ J ∩ f '' (P ×ˢ ({1} : Set ℝ)),
      y ∈ closure (J ∩ f '' (P ×ˢ Ioo a 1)) ∧
      y ∈ closure (J \ f '' (P ×ˢ Icc a 1)))
    (hmeet : (J ∩ f '' (P ×ˢ ({1} : Set ℝ))).Nonempty) :
    ∃ C : Set (Set (E × ℝ)), C.Finite ∧ C.PairwiseDisjoint id ∧
      ⋃₀ C = (P ×ˢ Icc a 1) ∩ f ⁻¹' J ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → E × ℝ,
        IsPLHomeomorphOn q (stdSimplex ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ (P ×ˢ ({a, 1} : Set ℝ)) := by
  obtain ⟨C, hCfin, hCdis, hcover, hC⟩ :=
    hf.exists_finite_crosscut_partition_of_regular_upper_strip hP hJ hJS L hc hca had hd
      hL hcard ha hseam hmeet
  have ha0 : 0 < a := hc.trans_lt hca
  have ha1 : a < 1 := had.trans_le hd
  have hstrip := hf.isPLHomeomorphOn_strip hP ha0.le le_rfl (Or.inl ha0)
  let g := Function.invFunOn f (P ×ˢ Icc a 1)
  have hg : IsPLHomeomorphOn g (f '' (P ×ˢ Icc a 1)) (P ×ˢ Icc a 1) := hstrip.symm
  have hAC : ∀ A ∈ C, A ⊆ J ∩ f '' (P ×ˢ Icc a 1) :=
    fun A hA x hx => hcover.subset (mem_sUnion.mpr ⟨A, hA, hx⟩)
  have hends : P ×ˢ ({a, 1} : Set ℝ) ⊆ P ×ˢ Icc a 1 := by
    rintro x ⟨hxP, hx | hx⟩
    · exact ⟨hxP, by rw [hx]; exact ⟨le_rfl, ha1.le⟩⟩
    · exact ⟨hxP, by rw [hx]; exact ⟨ha1.le, le_rfl⟩⟩
  have hgends : g '' (f '' (P ×ˢ ({a, 1} : Set ℝ))) = P ×ˢ ({a, 1} : Set ℝ) := by
    rw [image_image]
    calc
      (g ∘ f) '' (P ×ˢ ({a, 1} : Set ℝ)) = id '' (P ×ˢ ({a, 1} : Set ℝ)) :=
        image_congr fun x hx => hstrip.bijOn.invOn_invFunOn.1 (hends hx)
      _ = _ := image_id _
  refine ⟨(fun A : Set F => g '' A) '' C, hCfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz := hg.bijOn.injOn (hAC A hA hy).2 (hAC B hB hz).2 (hyx.trans hzx.symm)
    exact disjoint_left.mp (hCdis hA hB (fun h => hne (congrArg (fun T => g '' T) h)))
      hy (hyz.symm ▸ hz)
  · ext x
    constructor
    · rintro ⟨B, ⟨A, hA, rfl⟩, y, hy, rfl⟩
      have hyD := (hAC A hA hy).2
      refine ⟨hg.bijOn.mapsTo hyD, ?_⟩
      change f (g y) ∈ J
      rw [hstrip.bijOn.invOn_invFunOn.2 hyD]
      exact (hAC A hA hy).1
    · intro hx
      obtain ⟨A, hA, hfxA⟩ := mem_sUnion.mp (hcover.symm.subset
        ⟨hx.2, hstrip.bijOn.mapsTo hx.1⟩)
      exact mem_sUnion.mpr ⟨g '' A, ⟨A, hA, rfl⟩,
        ⟨f x, hfxA, hstrip.bijOn.invOn_invFunOn.1 hx.1⟩⟩
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨q, hq, hqb⟩ := hC A hA
    have hAD : A ⊆ f '' (P ×ˢ Icc a 1) := (hAC A hA).trans inter_subset_right
    have hAp : IsPolyhedron A := (show IsPLBall 1 A from ⟨q, hq⟩).isPolyhedron
    refine ⟨g ∘ q, hq.trans (hg.restrict hAp hAD), ?_⟩
    rw [image_comp, hqb, hg.bijOn.injOn.image_inter hAD (image_mono hends), hgends]

end DifferentialGeometry.Topology.PiecewiseLinear
