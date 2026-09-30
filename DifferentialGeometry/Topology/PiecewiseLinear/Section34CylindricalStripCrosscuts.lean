import DifferentialGeometry.Topology.PiecewiseLinear.Section34CircleCrosscutDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurveHeightSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCurveLevels

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.mem_image_strip_iff_height
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    {x : E × ℝ} (hx : x ∈ P ×ˢ Icc (0 : ℝ) 1) :
    f x ∈ f '' (P ×ˢ Icc a b) ↔ x.2 ∈ Icc a b := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyfull : y ∈ P ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hy.1, ha.le.trans hy.2.1, hy.2.2.trans hb.le⟩
    rcases hf.eq_or_endpoints y hyfull x hx hyx with h | h | h
    · exact h ▸ hy.2
    · exfalso
      linarith [hy.2.1, h.1]
    · exfalso
      linarith [hy.2.2, h.1]
  · intro ht
    exact ⟨x, ⟨hx.1, ht⟩, rfl⟩

theorem IsCylindricalDiagram.inter_closure_compl_strip_subset_rims
    [FiniteDimensional ℝ E]
    {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsCompact P)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    (f '' (P ×ˢ Icc a b)) ∩ closure (S \ f '' (P ×ˢ Icc a b)) ⊆
      f '' (P ×ˢ ({a, b} : Set ℝ)) := by
  let R : Set (E × ℝ) := P ×ˢ (Icc (0 : ℝ) a ∪ Icc b 1)
  have hR : IsCompact R := hP.prod (isCompact_Icc.union isCompact_Icc)
  have hRfull : R ⊆ P ×ˢ Icc (0 : ℝ) 1 := by
    rintro x ⟨hxP, hx | hx⟩
    · exact ⟨hxP, hx.1, hx.2.trans (hab.le.trans hb.le)⟩
    · exact ⟨hxP, (ha.le.trans hab.le).trans hx.1, hx.2⟩
  have hclosed : IsClosed (f '' R) :=
    (hR.image_of_continuousOn (hf.isPiecewiseAffineOn.continuousOn.mono hRfull)).isClosed
  have hcompl : S \ f '' (P ×ˢ Icc a b) ⊆ f '' R := by
    rintro y ⟨hyS, hyn⟩
    obtain ⟨x, hx, rfl⟩ := hf.image_eq.symm.subset hyS
    by_cases hxa : x.2 ≤ a
    · exact ⟨x, ⟨hx.1, Or.inl ⟨hx.2.1, hxa⟩⟩, rfl⟩
    · have hxb : b ≤ x.2 := by
        by_contra h
        exact hyn ⟨x, ⟨hx.1, (lt_of_not_ge hxa).le, (lt_of_not_ge h).le⟩, rfl⟩
      exact ⟨x, ⟨hx.1, Or.inr ⟨hxb, hx.2.2⟩⟩, rfl⟩
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  obtain ⟨z, hz, hzx⟩ := closure_minimal hcompl hclosed hy
  have hxfull : x ∈ P ×ˢ Icc (0 : ℝ) 1 :=
    ⟨hx.1, ha.le.trans hx.2.1, hx.2.2.trans hb.le⟩
  have hzx' : z = x := by
    rcases hf.eq_or_endpoints z (hRfull hz) x hxfull hzx with h | h | h
    · exact h
    · exfalso
      linarith [hx.2.2, h.2]
    · exfalso
      linarith [hx.2.1, h.2]
  subst z
  refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
  rcases hz.2 with hz | hz
  · exact Or.inl (le_antisymm hz.2 hx.2.1)
  · exact Or.inr (le_antisymm hx.2.2 hz.1)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.exists_finite_crosscut_partition_of_regular_strip
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite L.faces]
    {c a b d : ℝ} (hc : 0 ≤ c) (hca : c < a) (hab : a < b) (hbd : b < d) (hd : d ≤ 1)
    (hL : L.space = (P ×ˢ Icc c d) ∩ f ⁻¹' J)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (ha : a ∉ Prod.snd '' L.vertices) (hb : b ∉ Prod.snd '' L.vertices)
    (hmeet : (J ∩ f '' (P ×ˢ ({a, b} : Set ℝ))).Nonempty) :
    ∃ C : Set (Set F), C.Finite ∧ C.PairwiseDisjoint id ∧
      ⋃₀ C = J ∩ f '' (P ×ˢ Icc a b) ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → F,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ f '' (P ×ˢ ({a, b} : Set ℝ)) := by
  let D : Set F := f '' (P ×ˢ Icc a b)
  let W : Set F := f '' (P ×ˢ ({a, b} : Set ℝ))
  have ha0 : 0 < a := hc.trans_lt hca
  have hb1 : b < 1 := hbd.trans_le hd
  have hfstrip := hf.isPLHomeomorphOn_strip hP ha0.le hb1.le (Or.inl ha0)
  have hprod : IsPolyhedron (P ×ˢ Icc a b) := hP.prod isHPolytope_Icc.isPolyhedron
  have hD : IsPolyhedron D := hprod.image_of_isPiecewiseAffineOn
    hfstrip.isPiecewiseAffineOn hfstrip.bijOn.injOn
  have hLfull : L.space ⊆ P ×ˢ Icc (0 : ℝ) 1 := by
    rw [hL]
    exact fun _ h => ⟨h.1.1, hc.trans h.1.2.1, h.1.2.2.trans hd⟩
  have hLJ : MapsTo f L.space J := by rw [hL]; exact fun _ h => h.2
  have hinside : MapsTo f (L.space ∩ {x | a < x.2 ∧ x.2 < b}) (J ∩ (D \ W)) := by
    rintro x ⟨hxL, hxa, hxb⟩
    refine ⟨hLJ hxL, ⟨x, ⟨(hLfull hxL).1, hxa.le, hxb.le⟩, rfl⟩, ?_⟩
    rintro ⟨y, hy, hyx⟩
    have hyab : y ∈ P ×ˢ Icc a b := by
      rcases hy.2 with h | h
      · exact ⟨hy.1, by rw [h]; exact ⟨le_rfl, hab.le⟩⟩
      · exact ⟨hy.1, by rw [h]; exact ⟨hab.le, le_rfl⟩⟩
    have hyx' := hfstrip.bijOn.injOn hyab ⟨(hLfull hxL).1, hxa.le, hxb.le⟩ hyx
    have ht : x.2 = a ∨ x.2 = b := hyx' ▸ hy.2
    exact ht.elim hxa.ne' hxb.ne
  have houta : MapsTo f (L.space ∩ {x | x.2 < a}) (J \ D) := by
    rintro x ⟨hxL, hxa⟩
    exact ⟨hLJ hxL, fun h => hxa.not_ge
      ((hf.mem_image_strip_iff_height ha0 hb1 (hLfull hxL)).mp h).1⟩
  have houtb : MapsTo f (L.space ∩ {x | b < x.2}) (J \ D) := by
    rintro x ⟨hxL, hxb⟩
    exact ⟨hLJ hxL, fun h => hxb.not_ge
      ((hf.mem_image_strip_iff_height ha0 hb1 (hLfull hxL)).mp h).2⟩
  have hsides : ∀ y ∈ J ∩ W,
      y ∈ closure (J ∩ (D \ W)) ∧ y ∈ closure (J \ D) := by
    rintro y ⟨hyJ, x, ⟨hxP, hxt⟩, rfl⟩
    have hxL : x ∈ L.space := by
      rw [hL]
      refine ⟨⟨hxP, ?_, ?_⟩, hyJ⟩
      · rcases hxt with h | h <;> rw [h] <;> linarith
      · rcases hxt with h | h <;> rw [h] <;> linarith
    have hcont := hf.isPiecewiseAffineOn.continuousOn (x := x) (hLfull hxL)
    rcases hxt with hxa | hxb
    · obtain ⟨hlow, hhigh⟩ := mem_closure_height_sides_of_notMem_vertex_image L hcard
        (LinearMap.snd ℝ E ℝ) ha ⟨hxL, hxa⟩
      have hopen : IsOpen {z : E × ℝ | z.2 < b} := isOpen_lt continuous_snd continuous_const
      have hin := hopen.closure_inter ⟨hhigh, by change x.2 < b; rw [hxa]; exact hab⟩
      refine ⟨?_, (hcont.mono (inter_subset_left.trans hLfull)).mem_closure hlow houta⟩
      apply (hcont.mono (show L.space ∩ {z | a < z.2 ∧ z.2 < b} ⊆ _ from
        inter_subset_left.trans hLfull)).mem_closure _ hinside
      exact closure_mono (by rintro z ⟨⟨hzL, hza⟩, hzb⟩; exact ⟨hzL, hza, hzb⟩) hin
    · obtain ⟨hlow, hhigh⟩ := mem_closure_height_sides_of_notMem_vertex_image L hcard
        (LinearMap.snd ℝ E ℝ) hb ⟨hxL, hxb⟩
      have hopen : IsOpen {z : E × ℝ | a < z.2} := isOpen_lt continuous_const continuous_snd
      have hin := hopen.closure_inter ⟨hlow, by change a < x.2; rw [hxb]; exact hab⟩
      refine ⟨?_, (hcont.mono (inter_subset_left.trans hLfull)).mem_closure hhigh houtb⟩
      apply (hcont.mono (show L.space ∩ {z | a < z.2 ∧ z.2 < b} ⊆ _ from
        inter_subset_left.trans hLfull)).mem_closure _ hinside
      exact closure_mono (by rintro z ⟨⟨hzL, hzb⟩, hza⟩; exact ⟨hzL, hza, hzb⟩) hin
  have hproper : J ∩ D ⊂ J := by
    refine ⟨inter_subset_left, ?_⟩
    intro hsub
    obtain ⟨y, hy⟩ := hmeet
    have hyout := (hsides y hy).2
    have hempty : J \ D = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
      hx.2 (hsub hx.1).2
    rw [hempty, closure_empty] at hyout
    exact hyout
  exact hJ.exists_finite_crosscut_partition_in_region hJS hD
    (hf.inter_closure_compl_strip_subset_rims hP.isCompact ha0 hab hb1) hproper
    (fun y hy => (hsides y hy).1) (fun y hy => (hsides y hy).2)

theorem IsCylindricalDiagram.exists_source_crosscut_partition_of_regular_strip
    {f : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (L : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite L.faces]
    {c a b d : ℝ} (hc : 0 ≤ c) (hca : c < a) (hab : a < b) (hbd : b < d) (hd : d ≤ 1)
    (hL : L.space = (P ×ˢ Icc c d) ∩ f ⁻¹' J)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (ha : a ∉ Prod.snd '' L.vertices) (hb : b ∉ Prod.snd '' L.vertices)
    (hmeet : (J ∩ f '' (P ×ˢ ({a, b} : Set ℝ))).Nonempty) :
    ∃ C : Set (Set (E × ℝ)), C.Finite ∧ C.PairwiseDisjoint id ∧
      ⋃₀ C = (P ×ˢ Icc a b) ∩ f ⁻¹' J ∧
      ∀ A ∈ C, ∃ q : (Fin 2 → ℝ) → E × ℝ,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
        q '' stdSimplexBoundary 1 = A ∩ (P ×ˢ ({a, b} : Set ℝ)) := by
  obtain ⟨C, hCfin, hCdis, hcover, hC⟩ :=
    hf.exists_finite_crosscut_partition_of_regular_strip hP hJ hJS L hc hca hab hbd hd
      hL hcard ha hb hmeet
  have ha0 : 0 < a := hc.trans_lt hca
  have hb1 : b < 1 := hbd.trans_le hd
  have hstrip := hf.isPLHomeomorphOn_strip hP ha0.le hb1.le (Or.inl ha0)
  let g := Function.invFunOn f (P ×ˢ Icc a b)
  have hg : IsPLHomeomorphOn g (f '' (P ×ˢ Icc a b)) (P ×ˢ Icc a b) := hstrip.symm
  have hAC : ∀ A ∈ C, A ⊆ J ∩ f '' (P ×ˢ Icc a b) :=
    fun A hA x hx => hcover.subset (mem_sUnion.mpr ⟨A, hA, hx⟩)
  have hends : P ×ˢ ({a, b} : Set ℝ) ⊆ P ×ˢ Icc a b := by
    rintro x ⟨hxP, hx | hx⟩
    · exact ⟨hxP, by rw [hx]; exact ⟨le_rfl, hab.le⟩⟩
    · exact ⟨hxP, by rw [hx]; exact ⟨hab.le, le_rfl⟩⟩
  have hgends : g '' (f '' (P ×ˢ ({a, b} : Set ℝ))) = P ×ˢ ({a, b} : Set ℝ) := by
    rw [image_image]
    calc
      (g ∘ f) '' (P ×ˢ ({a, b} : Set ℝ)) = id '' (P ×ˢ ({a, b} : Set ℝ)) :=
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
    have hAD : A ⊆ f '' (P ×ˢ Icc a b) := (hAC A hA).trans inter_subset_right
    have hAp : IsPolyhedron A := (show IsPLBall 1 A from ⟨q, hq⟩).isPolyhedron
    refine ⟨g ∘ q, hq.trans (hg.restrict hAp hAD), ?_⟩
    rw [image_comp, hqb, hg.bijOn.injOn.image_inter hAD (image_mono hends), hgends]

end DifferentialGeometry.Topology.PiecewiseLinear
