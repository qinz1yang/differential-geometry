import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredGluing

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

namespace CollaredGluing

variable {G : CollaredGluing I X ι}

theorem block_eq [IsManifold I 1 X] (i : ι) :
    (G.toBoundaryGluing).block i = (G.left i).carrier ∪ (G.right i).carrier := rfl

theorem mem_block_iff [IsManifold I 1 X] {i : ι} {x : X} :
    x ∈ (G.toBoundaryGluing).block i ↔ x ∈ (G.left i).carrier ∨ x ∈ (G.right i).carrier :=
  Iff.rfl

theorem isOpen_quotientMk_image_of_disjoint_blocks [IsManifold I 1 X] {U : Set X}
    (hU : IsOpen U) (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) :
    IsOpen (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' U) := by
  have h := Topology.isOpen_quotient_mk_image_of_saturated (r := G.toBoundaryGluing.setoid)
    (W := U) ?_ hU
  · convert h using 2
    rfl
  · intro x y hxy
    constructor
    · intro hx
      rcases hxy with rfl | ⟨i, hxbl, hy⟩
      · exact hx
      · exact ((Set.disjoint_left.mp (hdisj i)) hx hxbl).elim
    · intro hy
      rcases hxy with rfl | ⟨i, hxbl, hy'⟩
      · exact hy
      · have hybl : y ∈ (G.toBoundaryGluing).block i :=
          hy'.symm ▸ (G.toBoundaryGluing).flip_mem_block hxbl
        exact ((Set.disjoint_left.mp (hdisj i)) hy hybl).elim

theorem injOn_quotientMk_of_disjoint_blocks [IsManifold I 1 X] {U : Set X}
    (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) :
    InjOn (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)) U := by
  intro x hx y hy hxy
  refine (G.toBoundaryGluing).eq_of_rel_of_notMem (fun i hi => ?_)
    ((Quotient.eq'' (s₁ := G.toBoundaryGluing.setoid)).mp hxy)
  exact (Set.disjoint_left.mp (hdisj i)) hx hi

theorem isOpenEmbedding_quotientMk_of_disjoint_blocks [IsManifold I 1 X] {U : Set X}
    (hU : IsOpen U) (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) :
    IsOpenEmbedding fun x : U => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact (continuous_quotient_mk' (s := G.toBoundaryGluing.setoid)).comp continuous_subtype_val
  · intro x y hxy
    exact Subtype.ext (G.injOn_quotientMk_of_disjoint_blocks hdisj x.2 y.2 hxy)
  · intro V hV
    have hV' : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val V hV
    have hdisj' : ∀ i, Disjoint (Subtype.val '' V) ((G.toBoundaryGluing).block i) := fun i =>
      Disjoint.mono_left (by rintro _ ⟨v, -, rfl⟩; exact v.2) (hdisj i)
    have himg : (fun x : U => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X)) '' V
        = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' (Subtype.val '' V) :=
      Set.image_comp _ _ _
    rw [himg]
    exact G.isOpen_quotientMk_image_of_disjoint_blocks hV' hdisj'

theorem range_quotientMk_subtype [IsManifold I 1 X] {U : Set X} :
    Set.range (fun x : U => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X))
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' U := by
  have hfun : (fun x : U => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X))
      = (fun x : X => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x) ∘ Subtype.val := rfl
  rw [hfun, Set.range_comp, Subtype.range_val]

noncomputable def ungluedEmbedding [IsManifold I 1 X] {U : Set X} (hU : IsOpen U)
    (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥U) :
    OpenPartialHomeomorph U (Quotient G.toBoundaryGluing.setoid) := by
  letI := hne
  exact (G.isOpenEmbedding_quotientMk_of_disjoint_blocks hU hdisj).toOpenPartialHomeomorph
    (fun x : U => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X))

theorem ungluedEmbedding_source [IsManifold I 1 X] {U : Set X} (hU : IsOpen U)
    (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥U) :
    (G.ungluedEmbedding hU hdisj hne).source = univ := by
  rw [ungluedEmbedding]
  exact IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

theorem ungluedEmbedding_target [IsManifold I 1 X] {U : Set X} (hU : IsOpen U)
    (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥U) :
    (G.ungluedEmbedding hU hdisj hne).target
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' U := by
  rw [ungluedEmbedding, IsOpenEmbedding.toOpenPartialHomeomorph_target,
    G.range_quotientMk_subtype (U := U)]

theorem ungluedEmbedding_apply [IsManifold I 1 X] {U : Set X} (hU : IsOpen U)
    (hdisj : ∀ i, Disjoint U ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥U) (x : U) :
    G.ungluedEmbedding hU hdisj hne x
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X) := by
  rw [ungluedEmbedding]
  exact congrFun (IsOpenEmbedding.toOpenPartialHomeomorph_apply _ _) x

noncomputable def ungluedChart [IsManifold I 1 X] (f : OpenPartialHomeomorph X H)
    (hdisj : ∀ i, Disjoint f.source ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥f.source) :
    OpenPartialHomeomorph (Quotient G.toBoundaryGluing.setoid) H :=
  (G.ungluedEmbedding f.open_source hdisj hne).symm.trans
    (f.subtypeRestr (s := (⟨f.source, f.open_source⟩ : TopologicalSpace.Opens X)) hne)

theorem ungluedChart_source [IsManifold I 1 X] (f : OpenPartialHomeomorph X H)
    (hdisj : ∀ i, Disjoint f.source ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥f.source) :
    (G.ungluedChart f hdisj hne).source
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' f.source := by
  rw [ungluedChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    G.ungluedEmbedding_target f.open_source hdisj hne,
    OpenPartialHomeomorph.subtypeRestr_source]
  ext q
  constructor
  · intro hq
    exact hq.1
  · intro hq
    exact ⟨hq, (G.ungluedEmbedding f.open_source hdisj hne).symm q |>.2⟩

theorem ungluedChart_target [IsManifold I 1 X] (f : OpenPartialHomeomorph X H)
    (hdisj : ∀ i, Disjoint f.source ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥f.source) :
    (G.ungluedChart f hdisj hne).target = f.target := by
  rw [ungluedChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    G.ungluedEmbedding_source f.open_source hdisj hne, Set.preimage_univ, Set.inter_univ]
  refine Set.Subset.antisymm
    (OpenPartialHomeomorph.subtypeRestr_target_subset (e := f)
      (s := (⟨f.source, f.open_source⟩ : TopologicalSpace.Opens X)) hne) ?_
  intro y hy
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target]
  exact ⟨hy, by simp [f.map_target hy]⟩

theorem ungluedChart_apply [IsManifold I 1 X] (f : OpenPartialHomeomorph X H)
    (hdisj : ∀ i, Disjoint f.source ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥f.source)
    {x : X} (hx : x ∈ f.source) :
    G.ungluedChart f hdisj hne (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x) = f x := by
  have hmk : G.ungluedEmbedding f.open_source hdisj hne ⟨x, hx⟩
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x :=
    G.ungluedEmbedding_apply f.open_source hdisj hne ⟨x, hx⟩
  rw [ungluedChart, OpenPartialHomeomorph.trans_apply, ← hmk,
    OpenPartialHomeomorph.left_inv (G.ungluedEmbedding f.open_source hdisj hne) (Set.mem_univ _),
    OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

theorem ungluedChart_symm_apply [IsManifold I 1 X] (f : OpenPartialHomeomorph X H)
    (hdisj : ∀ i, Disjoint f.source ((G.toBoundaryGluing).block i)) (hne : Nonempty ↥f.source)
    {y : H} (hy : y ∈ f.target) :
    (G.ungluedChart f hdisj hne).symm y
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (f.symm y) := by
  have hsub : f.symm y ∈ f.source := f.map_target hy
  have hmem : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (f.symm y)
      ∈ (G.ungluedChart f hdisj hne).source := by
    rw [G.ungluedChart_source f hdisj hne]
    exact ⟨f.symm y, hsub, rfl⟩
  have hy' : y = (G.ungluedChart f hdisj hne)
      (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (f.symm y)) := by
    rw [G.ungluedChart_apply f hdisj hne hsub, f.right_inv hy]
  conv_lhs => rw [hy']
  rw [OpenPartialHomeomorph.left_inv _ hmem]

theorem isClosed_iUnion_block [IsManifold I 1 X] :
    IsClosed (⋃ i, (G.toBoundaryGluing).block i) :=
  isClosed_iUnion_of_finite fun i => (G.toBoundaryGluing).isClosed_block i

theorem exists_ungluedChart [IsManifold I 1 X] {x : X}
    (hx : ∀ i, x ∉ (G.toBoundaryGluing).block i) :
    ∃ chart : OpenPartialHomeomorph (Quotient G.toBoundaryGluing.setoid) H,
      Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x ∈ chart.source ∧
        chart (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x) = chartAt H x x := by
  have hcompl : IsOpen (⋃ i, (G.toBoundaryGluing).block i)ᶜ :=
    isOpen_compl_iff.mpr G.isClosed_iUnion_block
  set U : Set X := (chartAt H x).source ∩ (⋃ i, (G.toBoundaryGluing).block i)ᶜ
  have hUopen : IsOpen U := (chartAt H x).open_source.inter hcompl
  have hxU : x ∈ U := ⟨mem_chart_source H x, by
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    exact fun h => h.elim fun i hi => hx i hi⟩
  have hsrc : ((chartAt H x).restr U).source = U := by
    rw [OpenPartialHomeomorph.restr_source, hUopen.interior_eq, Set.inter_eq_right]
    exact Set.inter_subset_left
  have hdisj : ∀ i, Disjoint ((chartAt H x).restr U).source ((G.toBoundaryGluing).block i) := by
    intro i
    rw [Set.disjoint_left]
    intro y hy hyb
    rw [hsrc] at hy
    exact hy.2 (Set.mem_iUnion.mpr ⟨i, hyb⟩)
  refine ⟨G.ungluedChart ((chartAt H x).restr U) hdisj ⟨x, hsrc.symm ▸ hxU⟩, ?_, ?_⟩
  · rw [G.ungluedChart_source ((chartAt H x).restr U) hdisj ⟨x, hsrc.symm ▸ hxU⟩]
    exact ⟨x, hsrc.symm ▸ hxU, rfl⟩
  · rw [G.ungluedChart_apply ((chartAt H x).restr U) hdisj ⟨x, hsrc.symm ▸ hxU⟩
        (hsrc.symm ▸ hxU),
      OpenPartialHomeomorph.restr_apply]

def ungluedLocus [IsManifold I 1 X] : Set (Quotient G.toBoundaryGluing.setoid) :=
  Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' (⋃ i, (G.toBoundaryGluing).block i)ᶜ

theorem mem_ungluedLocus [IsManifold I 1 X] {q : Quotient G.toBoundaryGluing.setoid} :
    q ∈ G.ungluedLocus ↔ ∃ x : X, (∀ i, x ∉ (G.toBoundaryGluing).block i)
      ∧ Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x = q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_compl_iff, Set.mem_iUnion] at hx
    exact ⟨x, fun i hi => hx ⟨i, hi⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by
      rw [Set.mem_compl_iff, Set.mem_iUnion]
      exact fun h => h.elim fun i hi => hx i hi, rfl⟩

theorem isOpen_ungluedLocus [IsManifold I 1 X] : IsOpen G.ungluedLocus := by
  refine G.isOpen_quotientMk_image_of_disjoint_blocks G.isClosed_iUnion_block.isOpen_compl ?_
  intro i
  rw [Set.disjoint_left]
  intro y hy hyb
  exact hy (Set.mem_iUnion.mpr ⟨i, hyb⟩)

theorem exists_ungluedChart_of_mem_ungluedLocus [IsManifold I 1 X]
    {q : Quotient G.toBoundaryGluing.setoid} (hq : q ∈ G.ungluedLocus) :
    ∃ (chart : OpenPartialHomeomorph (Quotient G.toBoundaryGluing.setoid) H) (x : X),
      q = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x ∧
      q ∈ chart.source ∧ chart q = chartAt H x x := by
  obtain ⟨x, hx, rfl⟩ := G.mem_ungluedLocus.mp hq
  exact ⟨(G.exists_ungluedChart hx).choose, x, rfl, (G.exists_ungluedChart hx).choose_spec⟩

theorem exists_left_carrier_of_mem_right_carrier [IsManifold I 1 X] {i : ι} {x : X}
    (hx : x ∈ (G.right i).carrier) :
    ∃ z : ↥(G.left i).carrier,
      Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (z : X)
        = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x := by
  refine ⟨(G.attaching i).symm ⟨x, hx⟩, ?_⟩
  exact Quotient.sound' ((G.toBoundaryGluing).setoid.symm
    ((G.toBoundaryGluing).rel_of_mem_right hx))

theorem exists_ungluedChart_or_seamChart [IsManifold I 1 X] (x : X) :
    (∃ chart : OpenPartialHomeomorph (Quotient G.toBoundaryGluing.setoid) H,
      Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x ∈ chart.source ∧
        chart (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x) = chartAt H x x)
      ∨ ∃ (i : ι) (z : ↥(G.left i).carrier),
          G.seamChart i (z, ⟨0, neg_nonpos.mpr (G.ε_pos i).le, (G.ε_pos i).le⟩)
            = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x := by
  by_cases hx : ∃ i, x ∈ (G.toBoundaryGluing).block i
  · right
    obtain ⟨i, hx | hx⟩ := hx
    · exact ⟨i, ⟨x, hx⟩, G.seamChart_zero i ⟨x, hx⟩⟩
    · obtain ⟨z, hz⟩ := G.exists_left_carrier_of_mem_right_carrier hx
      exact ⟨i, z, (G.seamChart_zero i z).trans hz⟩
  · exact Or.inl (G.exists_ungluedChart fun i hi => hx ⟨i, hi⟩)

theorem range_seamChart [IsManifold I 1 X] (i : ι) :
    Set.range (G.seamChart i) = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ''
      (range (G.collarLeft i) ∪ range (G.collarRight i)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro q ⟨p, rfl⟩
    obtain ⟨z, t⟩ := p
    by_cases ht : 0 ≤ (t : ℝ)
    · refine ⟨G.collarRight i (G.attaching i z, ⟨(t : ℝ), ht, t.2.2⟩),
        Or.inr ⟨(G.attaching i z, ⟨(t : ℝ), ht, t.2.2⟩), rfl⟩, ?_⟩
      exact (G.seamChart_apply_of_nonneg i (z, t) ht).symm
    · have ht' : (t : ℝ) ≤ 0 := le_of_lt (lt_of_not_ge ht)
      have hb : (0 : ℝ) ≤ -(t : ℝ) := by linarith [ht']
      have hb' : -(t : ℝ) ≤ G.ε i := by linarith [t.2.1]
      refine ⟨G.collarLeft i (z, ⟨-(t : ℝ), hb, hb'⟩),
        Or.inl ⟨(z, ⟨-(t : ℝ), hb, hb'⟩), rfl⟩, ?_⟩
      exact (G.seamChart_apply_of_nonpos i (z, t) ht').symm
  · rintro q ⟨x, hx | hx, rfl⟩
    · obtain ⟨⟨z, t⟩, rfl⟩ := hx
      have hb : -(G.ε i) ≤ -(t : ℝ) := by linarith [t.2.2]
      have hb' : -(t : ℝ) ≤ G.ε i := by linarith [t.2.1]
      refine ⟨(z, ⟨-(t : ℝ), hb, hb'⟩), ?_⟩
      rw [G.seamChart_apply_of_nonpos i _ (by linarith [t.2.1])]
      refine congrArg (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)) ?_
      refine congrArg (G.collarLeft i) (Prod.ext rfl (Subtype.ext ?_))
      simp
    · obtain ⟨⟨w, t⟩, rfl⟩ := hx
      refine ⟨((G.attaching i).symm w,
        ⟨(t : ℝ), by linarith [t.2.1, (G.ε_pos i).le], t.2.2⟩), ?_⟩
      rw [G.seamChart_apply_of_nonneg i _ t.2.1]
      rw [Homeomorph.apply_symm_apply]

theorem contMDiffOn_ungluedChart_trans_ungluedChart [IsManifold I ∞ X]
    {f f' : OpenPartialHomeomorph X H} (hf : f ∈ atlas H X) (hf' : f' ∈ atlas H X)
    (hd : ∀ i, Disjoint f.source ((G.toBoundaryGluing).block i))
    (hd' : ∀ i, Disjoint f'.source ((G.toBoundaryGluing).block i))
    (hne : Nonempty ↥f.source) (hne' : Nonempty ↥f'.source) :
    ContMDiffOn I I ∞
      ((G.ungluedChart f hd hne).symm.trans (G.ungluedChart f' hd' hne'))
      ((G.ungluedChart f hd hne).symm.trans (G.ungluedChart f' hd' hne')).source := by
  have hmem : f.symm.trans f' ∈ contDiffGroupoid ∞ I :=
    StructureGroupoid.compatible_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf)
      (IsManifold.subset_maximalAtlas hf')
  have htrans := contMDiffOn_of_mem_contDiffGroupoid hmem
  have key : ∀ q : H, q ∈ ((G.ungluedChart f hd hne).symm.trans
      (G.ungluedChart f' hd' hne')).source →
      q ∈ (f.symm.trans f').source ∧
      (G.ungluedChart f' hd' hne') ((G.ungluedChart f hd hne).symm q)
        = (f.symm.trans f') q := by
    intro q hq
    rw [OpenPartialHomeomorph.trans_source] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [OpenPartialHomeomorph.symm_source, G.ungluedChart_target f hd hne] at hq1
    rw [G.ungluedChart_source f' hd' hne'] at hq2
    obtain ⟨x', hx', hx'q⟩ := hq2
    have hsymm := G.ungluedChart_symm_apply f hd hne hq1
    have hmk : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (f.symm q)
        = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x' :=
      hsymm.symm.trans hx'q.symm
    have hrel : (G.toBoundaryGluing).rel (f.symm q) x' :=
      (Quotient.eq'' (s₁ := G.toBoundaryGluing.setoid)).mp hmk
    have hnot : ∀ i, f.symm q ∉ (G.toBoundaryGluing).block i := fun i hi =>
      (Set.disjoint_left.mp (hd i)) (f.map_target hq1) hi
    have heq : f.symm q = x' := (G.toBoundaryGluing).eq_of_rel_of_notMem hnot hrel
    have hx'' : f.symm q ∈ f'.source := by
      rw [heq]; exact hx'
    refine ⟨⟨hq1, hx''⟩, ?_⟩
    rw [OpenPartialHomeomorph.trans_apply, hsymm, hmk,
      G.ungluedChart_apply f' hd' hne' hx']
    exact congrArg f' heq.symm
  exact (htrans.mono fun q hq => (key q hq).1).congr fun q hq => (key q hq).2

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem unitIntervalCollaredGluing_notMem_block (i : Fin 1) :
    (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1)
      ∉ unitIntervalCollaredGluing.toBoundaryGluing.block i := by
  intro hmem
  have hb : (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) = {⊥, ⊤} := boundary_Icc
  have h1 : (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1)
      ∈ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) := by
    rw [← hb]
    exact unitIntervalCollaredGluing.block_subset_boundary i hmem
  have hbot : (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) ≠ ⊥ := by
    intro h
    have h2 := congrArg (Subtype.val : Icc (0 : ℝ) 1 → ℝ) h
    norm_num at h2
  have htop : (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) ≠ ⊤ := by
    intro h
    have h2 := congrArg (Subtype.val : Icc (0 : ℝ) 1 → ℝ) h
    norm_num at h2
  rcases h1 with h1 | h1
  · exact hbot h1
  · exact htop h1

theorem unitIntervalCollaredGluing_ungluedLocus_nonempty :
    unitIntervalCollaredGluing.ungluedLocus.Nonempty :=
  ⟨_, unitIntervalCollaredGluing.mem_ungluedLocus.mpr
    ⟨_, unitIntervalCollaredGluing_notMem_block, rfl⟩⟩

theorem unitIntervalCollaredGluing_exists_ungluedChart :
    ∃ chart : OpenPartialHomeomorph
        (Quotient unitIntervalCollaredGluing.toBoundaryGluing.setoid) (EuclideanHalfSpace 1),
      Quotient.mk'' (s₁ := unitIntervalCollaredGluing.toBoundaryGluing.setoid)
          (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) ∈ chart.source ∧
        chart (Quotient.mk'' (s₁ := unitIntervalCollaredGluing.toBoundaryGluing.setoid)
          (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1))
          = chartAt (EuclideanHalfSpace 1) (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1)
            (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :=
  unitIntervalCollaredGluing.exists_ungluedChart unitIntervalCollaredGluing_notMem_block

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
