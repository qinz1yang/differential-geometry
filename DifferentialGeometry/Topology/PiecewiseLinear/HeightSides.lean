import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.HeightChart
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLevelPolygons

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_mem_halfSpace_or_of_closed_partition {A B : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (P : Submodule ℝ E) (ℓ : E →ₗ[ℝ] ℝ)
    (hcover : ∀ᶠ x in 𝓝 0, x ∈ A ∪ B ↔ x ∈ P)
    (hinter : ∀ᶠ x in 𝓝 0, x ∈ A ∩ B ↔ x ∈ P ∧ ℓ x = 0)
    (hclA : (0 : E) ∈ closure (A \ B)) (hclB : (0 : E) ∈ closure (B \ A)) :
    (∀ᶠ x in 𝓝 0, x ∈ A ↔ x ∈ P ∧ 0 ≤ ℓ x) ∨
      (∀ᶠ x in 𝓝 0, x ∈ A ↔ x ∈ P ∧ ℓ x ≤ 0) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcover.and hinter)
  let Cpos : Set E := ((P : Set E) ∩ Metric.ball 0 ε) ∩ {x | 0 < ℓ x}
  let Cneg : Set E := ((P : Set E) ∩ Metric.ball 0 ε) ∩ {x | ℓ x < 0}
  have hchoice {C : Set E} (hC : Convex ℝ C) (hCP : C ⊆ P) (hCε : C ⊆ Metric.ball 0 ε)
      (hCℓ : ∀ x ∈ C, ℓ x ≠ 0) : C ⊆ A ∨ C ⊆ B := by
    by_cases hCA : C ⊆ A
    · exact Or.inl hCA
    obtain ⟨x, hxC, hxA⟩ := Set.not_subset.mp hCA
    have hxB : x ∈ B := ((hball (hCε hxC)).1.mpr (hCP hxC)).resolve_left hxA
    refine Or.inr fun y hyC => ?_
    by_contra hyB
    have hyA : y ∈ A := ((hball (hCε hyC)).1.mpr (hCP hyC)).resolve_right hyB
    obtain ⟨z, hzC, hzA, hzB⟩ := isPreconnected_closed_iff.mp hC.isPreconnected A B hA hB
      (fun z hz => (hball (hCε hz)).1.mpr (hCP hz)) ⟨y, hyC, hyA⟩ ⟨x, hxC, hxB⟩
    exact hCℓ z hzC ((hball (hCε hzC)).2.mp ⟨hzA, hzB⟩).2
  have hpos : Cpos ⊆ A ∨ Cpos ⊆ B := hchoice
    ((P.convex.inter (convex_ball 0 ε)).inter (convex_halfSpace_gt ℓ.isLinear 0))
    (fun _ hx => hx.1.1) (fun _ hx => hx.1.2) (fun _ hx => ne_of_gt hx.2)
  have hneg : Cneg ⊆ A ∨ Cneg ⊆ B := hchoice
    ((P.convex.inter (convex_ball 0 ε)).inter (convex_halfSpace_lt ℓ.isLinear 0))
    (fun _ hx => hx.1.1) (fun _ hx => hx.1.2) (fun _ hx => ne_of_lt hx.2)
  have hnotA (hposA : Cpos ⊆ A) (hnegA : Cneg ⊆ A) : False := by
    obtain ⟨x, hx, hxε⟩ := Metric.mem_closure_iff.mp hclB ε hε
    have hxball : x ∈ Metric.ball 0 ε := by rwa [Metric.mem_ball, dist_comm]
    have hxP : x ∈ P := (hball hxball).1.mp (Or.inr hx.1)
    have hxne : ℓ x ≠ 0 := fun heq => hx.2 ((hball hxball).2.mpr ⟨hxP, heq⟩).1
    rcases hxne.lt_or_gt with hlt | hgt
    · exact hx.2 (hnegA ⟨⟨hxP, hxball⟩, hlt⟩)
    · exact hx.2 (hposA ⟨⟨hxP, hxball⟩, hgt⟩)
  have hnotB (hposB : Cpos ⊆ B) (hnegB : Cneg ⊆ B) : False := by
    obtain ⟨x, hx, hxε⟩ := Metric.mem_closure_iff.mp hclA ε hε
    have hxball : x ∈ Metric.ball 0 ε := by rwa [Metric.mem_ball, dist_comm]
    have hxP : x ∈ P := (hball hxball).1.mp (Or.inl hx.1)
    have hxne : ℓ x ≠ 0 := fun heq => hx.2 ((hball hxball).2.mpr ⟨hxP, heq⟩).2
    rcases hxne.lt_or_gt with hlt | hgt
    · exact hx.2 (hnegB ⟨⟨hxP, hxball⟩, hlt⟩)
    · exact hx.2 (hposB ⟨⟨hxP, hxball⟩, hgt⟩)
  rcases hpos with hposA | hposB <;> rcases hneg with hnegA | hnegB
  · exact (hnotA hposA hnegA).elim
  · refine Or.inl ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with x hx
    constructor
    · intro hxA
      have hxP : x ∈ P := (hball hx).1.mp (Or.inl hxA)
      refine ⟨hxP, le_of_not_gt fun hlt => ?_⟩
      have hxB := hnegB ⟨⟨hxP, hx⟩, hlt⟩
      exact hlt.ne ((hball hx).2.mp ⟨hxA, hxB⟩).2
    · rintro ⟨hxP, hxge⟩
      rcases hxge.eq_or_lt with heq | hlt
      · exact ((hball hx).2.mpr ⟨hxP, heq.symm⟩).1
      · exact hposA ⟨⟨hxP, hx⟩, hlt⟩
  · refine Or.inr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with x hx
    constructor
    · intro hxA
      have hxP : x ∈ P := (hball hx).1.mp (Or.inl hxA)
      refine ⟨hxP, le_of_not_gt fun hgt => ?_⟩
      have hxB := hposB ⟨⟨hxP, hx⟩, hgt⟩
      exact hgt.ne' ((hball hx).2.mp ⟨hxA, hxB⟩).2
    · rintro ⟨hxP, hxle⟩
      rcases hxle.lt_or_eq with hlt | heq
      · exact hnegA ⟨⟨hxP, hx⟩, hlt⟩
      · exact ((hball hx).2.mpr ⟨hxP, heq⟩).1
  · exact (hnotB hposB hnegB).elim

variable [FiniteDimensional ℝ E]

theorem eventually_mem_fiber_iff_mem_levelPolygon_of_ne_vertex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {J : Set E} (hJ : J ∈ levelPolygons K.space ℓ (ℓ p))
    {q : E} (hq : q ∈ J) (hqp : q ≠ p) :
    ∀ᶠ x in 𝓝 q, x ∈ K.space ∩ {y | ℓ y = ℓ p} ↔ x ∈ J := by
  let C := levelPolygons K.space ℓ (ℓ p) \ {J}
  have hC : C.Finite := (finite_levelPolygons K (fun s hs => hK.card_le K hs) hdimE ℓ hℓ hinj (ℓ p)).subset sdiff_subset
  have hclosed : IsClosed ({p} ∪ ⋃₀ C) := by
    rw [sUnion_eq_biUnion]
    exact isClosed_singleton.union (hC.isClosed_biUnion fun T hT => hT.1.1.isPolyhedron.isClosed)
  have hqC : q ∉ {p} ∪ ⋃₀ C := by
    rintro (heq | hqC)
    · exact hqp heq
    obtain ⟨T, hT, hqT⟩ := mem_sUnion.mp hqC
    exact hqp (inter_subset_singleton_levelPolygons_of_ne K hK hdimE ℓ hℓ hinj hp hJ hT.1
      (Ne.symm hT.2) ⟨hq, hqT⟩)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hqC] with x hx
  constructor
  · intro hxlevel
    rw [fiber_eq_singleton_union_sUnion_levelPolygons K hK hdimE ℓ hℓ hinj hp] at hxlevel
    rcases hxlevel with hxp | hxpoly
    · exact (hx (Or.inl hxp)).elim
    obtain ⟨T, hT, hxT⟩ := mem_sUnion.mp hxpoly
    by_cases hTJ : T = J
    · exact hTJ ▸ hxT
    · exact (hx (Or.inr (mem_sUnion.mpr ⟨T, ⟨hT, hTJ⟩, hxT⟩))).elim
  · exact fun hxJ => hJ.2 hxJ

theorem eventually_mem_halfSpace_or_of_levelPolygon_partition
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {J A B : Set E} (hJ : J ∈ levelPolygons K.space ℓ (ℓ p))
    (hA : IsClosed A) (hB : IsClosed B) (hunion : A ∪ B = K.space) (hinter : A ∩ B = J)
    (hclA : closure (A \ B) = A) (hclB : closure (B \ A) = B) {q : E} (hq : q ∈ J) (hqp : q ≠ p) :
    (∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ ℓ q ≤ ℓ x) ∨
      (∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ ℓ x ≤ ℓ q) := by
  classical
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hqheight : ℓ q = ℓ p := (hJ.2 hq).2
  have hqK : q ∈ K.space := (hJ.2 hq).1
  have hqv : q ∉ K.vertices := fun hqv => hqp (hinj hqv hp hqheight)
  have hqA : q ∈ A := (hinter.symm.subset hq).1
  have hqB : q ∈ B := (hinter.symm.subset hq).2
  obtain ⟨s, hs, hqs⟩ := exists_face_mem_openSimplex K hqK
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (one_lt_card_of_mem_openSimplex_of_notMem_vertices K hs hqs hqv)
  have habspan : a - b ∈ vectorSpan ℝ (s : Set E) := vsub_mem_vectorSpan ℝ ha hb
  have habne : ℓ (a - b) ≠ 0 := by
    rw [map_sub, sub_ne_zero]
    intro heq
    exact hab (hinj (K.down_closed hs (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a))
      (K.down_closed hs (Finset.singleton_subset_iff.mpr hb) (Finset.singleton_nonempty b)) heq)
  obtain ⟨g, P, -, hg0, -, -, hheight, hchart⟩ :=
    exists_height_preserving_chart_of_transverse_face K hK ℓ hs hqs habspan habne
  have hgc : Filter.Tendsto g (𝓝 0) (𝓝 q) := by
    simpa only [hg0] using (g.continuous.continuousAt (x := 0)).tendsto
  have hgs : Filter.Tendsto g.symm (𝓝 q) (𝓝 0) := by
    rw [← hg0]
    simpa only [g.symm_apply_apply] using (g.symm.continuous.continuousAt (x := g 0)).tendsto
  have hlocal : ∀ᶠ y in 𝓝 0, g y ∈ K.space ↔ y ∈ P := by
    filter_upwards [hgc.eventually hchart] with y hy
    refine hy.trans ⟨?_, fun hyp => ⟨y, hyp, rfl⟩⟩
    rintro ⟨z, hz, hzy⟩
    exact g.injective hzy ▸ hz
  have hcover' : ∀ᶠ y in 𝓝 0, y ∈ g ⁻¹' A ∪ g ⁻¹' B ↔ y ∈ P := by
    filter_upwards [hlocal] with y hy
    change g y ∈ A ∪ B ↔ y ∈ P
    rwa [hunion]
  have hinter' : ∀ᶠ y in 𝓝 0, y ∈ g ⁻¹' A ∩ g ⁻¹' B ↔ y ∈ P ∧ ℓ.toLinearMap y = 0 := by
    filter_upwards [hlocal, hgc.eventually (eventually_mem_fiber_iff_mem_levelPolygon_of_ne_vertex
      K hK hdimE ℓ.toLinearMap hlinear hinj hp hJ hq hqp)] with y hy hJy
    change g y ∈ A ∩ B ↔ y ∈ P ∧ ℓ y = 0
    rw [hinter, ← hJy]
    change (g y ∈ K.space ∧ ℓ (g y) = ℓ p) ↔ _
    rw [hy, hheight, hqheight, add_eq_right]
  have hclosureA : (0 : E) ∈ closure ((g ⁻¹' A) \ (g ⁻¹' B)) := by
    change (0 : E) ∈ closure (g ⁻¹' (A \ B))
    rw [← g.preimage_closure]
    change g 0 ∈ closure (A \ B)
    rwa [hg0, hclA]
  have hclosureB : (0 : E) ∈ closure ((g ⁻¹' B) \ (g ⁻¹' A)) := by
    change (0 : E) ∈ closure (g ⁻¹' (B \ A))
    rw [← g.preimage_closure]
    change g 0 ∈ closure (B \ A)
    rwa [hg0, hclB]
  rcases eventually_mem_halfSpace_or_of_closed_partition (hA.preimage g.continuous) (hB.preimage g.continuous)
    P ℓ.toLinearMap hcover' hinter' hclosureA hclosureB with hge | hle
  · refine Or.inl ?_
    filter_upwards [hgs.eventually hge, hgs.eventually hlocal] with x hx hxS
    have hAx : x ∈ A ↔ g.symm x ∈ P ∧ 0 ≤ ℓ (g.symm x) := by
      change (g (g.symm x) ∈ A ↔ g.symm x ∈ P ∧ 0 ≤ ℓ (g.symm x)) at hx
      rwa [g.apply_symm_apply] at hx
    have hPx : g.symm x ∈ P ↔ x ∈ K.space := by
      simpa only [g.apply_symm_apply] using hxS.symm
    have hlevel : ℓ x = ℓ (g.symm x) + ℓ q := by
      simpa only [g.apply_symm_apply] using hheight (g.symm x)
    rw [hAx, hPx]
    exact and_congr_right fun _ => by constructor <;> intro h <;> linarith
  · refine Or.inr ?_
    filter_upwards [hgs.eventually hle, hgs.eventually hlocal] with x hx hxS
    have hAx : x ∈ A ↔ g.symm x ∈ P ∧ ℓ (g.symm x) ≤ 0 := by
      change (g (g.symm x) ∈ A ↔ g.symm x ∈ P ∧ ℓ (g.symm x) ≤ 0) at hx
      rwa [g.apply_symm_apply] at hx
    have hPx : g.symm x ∈ P ↔ x ∈ K.space := by
      simpa only [g.apply_symm_apply] using hxS.symm
    have hlevel : ℓ x = ℓ (g.symm x) + ℓ q := by
      simpa only [g.apply_symm_apply] using hheight (g.symm x)
    rw [hAx, hPx]
    exact and_congr_right fun _ => by constructor <;> intro h <;> linarith

theorem eventually_mem_halfSpace_along_levelPolygon_disk_partition
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {J A B : Set E} (hJ : J ∈ levelPolygons K.space ℓ (ℓ p))
    {gA gB : (Fin 3 → ℝ) → E} (hgA : IsPLHomeomorphOn gA (stdSimplex ℝ (Fin 3)) A)
    (hgB : IsPLHomeomorphOn gB (stdSimplex ℝ (Fin 3)) B)
    (hunion : A ∪ B = K.space) (hinter : A ∩ B = J)
    (hgAJ : gA '' stdSimplexBoundary 2 = J) (hgBJ : gB '' stdSimplexBoundary 2 = J) :
    (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x) ∨
      (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ ℓ x ≤ ℓ p) := by
  have hA : IsPLBall 2 A := ⟨gA, hgA⟩
  have hB : IsPLBall 2 B := ⟨gB, hgB⟩
  have hdiffA : A \ B = A \ J := by
    rw [← hinter]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hdiffB : B \ A = B \ J := by
    rw [← hinter]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hclA : closure (A \ B) = A := by
    rw [hdiffA, ← hgAJ]
    exact hgA.closure_sdiff_image_stdSimplexBoundary
  have hclB : closure (B \ A) = B := by
    rw [hdiffB, ← hgBJ]
    exact hgB.closure_sdiff_image_stdSimplexBoundary
  let U : Set E := {q | ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x}
  let V : Set E := {q | ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ ℓ x ≤ ℓ p}
  have hU : IsOpen U := isOpen_setOfPred_eventually_nhds
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hcover : J \ {p} ⊆ U ∪ V := by
    rintro q ⟨hq, hqp⟩
    have hchoice := eventually_mem_halfSpace_or_of_levelPolygon_partition K hK hdimE ℓ hℓ hinj hp hJ
      hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hunion hinter hclA hclB hq hqp
    have hheight : ℓ q = ℓ p := (hJ.2 hq).2
    rw [hheight] at hchoice
    exact hchoice
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hnotboth : ∀ q ∈ J \ {p}, q ∈ U → q ∈ V → False := by
    intro q hq hqU hqV
    have hqcl : q ∈ closure (A \ B) := hclA.symm ▸ (hinter.symm.subset hq.1).1
    have havoid : ∀ᶠ x in 𝓝 q, x ∉ A \ B := by
      filter_upwards [hqU, hqV, eventually_mem_fiber_iff_mem_levelPolygon_of_ne_vertex
        K hK hdimE ℓ.toLinearMap hlinear hinj hp hJ hq.1 hq.2] with x hxU hxV hxJ
      rintro ⟨hxA, hxB⟩
      have hlevel : ℓ x = ℓ p := le_antisymm (hxV.mp hxA).2 (hxU.mp hxA).2
      have hxJ' : x ∈ J := hxJ.mp ⟨(hxU.mp hxA).1, hlevel⟩
      exact hxB (hinter.symm.subset hxJ').2
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp havoid
    obtain ⟨x, hx, hxε⟩ := Metric.mem_closure_iff.mp hqcl ε hε
    exact hball (by rwa [Metric.mem_ball, dist_comm]) hx
  change J \ {p} ⊆ U ∨ J \ {p} ⊆ V
  by_cases hsub : J \ {p} ⊆ U
  · exact Or.inl hsub
  obtain ⟨q, hq, hqU⟩ := Set.not_subset.mp hsub
  have hqV := (hcover hq).resolve_left hqU
  refine Or.inr fun r hr => ?_
  by_contra hrV
  have hrU := (hcover hr).resolve_right hrV
  obtain ⟨z, hz, hzU, hzV⟩ := (hJ.1.isConnected_sdiff_singleton_one p).isPreconnected
    U V hU hV hcover ⟨r, hr, hrU⟩ ⟨q, hq, hqV⟩
  exact hnotboth z hz hzU hzV

private theorem eventually_mem_opposite_halfSpace_of_partition {X : Type*} [TopologicalSpace X]
    {A B S J : Set X} (hunion : A ∪ B = S) (hinter : A ∩ B = J) (f : X → ℝ) (r : ℝ) {q : X}
    (hJ : ∀ᶠ x in 𝓝 q, x ∈ S ∩ {y | f y = r} ↔ x ∈ J)
    (hA : ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ S ∧ r ≤ f x) :
    ∀ᶠ x in 𝓝 q, x ∈ B ↔ x ∈ S ∧ f x ≤ r := by
  filter_upwards [hJ, hA] with x hxJ hxA
  constructor
  · intro hxB
    have hxS : x ∈ S := hunion ▸ Or.inr hxB
    refine ⟨hxS, le_of_not_gt fun hgt => ?_⟩
    have hxA' := hxA.mpr ⟨hxS, hgt.le⟩
    have heq : f x = r := (hxJ.mpr (hinter.subset ⟨hxA', hxB⟩)).2
    exact hgt.ne' heq
  · rintro ⟨hxS, hxle⟩
    by_cases hxB : x ∈ B
    · exact hxB
    have hxA' : x ∈ A := (hunion.symm.subset hxS).resolve_right hxB
    have heq : f x = r := le_antisymm hxle (hxA.mp hxA').2
    exact (hinter.symm.subset (hxJ.mp ⟨hxS, heq⟩)).2

theorem eventually_mem_opposite_halfSpaces_along_levelPolygon_disk_partition
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {J A B : Set E} (hJ : J ∈ levelPolygons K.space ℓ (ℓ p))
    {gA gB : (Fin 3 → ℝ) → E} (hgA : IsPLHomeomorphOn gA (stdSimplex ℝ (Fin 3)) A)
    (hgB : IsPLHomeomorphOn gB (stdSimplex ℝ (Fin 3)) B)
    (hunion : A ∪ B = K.space) (hinter : A ∩ B = J)
    (hgAJ : gA '' stdSimplexBoundary 2 = J) (hgBJ : gB '' stdSimplexBoundary 2 = J) :
    (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q,
      (x ∈ A ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x) ∧ (x ∈ B ↔ x ∈ K.space ∧ ℓ x ≤ ℓ p)) ∨
    (∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q,
      (x ∈ A ↔ x ∈ K.space ∧ ℓ x ≤ ℓ p) ∧ (x ∈ B ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x)) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hlocal : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ K.space ∩ {y | ℓ y = ℓ p} ↔ x ∈ J :=
    fun _ hq => eventually_mem_fiber_iff_mem_levelPolygon_of_ne_vertex K hK hdimE ℓ.toLinearMap hlinear hinj hp hJ hq.1 hq.2
  rcases eventually_mem_halfSpace_along_levelPolygon_disk_partition K hK hdimE ℓ hℓ hinj hp hJ hgA hgB
    hunion hinter hgAJ hgBJ with hge | hle
  · refine Or.inl fun q hq => ?_
    exact (hge q hq).and (eventually_mem_opposite_halfSpace_of_partition hunion hinter ℓ (ℓ p) (hlocal q hq) (hge q hq))
  · refine Or.inr fun q hq => ?_
    have hJneg : ∀ᶠ x in 𝓝 q, x ∈ K.space ∩ {y | -ℓ y = -ℓ p} ↔ x ∈ J := by
      simpa only [neg_inj] using hlocal q hq
    have hAneg : ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ K.space ∧ -ℓ p ≤ -ℓ x := by
      simpa only [neg_le_neg_iff] using hle q hq
    have hB := eventually_mem_opposite_halfSpace_of_partition hunion hinter (fun x => -ℓ x) (-ℓ p) hJneg hAneg
    have hB' : ∀ᶠ x in 𝓝 q, x ∈ B ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x := by
      simpa only [neg_le_neg_iff] using hB
    exact (hle q hq).and hB'

end DifferentialGeometry.Topology.PiecewiseLinear
