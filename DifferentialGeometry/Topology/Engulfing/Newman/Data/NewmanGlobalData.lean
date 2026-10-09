import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanChartRefinement
import Mathlib.Geometry.Manifold.ChartedSpace

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] {n p : ℕ}

def hasAdaptedPiecewiseLinearCharts (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    (X : Set M) (n p : ℕ) : Prop :=
  ∀ y : M, ∃ b : AdaptedPiecewiseLinearChart K L f X n p, y ∈ b.toBufferedChart.core

theorem hasAdaptedPiecewiseLinearCharts.withMap {K L : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {X : Set M} (h : hasAdaptedPiecewiseLinearCharts K L f X n p)
    (g : C(K.space, M)) (hfix : ∀ x : K.space, x.1 ∈ L.space → g x = f x) :
    hasAdaptedPiecewiseLinearCharts K L g X n p := by
  intro y
  obtain ⟨b, hb⟩ := h y
  exact ⟨b.withMap g hfix, hb⟩

theorem hasAdaptedPiecewiseLinearCharts.toFinite {K L : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {X : Set M} (h : hasAdaptedPiecewiseLinearCharts K L f X n p)
    (hK : K.faces.Finite) (hX : IsClosed X) :
    Nonempty (FiniteAdaptedPiecewiseLinearCover K L f X n p) :=
  exists_finiteAdaptedPiecewiseLinearCover K L hK f hX (fun x => h (f x))

theorem hasAdaptedPiecewiseLinearCharts.refine {K L : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {X : Set M} (h : hasAdaptedPiecewiseLinearCharts K L f X n p)
    (P J : SimplicialComplex ℝ E) (hspace : P.space = K.space)
    (hJL : simplicialRefines J L) (hJspace : J.space ⊆ L.space)
    (g : C(P.space, M)) (hg : ∀ x, g x = f ⟨x.1, hspace ▸ x.2⟩) :
    hasAdaptedPiecewiseLinearCharts P J g X n p := by
  intro y
  obtain ⟨b, hyb⟩ := h y
  refine ⟨{
    toBufferedChart := b.toBufferedChart
    fixed_affine := ?_
    fixed_injective := ?_
    obstacle := b.obstacle
    obstacle_finite := b.obstacle_finite
    obstacle_dimension := b.obstacle_dimension
    obstacle_contains := b.obstacle_contains }, hyb⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hJL s hs
    obtain ⟨A, hA⟩ := b.fixed_affine t ht
    refine ⟨A, fun x hx hxcore => ?_⟩
    rw [hg]
    exact hA ⟨x.1, hspace ▸ x.2⟩ (hst hx) (by rwa [← hg])
  · intro x hx z hz hxz
    have hxz' : b.chart (f ⟨x.1, hspace ▸ x.2⟩) =
        b.chart (f ⟨z.1, hspace ▸ z.2⟩) := by
      simpa only [← hg] using hxz
    have hxmem : (⟨x.1, hspace ▸ x.2⟩ : K.space) ∈
        Subtype.val ⁻¹' L.space ∩ f ⁻¹' b.toBufferedChart.core := by
      refine ⟨hJspace (show x.1 ∈ J.space from hx.1), ?_⟩
      change f ⟨x.1, hspace ▸ x.2⟩ ∈ b.toBufferedChart.core
      rw [← hg]
      exact hx.2
    have hzmem : (⟨z.1, hspace ▸ z.2⟩ : K.space) ∈
        Subtype.val ⁻¹' L.space ∩ f ⁻¹' b.toBufferedChart.core := by
      refine ⟨hJspace (show z.1 ∈ J.space from hz.1), ?_⟩
      change f ⟨z.1, hspace ▸ z.2⟩ ∈ b.toBufferedChart.core
      rw [← hg]
      exact hz.2
    have heq := b.fixed_injective hxmem hzmem hxz'
    exact Subtype.ext (congrArg (fun w : K.space => w.1) heq)

def adaptedPiecewiseLinearChartOfDisjoint (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    (X : Set M) (b : BufferedChart M n)
    (hL : Disjoint (f '' (Subtype.val ⁻¹' L.space)) b.core)
    (hX : Disjoint X b.core) : AdaptedPiecewiseLinearChart K L f X n p where
  toBufferedChart := b
  fixed_affine := by
    intro s hs
    refine ⟨0, fun x hx hxcore => ?_⟩
    exact (disjoint_left.mp hL ⟨x, L.convexHull_subset_space hs hx, rfl⟩ hxcore).elim
  fixed_injective := by
    intro x hx y hy _
    exact (disjoint_left.mp hL ⟨x, hx.1, rfl⟩ hx.2).elim
  obstacle := ⊥
  obstacle_finite := finite_empty
  obstacle_dimension := fun _ hs => hs.elim
  obstacle_contains := by
    rintro y ⟨x, hx, rfl⟩
    exact (disjoint_left.mp hX hx.1 hx.2).elim

theorem exists_adaptedPiecewiseLinearChart_off_fixed_obstacle [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (f : C(K.space, M)) {X : Set M} (hX : IsClosed X)
    {y : M} (hy : y ∉ X ∪ f '' (Subtype.val ⁻¹' L.space)) :
    ∃ b : AdaptedPiecewiseLinearChart K L f X n p, y ∈ b.toBufferedChart.core := by
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  have hsource : IsCompact (Subtype.val ⁻¹' L.space : Set K.space) :=
    ((isCompact_space_of_finite_faces L hL).isClosed.preimage continuous_subtype_val).isCompact
  have hopen : IsOpen (X ∪ f '' (Subtype.val ⁻¹' L.space))ᶜ :=
    (hX.union (hsource.image f.continuous).isClosed).isOpen_compl
  obtain ⟨b, _, hyb⟩ := exists_bufferedChart_at
    (chartAt (EuclideanSpace ℝ (Fin n)) y) (mem_chart_source _ y)
  obtain ⟨c, _, hyc, hcore⟩ := b.exists_recenter hyb hopen hy
  refine ⟨adaptedPiecewiseLinearChartOfDisjoint K L f X c ?_ ?_, hyc⟩
  · exact disjoint_left.mpr (fun x hx hxc => (hcore hxc).2 (Or.inr hx))
  · exact disjoint_left.mpr (fun x hx hxc => (hcore hxc).2 (Or.inl hx))

theorem hasAdaptedPiecewiseLinearCharts_openEmbedding [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {j : EuclideanSpace ℝ (Fin n) → M} (hj : IsOpenEmbedding j) (p : ℕ) :
    hasAdaptedPiecewiseLinearCharts K L
      ⟨fun x => j x.1, hj.continuous.comp continuous_subtype_val⟩ ∅ n p := by
  let f : C(K.space, M) := ⟨fun x => j x.1, hj.continuous.comp continuous_subtype_val⟩
  intro y
  by_cases hy : y ∈ range j
  · let e := (hj.toOpenPartialHomeomorph j).symm
    have hye : y ∈ e.source := by
      change y ∈ (hj.toOpenPartialHomeomorph j).target
      rwa [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    obtain ⟨b, hb, hyb⟩ := exists_bufferedChart_at e hye
    have hcoords (x : K.space) : b.chart (f x) = x.1 := by
      rw [hb]
      exact hj.toOpenPartialHomeomorph_left_inv
    refine ⟨{
      toBufferedChart := b
      fixed_affine := fun s hs => ⟨AffineMap.id ℝ _, fun x _ _ => hcoords x⟩
      fixed_injective := ?_
      obstacle := ⊥
      obstacle_finite := finite_empty
      obstacle_dimension := fun _ hs => hs.elim
      obstacle_contains := ?_ }, hyb⟩
    · intro x _ z _ hxz
      apply Subtype.ext
      change b.chart (f x) = b.chart (f z) at hxz
      simpa only [hcoords] using hxz
    · simp only [empty_inter, image_empty, empty_subset]
  · apply exists_adaptedPiecewiseLinearChart_off_fixed_obstacle K L hK hL f isClosed_empty
    rintro (hyempty | ⟨x, _, hxy⟩)
    · exact hyempty.elim
    · exact hy ⟨x.1, hxy⟩

theorem hasAdaptedPiecewiseLinearCharts.of_union [T2Space M]
    {K L : SimplicialComplex ℝ E} {f : C(K.space, M)} {X : Set M}
    (h : hasAdaptedPiecewiseLinearCharts K L f X n p) (hK : K.faces.Finite)
    (D J : SimplicialComplex ℝ E) (hD : D.faces.Finite)
    (hJ : J.faces ⊆ L.faces ∪ D.faces)
    (bNew : AdaptedPiecewiseLinearChart K J f X n p)
    (hnew : f '' (Subtype.val ⁻¹' D.space) ⊆ bNew.toBufferedChart.core) :
    hasAdaptedPiecewiseLinearCharts K J f X n p := by
  classical
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  have hcompact : IsCompact (f '' (Subtype.val ⁻¹' D.space)) :=
    (((isCompact_space_of_finite_faces D hD).isClosed.preimage
      continuous_subtype_val).isCompact).image f.continuous
  intro y
  by_cases hy : y ∈ f '' (Subtype.val ⁻¹' D.space)
  · exact ⟨bNew, hnew hy⟩
  · obtain ⟨b, hyb⟩ := h y
    obtain ⟨c, _, hyc, hcore⟩ := b.exists_recenter hyb hcompact.isClosed.isOpen_compl hy
    have havoid : Disjoint (f '' (Subtype.val ⁻¹' D.space)) c.toBufferedChart.core :=
      disjoint_left.mpr (fun x hx hxc => (hcore hxc).2 hx)
    have hlocal (x : K.space) (hx : x.1 ∈ J.space) (hxc : f x ∈ c.toBufferedChart.core) :
        x.1 ∈ L.space := by
      obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      rcases hJ hs with hsL | hsD
      · exact L.convexHull_subset_space hsL hxs
      · exact (disjoint_left.mp havoid
          ⟨x, D.convexHull_subset_space hsD hxs, rfl⟩ hxc).elim
    refine ⟨{
      toBufferedChart := c.toBufferedChart
      fixed_affine := ?_
      fixed_injective := ?_
      obstacle := c.obstacle
      obstacle_finite := c.obstacle_finite
      obstacle_dimension := c.obstacle_dimension
      obstacle_contains := c.obstacle_contains }, hyc⟩
    · intro s hs
      rcases hJ hs with hsL | hsD
      · exact c.fixed_affine s hsL
      · refine ⟨0, fun x hx hxcore => ?_⟩
        exact (disjoint_left.mp havoid
          ⟨x, D.convexHull_subset_space hsD hx, rfl⟩ hxcore).elim
    · intro x hx z hz hxz
      exact c.fixed_injective ⟨hlocal x hx.1 hx.2, hx.2⟩
        ⟨hlocal z hz.1 hz.2, hz.2⟩ hxz

theorem hasAdaptedPiecewiseLinearCharts_of_chart [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hT : T.faces.Finite)
    (hTdim : ∀ s ∈ T.faces, s.card ≤ p + 1) (f : C(K.space, M))
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hfsource : ∀ x, f x ∈ e.source) (hfcoords : ∀ x, e (f x) = x.1)
    {X : Set M} (hX : IsClosed X) (hXsource : X ⊆ e.source)
    (hXpoly : e '' X ⊆ T.space) : hasAdaptedPiecewiseLinearCharts K L f X n p := by
  intro y
  by_cases hy : y ∈ e.source
  · obtain ⟨b, hb, hyb⟩ := exists_bufferedChart_at e hy
    have hcoords (x : K.space) : b.chart (f x) = x.1 := by rw [hb]; exact hfcoords x
    refine ⟨{
      toBufferedChart := b
      fixed_affine := fun s hs => ⟨AffineMap.id ℝ _, fun x _ _ => hcoords x⟩
      fixed_injective := ?_
      obstacle := T
      obstacle_finite := hT
      obstacle_dimension := hTdim
      obstacle_contains := ?_ }, hyb⟩
    · intro x _ z _ hxz
      apply Subtype.ext
      simpa only [hcoords] using hxz
    · rintro z ⟨x, hx, rfl⟩
      rw [hb]
      exact hXpoly ⟨x, hx.1, rfl⟩
  · apply exists_adaptedPiecewiseLinearChart_off_fixed_obstacle K L hK hL f hX
    rintro (hyX | ⟨x, _, rfl⟩)
    · exact hy (hXsource hyX)
    · exact hy (hfsource x)

end DifferentialGeometry.Topology.Engulfing
