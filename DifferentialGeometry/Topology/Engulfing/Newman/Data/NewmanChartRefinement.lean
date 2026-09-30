import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {M : Type*} [TopologicalSpace M] {n : ℕ}

theorem BufferedChart.exists_recenter (b : BufferedChart M n) {x : M}
    (hx : x ∈ b.core) {V : Set M} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ c : BufferedChart M n, c.chart = b.chart ∧ x ∈ c.core ∧ c.core ⊆ b.core ∩ V := by
  let W := (b.chart.target ∩ b.chart.symm ⁻¹' V) ∩ ball b.center b.innerRadius
  have hW : IsOpen W := (b.chart.symm.isOpen_inter_preimage hV).inter isOpen_ball
  have hxW : b.chart x ∈ W := by
    exact ⟨⟨b.chart.map_source hx.1,
      by simpa only [mem_preimage, b.chart.left_inv hx.1] using hxV⟩, hx.2⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW (b.chart x) hxW
  let c : BufferedChart M n :=
    { chart := b.chart
      center := b.chart x
      innerRadius := δ / 4
      outerRadius := δ / 2
      inner_pos := by positivity
      radii_lt := by linarith
      outer_subset := by
        intro y hy
        exact (hball (closedBall_subset_ball (by linarith : δ / 2 < δ) hy)).1.1 }
  refine ⟨c, rfl, ⟨hx.1, mem_ball_self c.inner_pos⟩, ?_⟩
  intro y hy
  have hyW := hball (ball_subset_ball (by dsimp [c]; linarith : c.innerRadius ≤ δ) hy.2)
  refine ⟨⟨hy.1, hyW.2⟩, ?_⟩
  have hyV : b.chart.symm (b.chart y) ∈ V := hyW.1.2
  simpa only [b.chart.left_inv hy.1] using hyV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ}

theorem AdaptedPiecewiseLinearChart.exists_recenter {K L : SimplicialComplex ℝ E}
    {g : C(K.space, M)} {X : Set M} (b : AdaptedPiecewiseLinearChart K L g X n p)
    {x : M} (hx : x ∈ b.toBufferedChart.core) {V : Set M} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ c : AdaptedPiecewiseLinearChart K L g X n p,
      c.chart = b.chart ∧ x ∈ c.toBufferedChart.core ∧
      c.toBufferedChart.core ⊆ b.toBufferedChart.core ∩ V := by
  obtain ⟨c, hc, hxc, hcore⟩ := b.toBufferedChart.exists_recenter hx hV hxV
  refine ⟨{
    toBufferedChart := c
    fixed_affine := ?_
    fixed_injective := ?_
    obstacle := b.obstacle
    obstacle_finite := b.obstacle_finite
    obstacle_dimension := b.obstacle_dimension
    obstacle_contains := ?_ }, hc, hxc, hcore⟩
  · intro s hs
    obtain ⟨A, hA⟩ := b.fixed_affine s hs
    exact ⟨A, fun x hx hxcore => by rw [hc]; exact hA x hx (hcore hxcore).1⟩
  · intro x hx y hy hxy
    rw [hc] at hxy
    exact b.fixed_injective ⟨hx.1, (hcore hx.2).1⟩ ⟨hy.1, (hcore hy.2).1⟩ hxy
  · rintro y ⟨z, hz, rfl⟩
    rw [hc]
    exact b.obstacle_contains ⟨z, ⟨hz.1, (hcore hz.2).1⟩, rfl⟩

theorem exists_finiteAdaptedPiecewiseLinearCover (K L : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (g : C(K.space, M)) {X : Set M} (hX : IsClosed X)
    (hlocal : ∀ x : K.space, ∃ b : AdaptedPiecewiseLinearChart K L g X n p,
      g x ∈ b.toBufferedChart.core) : Nonempty (FiniteAdaptedPiecewiseLinearCover K L g X n p) := by
  classical
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  choose b hb using hlocal
  have hcover : (univ : Set K.space) ⊆ ⋃ x, g ⁻¹' (b x).toBufferedChart.core :=
    fun x _ => mem_iUnion.mpr ⟨x, hb x⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x => g ⁻¹' (b x).toBufferedChart.core)
    (fun x => (b x).toBufferedChart.isOpen_core.preimage g.continuous) hcover
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp)).symm
  refine ⟨{ count := S.card, data := fun i => b (e i), covers := ?_, obstacle_closed := hX }⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  refine ⟨e.symm ⟨y, hy⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply, mem_preimage] using hxy

theorem exists_finiteAdaptedPiecewiseLinearCover_openEmbedding
    (K L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    {j : EuclideanSpace ℝ (Fin n) → M} (hj : IsOpenEmbedding j) (p : ℕ) :
    Nonempty (FiniteAdaptedPiecewiseLinearCover K L
      ⟨fun x => j x.1, hj.continuous.comp continuous_subtype_val⟩ ∅ n p) := by
  let g : C(K.space, M) := ⟨fun x => j x.1, hj.continuous.comp continuous_subtype_val⟩
  let e := (hj.toOpenPartialHomeomorph j).symm
  apply exists_finiteAdaptedPiecewiseLinearCover K L hK g isClosed_empty
  intro x
  have hx : g x ∈ e.source := by
    change j x.1 ∈ (hj.toOpenPartialHomeomorph j).target
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact mem_range_self _
  obtain ⟨b, hb, hxb⟩ := exists_bufferedChart_at e hx
  have hcoords (y : K.space) : b.chart (g y) = y.1 := by
    rw [hb]
    exact hj.toOpenPartialHomeomorph_left_inv
  refine ⟨{
    toBufferedChart := b
    fixed_affine := ?_
    fixed_injective := ?_
    obstacle := ⊥
    obstacle_finite := finite_empty
    obstacle_dimension := fun _ hs => hs.elim
    obstacle_contains := ?_ }, hxb⟩
  · intro s hs
    exact ⟨AffineMap.id ℝ _, fun y _ _ => hcoords y⟩
  · intro y _ z _ hyz
    apply Subtype.ext
    simpa only [hcoords] using hyz
  · simp only [empty_inter, image_empty, empty_subset]

end DifferentialGeometry.Topology.Engulfing
