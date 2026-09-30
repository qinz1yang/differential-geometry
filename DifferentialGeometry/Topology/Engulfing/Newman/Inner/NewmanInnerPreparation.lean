import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerModel
import DifferentialGeometry.Topology.Engulfing.Local.Buffers.StaticProtectedSubcomplex
import DifferentialGeometry.Topology.Engulfing.Local.Buffers.NewmanStableBuffers

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M] {n p : ℕ}

structure NewmanInnerGeometry (K L : SimplicialComplex ℝ E) (F : C(K.space, M))
    (X : Set M) (raw : E → EuclideanSpace ℝ (Fin n)) (Y : Set E) (p : ℕ) where
  gp : FiniteGPFaceModel K raw
  affine : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    EqOn raw A (convexHull ℝ (s : Set E))
  injective : ∀ s ∈ K.faces, InjOn raw (convexHull ℝ (s : Set E))
  chart : BufferedChart M n
  fixed_affine : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → F x ∈ chart.core →
      chart.chart (F x) = A x.val
  obstacle : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))
  obstacle_finite : obstacle.faces.Finite
  obstacle_dimension : ∀ s ∈ obstacle.faces, s.card ≤ p + 1
  obstacle_contains : chart.chart '' (X ∩ chart.core) ⊆ obstacle.space
  jointObstacle : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin gp.jointDimension))
  jointObstacle_faces : jointObstacle.faces ⊆ gp.joint.faces
  jointObstacle_dimension : ∀ s ∈ jointObstacle.faces, s.card ≤ p + 1
  jointObstacle_contains : chart.chart.symm ⁻¹' X ∩ raw '' Y ⊆
    ⋃ t ∈ jointObstacle.faces, convexHull ℝ (gp.vertices ''
      (t : Set (EuclideanSpace ℝ (Fin gp.jointDimension))))
  shared_avoids : ∀ s : K.faces, convexHull ℝ (s.val : Set E) ⊆ Y →
    ∀ t ∈ jointObstacle.faces, Disjoint
      (convexHull ℝ (gp.vertices ''
        (((gp.face s).val : Set (EuclideanSpace ℝ (Fin gp.jointDimension))) ∩ t)))
      (chart.chart.symm ⁻¹' X)

omit [DecidableEq E] in
theorem exists_newmanInnerModel_of_static_data
    (K L H D Y : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hHK : H.faces ⊆ K.faces)
    (hDK : D.faces ⊆ K.faces) (hYK : Y.faces ⊆ K.faces) (hYD : Y.space ⊆ D.space)
    (F : C(K.space, M)) (X : Set M) (raw : E → EuclideanSpace ℝ (Fin n))
    (a : NewmanInnerGeometry K L F X raw Y.space p)
    (cut : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hcut : cut.faces.Finite)
    {r₀ rB rU rCut rA δ : ℝ}
    (h₀B : r₀ < rB) (hBU : rB < rU) (hUC : rU < rCut)
    (hCA : rCut < rA) (hAR : rA < a.chart.outerRadius)
    (hcut_lower : closedBall a.chart.center rCut ⊆ cut.space)
    (hcut_upper : cut.space ⊆ ball a.chart.center a.chart.innerRadius)
    (hYraw : raw '' Y.space ⊆ closedBall a.chart.center r₀)
    (hmesh : ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
      ∀ y ∈ convexHull ℝ (s : Set E), dist (raw x) (raw y) < δ)
    (hgap : rU + δ ≤ rCut)
    (hfixed : ∀ x : K.space, x.val ∈ L.space ∩ D.space →
      F x ∈ a.chart.chart.source ∧ a.chart.chart (F x) = raw x.val)
    (hexact : ∀ x : K.space, x.val ∈ D.space → raw x.val ∈ cut.space →
      F x ∈ a.chart.chart.source ∧ a.chart.chart (F x) = raw x.val)
    (hentry : ∀ x : K.space, F x ∈ a.chart.chart.source →
      a.chart.chart (F x) ∈ closedBall a.chart.center a.chart.outerRadius →
        x.val ∈ D.space ∧ a.chart.chart (F x) = raw x.val) :
    Nonempty (NewmanInnerModel K L H F X raw Y.space p) := by
  classical
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  have h₀Cut : r₀ < rCut := (h₀B.trans hBU).trans hUC
  have h₀R : r₀ < a.chart.outerRadius := h₀Cut.trans (hCA.trans hAR)
  have hUR : rU < a.chart.outerRadius := hUC.trans (hCA.trans hAR)
  have hYcut : raw '' Y.space ⊆ cut.space :=
    hYraw.trans ((closedBall_subset_closedBall h₀Cut.le).trans hcut_lower)
  have hcut_target : cut.space ⊆ a.chart.chart.target :=
    hcut_upper.trans ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall a.chart.radii_lt.le)).trans a.chart.outer_subset)
  obtain ⟨C, hC, hCK, hYC, hCD, hCs, hLDC, hHDC, hCHcut⟩ :=
    exists_static_protected_subcomplex K L H D Y hK hLK hHK hDK hYK hYD
      raw a.chart.center hmesh cut.space
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hgap)).trans hcut_lower) hYcut
  have hCcut : raw '' ((C.space \ L.space) ∩ (H.space ∪ Y.space)) ⊆ cut.space := by
    rintro _ ⟨x, ⟨hxC, hxHY⟩, rfl⟩
    rcases hxHY with hxH | hxY
    · exact hCHcut ⟨x, ⟨hxC, hxH⟩, rfl⟩
    · exact hYcut (mem_image_of_mem raw hxY)
  have hcoords (x : K.space) (hx : x.val ∈ C.space) :
      F x ∈ a.chart.chart.source ∧ a.chart.chart (F x) = raw x.val := by
    by_cases hxL : x.val ∈ L.space
    · exact hfixed x ⟨hxL, hCD hx⟩
    · apply hexact x (hCD hx)
      apply hCcut
      refine ⟨x.val, ⟨⟨hx, hxL⟩, ?_⟩, rfl⟩
      rcases hCs hx with (hxL' | hxH) | hxY
      · exact (hxL hxL').elim
      · exact Or.inl hxH
      · exact Or.inr hxY
  obtain ⟨A, B, U, r, η, hA, hB, hU, hBU', hUA, hrR, hη, hBeq, hUeq, hcontrol⟩ :=
    exists_stable_restoration_buffers F a.chart.chart a.chart.center
      h₀B hBU hUC hCA hAR a.chart.outer_subset
  have hcovered : (Subtype.val ⁻¹' H.space) ∩ U ⊆ Subtype.val ⁻¹' C.space := by
    intro x hx
    have hxU := hUeq.subset hx.2
    have hxD := hentry x hxU.1 ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall hUR.le)) hxU.2)
    apply hHDC
    refine ⟨⟨hx.1, hxD.1⟩, ?_⟩
    change raw x.val ∈ ball a.chart.center rU
    rw [← hxD.2]
    exact hxU.2
  have hblock : (Subtype.val ⁻¹' Y.space : Set K.space) ⊆ B := by
    intro x hx
    have hxraw := hYraw (mem_image_of_mem raw hx)
    have hxcoord := hexact x (hYD hx) (hYcut (mem_image_of_mem raw hx))
    rw [hBeq]
    refine ⟨raw x.val, closedBall_subset_closedBall h₀B.le hxraw, ?_⟩
    rw [← hxcoord.2, a.chart.chart.left_inv hxcoord.1]
  refine ⟨{
    gp := a.gp
    affine := a.affine
    injective := a.injective
    chart := a.chart
    localComplex := C
    local_subcomplex := hCK
    block_local := subcomplex_space_subset C Y hYC
    local_covered := hCs
    coordinates := hcoords
    fixed_affine := a.fixed_affine
    cut := cut
    cut_finite := hcut
    cut_core := ?_
    fixed_covers := ?_
    local_raw_cut := hCcut
    obstacle := a.obstacle
    obstacle_finite := a.obstacle_finite
    obstacle_dimension := a.obstacle_dimension
    obstacle_contains := a.obstacle_contains
    jointObstacle := a.jointObstacle
    jointObstacle_faces := a.jointObstacle_faces
    jointObstacle_dimension := a.jointObstacle_dimension
    jointObstacle_contains := a.jointObstacle_contains
    shared_avoids := a.shared_avoids
    outerSource := A
    fixedSource := B
    blendSource := U
    outer_compact := hA
    fixed_closed := hB
    blend_open := hU
    fixed_blend := hBU'
    blend_outer := hUA
    covered_blend := hcovered
    block_fixed := hblock
    center := a.chart.center
    innerRadius := r
    outerRadius := a.chart.outerRadius
    radii_lt := hrR
    outer_target := a.chart.outer_subset
    support := ball a.chart.center a.chart.outerRadius
    support_open := isOpen_ball
    support_bounded := isBounded_ball
    support_target := (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      a.chart.outer_subset
    block_image := ?_
    tolerance := η
    tolerance_pos := hη
    control := ?_ }⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨a.chart.chart.map_target (hcut_target hy), ?_⟩
    change a.chart.chart (a.chart.chart.symm y) ∈ ball a.chart.center a.chart.innerRadius
    rw [a.chart.chart.right_inv (hcut_target hy)]
    exact hcut_upper hy
  · intro x hxL hxsource hxcut
    apply hLDC
    refine ⟨hxL, (hentry x hxsource ?_).1⟩
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall a.chart.radii_lt.le))
      (hcut_upper hxcut)
  · intro y hy
    have hyr := hYraw hy
    exact ⟨⟨a.chart.outer_subset (closedBall_subset_closedBall h₀R.le hyr), hYcut hy⟩,
      closedBall_subset_ball h₀R hyr⟩
  · intro g hg
    obtain ⟨hsource, hrange, hblend, hpre⟩ := hcontrol g hg
    exact ⟨hsource, hrange, fun x hx => ⟨(hblend x hx).1, hcut_lower (hblend x hx).2⟩,
      (preimage_mono (image_mono hYraw)).trans hpre⟩

omit [DecidableEq E] in
theorem exists_newmanInnerModel_of_gap
    (K L H D Y : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hHK : H.faces ⊆ K.faces)
    (hDK : D.faces ⊆ K.faces) (hYK : Y.faces ⊆ K.faces) (hYD : Y.space ⊆ D.space)
    (F : C(K.space, M)) (X : Set M) (raw : E → EuclideanSpace ℝ (Fin n))
    (a : NewmanInnerGeometry K L F X raw Y.space p)
    (cut : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hcut : cut.faces.Finite)
    (r t η : ℝ) (ht : 0 < t) (hηt : η ≤ t)
    (hinner : a.chart.innerRadius = r + 15 * t)
    (houter : a.chart.outerRadius = r + 18 * t)
    (hcut_lower : closedBall a.chart.center (r + 12 * t) ⊆ cut.space)
    (hcut_upper : cut.space ⊆ ball a.chart.center (r + 15 * t))
    (hYraw : raw '' Y.space ⊆ closedBall a.chart.center (r + 2 * t))
    (hmesh : ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
      ∀ y ∈ convexHull ℝ (s : Set E), dist (raw x) (raw y) < 5 * η)
    (hfixed : ∀ x : K.space, x.val ∈ L.space ∩ D.space →
      F x ∈ a.chart.chart.source ∧ a.chart.chart (F x) = raw x.val)
    (hexact : ∀ x : K.space, x.val ∈ D.space → raw x.val ∈ cut.space →
      F x ∈ a.chart.chart.source ∧ a.chart.chart (F x) = raw x.val)
    (hentry : ∀ x : K.space, F x ∈ a.chart.chart.source →
      a.chart.chart (F x) ∈ closedBall a.chart.center (r + 18 * t) →
        x.val ∈ D.space ∧ a.chart.chart (F x) = raw x.val) :
    Nonempty (NewmanInnerModel K L H F X raw Y.space p) := by
  classical
  apply exists_newmanInnerModel_of_static_data K L H D Y hK hLK hHK hDK hYK hYD F X raw a cut hcut
    (r₀ := r + 2 * t) (rB := r + 4 * t) (rU := r + 6 * t)
    (rCut := r + 12 * t) (rA := r + 16 * t) (δ := 5 * η)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by rw [houter]; linarith) hcut_lower
    (by simpa only [hinner] using hcut_upper) hYraw hmesh (by linarith) hfixed hexact
  simpa only [houter] using hentry

end

end DifferentialGeometry.Topology.Engulfing
