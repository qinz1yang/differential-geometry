import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanProtectedStep
import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerGeneralPosition
import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanExpansion
import DifferentialGeometry.Topology.SimplicialComplex.Expansion.SimplexAttachmentModel

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p : ℕ}

structure NewmanInnerModel (K L H : SimplicialComplex ℝ E) (F : C(K.space, M))
    (X : Set M) (raw : E → EuclideanSpace ℝ (Fin n)) (Y : Set E) (p : ℕ) where
  gp : FiniteGPFaceModel K raw
  affine : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    EqOn raw A (convexHull ℝ (s : Set E))
  injective : ∀ s ∈ K.faces, InjOn raw (convexHull ℝ (s : Set E))
  chart : BufferedChart M n
  localComplex : SimplicialComplex ℝ E
  local_subcomplex : localComplex.faces ⊆ K.faces
  block_local : Y ⊆ localComplex.space
  local_covered : localComplex.space ⊆ (L.space ∪ H.space) ∪ Y
  coordinates : ∀ x : K.space, x.val ∈ localComplex.space →
    F x ∈ chart.chart.source ∧ chart.chart (F x) = raw x.val
  fixed_affine : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → F x ∈ chart.core →
      chart.chart (F x) = A x.val
  cut : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))
  cut_finite : cut.faces.Finite
  cut_core : chart.chart.symm '' cut.space ⊆ chart.core
  fixed_covers : ∀ x : K.space, x.val ∈ L.space → F x ∈ chart.chart.source →
    chart.chart (F x) ∈ cut.space → x.val ∈ localComplex.space
  local_raw_cut : raw '' ((localComplex.space \ L.space) ∩ (H.space ∪ Y)) ⊆ cut.space
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
  outerSource : Set K.space
  fixedSource : Set K.space
  blendSource : Set K.space
  outer_compact : IsCompact outerSource
  fixed_closed : IsClosed fixedSource
  blend_open : IsOpen blendSource
  fixed_blend : fixedSource ⊆ blendSource
  blend_outer : blendSource ⊆ interior outerSource
  covered_blend : (Subtype.val ⁻¹' H.space) ∩ blendSource ⊆ Subtype.val ⁻¹' localComplex.space
  block_fixed : (Subtype.val ⁻¹' Y : Set K.space) ⊆ fixedSource
  center : EuclideanSpace ℝ (Fin n)
  innerRadius : ℝ
  outerRadius : ℝ
  radii_lt : innerRadius < outerRadius
  outer_target : closedBall center outerRadius ⊆ chart.chart.target
  support : Set (EuclideanSpace ℝ (Fin n))
  support_open : IsOpen support
  support_bounded : Bornology.IsBounded support
  support_target : closure support ⊆ chart.chart.target
  block_image : raw '' Y ⊆ (chart.chart.target ∩ cut.space) ∩ support
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  control : ∀ g : C(K.space, M), (∀ x, dist (g x) (F x) < tolerance) →
    (∀ x ∈ outerSource, g x ∈ chart.chart.source) ∧
    (∀ x ∈ outerSource, chart.chart (g x) ∈ closedBall center innerRadius) ∧
    (∀ x ∈ blendSource, g x ∈ chart.chart.source ∧ chart.chart (g x) ∈ cut.space) ∧
    g ⁻¹' (chart.chart.symm '' (raw '' Y)) ⊆ fixedSource

namespace NewmanInnerModel

variable {K L H : SimplicialComplex ℝ E} {F : C(K.space, M)} {X : Set M}
    {raw : E → EuclideanSpace ℝ (Fin n)} {Y : Set E}
    (d : NewmanInnerModel K L H F X raw Y p)

def good (g : C(K.space, M)) : Prop :=
  EqOn g F (Subtype.val ⁻¹' (L.space ∪ d.localComplex.space)) ∧
    ∀ x, dist (g x) (F x) < d.tolerance

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem good_initial : d.good F :=
  ⟨fun _ _ => rfl, fun _ => by simpa only [dist_self] using d.tolerance_pos⟩

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem exists_near_margin (hK : K.faces.Finite) {g : C(K.space, M)}
    (hg : ∀ x, dist (g x) (F x) < d.tolerance) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g' : C(K.space, M),
      (∀ x, dist (g' x) (g x) < δ) → ∀ x, dist (g' x) (F x) < d.tolerance := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isCompact_space_of_finite_faces K hK)
  cases isEmpty_or_nonempty K.space with
  | inl he =>
    let : IsEmpty K.space := he
    exact ⟨1, zero_lt_one, fun _ _ x => isEmptyElim x⟩
  | inr hn =>
    let : Nonempty K.space := hn
    obtain ⟨x, -, hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set K.space).Nonempty)
      (g.continuous.dist F.continuous).continuousOn
    refine ⟨(d.tolerance - dist (g x) (F x)) / 2, by linarith [hg x], ?_⟩
    intro g' hnear y
    have hm := hmax (mem_univ y)
    change dist (g y) (F y) ≤ dist (g x) (F x) at hm
    have ht := dist_triangle (g' y) (g y) (F y)
    have hn' := hnear y
    linarith [hg x]

end NewmanInnerModel

end DifferentialGeometry.Topology.Engulfing
