import DifferentialGeometry.Geometry.Comparison.Soul.Separators
import DifferentialGeometry.Geometry.Comparison.Soul.BoundarySupport
import DifferentialGeometry.Geometry.Comparison.Soul.GeodesicInterior
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceField

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

def minimizingDirectionsTo (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (S : Set M) (q : M) : Set (TangentSpace I q) :=
  {u | g.inner q u u = 1 ∧ intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S}

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem minimizingDirectionsTo_nonempty
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hSne : S.Nonempty) (hS : IsCompact S) {q : M} (hq : q ∉ S) :
    (minimizingDirectionsTo g hEnorm S q).Nonempty := by
  have hd : 0 < Metric.infDist q S := (hS.isClosed.notMem_iff_infDist_pos hSne).1 hq
  obtain ⟨s, hs, hdist⟩ := hS.exists_infDist_eq_dist hSne q
  obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm q s (hdist ▸ hd)
  refine ⟨u, hu, ?_⟩
  rw [hdist, hend]
  exact hs

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem isCompact_minimizingDirectionsTo
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsClosed S) (q : M) :
    IsCompact (minimizingDirectionsTo g hEnorm S q) := by
  have hc : Continuous (fun u : TangentSpace I q =>
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S)) := by
    have hexp : Continuous (fun u : TangentSpace I q =>
        expMapIntrinsic g hEnorm q (Metric.infDist q S • u)) :=
      (expMapIntrinsic_continuous g hEnorm q).comp
        (continuous_const.smul continuous_id :
          Continuous (fun u : TangentSpace I q => Metric.infDist q S • u))
    simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hexp
  exact (gUnitSphere_isCompact g q).inter_right (hS.preimage hc)

theorem exists_unit_outward_infDist_of_separator
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {S : Set M} (hSne : S.Nonempty) (hS : IsClosed S) {q : M} (hq : q ∉ S)
    {C : Set M} (hCclosed : IsClosed C)
    (hC : IsTotallyConvex g C) (hqB : q ∈ relBoundary I C)
    (hSN : S ⊆ maxSliceLocus I C) :
    ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
      ∀ u ∈ minimizingDirectionsTo g hEnorm S q, g.inner q v u < 0 := by
  have hd : 0 < Metric.infDist q S := (hS.notMem_iff_infDist_pos hSne).1 hq
  obtain ⟨w, hw, hwu⟩ := exists_unit_strict_support_relBoundary hEnorm hsec hC hCclosed hqB
  refine ⟨-w, ?_, ?_⟩
  · simpa only [map_neg, neg_apply, neg_neg] using hw
  · intro u hu
    have hinner := isInnerDirection_of_intrinsicGeodesic_endpoint hEnorm hC
      (relBoundary_subset hqB) hd (hSN hu.2)
    have hpos := hwu u hinner
    rw [map_neg, neg_apply, g.symm]
    exact neg_neg_of_pos hpos

theorem exists_soul_set_with_outward_directions [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      ∀ q ∉ S, ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
        ∀ u ∈ minimizingDirectionsTo g hEnorm S q, g.inner q v u < 0 := by
  obtain ⟨S, hSne, hScomp, hSconv, hSB, hSdim, hsep⟩ :=
    exists_soul_set_with_convex_separators g hEnorm hsec p
  refine ⟨S, hSne, hScomp, hSconv, hSB, hSdim, ?_⟩
  intro q hq
  obtain ⟨C, hCcomp, _, hC, hqB, hSN⟩ := hsep q hq
  exact exists_unit_outward_infDist_of_separator hEnorm hsec hSne hScomp.isClosed hq
    hCcomp.isClosed hC hqB hSN

theorem exists_soul_set_with_smooth_outward_fields [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      ∀ a b : ℝ, 0 < a → a < b → ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
        (∀ q, g.inner q (X q) (X q) < 4) ∧
        (∀ q, Metric.infDist q S ≤ a → X q = 0) ∧
        ∀ q, b ≤ Metric.infDist q S → ∀ u ∈ minimizingDirectionsTo g hEnorm S q,
          g.inner q (X q) u < 0 := by
  obtain ⟨S, hSne, hScomp, hSconv, hSB, hSdim, hout⟩ :=
    exists_soul_set_with_outward_directions g hEnorm hsec p
  refine ⟨S, hSne, hScomp, hSconv, hSB, hSdim, ?_⟩
  intro a b ha hab
  obtain ⟨X, hbound, hzero, hneg⟩ := exists_smooth_outward_field_infDist g hEnorm hScomp.isClosed hab
    (by
      intro q hq
      have hqS : q ∉ S := (hScomp.isClosed.notMem_iff_infDist_pos hSne).2
        (ha.trans (hab.trans_le hq))
      obtain ⟨v, hv, hvu⟩ := hout q hqS
      exact ⟨v, hv, fun u hu hend => hvu u ⟨hu, hend⟩⟩)
  exact ⟨X, hbound, hzero, fun q hq u hu => hneg q hq u hu.1 hu.2⟩

end DifferentialGeometry.Geometry.Topology
