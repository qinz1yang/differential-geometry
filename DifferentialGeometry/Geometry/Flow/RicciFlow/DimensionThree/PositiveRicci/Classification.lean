import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Compactness.Limit

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Topology.ThreeManifold
open DifferentialGeometry.Geometry

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HamiltonPositiveRicci

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

theorem hamilton_constant_positive_sectional_curvature_of_injectivity_radius_bound
    {omega : Real} (h0omega : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamiltonReferenceRadius)
    (hscalar : forall t : Real, t ∈ P.D.carrier →
      forall x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P)
    (hinj : FlowerScaleInjBound (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  classical
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  change FlowerScaleInjBound (I := I) X at hinj
  have hcpl : SeqMetricComplete (I := I) (X.atZero (I := I)) := by
    refine ⟨?_⟩
    intro k
    change MetricComplete (I := I) ((X.term k).atTime (I := I) 0)
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact (X.term k).M ?_ ?_
    with_unfolding_all
      exact hM.1
  have hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M := by
    intro k
    change @ConnectedSpace (X.term k).M (X.term k).topology
    with_unfolding_all
      exact hM.2.1
  let hderiv : FlowDerivativeInput (I := I) X :=
    hamiltonSourceDerivativeInput (I := I) h0omega hM.1 P hD Q hsel hrm hwindow
  let seed : MetricCompactSeed (I := I) (X.atZero (I := I)) :=
    metricSeedOfBG (I := I) (X.atZero (I := I))
      hcpl hderiv.atZeroGeom hinj hconn
  have hd : Nonempty (BoundedGeometryNormalData (I := I) (X.atZero (I := I)) seed.decay) :=
    exists_bounded_geometry_normal_data (I := I) (X.atZero (I := I))
      hcpl hconn hderiv.atZeroGeom seed.decay seed.realizes
  let canon : CanonicalMetricCompactness (I := I) (X.atZero (I := I)) :=
    seed.higherRegularityCanonicalMetricCompactness (Classical.choice hd) hcpl hconn
  have hcanonConn :
      letI : TopologicalSpace canon.compactness.limit.M := canon.compactness.limit.topology
      ConnectedSpace canon.compactness.limit.M := by
    simpa only [canon] using
      seed.higher_regularity_canonical_metric_compactness_connected (Classical.choice hd) hcpl hconn
  obtain ⟨d, hlimCpl⟩ :=
    hamilton_flow_upgrade_of_metric_compactness (I := I) h0omega hM.1 P hD Q hsel hrm
      hwindow canon
  have hlimitConn :
      letI : TopologicalSpace d.data.L.M := d.data.L.topology
      ConnectedSpace d.data.L.M :=
    flow_upgrade_data_connected (I := I) d hcanonConn
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(hamiltonReferenceRadius ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg hamiltonReferenceRadius), le_rfl⟩
  let mc := canon.compactness.compSubseq d.φ d.hφ
  exact constant_positive_sectional_curvature_of_smooth_cgh
    (I := I) (M := M) h0omega hM P hD Q hsel hscalar hpinch
    (hamiltonSourceLink (I := I) h0omega P hD Q hsel hwindow)
    hzero d.data.L mc.subseq mc.strictMono
    (Classical.choice (flow_upgrade_data_converges (I := I) d)) hlimCpl hlimitConn

theorem hamilton_constant_positive_sectional_curvature_of_volume_noncollapse
    {omega : Real} (h0omega : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamiltonReferenceRadius)
    (hscalar : forall t : Real, t ∈ P.D.carrier →
      forall x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P)
    (V : FlowerScaleVolData (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow))
    (hvol : IsFlowerScaleVolBound (I := I) V) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  classical
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  change FlowerScaleVolData (I := I) X at V
  change IsFlowerScaleVolBound (I := I) V at hvol
  have hcpl : SeqMetricComplete (I := I) (X.atZero (I := I)) := by
    refine ⟨?_⟩
    intro k
    change MetricComplete (I := I) ((X.term k).atTime (I := I) 0)
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact (X.term k).M ?_ ?_
    with_unfolding_all
      exact hM.1
  have hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M := by
    intro k
    change @ConnectedSpace (X.term k).M (X.term k).topology
    with_unfolding_all
      exact hM.2.1
  let hderiv : FlowDerivativeInput (I := I) X :=
    hamiltonSourceDerivativeInput (I := I) h0omega hM.1 P hD Q hsel hrm hwindow
  have hinj : FlowerScaleInjBound (I := I) X :=
    flowInjOfVol (I := I) X hcpl hconn hderiv.atZeroGeom V hvol
  exact hamilton_constant_positive_sectional_curvature_of_injectivity_radius_bound
    (I := I) (M := M) h0omega hM P hD Q hsel hrm hwindow
    hscalar hpinch hinj

theorem hamilton_constant_positive_sectional_curvature_of_pinching
    {omega : Real} (h0omega : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamiltonReferenceRadius)
    (hscalar : ∀ t : Real, t ∈ P.D.carrier →
      ∀ x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  obtain ⟨V, hV⟩ :=
    exists_hamilton_vol (I := I) h0omega hM P hD Q hsel hrm hwindow
  exact hamilton_constant_positive_sectional_curvature_of_volume_noncollapse
    (I := I) (M := M) h0omega hM P hD Q hsel hrm hwindow
    hscalar hpinch V hV

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hamilton_admits_constant_positive_sectional_curvature
    (hM : isClosedThreeManifold (I := I) (M := M))
    (hpos : admitsPositiveRicci (I := I) (M := M)) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  let : I.Boundaryless := hM.2.2.1
  let : NeZero (Module.finrank Real E) := ⟨by
    rw [hM.2.2.2]; norm_num⟩
  rcases hpos with ⟨g0, hg0⟩
  let : CompactSpace M := hM.1
  rcases hamilton_finite_time_flow_exists_on_closed_open
      (I := I) (M := M) hM g0 hg0 with
    ⟨omega, h0omega, P, hD⟩
  have hnonnegative : hamiltonRicciNonnegative (I := I) P omega :=
    hamilton_ricci_nonnegative (I := I) (M := M) h0omega hM hg0 P hD
  have hscalarBlow : hamiltonScalarBlowup (I := I) P :=
    hamilton_scalar_blowup (I := I) (M := M) h0omega hM P hD hnonnegative
  rcases hamilton_exists_blowup_point_sequence
      (I := I) (M := M) h0omega P hD hscalarBlow with
    ⟨Q, hsel⟩
  have hric : hamiltonRescaledRicciNonnegative (I := I) P Q :=
    hamilton_rescaled_ricci_nonnegative
      (I := I) (M := M) h0omega hM g0 hg0 P hD Q hsel
  have hpinch : hamiltonPinchingEstimate (I := I) P :=
    hamilton_pinching_implies_pinch_estimate
      (I := I) (M := M) h0omega hM g0 hg0 P hD
  have hrm : hamiltonRiemannCurvatureBound (I := I) P Q :=
    hamilton_rescaled_curvature_bound (I := I) (M := M) hM g0 P Q hsel hric
  have hwindow : hamiltonWindow (I := I) P Q hamiltonReferenceRadius :=
    hamilton_reference_radius_window (I := I) P Q hsel
  have hscalar :
      ∀ t : Real, t ∈ P.D.carrier → ∀ x : M, 0 < P.S.scalar t x :=
    hamilton_scalar_positive (I := I) (M := M) h0omega hM g0 hg0 P hD
  exact hamilton_constant_positive_sectional_curvature_of_pinching
    (I := I) (M := M) h0omega hM P hD Q hsel hrm hwindow
    hscalar hpinch


end HamiltonPositiveRicci
end RicciFlow
end PDE
end DifferentialGeometry
