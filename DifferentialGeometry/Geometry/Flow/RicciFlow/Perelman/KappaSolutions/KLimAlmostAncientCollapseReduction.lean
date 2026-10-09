import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KappaSeedFrontierConsolidation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimInstance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimSeedCollapseInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.AllScales

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem kappaNoncollapsedBelowScale_iff_spatially_of_rmControlled
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : ℝ}
    (hreg : ∀ (t : D.FlowTime) (B : FlowMetricBall S t),
      B.radius ≤ rho → B.IsSpatiallyRmControlled → B.IsRmControlled) :
    KappaNoncollapsedBelowScale S kappa rho ↔
      SpatiallyKappaNoncollapsedBelowScale S kappa rho :=
  ⟨fun h => ⟨h.1, fun t B hr hs => h.2 t B hr (hreg t B hr hs)⟩,
    fun h => kappaNoncollapsedBelowScale_of_spatially h⟩

theorem kappaNoncollapsedBelowScale_of_kappaNoncollapsedOnAllScales
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : ℝ}
    (h : KappaNoncollapsedOnAllScales S kappa) (hrho : 0 < rho) :
    KappaNoncollapsedBelowScale S kappa rho :=
  (kappa_noncollapsed_on_all_scales_iff.mp h).2 rho hrho

namespace CanonicalNeighborhood

private local instance reductionPointedTopology
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance reductionPointedCharted
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance reductionPointedSmooth
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance reductionPointedC1
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance reductionPointedT2
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance reductionPointedSigma
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

theorem kappa_pos_of_pointedFlowNoncollapsedAllScales
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
    (B : FlowMetricBall (I := I) (M := F.M) F.S time)
    (hB : B.IsSpatiallyRmControlled)
    (h : PointedFlowNoncollapsedAllScales (I := I) F kappa) : 0 < kappa :=
  (h time B hB).1

theorem pointedFlowNoncollapsedAllScales_iff_forall_belowScale
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ} :
    PointedFlowNoncollapsedAllScales (I := I) F kappa ↔
      ∀ rho : ℝ, 0 < rho →
        SpatiallyKappaNoncollapsedBelowScale (I := I) (M := F.M) F.S kappa rho := by
  constructor
  · intro h rho hrho
    exact ⟨hrho, fun t B _ hr => h t B hr⟩
  · intro h t B hr
    exact (h B.radius B.radius_pos).2 t B le_rfl hr

theorem kappaNoncollapsedOnAllScales_of_pointedFlowNoncollapsedAllScales
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ} (hkappa : 0 < kappa)
    (h : PointedFlowNoncollapsedAllScales (I := I) F kappa) :
    KappaNoncollapsedOnAllScales (I := I) (M := F.M) F.S kappa :=
  ⟨hkappa, fun t B hB => h t B (B.isSpatiallyRmControlled_of_isRmControlled hB)⟩

end CanonicalNeighborhood

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.DifferentialGeometry.Manifold Set _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open scoped _root_.DifferentialGeometry.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [I.Boundaryless] in
theorem kLimAlmostAncientCollapse_iff_ballBound (kappa : ℝ) :
    KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa ↔
      ∀ eps : ℝ, 0 < eps →
        ∃ A L : ℝ, 1 ≤ A ∧
          KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L := by
  constructor
  · intro h eps heps
    obtain ⟨A, L, hA, _hAL, hbound⟩ := h eps heps
    exact ⟨A, L, hA, hbound⟩
  · intro h eps heps
    obtain ⟨A, L, hA, hbound⟩ := h eps heps
    refine ⟨A, max L (A ^ 2), hA, le_max_right _ _, ?_⟩
    intro D F hK x Q r hQ hxQ hr hlocal hscale
    exact hbound D F hK x Q r hQ hxQ hr hlocal ((le_max_left L (A ^ 2)).trans hscale)

omit [I.Boundaryless] in
theorem kLimAlmostAncientCollapseFields_iff_ballBound (kappa : ℝ) :
    KLimAlmostAncientCollapseFields.{u, uE, uH} (I := I) kappa ↔
      ∀ eps : ℝ, 0 < eps →
        ∃ A L : ℝ, 1 ≤ A ∧
          KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L :=
  (kLimAlmostAncientCollapse_iff_fields (I := I)).symm.trans
    (kLimAlmostAncientCollapse_iff_ballBound (I := I) kappa)

theorem kLimHarnackCollapseBound_of_seedAncientLimit_and_ballBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : ∀ eps : ℝ, 0 < eps →
      ∃ A L : ℝ, 1 ≤ A ∧
        KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  kLimHarnackCollapseBound_of_seedAncientLimit_and_almostAncientCollapse (I := I) hdim hseed
    ((kLimAlmostAncientCollapse_iff_ballBound (I := I) kappa).2 hcollapse)

theorem kLimLocalCurvatureBound_of_seedAncientLimit_and_ballBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : ∀ eps : ℝ, 0 < eps →
      ∃ A L : ℝ, 1 ≤ A ∧
        KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L) :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa :=
  kLimLocalCurvatureBound_of_harnackCollapseBound (I := I) hdim
    (kLimHarnackCollapseBound_of_seedAncientLimit_and_ballBound (I := I) hdim hseed hcollapse)

theorem kLimTerminalDerivativeBound_of_seedAncientLimit_and_ballBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : ∀ eps : ℝ, 0 < eps →
      ∃ A L : ℝ, 1 ≤ A ∧
        KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L) :
    KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa :=
  kLimTerminalDerivativeBound_of_harnackCollapseBound (I := I) hdim
    (kLimHarnackCollapseBound_of_seedAncientLimit_and_ballBound (I := I) hdim hseed hcollapse)

theorem modelCurvatureBoundNearBase_of_seedAncientLimit_and_ballBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : ∀ eps : ℝ, 0 < eps →
      ∃ A L : ℝ, 1 ≤ A ∧
        KLimAlmostAncientCollapseBallBound.{u, uE, uH} (I := I) kappa eps A L) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa :=
  FiniteHorn.modelCurvatureBoundNearBase_of_harnackCollapseBound (I := I) hdim
    (kLimHarnackCollapseBound_of_seedAncientLimit_and_ballBound (I := I) hdim hseed hcollapse)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood.FiniteHorn
open scoped _root_.DifferentialGeometry.Manifold ContDiff _root_.Topology ENNReal

universe u

theorem not_pointedFlowNoncollapsedAllScales_euclideanFlatFlow_of_nonpos
    {kappa : ℝ} (h : kappa ≤ 0) :
    ¬ PointedFlowNoncollapsedAllScales (I := I3) euclideanFlatFlow kappa := by
  intro hnc
  let time : ancientTimeInterval.FlowTime :=
    ⟨(0 : ℝ), by
      simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using (le_refl (0 : ℝ))⟩
  let B : FlowMetricBall (I := I3) (M := ThreeSpace) euclideanFlatFlow.S time :=
    ⟨0, 1, zero_lt_one⟩
  have hctrl : B.IsSpatiallyRmControlled := by
    intro x _hx
    have hrm : FlowMetricBall.rmNormSq (I := I3) euclideanFlatFlow.S (time : ℝ) x = 0 := by
      have hflat : euclideanFlatFlow.rmNormSq (I := I3) (time : ℝ) x = 0 :=
        euclideanFlatFlow_rmNormSq (time : ℝ) x
      simpa only [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq, SolutionOn.family_metric]
        using hflat
    change (1 : ℝ) ^ 4 *
      FlowMetricBall.rmNormSq (I := I3) euclideanFlatFlow.S (time : ℝ) x ≤ 1
    rw [hrm]
    norm_num
  exact absurd (hnc time B hctrl).1 (not_lt.mpr h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
