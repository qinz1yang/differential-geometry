import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeLocalCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeedVolume

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance harnackCollapseTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance harnackCollapseCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance harnackCollapseSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance harnackCollapseC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance harnackCollapseT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance harnackCollapseSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact


def KLimSeedVolumeBound (kappa : ℝ) : Prop :=
  ∃ v : ℝ, 0 < v ∧
    ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
      KLim (I := I) kappa F → ∀ x : F.M, F.S.scalar 0 x = 1 →
        ENNReal.ofReal v ≤
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) x 1)


def KLimAnchoredScalarBound (kappa : ℝ) : Prop :=
  ∀ v D : ℝ, 0 < v → 0 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ p : F.M,
          ENNReal.ofReal v ≤
            riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
              (riemannianBallOf (I := I) (F.S.base.metric 0) p 1) →
          ∀ q : F.M, q ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p D →
            F.S.scalar 0 q ≤ C


def KLimHarnackCollapseBound (kappa : ℝ) : Prop :=
  KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa ∧
    KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa


omit [I.Boundaryless] in
theorem exists_normalized_bounded_distance_scalar_constant_of_harnackCollapse
    {kappa : ℝ}
    (h : KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa) (D : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F → ∀ x : F.M, F.S.scalar 0 x = 1 →
          ∀ y : F.M, riemannianEDistOf (I := I) (F.S.base.metric 0) x y ≤
            ENNReal.ofReal D → F.S.scalar 0 y ≤ C := by
  obtain ⟨hseed, hanchored⟩ := h
  obtain ⟨v, hv, hseedVolume⟩ := hseed
  obtain ⟨C, hC, hbound⟩ :=
    hanchored v (max D 0 + 1) hv (by positivity)
  refine ⟨C, hC, ?_⟩
  intro T F hK x hx y hy
  apply hbound T F hK x (hseedVolume T F hK x hx) y
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
    (lt_of_le_of_lt (le_max_left D 0) (lt_add_one (max D 0))))


omit [I.Boundaryless] in
theorem kLimLocalCurvatureBound_of_harnackCollapseBound
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa) :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa := by
  classical
  choose C hC hbound using fun A : ℝ =>
    exists_normalized_bounded_distance_scalar_constant_of_harnackCollapse
      (I := I) h A
  refine ⟨C, hC, ?_⟩
  intro D F hK hbase A y hy t ht
  have hterminal := hbound A D F hK F.basepoint hbase y hy
  exact ⟨⟨hK.scalar_nonneg ht y, (hK.scalar_le_terminal ht y).trans hterminal⟩,
    hK.rmNormSq_le_of_terminal_scalar_le F hdim ht y hterminal⟩


omit [I.Boundaryless] in
theorem exists_normalized_klim_local_curvature_constants_of_harnackCollapse
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim (I := I) kappa F → F.S.scalar 0 F.basepoint = 1 →
          ∀ A : ℝ, ∀ y : F.M,
            riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
              ENNReal.ofReal A → ∀ t : ℝ, t ≤ 0 →
            (0 ≤ F.S.scalar t y ∧ F.S.scalar t y ≤ C A) ∧
              F.rmNormSq (I := I) t y ≤ 3 * (C A) ^ 2 := by
  simpa only [KLimLocalCurvatureBound] using
    kLimLocalCurvatureBound_of_harnackCollapseBound (I := I) hdim h


private theorem harnackCollapseThreeSpaceFinrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]


theorem kLimLocalCurvatureBound_threeSpace_of_harnackCollapseBound
    (h : KLimHarnackCollapseBound.{u, 0, 0} (I := I3) universalKappaConstant) :
    KLimLocalCurvatureBound.{u, 0, 0} (I := I3) universalKappaConstant :=
  kLimLocalCurvatureBound_of_harnackCollapseBound (I := I3)
    harnackCollapseThreeSpaceFinrank h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
