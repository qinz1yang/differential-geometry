import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaticSurfaceLocalCompactness


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

universe u uE uH

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


private theorem metricScalarAt_nonneg_of_sectional_nonneg
    (g : SmoothRiemannianMetric I M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x), 0 ≤ metricRm04StandardAt (I := I) g x v w w v)
    (x : M) : 0 ≤ metricScalarAt (I := I) g x := by
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal g b hb]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hsec x (b j) (b i)

end Scalar

section Flow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance rankOneTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance rankOneCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance rankOneSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance rankOneC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance rankOneT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance rankOneSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance rankOneTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance rankOneInhabited {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : Inhabited F.M := ⟨F.basepoint⟩
private local instance rankOneLocallyPathConnected {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
private local instance rankOneSemilocallySimplyConnected {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)
private local instance rankOneMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance rankOneBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

omit [I.Boundaryless] in
private theorem klim_terminal_tensor_noncollapsed {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (p : F.M) (rho : ℝ) (hrho : 0 < rho)
    (hRm : ∀ z ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p rho,
      rho ^ 4 * normSq0S (I := I) (F.S.base.metric 0) z 4
        (metricRm04At (I := I) (F.S.base.metric 0) z) ≤ 1) :
    ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        (riemannianBallOf (I := I) (F.S.base.metric 0) p rho) := by
  have h0 : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  let B : FlowMetricBall (I := I) (M := F.M) F.S ⟨0, h0⟩ := ⟨p, rho, hrho⟩
  have hB : B.IsSpatiallyRmControlled := by
    intro z hz
    simpa only [B, FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply] using hRm z hz
  have hvolume := (hK.noncollapsed ⟨0, h0⟩ B hB).2
  change ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
      (riemannianBallOf (I := I) (F.S.base.metric 0) p rho) at hvolume
  exact hvolume


theorem KLim.rankOne_terminal_scalar_bddAbove {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :
    BddAbove (Set.range (F.S.scalar 0)) := by
  classical
  let _ : ConnectedSpace F.M := hK.connected
  have hdim2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := ⟨by rw [hdim2]; norm_num⟩
  have hsecnn : ∀ (x : P.S) (v w : TangentSpace (𝓡 2) x),
      0 ≤ metricRm04StandardAt (I := 𝓡 2) P.h x v w w v :=
    (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff (I := 𝓡 2) P.h).mp
      P.positive.toNonnegative
  have hsec : ∀ z : P.S, metricRm04At (I := 𝓡 2) P.h z ∈
      tensor04SectionalNonnegativeCone (I := 𝓡 2) (M := P.S) := fun z =>
    (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := 𝓡 2) P.h z).mpr (hsecnn z)
  have hnonneg : ∀ z : P.S, 0 ≤ metricScalarAt (I := 𝓡 2) P.h z :=
    metricScalarAt_nonneg_of_sectional_nonneg (I := 𝓡 2) P.h hsecnn
  have hnc : ∀ (p : P.S) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := 𝓡 2) P.h p rho,
        rho ^ 4 * normSq0S (I := 𝓡 2) P.h z 4 (metricRm04At (I := 𝓡 2) P.h z) ≤ 1) →
      ENNReal.ofReal (kappa / 2) *
          ENNReal.ofReal rho ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) ≤
        riemannianVolumeMeasure (I := 𝓡 2) (M := P.S) P.h
          (riemannianBallOf (I := 𝓡 2) P.h p rho) := by
    intro p rho hrho hRm
    rw [hdim2]
    exact universalCover_split_surface_tensor_half_noncollapsed (F.S.base.metric 0) hdim
      P.h P.Phi P.product kappa hK.kappa_pos.le
      (klim_terminal_tensor_noncollapsed hK) p rho hrho hRm
  have hbdd : BddAbove (Set.range (metricScalarAt (I := 𝓡 2) P.h)) :=
    static_surface_scalar_bddAbove_of_local_normalized_jets (I := 𝓡 2) P.h
      (terminal_surface_factor_local_jets hK hdim P) P.complete hdim2 hnonneg hsec
      (kappa / 2) (by linarith [hK.kappa_pos]) hnc
  have hdown : BddAbove (Set.range (metricScalarAt (I := I) (F.S.base.metric 0))) :=
    (bddAbove_scalar_iff_of_universalCover_product (F.S.base.metric 0) P.h P.Phi
      P.product).mpr hbdd
  exact hdown

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
