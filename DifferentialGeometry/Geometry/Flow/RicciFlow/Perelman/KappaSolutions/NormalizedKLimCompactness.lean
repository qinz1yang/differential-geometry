import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance normalizedCompactTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance normalizedCompactCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance normalizedCompactSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance normalizedCompactC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance normalizedCompactT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance normalizedCompactSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalized_klim_canonical_slice_limit
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval) (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I) (X.term i) 1) :
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        ConnectedSpace L.M ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        PointedFlowScalarAtBase (I := I) L 1 ∧
        PointedFlowNotFlat (I := I) L ∧
        (∀ t ∈ X.D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) L t) ∧
        PointedFlowNoncollapsedAllScales (I := I) L kappa ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨C, _hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants (I := I) hdim kappa
  obtain ⟨iota, hiota, hinj⟩ :=
    exists_normalized_klim_base_injectivity (I := I) hdim kappa (hsource 0).kappa_pos
  let hbaseInj : FlowScaleInjectivityBound (I := I) X :=
    { ρ := iota
      pos := hiota
      bound := fun i => hinj X.D (X.term i) (hsource i) (hbase i) }
  have hlocalInput : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ z : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
            (X.term i).basepoint z ≤ ENNReal.ofReal A →
              (X.term i).rmNormSq (I := I) t z ≤ K := by
    intro A _hA T _hT
    refine ⟨3 * (C A) ^ 2, mul_nonneg (by norm_num) (sq_nonneg _),
      Filter.Eventually.of_forall ?_⟩
    intro i
    dsimp only
    intro t ht z hz
    exact (hbound X.D (X.term i) (hsource i) (hbase i) A z hz t ht.2).2
  have hlowerInput : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ z : (X.term i).M, ∀ v : TangentSpace I z,
          c * ((X.term i).S.base.metric 0).inner z v v ≤
            ((X.term i).S.base.metric t).inner z v v := by
    intro T _hT
    refine ⟨1, zero_lt_one, Filter.Eventually.of_forall ?_⟩
    intro i
    dsimp only
    intro t ht z v
    simpa only [one_mul] using (hsource i).metric_inner_le ht.2 le_rfl z v
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconvergence⟩ :=
    exists_local_ancient_flow_compactness X hD
      ⟨fun i t ht => (hsource i).complete t ht⟩
      (fun i => (hsource i).connected) hbaseInj hlocalInput hlowerInput
  have hconv : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := X) (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k := by
    intro t ht
    obtain ⟨Ct, hct, _href⟩ := hconvergence t ht
    exact ⟨Ct, hct⟩
  have ht0 : (0 : ℝ) ∈ X.D.carrier := by simp [hD]
  obtain ⟨C0, hc0⟩ := hconv 0 ht0
  have hscalarBase : PointedFlowScalarAtBase (I := I) L 1 := by
    apply pointedScalar_base_eq_of_metricCG_canonical_domains C0 hc0
    intro k
    exact hbase (phi k)
  have hnotflat : PointedFlowNotFlat (I := I) L :=
    pointedFlowNotFlat_of_scalar_ne_zero L ht0 L.basepoint
      (by change L.S.scalar 0 L.basepoint ≠ 0; rw [hscalarBase]; norm_num)
  have hoperator : ∀ t ∈ X.D.carrier,
      PointedFlowNonnegativeCurvatureOperator (I := I) L t := by
    intro t ht
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hcone : ∀ y : L.M,
        metricAlgebraicCurvatureTensorAt (I := I) (L.S.base.metric t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence Ct hct
      intro K _hK
      refine Filter.Eventually.of_forall ?_
      intro k y _hy _hs
      change metricAlgebraicCurvatureTensorAt (I := I)
          ((X.term (phi k)).S.base.metric t) (Phi.map k y) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I)
      apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
      intro n c v w
      have h := (hsource (phi k)).nonnegativeCurvatureOperator t ht
        (Phi.map k y) n c v w
      simpa only [algebraicCurvatureOperatorQuadraticEval,
        metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
        metricRm04_apply] using h
    intro y n c v w
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone y)) n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  have hnoncollapsed : PointedFlowNoncollapsedAllScales (I := I) L kappa := by
    intro time B hcurvature
    obtain ⟨Ct, hct⟩ := hconv time time.property
    have hnc := tensor_noncollapsed_of_pointed_canonical_convergence Ct hct
      (hcomplete time time.property) kappa (fun i p r hr hcurv => by
        let b : FlowMetricBall (X.term i).S time := ⟨p, r, hr⟩
        have hb : b.IsSpatiallyRmControlled := by
          intro z hz
          exact hcurv z hz
        exact ((hsource i).noncollapsed time b hb).2)
    exact ⟨(hsource 0).kappa_pos, hnc B.center B.radius B.radius_pos hcurvature⟩
  exact ⟨L, phi, hphi, Phi, hconnected, hcomplete, hscalarBase, hnotflat,
    hoperator, hnoncollapsed, hconv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
