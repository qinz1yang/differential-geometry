import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimSelectedInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance klimSelectedFlowTopology : TopologicalSpace F.M := F.topology
local instance klimSelectedFlowCharted : ChartedSpace H F.M := F.charted
local instance klimSelectedFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance klimSelectedFlowOne : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance klimSelectedFlowT2 : T2Space F.M := F.t2
local instance klimSelectedFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {kappa : ℝ}

omit [I.Boundaryless] in
theorem KLim.metric_zero_le (hK : KLim kappa F) {s : ℝ} (hs : s ≤ 0)
    (x : F.M) (v : TangentSpace I x) :
    (F.S.base.metric 0).inner x v v ≤ (F.S.base.metric s).inner x v v := by
  have hRic : ∀ q ∈ Set.Ioo s 0, ∀ y : F.M, ∀ w : TangentSpace I y,
      0 ≤ F.S.ricciAt q y (vec2 w w) := by
    intro q hq y w
    have hqmem : q ∈ D.carrier := by
      simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2.le
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric q) y).mpr
    intro n c a b
    simpa [SolutionFamily.rm04, metricRm04StandardAt_apply, vec4] using
      hK.nonnegativeCurvatureOperator q hqmem y n c a b
  have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior F.S F.isSolution
    (a := s) (b := 0)
    (fun q hq => by simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2)
    (fun q hq => by simpa only [hK.regular_eq, Set.mem_Iio] using hq.2)
    hRic x v
  exact hanti ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs

omit [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem klimSelectedFlow_edist_comm
    (g : SmoothRiemannianMetric I F.M) (y z : F.M) :
    riemannianEDistOf (I := I) g y z = riemannianEDistOf (I := I) g z y := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I y z = Manifold.riemannianEDist I z y
  exact Manifold.riemannianEDist_comm (I := I) (x := y) (y := z)

omit [I.Boundaryless] in
theorem eventually_terminalCurvatureNormalizedFlowSeq_klim_three_rmNormSq_bound
    (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop)
    {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ i in atTop, ∀ s ≤ (0 : ℝ), ∀ z : F.M,
      @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
          (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
          (x i) z ≤ ENNReal.ofReal A →
        ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z ≤
          48 := by
  filter_upwards [hexpand.eventually_gt_atTop A] with i hi
  intro s hs z hz
  let g : @SmoothRiemannianMetric E _ _ H _ I F.M F.topology F.charted F.smooth :=
    scaleMetric (F.S.scalar 0 (x i)) (hQ i)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
  have hdist : (riemannianEDistOf (I := I) g z (x i)).toReal <
      r i * Real.sqrt (F.S.scalar 0 (x i)) := by
    exact (congrArg ENNReal.toReal (klimSelectedFlow_edist_comm F g z (x i))).trans_lt
      ((ENNReal.toReal_le_of_le_ofReal hA hz).trans_lt hi)
  exact terminalCurvatureNormalizedFlowSeq_klim_three_rmNormSq_bound
    F hK hdim x hQ i (r i) (hlocal i) hs z hdist

theorem exists_terminalCurvatureNormalizedFlowSeq_klim_three_ancient_limit
    (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop)
    (hlarge : ∀ i, 1 / 4 < r i * Real.sqrt (F.S.scalar 0 (x i))) :
    let Y := terminalCurvatureNormalizedFlowSeq F hK x hQ
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) Y (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ≤ (0 : ℝ), MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ≤ (0 : ℝ),
          ∃ C : MetricConvergenceData (I := I)
              (Phi.atTime (X := Y) (L := L) (phi := phi) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (X := Y) (L := L) (phi := phi) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I)
                  (Phi.atTime (X := Y) (L := L) (phi := phi) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I)
                  (Phi.atTime (X := Y) (L := L) (phi := phi) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I)
                  (Phi.atTime (X := Y) (L := L) (phi := phi) t) k) := D.smooth
              D.referenceMetric = D.limitMetric) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let Y := terminalCurvatureNormalizedFlowSeq F hK x hQ
  have hterms (i : ℕ) : KLim kappa (Y.term i) :=
    KLim.curvatureNormalizedFlow F hK
      0 (F.S.scalar 0 (x i)) (hQ i)
      (by simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
      (x i) rfl
  let hinj : FlowScaleInjectivityBound (I := I) Y :=
    terminalCurvatureNormalizedFlowSeq_klim_three_baseInjBound F hK hdim
      x r hQ hlocal hlarge
  have hlocalInput : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (Y.term i).M := (Y.term i).topology
        let _ : ChartedSpace H (Y.term i).M := (Y.term i).charted
        let _ : IsManifold I ∞ (Y.term i).M := (Y.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ z : (Y.term i).M,
          riemannianEDistOf (I := I) ((Y.term i).S.base.metric 0)
              (Y.term i).basepoint z ≤ ENNReal.ofReal A →
            (Y.term i).rmNormSq (I := I) t z ≤ K := by
    intro A hA T _hT
    refine ⟨48, by norm_num, ?_⟩
    filter_upwards [eventually_terminalCurvatureNormalizedFlowSeq_klim_three_rmNormSq_bound
      F hK hdim x r hQ hlocal hexpand hA.le] with i hi
    intro t ht z hz
    change F.M at z
    exact hi t ht.2 z hz
  have hlowerInput : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (Y.term i).M := (Y.term i).topology
        let _ : ChartedSpace H (Y.term i).M := (Y.term i).charted
        let _ : IsManifold I ∞ (Y.term i).M := (Y.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ z : (Y.term i).M, ∀ v : TangentSpace I z,
          c * ((Y.term i).S.base.metric 0).inner z v v ≤
            ((Y.term i).S.base.metric t).inner z v v := by
    intro T _hT
    refine ⟨1, zero_lt_one, Filter.Eventually.of_forall ?_⟩
    intro i
    dsimp only
    intro t ht z v
    have horder := KLim.metric_zero_le (Y.term i) (hterms i) ht.2 z v
    simpa only [one_mul] using horder
  obtain ⟨L, phi, hphi, Phi, hconnected, hcomplete, hconvergence⟩ :=
    exists_local_ancient_flow_compactness Y rfl
      (terminalCurvatureNormalizedFlowSeq_complete F hK x hQ)
      (terminalCurvatureNormalizedFlowSeq_connected F hK x hQ)
      hinj hlocalInput hlowerInput
  refine ⟨L, phi, hphi, Phi, hconnected, ?_, ?_⟩
  · intro t ht
    exact hcomplete t (by change t ∈ ancientTimeInterval.carrier; simpa using ht)
  · intro t ht
    exact hconvergence t (by change t ∈ ancientTimeInterval.carrier; simpa using ht)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
