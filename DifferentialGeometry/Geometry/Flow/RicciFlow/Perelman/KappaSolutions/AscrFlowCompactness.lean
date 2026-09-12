import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrNormalizedSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrSelectedInjectivity
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
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ascrFlowTopology : TopologicalSpace F.M := F.topology
local instance ascrFlowCharted : ChartedSpace H F.M := F.charted
local instance ascrFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance ascrFlowOne : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ascrFlowT2 : T2Space F.M := F.t2
local instance ascrFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {kappa : ℝ}

omit [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem ascrFlow_edist_comm
    (g : SmoothRiemannianMetric I F.M) (y z : F.M) :
    riemannianEDistOf (I := I) g y z = riemannianEDistOf (I := I) g z y := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I y z = Manifold.riemannianEDist I z y
  exact Manifold.riemannianEDist_comm (I := I) (x := y) (y := z)

omit [I.Boundaryless] in
theorem eventually_terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound
    (hF : IsAncientKappaSolution (I := I) kappa F) (hK : KLim kappa F)
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
    exact (congrArg ENNReal.toReal (ascrFlow_edist_comm F g z (x i))).trans_lt
      ((ENNReal.toReal_le_of_le_ofReal hA hz).trans_lt hi)
  exact terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound
    F hF hK hdim x hQ i (r i) (hlocal i) hs z hdist

theorem exists_terminalCurvatureNormalizedFlowSeq_three_ancient_limit
    (hF : IsAncientKappaSolution (I := I) kappa F) (hK : KLim kappa F)
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
  have hterms (i : ℕ) : IsAncientKappaSolution (I := I) kappa (Y.term i) :=
    isAncientKappaSolution_curvatureNormalizedFlow F hF
      0 (F.S.scalar 0 (x i)) (hQ i) (by simp) (x i) rfl
  let hinj : FlowScaleInjectivityBound (I := I) Y :=
    terminalCurvatureNormalizedFlowSeq_three_baseInjBound F hF hK hdim
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
    filter_upwards [eventually_terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound
      F hF hK hdim x r hQ hlocal hexpand hA.le] with i hi
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
    have horder := ancientModel_metric_zero_le (Y.term i) (hterms i) ht.2 z v
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

theorem ancientKappaThree_exists_ascr_ancient_limit
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (p : F.M) :
    let hK := ancientKappaThree_toKLim F hF hdim
    let d := fun y z : F.M =>
      (riemannianEDistOf (I := I) (F.S.base.metric 0) y z).toReal
    ∃ (x : ℕ → F.M) (r eps : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)),
      (∀ i, 0 < r i ∧ r i ≤ d p (x i) / 6) ∧
      (∀ i, 0 < eps i ∧ eps i < 1) ∧ StrictAnti eps ∧
      Tendsto eps atTop (𝓝 0) ∧
      Pairwise (fun i j =>
        Disjoint
          {z : F.M | riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i) <
            ENNReal.ofReal (r i)}
          {z : F.M | riemannianEDistOf (I := I) (F.S.base.metric 0) z (x j) <
            ENNReal.ofReal (r j)}) ∧
      Tendsto (fun i => d p (x i)) atTop atTop ∧
      Tendsto (fun i => F.S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => d p (x i) / r i) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop ∧
      Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) * d p (x i)) atTop atTop ∧
      (∀ i, 1 / 4 < r i * Real.sqrt (F.S.scalar 0 (x i))) ∧
      (∀ i z, d z (x i) < r i →
        F.S.scalar 0 z ≤ (1 + eps i) * F.S.scalar 0 (x i)) ∧
      let Y := terminalCurvatureNormalizedFlowSeq F hK x hQ
      (∀ i, IsAncientKappaSolution (I := I) kappa (Y.term i)) ∧
      (∀ i, PointedFlowScalarAtBase (I := I) (Y.term i) 1) ∧
      (∀ A : ℝ, 0 ≤ A → ∀ᶠ i in atTop, ∀ s ≤ (0 : ℝ), ∀ z : F.M,
        @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
            ((Y.atZero (I := I)).obj i).metric (x i) z ≤ ENNReal.ofReal A →
          (Y.term i).rmNormSq (I := I) s z ≤ 48) ∧
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
  let hK : KLim kappa F := ancientKappaThree_toKLim F hF hdim
  obtain ⟨x, r, eps, hQ, hr, heps, hanti, hepsLimit, hdisjoint,
      hescape, hQr, hratio, hexpand, hscaledEscape, hlocal,
      hterms, _hcomplete, _hconnected, _hnoncollapse, _hoperator, _hbase,
      _hbackward, _heventual⟩ :=
    ancientKappaThree_exists_ascr_normalized_sequence F hF hdim hnoncompact p
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexpand.eventually_gt_atTop (1 / 4))
  let shift : ℕ → ℕ := fun i => N + i
  have hshift : StrictMono shift := by
    intro i j hij
    exact Nat.add_lt_add_left hij N
  let x' : ℕ → F.M := x ∘ shift
  let r' : ℕ → ℝ := r ∘ shift
  let eps' : ℕ → ℝ := eps ∘ shift
  let hQ' : ∀ i, 0 < F.S.scalar 0 (x' i) := fun i => hQ (shift i)
  have hlarge (i : ℕ) : 1 / 4 < r' i * Real.sqrt (F.S.scalar 0 (x' i)) :=
    hN (shift i) (Nat.le_add_right N i)
  have hexpand' : Tendsto (fun i => r' i * Real.sqrt (F.S.scalar 0 (x' i)))
      atTop atTop := hexpand.comp hshift.tendsto_atTop
  have hlocal4 (i : ℕ) (z : F.M)
      (hz : (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x' i)).toReal < r' i) :
      F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x' i) := by
    exact (hlocal (shift i) z hz).trans (mul_le_mul_of_nonneg_right
      (by linarith [(heps (shift i)).2]) (hQ' i).le)
  refine ⟨x', r', eps', hQ', (fun i => hr (shift i)),
    (fun i => heps (shift i)), hanti.comp_strictMono hshift,
    hepsLimit.comp hshift.tendsto_atTop, ?_, hescape.comp hshift.tendsto_atTop,
    hQr.comp hshift.tendsto_atTop, hratio.comp hshift.tendsto_atTop,
    hexpand', hscaledEscape.comp hshift.tendsto_atTop, hlarge,
    (fun i => hlocal (shift i)), ?_⟩
  · intro i j hij
    exact hdisjoint (fun h => hij (hshift.injective h))
  · refine ⟨(fun i => hterms (shift i)),
      terminalCurvatureNormalizedFlowSeq_scalar_base F hK x' hQ',
      (fun A hA => eventually_terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound
        F hF hK hdim x' r' hQ' hlocal4 hexpand' hA), ?_⟩
    exact exists_terminalCurvatureNormalizedFlowSeq_three_ancient_limit
      F hF hK hdim x' r' hQ' hlocal4 hexpand' hlarge

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
