import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackSelectedInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance klimLocalMeasurableE : MeasurableSpace E := borel E
private local instance klimLocalBorelE : BorelSpace E := ⟨rfl⟩

section OneFlow

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance klimLocalTopology : TopologicalSpace F.M := F.topology
local instance klimLocalCharted : ChartedSpace H F.M := F.charted
local instance klimLocalSmooth : IsManifold I ∞ F.M := F.smooth
local instance klimLocalC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance klimLocalT2 : T2Space F.M := F.t2
local instance klimLocalSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance klimLocalTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

theorem KLim.terminal_smallBall_volume_three (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hquarter : ∀ z : F.M,
      riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint z <
        ENNReal.ofReal (1 / 4) → F.S.scalar 0 z ≤ 2)
    (s : ℝ) (hs : 0 < s) (hsQuarter : s ≤ 1 / 4) :
    ENNReal.ofReal kappa * ENNReal.ofReal s ^ 3 ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        (riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint s) := by
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  let B := PointedFlowData.baseFlowBall (I := I) F hzero s hs
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    change riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint z <
      ENNReal.ofReal s at hz
    have hzQuarter : riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint z <
        ENNReal.ofReal (1 / 4) :=
      hz.trans_le (ENNReal.ofReal_le_ofReal hsQuarter)
    have hRm : F.rmNormSq (I := I) 0 z ≤ 12 := by
      have hbound := KLim.rmNormSq_le_of_terminal_scalar_le F hK hdim le_rfl z
        (hquarter z hzQuarter)
      norm_num at hbound
      exact hbound
    have hpow : s ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hs.le hsQuarter 4
    have hmul := mul_le_mul_of_nonneg_left hRm (pow_nonneg hs.le 4)
    change s ^ 4 * F.rmNormSq (I := I) 0 z ≤ 1
    nlinarith
  have hvolume := (hK.noncollapsed ⟨0, hzero⟩ B hcontrol).2
  change ENNReal.ofReal kappa * ENNReal.ofReal s ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
      (riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint s) at hvolume
  simpa only [hdim] using hvolume

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem klim_terminal_hasInjRadiusAt (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hquarter : ∀ z : F.M,
      riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint z <
        ENNReal.ofReal (1 / 4) → F.S.scalar 0 z ≤ 2)
    (R : ℝ) (hR : 0 < R) (hRQuarter : R ≤ 1 / 4)
    (hRpi : R ≤ Real.pi / Real.sqrt 7)
    (herror : ∀ a : ℝ, 0 ≤ a → a ≤ R →
      gronwallBound 0 (max (Real.sqrt (Module.finrank ℝ E : ℝ) * 7 * a ^ 2) 1)
        (Real.sqrt (Module.finrank ℝ E : ℝ) * 7 * a ^ 2) 1 ≤ 1 / 4) :
    HasInjRadiusAt (I := I) (F.atTime (I := I) 0) F.basepoint
      (selectedCGTInjRadius E kappa R) := by
  have hη : 0 < selectedCGTInjRadius E kappa R :=
    selectedCGTInjRadius_pos (E := E) hK.kappa_pos hR
  refine ⟨hη, ?_⟩
  intro hcomplete
  let Y := F.atTime (I := I) 0
  let _ : TopologicalSpace Y.M := Y.topology
  let _ : ChartedSpace H Y.M := Y.charted
  let _ : IsManifold I ∞ Y.M := Y.smooth
  let _ : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let _ : T2Space Y.M := Y.t2
  let _ : SigmaCompactSpace Y.M := Y.sigmaCompact
  let _ : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let _ : RiemannianBundle (fun y : Y.M => TangentSpace I y) := Y.riemBundle (I := I)
  let _ : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) := Y.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let _ : EMetricSpace Y.M := Y.emetricSpace (I := I)
  have : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let _ : ConnectedSpace Y.M := hK.connected
  let hEnorm : IsMetricNorm (I := I) Y.metric := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) Y.metric y v
  let g : @SmoothRiemannianMetric E _ _ H _ I F.M F.topology F.charted F.smooth :=
    F.S.base.metric 0
  have hRm : ∀ y : Y.M,
      riemannianEDist I Y.basepoint y < ENNReal.ofReal (1 / 4) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) Y.metric y 4
        (metricRm04At (I := I) Y.metric y)) ≤ 7 := by
    intro y hy
    have hyOf : @riemannianEDistOf E _ _ H _ I Y.M
        Y.topology Y.charted Y.smooth Y.metric Y.basepoint y <
        ENNReal.ofReal (1 / 4) := by
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) Y.metric hEnorm]
      exact hy
    change F.M at y
    change riemannianEDistOf (I := I) g F.basepoint y <
      ENNReal.ofReal (1 / 4) at hyOf
    have hsq := KLim.rmNormSq_le_of_terminal_scalar_le F hK hdim le_rfl y
      (hquarter y hyOf)
    change Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04 (I := I) g y) ≤ 3 * 2 ^ 2 at hsq
    rw [metricRm04_apply] at hsq
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y)) ≤ 7
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, hsq.trans (by norm_num)⟩
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hRic : RicciBoundedBelow (I := I) Y.metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    intro y v
    change F.M at y
    change TangentSpace I y at v
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) g y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) g y).mpr
      intro m c a b
      have ht := hK.nonnegativeCurvatureOperator 0 hzero y m c a b
      change 0 ≤ ∑ j, ∑ l, c j * c l *
        (metricRm04 (I := I) (M := F.M) g y)
          (vec4 (I := I) (a j) (b j) (b l) (a l)) at ht
      simpa only [metricRm04StandardAt_apply, metricRm04_apply] using ht
    have h := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) g y hcone v
    change (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) *
      g.inner y v v ≤ ricciTensor (I := I) g y v v
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, neg_zero, zero_mul,
      metricRicciAt_apply_eq_ricciTensor] using h
  have hs : 0 < R / 8 := by positivity
  have hsQuarter : R / 8 ≤ 1 / 4 := by linarith
  have hvolOf := KLim.terminal_smallBall_volume_three F hK hdim hquarter
    (R / 8) hs hsQuarter
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        {y : Y.M | riemannianEDist I Y.basepoint y < ENNReal.ofReal (R / 8)} := by
    change ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ 3 ≤
      riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        {y : Y.M | riemannianEDistOf (I := I) Y.metric Y.basepoint y <
          ENNReal.ofReal (R / 8)} at hvolOf
    simpa only [hdim,
      riemannianEDistOf_eq_riemannianEDist (I := I) Y.metric hEnorm] using hvolOf
  have hcgt := intrInj_ge_vol_of_ball (I := I) Y.metric hEnorm Y.basepoint
    (K := 7) (ρ := (1 / 4 : ℝ)) (R := R)
    (by norm_num) hR hRQuarter hRpi hRm herror
    (r₀ := R / 8) (s := R / 8) hs hs (by linarith) (by linarith)
    (q := 0) (by norm_num) hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  rw [hhalf, hadd] at hcgt
  have hinj := (selectedCGTInjRadius_le_quotient (E := E) hK.kappa_pos.le hR).trans hcgt
  convert hinj using 1 <;> rfl

end OneFlow

section Sequence

variable [I.Boundaryless] (X : PointedFlowSeq.{u, uE, uH} (I := I)) {kappa : ℝ}

def klim_three_baseInjBound [NeZero (Module.finrank ℝ E)]
    (hK : ∀ i, KLim kappa (X.term i)) (hdim : Module.finrank ℝ E = 3)
    (hquarter : ∀ i,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint z <
          ENNReal.ofReal (1 / 4) → (X.term i).S.scalar 0 z ≤ 2) :
    FlowScaleInjectivityBound (I := I) X := by
  classical
  let hscale := exists_uniform_local_jacobi_scale
    (Module.finrank ℝ E) (R := (1 / 4 : ℝ)) (K := 7) (by norm_num) (by norm_num)
  let rJ : ℝ := hscale.choose
  have hrJ : 0 < rJ := hscale.choose_spec.1
  have hrJQuarter : rJ ≤ 1 / 4 := hscale.choose_spec.2.1
  have herror := hscale.choose_spec.2.2
  let R : ℝ := min rJ (Real.pi / Real.sqrt 7)
  have hR : 0 < R := lt_min hrJ (div_pos Real.pi_pos (by positivity))
  have hRj : R ≤ rJ := min_le_left _ _
  refine
    { ρ := selectedCGTInjRadius E kappa R
      pos := selectedCGTInjRadius_pos (E := E) (hK 0).kappa_pos hR
      bound := ?_ }
  intro i
  exact klim_terminal_hasInjRadiusAt (X.term i) (hK i) hdim (hquarter i)
    R hR (hRj.trans hrJQuarter) (min_le_right _ _)
    (fun a ha haR => herror a ha (haR.trans hRj))

omit [I.Boundaryless] in
theorem eventually_klim_three_rmNormSq_bound
    (hK : ∀ i, KLim kappa (X.term i)) (hdim : Module.finrank ℝ E = 3)
    (r : ℕ → ℝ)
    (hlocal : ∀ i,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint z <
          ENNReal.ofReal (r i) → (X.term i).S.scalar 0 z ≤ 2)
    (hexpand : Tendsto r atTop atTop) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ i in atTop,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ t ≤ (0 : ℝ), ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint z ≤
          ENNReal.ofReal A → (X.term i).rmNormSq (I := I) t z ≤ 12 := by
  filter_upwards [hexpand.eventually_gt_atTop A] with i hi
  let _ : TopologicalSpace (X.term i).M := (X.term i).topology
  let _ : ChartedSpace H (X.term i).M := (X.term i).charted
  let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
  intro t ht z hz
  have hscalar : (X.term i).S.scalar 0 z ≤ 2 :=
    hlocal i z (hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hA.trans_lt hi)).mpr hi))
  have hbound := KLim.rmNormSq_le_of_terminal_scalar_le (X.term i) (hK i) hdim ht z hscalar
  norm_num at hbound
  exact hbound

theorem exists_klim_three_ancient_limit
    (hD : X.D = ancientTimeInterval)
    (hK : ∀ i, KLim kappa (X.term i)) (hdim : Module.finrank ℝ E = 3)
    (r : ℕ → ℝ) (hlarge : ∀ i, 1 / 4 < r i)
    (hlocal : ∀ i,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint z <
          ENNReal.ofReal (r i) → (X.term i).S.scalar 0 z ≤ 2)
    (hexpand : Tendsto r atTop atTop) :
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I)
                  (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I)
                  (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I)
                  (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.smooth
              D.referenceMetric = D.limitMetric) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hquarter : ∀ i,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint z <
          ENNReal.ofReal (1 / 4) → (X.term i).S.scalar 0 z ≤ 2 := by
    intro i
    dsimp only
    intro z hz
    exact hlocal i z (hz.trans_le (ENNReal.ofReal_le_ofReal (hlarge i).le))
  have hcomplete : FlowMetricComplete (I := I) X := ⟨fun i t ht => (hK i).complete t ht⟩
  have hlocalInput : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ z : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint z ≤
            ENNReal.ofReal A → (X.term i).rmNormSq (I := I) t z ≤ K := by
    intro A hA T _hT
    refine ⟨12, by norm_num, ?_⟩
    filter_upwards [eventually_klim_three_rmNormSq_bound X hK hdim r hlocal hexpand hA.le]
      with i hi
    intro t ht z hz
    exact hi t ht.2 z hz
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
    simpa only [one_mul] using (hK i).metric_inner_le ht.2 le_rfl z v
  exact exists_local_ancient_flow_compactness X hD hcomplete
    (fun i => (hK i).connected) (klim_three_baseInjBound X hK hdim hquarter)
    hlocalInput hlowerInput

end Sequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
