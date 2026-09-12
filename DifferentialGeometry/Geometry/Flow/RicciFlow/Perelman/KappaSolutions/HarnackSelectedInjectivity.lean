import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLocalGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCGTInjectivity

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
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance selectedInjMeasurableE : MeasurableSpace E := borel E
private local instance selectedInjBorelE : BorelSpace E := ⟨rfl⟩

def selectedCGTDenominator (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R : ℝ) : ℝ :=
  1 + ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ).toReal * hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8) +
    ((volume : Measure E).toSphere Set.univ).toReal *
      hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4)


def selectedCGTInjRadius (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (kappa R : ℝ) : ℝ :=
  (R / 16) * (kappa * (R / 8) ^ Module.finrank ℝ E) / selectedCGTDenominator E R

theorem selectedCGTDenominator_pos {R : ℝ} (hR : 0 < R) :
    0 < selectedCGTDenominator E R := by
  have hsmall : 0 ≤ hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8) :=
    (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hlarge : 0 ≤ hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4) :=
    (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  unfold selectedCGTDenominator
  positivity

theorem selectedCGTInjRadius_pos {kappa R : ℝ} (hκ : 0 < kappa) (hR : 0 < R) :
    0 < selectedCGTInjRadius E kappa R := by
  unfold selectedCGTInjRadius
  exact div_pos (mul_pos (by positivity) (mul_pos hκ (pow_pos (by positivity) _)))
    (selectedCGTDenominator_pos (E := E) hR)

variable [NeZero (Module.finrank ℝ E)]

theorem selectedCGTInjRadius_le_quotient {kappa R : ℝ}
    (hκ : 0 ≤ kappa) (hR : 0 < R) :
    ENNReal.ofReal (selectedCGTInjRadius E kappa R) ≤
      ENNReal.ofReal (R / 16) *
        (ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E) /
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
            Set.univ * ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8)) +
          (volume : Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4))) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  let _ : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Module.nontrivial_of_finrank_pos hfin
  let b : ℝ := ((volume : Measure (EuclideanSpace ℝ
    (Fin (Module.finrank ℝ E)))).toSphere Set.univ).toReal
  let p : ℝ := ((volume : Measure E).toSphere Set.univ).toReal
  let m : ℝ := hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 8)
  let l : ℝ := hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) (R / 4)
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hm : 0 ≤ m := (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hl : 0 ≤ l := (hyperbolicRadialVolume_pos (by norm_num : (0 : ℝ) ≤ 0) (by positivity)).le
  have hbeq : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere
      Set.univ = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hpeq : (volume : Measure E).toSphere Set.univ = ENNReal.ofReal p :=
    (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
  have hden :
      (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ *
          ENNReal.ofReal m + (volume : Measure E).toSphere Set.univ * ENNReal.ofReal l ≤
        ENNReal.ofReal (selectedCGTDenominator E R) := by
    rw [hbeq, hpeq, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hp,
      ← ENNReal.ofReal_add (mul_nonneg hb hm) (mul_nonneg hp hl)]
    apply ENNReal.ofReal_le_ofReal
    change b * m + p * l ≤ 1 + b * m + p * l
    linarith
  rw [selectedCGTInjRadius,
    ENNReal.ofReal_div_of_pos (selectedCGTDenominator_pos (E := E) hR),
    ENNReal.ofReal_mul (by positivity : 0 ≤ R / 16), ENNReal.ofReal_mul hκ,
    ENNReal.ofReal_pow (by positivity : 0 ≤ R / 8)]
  exact ENNReal.div_le_div le_rfl hden

variable [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance selectedInjTopology : TopologicalSpace F.M := F.topology
local instance selectedInjCharted : ChartedSpace H F.M := F.charted
local instance selectedInjSmooth : IsManifold I ∞ F.M := F.smooth
local instance selectedInjC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance selectedInjSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance selectedInjT2 : T2Space F.M := F.t2
local instance selectedInjTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem selectedInj_edist_comm (g : SmoothRiemannianMetric I F.M) (y z : F.M) :
    riemannianEDistOf (I := I) g y z = riemannianEDistOf (I := I) g z y := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I y z = Manifold.riemannianEDist I z y
  exact Manifold.riemannianEDist_comm (I := I) (x := y) (y := z)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem terminalCurvatureNormalizedFlowSeq_smallBall_volume (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hlarge : 1 / 2 < r * Real.sqrt (F.S.scalar 0 (x i)))
    {s : ℝ} (hs : 0 < s) (hsHalf : s ≤ 1 / 2) :
    ENNReal.ofReal kappa * ENNReal.ofReal s ^ Module.finrank ℝ E ≤
      @riemannianVolumeMeasure E _ _ _ H _ I F.M F.topology F.charted F.smooth
        F.t2 F.sigmaCompact
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        {z : F.M | @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
          (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
          (x i) z < ENNReal.ofReal s} := by
  let g : SmoothRiemannianMetric I F.M :=
    scaleMetric (F.S.scalar 0 (x i)) (hQ i)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
  let B := PointedFlowData.baseFlowBall (I := I)
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i)
    (by change (0 : ℝ) ≤ 0; exact le_rfl) s hs
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    change F.M at z
    have hz0 : @riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.base.metric 0)
        (x i) z < ENNReal.ofReal s := hz
    have hzreal : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
        z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i)) := by
      change (riemannianEDistOf (I := I) g z (x i)).toReal <
        r * Real.sqrt (F.S.scalar 0 (x i))
      change riemannianEDistOf (I := I) g (x i) z < ENNReal.ofReal s at hz0
      exact (congrArg ENNReal.toReal (selectedInj_edist_comm F g z (x i))).trans_lt
        (((ENNReal.toReal_lt_of_lt_ofReal hz0).trans_le hsHalf).trans hlarge)
    have hRm := terminalCurvatureNormalizedFlowSeq_rmNormSq_bound
      F hK hdim x hQ i r hlocal (s := 0) le_rfl z hzreal
    have hpow : s ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hs.le hsHalf 4
    have hmul := mul_le_mul_of_nonneg_left hRm (pow_nonneg hs.le 4)
    change s ^ 4 *
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) 0 z ≤ 1
    nlinarith
  have hnc := terminalCurvatureNormalizedFlowSeq_noncollapsed F hK x hQ i
    (⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩) B hcontrol
  exact hnc.2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def terminalCurvatureNormalizedFlowSeq_baseInjBound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hlarge : ∀ i, 1 / 2 < r i * Real.sqrt (F.S.scalar 0 (x i))) :
    FlowScaleInjectivityBound (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ) := by
  classical
  let hscale := exists_uniform_local_jacobi_scale
    (Module.finrank ℝ E) (R := (1 / 2 : ℝ)) (K := 4) (by norm_num) (by norm_num)
  let rJ : ℝ := hscale.choose
  have hrJ : 0 < rJ := hscale.choose_spec.1
  have hrJHalf : rJ ≤ 1 / 2 := hscale.choose_spec.2.1
  have herror := hscale.choose_spec.2.2
  let R : ℝ := min rJ (Real.pi / Real.sqrt 4)
  have hR : 0 < R := lt_min hrJ (div_pos Real.pi_pos (by positivity))
  have hRj : R ≤ rJ := min_le_left _ _
  have hRHalf : R ≤ 1 / 2 := hRj.trans hrJHalf
  have hRpi : R ≤ Real.pi / Real.sqrt 4 := min_le_right _ _
  have hs : 0 < R / 8 := by positivity
  have hsHalf : R / 8 ≤ 1 / 2 := by linarith
  have hη : 0 < selectedCGTInjRadius E kappa R :=
    selectedCGTInjRadius_pos (E := E) hK.kappa_pos hR
  let Y := (terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)
  refine { ρ := selectedCGTInjRadius E kappa R, pos := hη, bound := ?_ }
  intro i
  refine ⟨hη, ?_⟩
  intro hcomplete
  let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
  let _ : ChartedSpace H (Y.obj i).M := (Y.obj i).charted
  let _ : IsManifold I ∞ (Y.obj i).M := (Y.obj i).smooth
  let _ : IsManifold I 1 (Y.obj i).M :=
    IsManifold.of_le (I := I) (M := (Y.obj i).M) (n := ∞) (by decide)
  let _ : T2Space (Y.obj i).M := (Y.obj i).t2
  let _ : SigmaCompactSpace (Y.obj i).M := (Y.obj i).sigmaCompact
  let _ : T2Space (TangentBundle I (Y.obj i).M) := (Y.obj i).t2TangentBundle
  let _ : RiemannianBundle (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle (I := I)
  let _ : (y : (Y.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (Y.obj i).riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle_cont (I := I)
  let _ : EMetricSpace (Y.obj i).M := (Y.obj i).emetricSpace (I := I)
  have : IsRiemannianManifold I (Y.obj i).M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace (Y.obj i).M := MetricComplete.complete (I := I) (Y.obj i) hcomplete
  let _ : ConnectedSpace (Y.obj i).M := hK.connected
  let hEnorm : IsMetricNorm (I := I) (Y.obj i).metric := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (Y.obj i).metric y v
  let g : SmoothRiemannianMetric I F.M :=
    scaleMetric (F.S.scalar 0 (x i)) (hQ i)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
  have hRm : ∀ y : (Y.obj i).M,
      riemannianEDist I (Y.obj i).basepoint y < ENNReal.ofReal (1 / 2) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (Y.obj i).metric y 4
        (metricRm04At (I := I) (Y.obj i).metric y)) ≤ 4 := by
    intro y hy
    have hyOf : @riemannianEDistOf E _ _ H _ I (Y.obj i).M
        (Y.obj i).topology (Y.obj i).charted (Y.obj i).smooth
        (Y.obj i).metric (Y.obj i).basepoint y <
        ENNReal.ofReal (1 / 2) := by
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      exact hy
    change F.M at y
    change riemannianEDistOf (I := I) g (x i) y < ENNReal.ofReal (1 / 2) at hyOf
    have hyreal : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
        y (x i)).toReal <
        r i * Real.sqrt (F.S.scalar 0 (x i)) := by
      change (riemannianEDistOf (I := I) g y (x i)).toReal <
        r i * Real.sqrt (F.S.scalar 0 (x i))
      exact (congrArg ENNReal.toReal (selectedInj_edist_comm F g y (x i))).trans_lt
        ((ENNReal.toReal_lt_of_lt_ofReal hyOf).trans (hlarge i))
    have hsq := terminalCurvatureNormalizedFlowSeq_rmNormSq_bound
      F hK hdim x hQ i (r i) (hlocal i) (s := 0) le_rfl y hyreal
    change Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04 (I := I) g y) ≤ 16 at hsq
    rw [metricRm04_apply] at hsq
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y)) ≤ 4
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hfour : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [hfour]
    exact hsq
  have hnonneg := terminalCurvatureNormalizedFlowSeq_nonnegativeCurvatureOperator
    F hK x hQ i (s := 0) le_rfl
  have hRic : RicciBoundedBelow (I := I) (Y.obj i).metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    intro y v
    change F.M at y
    change TangentSpace I y at v
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) g y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) g y).mpr
      intro m c a b
      have hraw := hnonneg y m c a b
      change 0 ≤ ∑ j, ∑ k, c j * c k *
        (metricRm04 (I := I) g y) (vec4 (a j) (b j) (b k) (a k)) at hraw
      simpa only [metricRm04StandardAt_apply, metricRm04_apply] using hraw
    have h := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) g y hcone v
    change (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) *
      g.inner y v v ≤ ricciTensor (I := I) g y v v
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, neg_zero, zero_mul,
      metricRicciAt_apply_eq_ricciTensor] using h
  have hvolOf := terminalCurvatureNormalizedFlowSeq_smallBall_volume
    F hK hdim x hQ i (r i) (hlocal i) (hlarge i) hs hsHalf
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDist I (Y.obj i).basepoint y <
          ENNReal.ofReal (R / 8)} := by
    change ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDistOf (I := I) (Y.obj i).metric
          (Y.obj i).basepoint y < ENNReal.ofReal (R / 8)} at hvolOf
    simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      using hvolOf
  have hcgt := intrInj_ge_vol_of_ball (I := I) (Y.obj i).metric hEnorm
    (Y.obj i).basepoint (K := 4) (ρ := (1 / 2 : ℝ)) (R := R)
    (by norm_num) hR hRHalf hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRj))
    (r₀ := R / 8) (s := R / 8) hs hs (by linarith) (by linarith)
    (q := 0) (by norm_num) hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  rw [hhalf, hadd] at hcgt
  have hinj := (selectedCGTInjRadius_le_quotient (E := E) hK.kappa_pos.le hR).trans hcgt
  simpa only [Y, PointedRiemannianManifold.intrinsicInjRadius] using hinj

theorem exists_terminalCurvatureNormalizedFlowSeq_baseInjBound_tail (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop) :
    ∃ N : ℕ, Nonempty (FlowScaleInjectivityBound (I := I)
      (terminalCurvatureNormalizedFlowSeq F hK (fun i => x (N + i))
        (fun i => hQ (N + i)))) := by
  have hevent : ∀ᶠ i in atTop, 1 / 2 < r i * Real.sqrt (F.S.scalar 0 (x i)) :=
    hexpand (eventually_gt_atTop (1 / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ⟨terminalCurvatureNormalizedFlowSeq_baseInjBound F hK hdim
    (fun i => x (N + i)) (fun i => r (N + i)) (fun i => hQ (N + i))
    (fun i => hlocal (N + i)) ?_⟩⟩
  intro i
  exact hN (N + i) (Nat.le_add_right N i)

theorem exists_harnack_terminal_blowup_with_baseInjBound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (hunbounded : ¬ BddAbove (Set.range (F.S.scalar 0))) (p : F.M) :
    ∃ (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)),
      (∀ i, 0 < r i ∧ r i ≤ 1 / 2) ∧
      Tendsto (fun i => F.S.scalar 0 (x i)) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop ∧
      Tendsto (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
        atTop atTop ∧
      Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
        (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) atTop atTop ∧
      (∀ i z, (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i)) ∧
      Nonempty (FlowScaleInjectivityBound (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ)) ∧
      (∀ i, PointedFlowScalarAtBase (I := I)
        ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i) 1) := by
  obtain ⟨x, r, hQ, hr, hQescape, _hQr, hexpand, hdist, hscaledDist,
    _hratio, hlocal, _hbackward, _hclosed⟩ :=
    exists_harnack_terminal_blowup_sequence F hK hunbounded p
  obtain ⟨N, hInj⟩ := exists_terminalCurvatureNormalizedFlowSeq_baseInjBound_tail
    F hK hdim x r hQ hlocal hexpand
  have hshift : Tendsto (fun i : ℕ => N + i) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N
  refine ⟨(fun i => x (N + i)), (fun i => r (N + i)), (fun i => hQ (N + i)),
    (fun i => hr (N + i)), ?_, ?_, ?_, ?_, (fun i => hlocal (N + i)), hInj, ?_⟩
  · simpa only [Function.comp_def] using hQescape.comp hshift
  · simpa only [Function.comp_def] using hexpand.comp hshift
  · simpa only [Function.comp_def] using hdist.comp hshift
  · simpa only [Function.comp_def] using hscaledDist.comp hshift
  · intro i
    exact terminalCurvatureNormalizedFlowSeq_scalar_base F hK
      (fun j => x (N + j)) (fun j => hQ (N + j)) i

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
