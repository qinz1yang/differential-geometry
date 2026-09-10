import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderTranslationSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelCurvatureTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverCurvatureNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientCylinderSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private local instance ancientCylinderSphereNonempty : Nonempty SphereTwo :=
  ⟨⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩⟩
private local instance ancientCylinderSphereMeasurable : MeasurableSpace SphereTwo := borel SphereTwo
private local instance ancientCylinderSphereBorel : BorelSpace SphereTwo := ⟨rfl⟩
private local instance ancientCylinderSphereC1 : IsManifold (𝓡 2) 1 SphereTwo :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem ancientCylinder_sphere_norm_bound
    (h : SmoothRiemannianMetric (𝓡 2) SphereTwo) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : SphereTwo,
      normSq0S (I := 𝓡 2) h x 4 (metricRm04At (I := 𝓡 2) h x) ≤ K := by
  have hcont := normSq0S_cont (I := 𝓡 2) h (metricRm04 (I := 𝓡 2) h)
  obtain ⟨x, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.continuousOn
  exact ⟨_, normSq0S_nonneg (I := 𝓡 2) h x 4 (metricRm04At (I := 𝓡 2) h x),
    fun y => hmax (mem_univ y)⟩

private theorem ancientCylinder_sphere_norm_scale
    (h : SmoothRiemannianMetric (𝓡 2) SphereTwo) (c : ℝ) (hc : 0 < c) (x : SphereTwo) :
    normSq0S (I := 𝓡 2) (scaleMetric c hc h) x 4
        (metricRm04At (I := 𝓡 2) (scaleMetric c hc h) x) =
      (c⁻¹) ^ 2 * normSq0S (I := 𝓡 2) h x 4 (metricRm04At (I := 𝓡 2) h x) := by
  change normSq0S (I := 𝓡 2) (scaleMetric c hc h) x 4
    (metricRm04 (I := 𝓡 2) (scaleMetric c hc h) x) =
      (c⁻¹) ^ 2 * normSq0S (I := 𝓡 2) h x 4 (metricRm04 (I := 𝓡 2) h x)
  rw [metricRm_scale, normSq0S_scale, normSq0S_smul]
  field_simp [hc.ne']

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientCylinderBaseTopology : TopologicalSpace F.M := F.topology
local instance ancientCylinderBaseCharted : ChartedSpace H F.M := F.charted
local instance ancientCylinderBaseSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientCylinderBaseC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance ancientCylinderBaseT2 : T2Space F.M := F.t2
local instance ancientCylinderBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientCylinderBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance ancientCylinderBaseMeasurable : MeasurableSpace F.M := borel F.M
local instance ancientCylinderBaseBorel : BorelSpace F.M := ⟨rfl⟩
local instance ancientCylinderBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance ancientCylinderBaseSemilocallySimplyConnected : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem ancientKappa_fixed_cylinder_deck_translation_eq_zero {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (T : ℝ) (hT : 0 < T)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
          x v w + a * b)
    (gamma : FundamentalGroup F.M (default : F.M)) (A : SphereTwo ≃ SphereTwo)
    (c : ℝ) (hdeck : ∀ (x : SphereTwo) (s : ℝ),
      gamma • Psi (x, s) = Psi (A x, s + c)) : c = 0 := by
  by_contra hc
  let _ : ConnectedSpace F.M := hF.connected
  let _ : PathConnectedSpace F.M := PathConnectedSpace.of_locallyPathConnectedSpace
  have hkappa : 0 < kappa := hF.kappa_pos
  let h : SmoothRiemannianMetric (𝓡 2) SphereTwo :=
    roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  let _ : IsFiniteMeasure (riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace h
  let Harea : ℝ := (riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ).toReal
  have hHarea : 0 ≤ Harea := ENNReal.toReal_nonneg
  have hHreal : riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) h univ =
      ENNReal.ofReal Harea :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  obtain ⟨K, hK, hnorm⟩ := ancientCylinder_sphere_norm_bound h
  let B := K + 1
  have hB : 0 < B := by dsimp only [B]; linarith
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith
  have hKB : K ≤ B ^ 4 :=
    (by dsimp only [B]; linarith : K ≤ B).trans (le_self_pow₀ hB1 (by decide : 4 ≠ 0))
  let z := Real.sqrt (2 * T) + 2 * |c| * Harea * B ^ 3 / kappa + 1
  have hquot : 0 ≤ 2 * |c| * Harea * B ^ 3 / kappa := by positivity
  have hz : 0 < z := by dsimp only [z]; positivity
  have hzsqrt : Real.sqrt (2 * T) ≤ z := by dsimp only [z]; linarith
  have hzlarge : 2 * |c| * Harea * B ^ 3 < kappa * z := by
    have hlt : 2 * |c| * Harea * B ^ 3 / kappa < z := by
      dsimp only [z]
      linarith [Real.sqrt_nonneg (2 * T)]
    have h := (div_lt_iff₀ hF.kappa_pos).mp hlt
    simpa only [mul_comm] using h
  let t := T - z ^ 2 / 2
  have ht : t ≤ 0 := by
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg (2 * T)) hz.le).mpr hzsqrt
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * T)] at hsquare
    dsimp only [t]
    linarith
  have hscale : 2 * (T - t) = z ^ 2 := by dsimp only [t]; ring
  have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
  let hScaled := scaleMetric (z ^ 2) hzsq h
  let gP := Diffeomorph.pullbackMetricCross
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Psi
  have hprodLift : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        hScaled.inner x v w + a * b := by
    intro x s v w a b
    change (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        (scaleMetric (z ^ 2) hzsq h).inner x v w + a * b
    rw [hproduct t ht, hscale, scaleMetric_inner]
  have hprodGeneral : ∀ (p : SphereTwo × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = hScaled.inner p.1 v.1 w.1 + v.2 * w.2 := by
    intro p v w
    change (Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Psi).inner
        p v w = _
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hprodLift p.1 p.2 v.1 w.1 v.2 w.2
  have hprod : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      gP.inner (x, s) (v, a) (w, b) = hScaled.inner x v w + a * b :=
    fun x s v w a b => hprodGeneral (x, s) (v, a) (w, b)
  let r := z / B
  have hr : 0 < r := div_pos hz hB
  have hcurvature : ∀ x : F.M,
      r ^ 4 * normSq0S (I := I) (F.S.family.metric t) x 4
        (metricRm04At (I := I) (F.S.family.metric t) x) ≤ 1 := by
    intro x
    let x' : UniversalCover F.M :=
      ⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (default : F.M) x)⟩
    let p := Psi.symm x'
    have hp : UniversalCover.proj (Psi p) = x := by
      change UniversalCover.proj (Psi (Psi.symm x')) = x
      rw [Psi.apply_symm_apply]
      rfl
    have hnormPoint : normSq0S (I := I) (F.S.family.metric t) x 4
        (metricRm04At (I := I) (F.S.family.metric t) x) ≤ (z ^ 2)⁻¹ ^ 2 * K := by
      calc
        _ = normSq0S (I := I) (UniversalCover.liftedMetric (I := I) (F.S.family.metric t))
            (Psi p) 4 (metricRm04At (I := I)
              (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) (Psi p)) := by
          rw [metricRmNormSq_lifted, hp]
        _ = normSq0S (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p 4
            (metricRm04At (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p) :=
          (metricRmNormSq_pullbackCross
            (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Psi p).symm
        _ = normSq0S (I := 𝓡 2) hScaled p.1 4 (metricRm04At (I := 𝓡 2) hScaled p.1) :=
          metricRmNormSq_product_real_of_inner_eq hScaled gP hprod p.1 p.2
        _ = (z ^ 2)⁻¹ ^ 2 * normSq0S (I := 𝓡 2) h p.1 4
            (metricRm04At (I := 𝓡 2) h p.1) := ancientCylinder_sphere_norm_scale h (z ^ 2) hzsq p.1
        _ ≤ (z ^ 2)⁻¹ ^ 2 * K := mul_le_mul_of_nonneg_left (hnorm p.1) (sq_nonneg _)
    calc
      _ ≤ r ^ 4 * ((z ^ 2)⁻¹ ^ 2 * K) :=
        mul_le_mul_of_nonneg_left hnormPoint (pow_nonneg hr.le 4)
      _ = K / B ^ 4 := by dsimp only [r]; field_simp [hz.ne', hB.ne']
      _ ≤ 1 := (div_le_one (pow_pos hB 4)).mpr hKB
  let time : RealTimeInterval.FlowTime ancientTimeInterval := ⟨t, ht⟩
  let ball : FlowMetricBall (I := I) (M := F.M) F.S time := ⟨F.basepoint, r, hr⟩
  have hball : ball.IsSpatiallyRmControlled := by
    intro x _
    simpa only [ball, time, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      metricRm04_apply, SolutionOn.family] using hcurvature x
  have hlower := (hF.noncollapsed time ball hball).2
  change ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.family.metric t)
      (riemannianBallOf (I := I) (F.S.family.metric t) F.basepoint r) at hlower
  rw [hdim] at hlower
  have htotal := cylinderDeck_translation_total_volume_le
    (F.S.family.metric t) hScaled Psi hprodLift gamma A c hc hdeck
  have hvolscale : riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo) hScaled univ =
      ENNReal.ofReal (z ^ 2) * ENNReal.ofReal Harea := by
    change riemannianVolumeMeasure (I := 𝓡 2) (M := SphereTwo)
      (scaleMetric (z ^ 2) hzsq h) univ = _
    rw [surfaceVolume_scaleMetric h (by simp) (z ^ 2) hzsq, Measure.smul_apply, hHreal]
    rfl
  rw [hvolscale] at htotal
  have hvol := (hlower.trans (measure_mono (subset_univ _))).trans htotal
  have hreal : kappa * r ^ 3 ≤ (2 * |c|) * (z ^ 2 * Harea) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (2 * |c|) * (z ^ 2 * Harea))).mp
    simpa only [ENNReal.ofReal_mul hF.kappa_pos.le, ENNReal.ofReal_pow hr.le,
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * |c|), ENNReal.ofReal_mul hzsq.le] using hvol
  have hcancel : kappa * z ≤ 2 * |c| * Harea * B ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hreal (pow_nonneg hB.le 3)
    have hl : (kappa * r ^ 3) * B ^ 3 = (kappa * z) * z ^ 2 := by
      dsimp only [r]
      field_simp [hB.ne']
    have hrhs : ((2 * |c|) * (z ^ 2 * Harea)) * B ^ 3 =
        (2 * |c| * Harea * B ^ 3) * z ^ 2 := by ring
    rw [hl, hrhs] at h
    exact (mul_le_mul_iff_left₀ hzsq).mp h
  exact (not_le_of_gt hzlarge) hcancel

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
