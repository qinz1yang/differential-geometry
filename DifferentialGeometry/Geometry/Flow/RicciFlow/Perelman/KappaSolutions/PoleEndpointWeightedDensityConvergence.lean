import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MeasureConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientUniformWeightedDensityTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientWeightedClosedBallDensityTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityTails
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityMeasure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.tendsto_lintegral_poleEndpoint_sqrt_redLength_mul_redDensity
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)))
    (ell : P.M → ℝ) (hell : Continuous ell)
    (hconv : TendstoLocallyUniformly
      (fun k y => redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) y) (1 - t)) ell atTop) :
    (∀ y, 0 ≤ ell y) ∧
    Integrable (fun y => Real.sqrt (ell y) * Real.exp (-ell y -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
      (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)) ∧
    Tendsto (fun k => ∫⁻ y : F.M,
      ENNReal.ofReal (Real.sqrt (redLength ((U).term (phi (co.φ k))).S 0 p y (1 - t)) *
        redDensity ((U).term (phi (co.φ k))).S 0 p y (1 - t))
        ∂riemannianVolumeMeasure (I := I) (M := F.M)
          (((U).term (phi (co.φ k))).S.base.metric (-(1 - t)))) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (Real.sqrt (ell y) * Real.exp (-ell y -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨s, _, x, hx⟩ := (hancient 0).notFlat
    exact Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric s) x (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 s x) hx⟩
  have hlag : 0 < 1 - t := by linarith
  let f : ℝ → ℝ := fun r => Real.sqrt r * Real.exp (-r -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hf : Continuous f := by dsimp only [f]; fun_prop
  let density (k : ℕ) (y : F.M) :=
    Real.sqrt (redLength ((U).term (phi (co.φ k))).S 0 p y (1 - t)) *
      redDensity ((U).term (phi (co.φ k))).S 0 p y (1 - t)
  have hDensity (k : ℕ) : Measurable (density k) := by
    have hcost := continuous_redLength_of_ancient ((U).term (phi (co.φ k)))
      (hancient (phi (co.φ k))) p hlag
    change Measurable (fun y => f (redLength ((U).term (phi (co.φ k))).S 0 p y (1 - t)))
    exact (hf.comp hcost).measurable
  have hnonneg (k : ℕ) (y : P.M) :
      0 ≤ redLength ((U).term (phi (co.φ k))).S 0 p (Phi.map (co.φ k) y) (1 - t) := by
    obtain ⟨B, hB⟩ := (hancient (phi (co.φ k))).globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg _ 0 hlag.le
    intro s hs w
    simpa only [zero_sub] using (hB (-s) (by
      rw [ancientTimeInterval_carrier]
      exact neg_nonpos.mpr hs.1) w).1
  have hellNonneg (y : P.M) : 0 ≤ ell y :=
    ge_of_tendsto (hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ y))
      (Eventually.of_forall fun k => hnonneg k y)
  have hdensityConv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) (fun y => f (ell y)) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_tendsto] at hconv ⊢
    intro x
    have hleft : Tendsto (fun z : ℕ × P.M => ell z.2) (atTop ×ˢ 𝓝 x) (𝓝 (ell x)) :=
      hell.continuousAt.tendsto.comp tendsto_snd
    have hright : Tendsto
        (fun z : ℕ × P.M => redLength ((U).term (phi (co.φ z.1))).S 0 p
          (Phi.map (co.φ z.1) z.2) (1 - t)) (atTop ×ˢ 𝓝 x) (𝓝 (ell x)) :=
      hleft.congr_uniformity (hconv x)
    have hpair := (hf.continuousAt.tendsto.comp hleft).prodMk_nhds
      (hf.continuousAt.tendsto.comp hright)
    simpa only [f, density, redDensity, Function.comp_def] using
      hpair.mono_right (nhds_le_uniformity (f (ell x)))
  let K : ℝ := max ((1 - t) ^ 2) ((1 / (1 - t)) ^ 2)
  have hK : 0 ≤ K := (sq_nonneg (1 - t)).trans (le_max_left _ _)
  have hcost (i : ℕ) : redLength ((U).term i).S 0 p (q i) (1 - t) ≤ K * A := by
    have hratio := ancient_redLength_le_mul_time_ratio ((U).term i) (hancient i)
      p (q i) zero_lt_one hlag
    simp only [div_one] at hratio
    exact hratio.trans (mul_le_mul_of_nonneg_left (hbase i) hK)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_ancient_sqrt_redLength_mul_redDensity_integral_bound
    (I := I) (a := 1 - t) (b := 1 - t) (B := K * A) hlag le_rfl
  have htime : -(1 - t) = t - 1 := by ring
  have hmass (k : ℕ) :
      (∫⁻ y : ((Y).term (phi (co.φ k))).M, ENNReal.ofReal (density k y)
        ∂riemannianVolumeMeasure (I := I) (M := ((Y).term (phi (co.φ k))).M)
          (((Y).term (phi (co.φ k))).S.base.metric t)) =
      ∫⁻ y : F.M, ENNReal.ofReal (density k y)
        ∂riemannianVolumeMeasure (I := I) (M := F.M)
          (((U).term (phi (co.φ k))).S.base.metric (-(1 - t))) := by
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift, htime]
    rfl
  have htail (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ r : ℝ, 0 ≤ r ∧ ∀ᶠ k in atTop,
      (∫⁻ y in (riemannianClosedBallOf (I := I) (M := F.M)
        (((Y).term (phi (co.φ k))).S.base.metric t) (Phi.map (co.φ k) P.basepoint) r)ᶜ,
        ENNReal.ofReal (density k y)
          ∂riemannianVolumeMeasure (I := I) (M := ((Y).term (phi (co.φ k))).M)
            (((Y).term (phi (co.φ k))).S.base.metric t)) < ε := by
    obtain ⟨N, hN⟩ := exists_uniform_ancient_sqrt_redLength_mul_redDensity_closedBall_compl_bound
      (I := I) (a := 1 - t) (b := 1 - t) (B := K * A) hlag le_rfl hε
    refine ⟨N, Nat.cast_nonneg N, Eventually.of_forall ?_⟩
    intro k
    have hcenter : Phi.map (co.φ k) P.basepoint = q (phi (co.φ k)) :=
      Phi.basepoint_map (co.φ k)
    rw [hcenter, poleEndpointRescaledFlowSeq_metric_eq_shift, ← htime]
    exact hN ((U).term (phi (co.φ k))) (hancient (phi (co.φ k))) p
      (q (phi (co.φ k))) ⟨le_rfl, le_rfl⟩ (hcost (phi (co.φ k)))
  have hmain := HalfLineMetricConvergenceData.tendsto_lintegral_density_of_ball_tails
    Phi co ht hcomplete P.basepoint density (fun y => f (ell y))
    hDensity (hf.comp hell) hdensityConv hC
    (fun k => (hmass k).le.trans
      (hbound ((U).term (phi (co.φ k))) (hancient (phi (co.φ k))) p
        (q (phi (co.φ k))) ⟨le_rfl, le_rfl⟩ (hcost (phi (co.φ k))))) htail
  refine ⟨hellNonneg, ?_, ?_⟩
  · refine ⟨(hf.comp hell).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)))).2
    exact hmain.1.trans_lt hC
  · simpa only [hmass, f, density] using hmain.2

end DifferentialGeometry.CheegerGromovCompactness

end
