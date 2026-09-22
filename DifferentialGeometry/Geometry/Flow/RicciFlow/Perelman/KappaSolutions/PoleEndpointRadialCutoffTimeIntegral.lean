import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointRadialCutoffFluxIntegrable
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GradientFlux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineGramContinuity
import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
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

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace HalfLineMetricConvergenceData

private theorem continuousOn_chartGramMatrix_time_sub
    {X : PointedFlowSeq (I := I)} (Phi : PointedCGHMaps X P phi)
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : Iic (0 : ℝ) ⊆ X.D.carrier) {a c : ℝ} (ha : 1 ≤ a)
    (alpha : P.M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun v : Ioo a c × P.M =>
      Tensor.Coordinates.chartGramMatrix (co.gInf (1 - (v.1 : ℝ))) alpha v.2 i j)
      (univ ×ˢ (chartAt H alpha).source) := by
  have hc := continuousOn_chartGramMatrix
    (I := I) (X := X) (P := P) (phi := phi) Phi
    (R := R) (bf := bf) (hsrc := hsrc) (htgt := htgt) co hcarrier alpha i j
  have hmap : Continuous (fun v : Ioo a c × P.M => (1 - (v.1 : ℝ), v.2)) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  have hmaps : MapsTo (fun v : Ioo a c × P.M => (1 - (v.1 : ℝ), v.2))
      (univ ×ˢ (chartAt H alpha).source)
      (Iic (0 : ℝ) ×ˢ (chartAt H alpha).source) := by
    intro v hv
    exact ⟨sub_nonpos.mpr (ha.trans v.1.property.1.le), hv.2⟩
  have hcomp := ContinuousOn.comp'
    (g := fun q : ℝ × P.M =>
      Tensor.Coordinates.chartGramMatrix (co.gInf q.1) alpha q.2 i j)
    (f := fun v : Ioo a c × P.M => (1 - (v.1 : ℝ), v.2))
    (s := univ ×ˢ (chartAt H alpha).source)
    (t := Iic (0 : ℝ) ×ˢ (chartAt H alpha).source)
    hc hmap.continuousOn hmaps
  exact hcomp

private theorem integrable_integral_gaussian_gradient_pairing
    {a c : ℝ} (ha : 1 ≤ a) (qref : SmoothRiemannianMetric I P.M)
    (G : Ioo a c → SmoothRiemannianMetric I P.M)
    (ell : C(P.M × Ici (1 : ℝ), ℝ)) (cutoff : P.M → ℝ) (hcutoff : Continuous cutoff)
    (hgram : ∀ (alpha : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun v : Ioo a c × P.M =>
        Tensor.Coordinates.chartGramMatrix (G v.1) alpha v.2 i j)
        (univ ×ˢ (chartAt H alpha).source)) (C : ℝ)
    (hbound : ∀ s : Ioo a c,
      ∫ y, |Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ))) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (G s).inner y (gradientFun (G s)
          (fun x => ell (x, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ)))) y)
          (gradientFun (G s) cutoff y)|
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s) ≤ C) :
    let f : Ioo a c → P.M → ℝ := fun s y =>
      ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ)))
    let w : Ioo a c × P.M → ℝ := fun v => Real.exp (-f v.1 v.2 -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (v.1 : ℝ) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
    let flux : Ioo a c → P.M → ℝ := fun s y =>
      w (s, y) * (G s).inner y (gradientFun (G s) (f s) y)
        (gradientFun (G s) cutoff y)
    Integrable (fun s => ∫ y, flux s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)) volume ∧
      |∫ s : Ioo a c, ∫ y, flux s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)| ≤
        C * volume.real (univ : Set (Ioo a c)) := by
  intro f w flux
  have hf : Continuous (Function.uncurry f) :=
    ell.continuous.comp (continuous_snd.prodMk
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _))
  have hh : Continuous (Function.uncurry (fun _ : Ioo a c => cutoff)) :=
    hcutoff.comp continuous_snd
  have hw : Continuous w := by
    have hlog : Continuous (fun v : Ioo a c × P.M => Real.log (v.1 : ℝ)) :=
      (continuous_subtype_val.comp continuous_fst).log (fun v =>
        ne_of_gt (zero_lt_one.trans_le (ha.trans v.1.property.1.le)))
    exact Real.continuous_exp.comp
      ((hf.neg.sub (continuous_const.mul hlog)).sub continuous_const)
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology P.M := ChartedSpace.secondCountable_of_sigmaCompact H P.M
  let : IsFiniteMeasure (volume : Measure (Ioo a c)) := ⟨by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
    exact measure_Ioo_lt_top⟩
  obtain ⟨hi, hb⟩ := integrable_integral_mul_inner_gradientFun_family
    qref G volume f (fun _ => cutoff) w hf hh hgram hw.aestronglyMeasurable
    (integrable_const C) (Eventually.of_forall hbound)
  have hconst : (∫ _ : Ioo a c, C) = C * volume.real (univ : Set (Ioo a c)) := by
    rw [integral_const, smul_eq_mul, mul_comm]
  rw [hconst] at hb
  exact ⟨hi, hb⟩

theorem exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ell : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ell atTop)
    {a c : ℝ} (ha : 1 ≤ a) (hac : a ≤ c)
    (hcomplete : ∀ s ∈ Icc a c, MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : P.M, ∀ r : ℝ, 0 < r →
      let flux := fun (s : Ioo a c) (y : P.M) =>
        Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ))) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (co.gInf (1 - (s : ℝ))).inner y
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (fun x => ell (x, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ)))) y)
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (radialDistanceCutoff (co.gInf (1 - a)) z r) y)
      (∀ s, Integrable (flux s)
        (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ))))) ∧
      Integrable (fun s : Ioo a c => ∫ y, flux s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) volume ∧
      |∫ s : Ioo a c, ∫ y, flux s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))| ≤
        (C / r) * volume.real (univ : Set (Ioo a c)) := by
  obtain ⟨C, hC, hlintegral⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_lintegral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  obtain ⟨_, _, hspatial⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  refine ⟨C, hC, ?_⟩
  intro z r hr
  let G : Ioo a c → SmoothRiemannianMetric I P.M := fun s => co.gInf (1 - (s : ℝ))
  let f : Ioo a c → P.M → ℝ := fun s y =>
    ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ)))
  let w : Ioo a c × P.M → ℝ := fun v => Real.exp (-f v.1 v.2 -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (v.1 : ℝ) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let cutoff := radialDistanceCutoff (co.gInf (1 - a)) z r
  let flux : Ioo a c → P.M → ℝ := fun s y =>
    w (s, y) * (G s).inner y (gradientFun (G s) (f s) y)
      (gradientFun (G s) cutoff y)
  change (∀ s, Integrable (flux s) (riemannianVolumeMeasure (I := I) (M := P.M) (G s))) ∧
    Integrable (fun s => ∫ y, flux s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)) volume ∧
    |∫ s : Ioo a c, ∫ y, flux s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)| ≤
      (C / r) * volume.real (univ : Set (Ioo a c))
  have hfi (s : Ioo a c) : Integrable (flux s)
      (riemannianVolumeMeasure (I := I) (M := P.M) (G s)) :=
    (hspatial z ⟨(s : ℝ), ha.trans s.property.1.le⟩
      ⟨s.property.1.le, s.property.2.le⟩ r hr).1
  have hnorm (s : Ioo a c) :
      (∫ y, |flux s y| ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)) ≤ C / r := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hlintegral z ⟨(s : ℝ), ha.trans s.property.1.le⟩
        ⟨s.property.1.le, s.property.2.le⟩ r hr)
    rw [ENNReal.toReal_ofReal (div_nonneg hC hr.le)] at hb
    have heq := integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y => abs_nonneg (flux s y)) (hfi s).abs.aestronglyMeasurable
    exact heq.trans_le hb
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  have hcutoff : Continuous cutoff :=
    continuous_radialDistanceCutoff (co.gInf (1 - a)) z hr
  have hgram : ∀ (alpha : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun v : Ioo a c × P.M =>
        Tensor.Coordinates.chartGramMatrix (G v.1) alpha v.2 i j)
        (univ ×ˢ (chartAt H alpha).source) :=
    fun alpha i j => continuousOn_chartGramMatrix_time_sub Phi co
      (fun _ ht => ht) ha alpha i j
  exact ⟨hfi, integrable_integral_gaussian_gradient_pairing ha
    (co.gInf (1 - a)) G ell cutoff hcutoff hgram (C / r) hnorm⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
