import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointWeightedRadialFluxLimit
import DifferentialGeometry.Analysis.Integration.Integral.WeightedFluxLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSelectedDensityIntegrable
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineCutoffMass
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.CutoffLimit
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact


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

private theorem integrable_deriv_and_integral_eq_zero_of_tsupport
    {η : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hη : ContDiff ℝ 1 η) (hηsupp : tsupport η ⊆ Ioo a c) :
    Integrable (deriv η) (volume.restrict (Ioc a c)) ∧
      (∫ t in Ioc a c, deriv η t) = 0 ∧
      Integrable (fun t : Ioo a c => deriv η (t : ℝ)) ∧
      (∫ t : Ioo a c, deriv η (t : ℝ)) = 0 := by
  have hηa : η a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ha => (lt_irrefl a) (hηsupp ha).1)
  have hηc : η c = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hc => (lt_irrefl c) (hηsupp hc).2)
  have hD : IntervalIntegrable (deriv η) volume a c :=
    hη.continuous_deriv_one.intervalIntegrable a c
  have hDIoc : IntegrableOn (deriv η) (Ioc a c) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mp hD
  have hDIoo : IntegrableOn (deriv η) (Ioo a c) volume :=
    hDIoc.mono_set Ioo_subset_Ioc_self
  have hzero : (∫ t in Ioc a c, deriv η t) = 0 := by
    rw [← intervalIntegral.integral_of_le hac,
      intervalIntegral.integral_deriv_eq_sub (fun _ _ => hη.differentiable one_ne_zero _) hD,
      hηa, hηc, sub_self]
  have hDsub : Integrable (fun t : Ioo a c => deriv η (t : ℝ)) := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hDIoo
  refine ⟨hDIoc, hzero, hDsub, ?_⟩
  calc
    (∫ t : Ioo a c, deriv η (t : ℝ)) = ∫ t in Ioo a c, deriv η t :=
      integral_subtype measurableSet_Ioo (deriv η)
    _ = ∫ t in Ioc a c, deriv η t := integral_Ioc_eq_integral_Ioo.symm
    _ = 0 := hzero

private theorem integrable_and_integral_time_transport {a c : ℝ}
    (f : ℝ → ℝ) (fI : Ioo a c → ℝ)
    (hmatch : ∀ t : Ioo a c, fI t = f (t : ℝ)) :
    (Integrable f (volume.restrict (Ioc a c)) ↔ Integrable fI volume) ∧
      (∫ t in Ioc a c, f t) = ∫ t : Ioo a c, fI t := by
  have hfun : fI = (fun t : Ioo a c => f (t : ℝ)) := funext hmatch
  subst fI
  constructor
  · rw [← restrict_Ioo_eq_restrict_Ioc]
    exact integrableOn_iff_comap_subtypeVal measurableSet_Ioo
  · rw [integral_Ioc_eq_integral_Ioo]
    exact (integral_subtype measurableSet_Ioo f).symm

theorem tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass
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
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (ellG : P.M × ℝ → ℝ)
    (hagree : ∀ (s : Ioo a c) (x : P.M),
      ellG (x, (s : ℝ)) = ell (x, ⟨(s : ℝ), ha.trans s.property.1.le⟩))
    (m : ℝ)
    (hmass : ∀ᵐ s : Ioo a c, (∫ y,
      Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ))) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) = m)
    (z : P.M) (eta : ℝ → ℝ) (heta : ContDiff ℝ 1 eta)
    (hetasupp : tsupport eta ⊆ Ioo a c)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {radii : ι → ℝ} (hradii : Tendsto radii l atTop) :
    let residual := fun (i : ι) (s : ℝ) (y : P.M) =>
      Real.exp (-ellG (y, s) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (deriv (fun t => eta t * radialDistanceCutoff (co.gInf (1 - a)) z (radii i) y) s +
          (co.gInf (1 - s)).inner y
            (gradientFun (co.gInf (1 - s)) (fun x => ellG (x, s)) y)
            (gradientFun (co.gInf (1 - s))
              (fun x => eta s * radialDistanceCutoff (co.gInf (1 - a)) z (radii i) x) y))
    Tendsto (fun i => ∫ s in Ioc a c, ∫ y, residual i s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) l (𝓝 0) ∧
      ∀ᶠ i in l,
        (∀ᵐ s ∂volume.restrict (Ioc a c), Integrable (residual i s)
          (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s)))) ∧
        Integrable (fun s => ∫ y, residual i s y
          ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s)))
          (volume.restrict (Ioc a c)) := by
  intro residual
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : IsFiniteMeasure (volume : Measure (Ioo a c)) := ⟨by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
    exact measure_Ioo_lt_top⟩
  let μ : Measure ℝ := volume.restrict (Ioc a c)
  let g : ℝ → SmoothRiemannianMetric I P.M := fun s => co.gInf (1 - s)
  let ν : ℝ → Measure P.M := fun s => riemannianVolumeMeasure (I := I) (M := P.M) (g s)
  let w : ℝ × P.M → ℝ := fun v => Real.exp (-ellG (v.2, v.1) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log v.1 -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let X : ℝ → (y : P.M) → TangentSpace I y :=
    fun s => gradientFun (g s) (fun x => ellG (x, s))
  let χ : ι → P.M → ℝ := fun i => radialDistanceCutoff (co.gInf (1 - a)) z (radii i)
  let ellS : Ioo a c → P.M → ℝ := fun s y =>
    ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ)))
  let u : Ioo a c → P.M → ℝ := fun s y => Real.exp (-ellS s y -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let flux : ι → Ioo a c → P.M → ℝ := fun i s y =>
    u s y * (g s).inner y (gradientFun (g s) (ellS s) y) (gradientFun (g s) (χ i) y)
  have hw (s : Ioo a c) : (fun y => w ((s : ℝ), y)) = u s := by
    funext y
    dsimp only [w, u, ellS]
    rw [hagree s y]
  have hw_apply (s : Ioo a c) (y : P.M) : w ((s : ℝ), y) = u s y :=
    congrFun (hw s) y
  have hX (s : Ioo a c) : X s = gradientFun (g s) (ellS s) := by
    have hslices : (fun y => ellG (y, (s : ℝ))) = ellS s := funext (hagree s)
    dsimp only [X]
    rw [hslices]
  have hflux (i : ι) (s : Ioo a c) :
      (fun y => w ((s : ℝ), y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y)) =
        flux i s := by
    change (fun y => (fun x => w ((s : ℝ), x)) y *
      (g s).inner y (X s y) (gradientFun (g s) (χ i) y)) = _
    rw [hw s, hX s]
  have hu (s : Ioo a c) : Integrable (u s) (ν s) :=
    co.integrable_poleEndpoint_redDensity_of_redLength F hcar hreg b hbmem tau q hsigma
      Phi kappa hancient p hbase psi hpsi ell hconv
      (ha.trans s.property.1.le) (hcomplete s ⟨s.property.1.le, s.property.2.le⟩)
  have hwSpatial : ∀ᵐ s ∂μ, Integrable (fun y => w (s, y)) (ν s) := by
    dsimp only [μ]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply (ae_restrict_iff_subtype measurableSet_Ioo).2
    exact Eventually.of_forall fun s => by rw [hw s]; exact hu s
  have hwnonneg : ∀ᵐ s ∂μ, ∀ᵐ y ∂ν s, 0 ≤ w (s, y) :=
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => Real.exp_nonneg _
  have hwMass : ∀ᵐ s ∂μ, (∫ y, w (s, y) ∂ν s) = m := by
    dsimp only [μ]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply (ae_restrict_iff_subtype measurableSet_Ioo).2
    filter_upwards [hmass] with s hs
    rw [hw s]
    exact hs
  have hpos : ∀ᶠ i in l, 0 < radii i := hradii.eventually (eventually_gt_atTop 0)
  have hχmeas : ∀ᶠ i in l, Measurable (χ i) := hpos.mono fun i hi =>
    (continuous_radialDistanceCutoff (co.gInf (1 - a)) z hi).measurable
  have hχbound : ∀ᶠ i in l, ∀ y, ‖χ i y‖ ≤ 1 := hpos.mono fun i hi y => by
    obtain ⟨hzero, hone⟩ := radialDistanceCutoff_mem_Icc (co.gInf (1 - a)) z hi y
    rw [Real.norm_of_nonneg hzero]
    exact hone
  have hχone : ∀ y, Tendsto (fun i => χ i y) l (𝓝 1) :=
    tendsto_radialDistanceCutoff (co.gInf (1 - a)) z hradii
  obtain ⟨hD, hDzero, _, _⟩ :=
    integrable_deriv_and_integral_eq_zero_of_tsupport hac heta hetasupp
  obtain ⟨tmax, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hac) heta.continuous.norm.continuousOn
  let K : ℝ := ‖eta tmax‖
  have hetaBound : ∀ᵐ s : Ioo a c, |eta (s : ℝ)| ≤ K := Eventually.of_forall fun s => by
    exact hmax ⟨s.property.1.le, s.property.2.le⟩
  have hetaNormBound : ∀ᵐ s : Ioo a c, ‖eta (s : ℝ)‖ ≤ K := hetaBound
  have hetaMeas : AEStronglyMeasurable (fun s : Ioo a c => eta (s : ℝ)) volume :=
    (heta.continuous.comp continuous_subtype_val).aestronglyMeasurable
  have hmassMeas : ∀ᶠ i in l,
      AEStronglyMeasurable (fun s => ∫ y, χ i y * w (s, y) ∂ν s) μ := by
    filter_upwards [hpos, hχbound] with i hi hbi
    have hmI : AEStronglyMeasurable (fun s : Ioo a c => ∫ y, χ i y * u s y ∂ν s) volume :=
      co.aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp Phi
        (fun _ ht => ht) ha volume ell z hi
    have hbI : ∀ᵐ s : Ioo a c, ‖∫ y, χ i y * u s y ∂ν s‖ ≤ m := by
      filter_upwards [hmass] with s hms
      have hnormmass : (∫ y, ‖u s y‖ ∂ν s) = m := by
        calc
          (∫ y, ‖u s y‖ ∂ν s) = ∫ y, u s y ∂ν s := by
            apply integral_congr_ae
            exact Eventually.of_forall fun y => Real.norm_of_nonneg (Real.exp_nonneg _)
          _ = m := hms
      rw [← hnormmass]
      apply norm_integral_le_of_norm_le (hu s).norm
      exact Eventually.of_forall fun y => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hbi y)
    have hmInt : Integrable (fun s : Ioo a c => ∫ y, χ i y * u s y ∂ν s) volume :=
      Integrable.of_bound hmI m hbI
    have htr := integrable_and_integral_time_transport
      (fun s => ∫ y, χ i y * w (s, y) ∂ν s)
      (fun s : Ioo a c => ∫ y, χ i y * u s y ∂ν s)
      (fun s => by simp_rw [hw_apply s])
    exact (htr.1.mpr hmInt).aestronglyMeasurable
  obtain ⟨_, _, hfluxInt⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  have hfluxSpatial : ∀ᶠ i in l, ∀ᵐ s ∂μ,
      Integrable (fun y => eta s *
        (w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y))) (ν s) := by
    filter_upwards [hpos] with i hi
    dsimp only [μ]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply (ae_restrict_iff_subtype measurableSet_Ioo).2
    apply Eventually.of_forall
    intro s
    have hfi : Integrable (flux i s) (ν s) := (hfluxInt z (radii i) hi).1 s
    have hscaled := hfi.const_mul (eta s)
    simpa only [← hflux i s] using hscaled
  have hfluxTime : ∀ᶠ i in l, Integrable (fun s => eta s *
      (∫ y, w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s)) μ := by
    filter_upwards [hpos] with i hi
    have hfi : Integrable (fun s : Ioo a c => ∫ y, flux i s y ∂ν s) volume :=
      (hfluxInt z (radii i) hi).2.1
    have hweighted := hfi.bdd_mul hetaMeas hetaNormBound
    exact (integrable_and_integral_time_transport
      (fun s => eta s * (∫ y, w (s, y) *
        (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s))
      (fun s : Ioo a c => eta s * ∫ y, flux i s y ∂ν s)
      (fun s => by rw [hflux i s])).1.mpr hweighted
  have hfluxLimI := co.tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
    ha hac hcomplete z (fun s : Ioo a c => eta (s : ℝ))
    hetaMeas hetaBound hradii
  have hfluxLim : Tendsto (fun i => ∫ s, eta s *
      (∫ y, w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s) ∂μ)
      l (𝓝 0) := by
    have heq : (fun i => ∫ s, eta s *
        (∫ y, w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s) ∂μ) =
        (fun i => ∫ s : Ioo a c, eta s * ∫ y, flux i s y ∂ν s) := by
      funext i
      exact (integrable_and_integral_time_transport
        (fun s => eta s * (∫ y, w (s, y) *
          (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s))
        (fun s : Ioo a c => eta s * ∫ y, flux i s y ∂ν s)
        (fun s => by rw [hflux i s])).2
    rw [heq]
    exact hfluxLimI
  have hmain :=
    integrable_and_tendsto_integral_integral_parabolic_test_residual_prod_zero_of_const_mass
    μ ν g w X eta χ hχmeas hχbound hχone hwSpatial hwnonneg m hwMass
    hD hDzero hmassMeas hfluxSpatial hfluxTime hfluxLim
  exact ⟨hmain.2, hmain.1⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
