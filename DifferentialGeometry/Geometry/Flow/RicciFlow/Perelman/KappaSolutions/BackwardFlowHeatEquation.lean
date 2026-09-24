import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowHeatDistribution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowDensityFlux
import DifferentialGeometry.Analysis.Parabolic.WeakEquationExhaustion
import DifferentialGeometry.Analysis.Calculus.ContDiff.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set _root_.MeasureTheory Bundle
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff ENNReal NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace L.M := borel L.M
private local instance (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace L.M := ⟨rfl⟩

private theorem tendsto_backward_flow_cutoff_tensor_mass
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ}
    (hconv : ∀ theta : Icc (1 : ℝ) T,
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta)),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) (1 - theta)) i)
    (hcomplete : ∀ theta : Icc (1 : ℝ) T, MetricComplete (L.atTime (1 - theta)))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (μ : MeasureTheory.Measure (Icc (1 : ℝ) T)) [IsFiniteMeasure μ]
    (ψ : C(Icc (1 : ℝ) T, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → NNReal) (ha : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ theta : Icc (1 : ℝ) T, ψ theta *
      ∫ x : L.M, perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta)) x *
        Analysis.CutoffProfile.evalue
          ((a i : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint x)
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric (1 - theta)) ∂μ)
      l (𝓝 ((∫ theta, ψ theta ∂μ) * (asymptoticReducedVolume F.S 0 p).toReal)) := by
  let R := L.S.base.metric 0
  let g : Icc (1 : ℝ) T → SmoothRiemannianMetric I L.M := fun theta => L.S.base.metric (1 - theta)
  let u : Icc (1 : ℝ) T → L.M → ℝ := fun theta =>
    perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta))
  let χ : ι → L.M → ℝ := fun i x => Analysis.CutoffProfile.evalue
    ((a i : ℝ≥0∞) * riemannianEDistOf R L.basepoint x)
  let w : ι → Icc (1 : ℝ) T × L.M → ℝ := fun i z =>
    χ i z.2 * (ψ z.1 * (riemannianVolumeDensity R (g z.1) z.2 * u z.1 z.2))
  have hm : Integrable (fun z : Icc (1 : ℝ) T × L.M =>
      riemannianVolumeDensity R (g z.1) z.2 * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) :=
    integrable_backward_flow_limit_perelmanDensity F hF p tau htau q L hescape Phi
      hconv hcomplete ell hlim μ R
  have hp := hm.bdd_mul (c := ‖ψ‖) (ψ.continuous.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall fun z => ψ.norm_coe_le_norm z.1)
  have hi (i : ι) : Integrable (w i)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) := by
    have hc : Continuous (fun z : Icc (1 : ℝ) T × L.M => χ i z.2) :=
      Analysis.CutoffProfile.continuous_evalue.comp
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          ((continuous_riemannianEDist R L.basepoint).comp continuous_snd))
    exact hp.bdd_mul (c := 1) hc.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.CutoffProfile.evalue_mem_Icc _).1]
      exact (Analysis.CutoffProfile.evalue_mem_Icc _).2)
  have hlimit : Tendsto (fun i => ∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) l
      (𝓝 ((∫ theta, ψ theta ∂μ) * (asymptoticReducedVolume F.S 0 p).toReal)) :=
    tendsto_integral_backward_flow_limit_perelmanDensity_cutoff F hF p tau htau q L hescape Phi
      hconv hcomplete ell hlim μ R ψ a ha
  have heq (i : ι) : (∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) =
      ∫ theta, ψ theta * ∫ x, u theta x * χ i x
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g theta) ∂μ := by
    have hf : Integrable (fun z : Icc (1 : ℝ) T × L.M =>
        riemannianVolumeDensity R (g z.1) z.2 • (ψ z.1 * (u z.1 z.2 * χ i z.2)))
        (μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R)) := by
      apply (hi i).congr
      filter_upwards [] with z
      dsimp only [w]
      rw [smul_eq_mul]
      ring
    calc
      _ = ∫ z, riemannianVolumeDensity R (g z.1) z.2 • (ψ z.1 * (u z.1 z.2 * χ i z.2))
          ∂μ.prod (riemannianVolumeMeasure (I := I) (M := L.M) R) := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp only [w]
        rw [smul_eq_mul]
        ring
      _ = ∫ theta, ∫ x, ψ theta * (u theta x * χ i x)
          ∂riemannianVolumeMeasure (I := I) (M := L.M) (g theta) ∂μ :=
        integral_prod_volumeDensity_smul μ R g (fun z => ψ z.1 * (u z.1 z.2 * χ i z.2)) hf
      _ = _ := by simp only [integral_const_mul]
  simp_rw [heq] at hlimit
  exact hlimit

private theorem integral_subtype_comap_smul_eq_of_tsupport_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (ψ : ℝ → ℝ) (f : ℝ → F) (hs : tsupport ψ ⊆ Icc a b) :
    (∫ t : Icc a b, ψ t • f t ∂volume.comap Subtype.val) =
      ∫ t, ψ t • f t := by
  rw [integral_subtype_comap (f := fun t => ψ t • f t) measurableSet_Icc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hs h)), zero_smul]

private theorem tendsto_backward_flow_cutoff_defect
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 < T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : tsupport ψ ⊆ Ioo 1 T)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ≥0) (ha : Tendsto a l (𝓝 0)) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => ell (x, projIcc 1 T hT.le t))
    let g := fun t => L.S.base.metric (1 - t)
    let χ := fun i x => Analysis.CutoffProfile.evalue
      ((a i : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint x)
    Tendsto (fun i =>
      (∫ t, deriv ψ t * ∫ x, u t x * χ i x
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) -
      ∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) (χ i) x)
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) l (𝓝 0) := by
  let μ : MeasureTheory.Measure (Icc (1 : ℝ) T) := volume.comap Subtype.val
  let _ : IsFiniteMeasure μ := by
    let _ : MeasureSpace (Icc (1 : ℝ) T) := Measure.Subtype.measureSpace
    constructor
    change (volume.comap (Subtype.val : Icc (1 : ℝ) T → ℝ)) univ < ⊤
    rw [← Measure.Subtype.volume_def, Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top
  let ψ₀ : C(Icc (1 : ℝ) T, ℝ) := ⟨fun t => ψ t, hψ.continuous.comp continuous_subtype_val⟩
  let ψ₁ : C(Icc (1 : ℝ) T, ℝ) := ⟨fun t => deriv ψ t,
    (hψ.continuous_deriv le_rfl).comp continuous_subtype_val⟩
  have hm := tendsto_backward_flow_cutoff_tensor_mass F hF p tau htau q L hescape Phi
    (fun theta => hconv (1 - theta) ⟨sub_le_sub_left theta.property.2 1,
      sub_nonpos.mpr theta.property.1⟩)
    (fun theta => hcomplete (1 - theta) ⟨sub_le_sub_left theta.property.2 1,
      sub_nonpos.mpr theta.property.1⟩) ell hlim μ ψ₁ a ha
  have hz : (∫ t : Icc (1 : ℝ) T, ψ₁ t ∂μ) = 0 := by
    change (∫ t : Icc (1 : ℝ) T, deriv ψ t ∂volume.comap Subtype.val) = 0
    rw [integral_subtype_comap measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hT.le]
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hψ.differentiable (by norm_num) t)
      ((hψ.continuous_deriv le_rfl).intervalIntegrable 1 T)]
    have ha0 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hψs h).1.false)
    have hb0 : ψ T = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hψs h).2.false)
    rw [ha0, hb0, sub_self]
  rw [hz, zero_mul] at hm
  have hf := tendsto_integral_backward_flow_limit_perelmanDensity_cutoff_flux
    F hF p tau htau q L hescape Phi hT.le hconv hcomplete ell hlim μ ψ₀ a ha
  have hresult := hm.sub hf
  simp only [sub_zero] at hresult
  have hψcc : tsupport ψ ⊆ Icc 1 T := hψs.trans Ioo_subset_Icc_self
  have hdcc : tsupport (deriv ψ) ⊆ Icc 1 T := tsupport_deriv_subset.trans hψcc
  have heq (φ : ℝ → ℝ) (f : ℝ → ℝ) (hs : tsupport φ ⊆ Icc 1 T) :
      (∫ t : Icc (1 : ℝ) T, φ t * f t ∂μ) = ∫ t, φ t * f t := by
    exact integral_subtype_comap_smul_eq_of_tsupport_subset φ f hs
  convert hresult using 1
  funext i
  congr 1
  · rw [← heq (deriv ψ) _ hdcc]
    apply integral_congr_ae
    filter_upwards [] with theta
    simp only [projIcc_val, ψ₁, ContinuousMap.coe_mk]
  · rw [← heq ψ _ hψcc]
    apply integral_congr_ae
    filter_upwards [] with theta
    simp only [projIcc_val, ψ₀, ContinuousMap.coe_mk]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set _root_.MeasureTheory Bundle
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff ENNReal NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace L.M := borel L.M
private local instance (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace L.M := ⟨rfl⟩

private theorem integrable_backward_flow_cutoff_flux_slice
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ} (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    {T : ℝ} (hT : 1 ≤ T)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hlim : ∀ theta : Icc (1 : ℝ) T, ∀ x : L.M,
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))))
    (a : ℝ≥0) (theta : Icc (1 : ℝ) T) :
    Integrable (fun x : L.M => (L.S.base.metric (1 - theta)).inner x
      (gradFun (L.S.base.metric (1 - theta))
        (perelmanDensity (Module.finrank ℝ E) theta (fun y => ell (y, theta))) x)
      (gradFun (L.S.base.metric (1 - theta)) (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint y)) x))
      (riemannianVolumeMeasure (I := I) (M := L.M) (L.S.base.metric (1 - theta))) := by
  let _ := riemannianVolumeMeasure_sigmaFinite (L.S.base.metric 0)
  let ψ : C(Icc (1 : ℝ) T, ℝ) := ⟨fun _ => 1, continuous_const⟩
  have hi := integrable_backward_flow_limit_perelmanDensity_cutoff_flux
    F hF p tau htau q L hescape Phi hT hconv hcomplete ell hlim (Measure.dirac theta) ψ a
  simp only [ψ, ContinuousMap.coe_mk, mul_one] at hi
  have hi' := hi.prod_right_ae
  rw [ae_dirac_eq] at hi'
  apply (integrable_riemannianVolumeMeasure_iff (L.S.base.metric 0)
    (L.S.base.metric (1 - theta)) _).mpr
  exact hi'

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff _root_.Topology NNReal ENNReal Matrix.Norms.Elementwise

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

omit [NeZero (Module.finrank ℝ E)] in
theorem backward_flow_limit_perelmanDensity_tensor_weak_eq_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (α : L.M) (χ : C(L.M, ℝ)) (hχc : HasCompactSupport (χ : L.M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχsm : ContMDiff I 𝓘(ℝ) ∞ (χ : L.M → ℝ))
    (hχs : tsupport (χ : L.M → ℝ) ⊆ (chartAt H α).source)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo 1 T) (hψ0 : ∀ t, 0 ≤ ψ t) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => ell (x, projIcc 1 T hT.le t))
    let g := fun t => L.S.base.metric (1 - t)
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * χ x
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) =
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t) := by
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let _ : Nonempty L.M := ⟨L.basepoint⟩
  let _ : ConnectedSpace L.M := { isPreconnected_univ := PreconnectedSpace.isPreconnected_univ, toNonempty := inferInstance }
  let u : ℝ → C(L.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => ell (x, projIcc 1 T hT.le t)),
      continuous_const.mul (Real.continuous_exp.comp
        (ell.continuous.comp (continuous_id.prodMk continuous_const)).neg)⟩
  let g : ℝ → SmoothRiemannianMetric I L.M := fun t => L.S.base.metric (1 - t)
  have hR : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) (hcomplete 0 ⟨sub_nonpos.mpr hT.le, le_rfl⟩)⟩
  obtain ⟨Cχ, hCχ⟩ := Geometry.Riemannian.exists_lipschitz_constant_of_smooth_compact_support
    (L.S.base.metric 0) hR hχsm hχc
  have hwχ := backward_flow_limit_perelmanDensity_tensor_weak_le
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip χ hχc hχ0 hCχ hψ hψc hψs hψ0
  refine ⟨hwχ.1, hwχ.2.1, ?_⟩
  let a : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have ha : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ha0 (n : ℕ) : 0 < a n := by dsimp only [a]; positivity
  let ζ : ℕ → C(L.M, ℝ) := fun n =>
    ⟨fun x => Analysis.CutoffProfile.evalue
      ((a n : ℝ≥0∞) * riemannianEDistOf (L.S.base.metric 0) L.basepoint x),
      Analysis.CutoffProfile.continuous_evalue.comp
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          (Geometry.Riemannian.continuous_riemannianEDist (L.S.base.metric 0) L.basepoint))⟩
  have hlim (theta : Icc (1 : ℝ) T) (x : L.M) :
      Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * theta))
        atTop (𝓝 (ell (x, theta))) :=
    (hell {(x, theta)} isCompact_singleton).tendsto_at (x := (x, theta)) (mem_singleton _)
  have hu : LocallyLipschitzOn (Ioo 1 T ×ˢ (extChartAt I α).target)
      (fun z : ℝ × E => u z.1 ((extChartAt I α).symm z.2)) :=
    (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip α (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩)
  have hχi (t : ℝ) (ht : t ∈ Ioo 1 T) :
      Integrable (fun x => (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x))
        (riemannianVolumeMeasure (I := I) (M := L.M) (g t)) := by
    have hus : LocallyLipschitzOn (extChartAt I α).target (scalarOnE (I := I) α (u t)) := by
      apply locallyLipschitzOn_iff_restrict.mpr
      have hmap : LipschitzWith 1 (fun x : (extChartAt I α).target =>
          (⟨(t, x.1), ht, x.2⟩ : Ioo 1 T ×ˢ (extChartAt I α).target)) := by
        simpa only [one_mul, Function.comp_apply] using
          ((LipschitzWith.prodMk_left t).comp (LipschitzWith.subtype_val (extChartAt I α).target)).subtype_mk
            (fun x => ⟨ht, x.2⟩)
      have hh : LocallyLipschitz
          (((Ioo 1 T ×ˢ (extChartAt I α).target).domRestrict
            (fun z : ℝ × E => u z.1 ((extChartAt I α).symm z.2))) ∘
            (fun x : (extChartAt I α).target =>
              (⟨(t, x.1), ht, x.2⟩ : Ioo 1 T ×ˢ (extChartAt I α).target))) :=
        hu.restrict.comp hmap.locallyLipschitz
      exact hh
    have hχchart : ContDiffOn ℝ 1 (scalarOnE (I := I) α χ) (extChartAt I α).target :=
      (scalarOnE_contDiffOn α hχsm).of_le (by simp)
    exact Analysis.integrable_inner_gradFun_of_locallyLipschitzOn_chart (g t) α (u t) χ hus
      (hχchart.locallyLipschitzOn_of_isOpen (isOpen_extChartAt_target (I := I) α)) hχc hχs
  apply Analysis.Parabolic.integral_tensor_test_eq_of_exhaustion (L.S.base.metric 0) g u hψs
    (fun η hηc hη0 hηL => by
      obtain ⟨Cη, hCη⟩ := hηL
      exact backward_flow_limit_perelmanDensity_tensor_weak_le
        F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip η hηc hη0 hCη hψ hψc hψs hψ0)
    χ hχc hχ0 ⟨Cχ, hCχ⟩ hχi ζ
    (fun n => Geometry.Riemannian.hasCompactSupport_distance_cutoff
      (L.S.base.metric 0) hR L.basepoint (ha0 n))
    (fun n x => (Analysis.CutoffProfile.evalue_mem_Icc _).1)
    (fun n => ⟨⟨Analysis.CutoffProfile.derivBound, Analysis.CutoffProfile.derivBound_nonneg⟩ * a n,
      Geometry.Riemannian.edist_distance_cutoff_le (L.S.base.metric 0) L.basepoint (a n)⟩)
    (fun n t ht => ?_)
    (Geometry.Riemannian.eventually_distance_cutoff_eq_one_on_isCompact
      (L.S.base.metric 0) L.basepoint hχc a ha)
    (tendsto_backward_flow_cutoff_defect F hF p tau htau q L hescape Phi hT
      hconv hcomplete ell hlim hψ hψs a ha)
  have ht' : t ∈ Icc (1 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hi := integrable_backward_flow_cutoff_flux_slice F hF p tau htau q L hescape Phi hT.le
    hconv hcomplete ell hlim (a n) ⟨t, ht'⟩
  simpa only [g, u, ζ, ContinuousMap.coe_mk, projIcc_of_mem hT.le ht'] using hi

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem backward_flow_limit_perelmanDensity_weak_eq_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    (α : L.M) {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo 1 T ×ˢ (extChartAt I α).target) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I α).symm w.2)
    let ρ := fun w : ℝ × E => chartDensityOnE (L.S.base.metric (1 - w.1)) α w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (L.S.base.metric (1 - w.1)) α i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂volume.prod (modelHaar (E := E))) =
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂volume.prod (modelHaar (E := E)) := by
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let u : ℝ → C(L.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => ell (x, projIcc 1 T hT.le t)),
      continuous_const.mul (Real.continuous_exp.comp
        (ell.continuous.comp (continuous_id.prodMk continuous_const)).neg)⟩
  apply Analysis.Parabolic.integral_chart_test_eq_of_tensor_test isOpen_Ioo
    (fun t => L.S.base.metric (1 - t)) α u
    ((locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip α (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩))
    (fun i j => ?_)
    (fun ψ hψ hψc hψs hψ0 => backward_flow_limit_perelmanDensity_weak_le_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip α
      (volume.prod (modelHaar (E := E)))
      ((hψ.of_le (by simp) : ContDiff ℝ 1 ψ).locallyLipschitz.locallyLipschitzOn)
      hψc hψs hψ0)
    (fun χ hχsm hχc hχs hχ0 ψ hψ hψc hψs hψ0 =>
      (backward_flow_limit_perelmanDensity_tensor_weak_eq_in_chart
        F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete
        α χ hχc hχ0 hχsm hχs (hψ.of_le (by simp)) hψc hψs hψ0).2.2)
    hφ hφc hφs
  have hmap : ContinuousOn (fun z : ℝ × L.M => (1 - z.1, z.2))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : MapsTo (fun z : ℝ × L.M => (1 - z.1, z.2))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (ancientTimeInterval.carrier ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    fun z hz => ⟨show 1 - z.1 ≤ 0 from sub_nonpos.mpr hz.1.1.le, hz.2⟩
  have hc : ContinuousOn
      ((fun z : ℝ × L.M => chartGramMatrix (L.S.base.metric z.1) α z.2 i j) ∘
        (fun z : ℝ × L.M => (1 - z.1, z.2)))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (L.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier α i j).comp hmap hmaps
  exact hc

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
