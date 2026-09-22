import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSelectedMassConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeScaling


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem poleRescaledFlowSeq_redVolume
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (p : F.M)
    {theta : ℝ} (htheta : 0 < theta) :
    redVolume ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S
      0 p theta = intrinsicReducedVolume F.S b p ((tau i + b) * theta) := by
  change intrinsicReducedVolume
      (parabolicSolution F.S b (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) hbmem)
      0 p theta = intrinsicReducedVolume F.S b p ((tau i + b) * theta)
  have h := intrinsicReducedVolume_parabolic F.S b (tau i + b)⁻¹ b
    ((tau i + b) * theta) (inv_pos.mpr (hsigma i)) hbmem
    (mul_pos (hsigma i) htheta) p
  simpa only [parabolicBackward, sub_self, mul_zero,
    inv_mul_cancel_left₀ (hsigma i).ne'] using h

theorem tendsto_poleRescaledFlowSeq_redVolume
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (p : F.M)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S b p) (Ioi 0))
    (eta : ℕ → ℕ)
    (hescape : Tendsto (fun k => tau (eta k) + b) atTop atTop)
    {theta : ℝ} (htheta : 0 < theta) :
    Tendsto (fun k => redVolume
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term (eta k)).S
        0 p theta) atTop (𝓝 (asymptoticReducedVolume F.S b p)) := by
  have h := intrinsicReducedVolume_tendsto_mul_atTop_of_antitone F.S b p hmono
    (fun k => hsigma (eta k)) hescape htheta
  simpa only [poleRescaledFlowSeq_redVolume F hcar hreg b hbmem tau q hsigma
    _ p htheta] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

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

namespace HalfLineMetricConvergenceData

theorem lintegral_poleEndpoint_redDensity_limit_eq_asymptoticReducedVolume_of_tendsto
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S b p) (Ioi 0))
    (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (hescape : Tendsto (fun k => tau (phi (co.φ (psi k))) + b) atTop atTop)
    (ell : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ell atTop)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I))) :
    let lag : Ici (1 : ℝ) := ⟨1 - t, by change 1 ≤ 1 - t; linarith⟩
    (∫⁻ y, ENNReal.ofReal (Real.exp (-ell (y, lag) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)) =
        asymptoticReducedVolume F.S b p := by
  have hmass := HalfLineMetricConvergenceData.tendsto_poleEndpoint_redVolume_of_redLength
    F hcar hreg b hbmem tau q hsigma Phi co kappa hancient p hbase
    psi hpsi ell hconv ht hcomplete
  have hasymptotic := tendsto_poleRescaledFlowSeq_redVolume
    F hcar hreg b hbmem tau q hsigma p hmono
    (fun k => phi (co.φ (psi k))) hescape (show 0 < 1 - t by linarith)
  exact tendsto_nhds_unique hmass.2 hasymptotic

theorem lintegral_poleEndpoint_redDensity_limit_eq_asymptoticReducedVolume
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S b p) (Ioi 0))
    (hescape : Tendsto tau atTop atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (ell : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ell atTop)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I))) :
    let lag : Ici (1 : ℝ) := ⟨1 - t, by change 1 ≤ 1 - t; linarith⟩
    (∫⁻ y, ENNReal.ofReal (Real.exp (-ell (y, lag) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)) =
        asymptoticReducedVolume F.S b p := by
  have hindex : Tendsto (fun k => phi (co.φ (psi k))) atTop atTop :=
    hphi.tendsto_atTop.comp (co.strictMono.tendsto_atTop.comp hpsi.tendsto_atTop)
  have htau := hescape.comp hindex
  have hselected : Tendsto (fun k => tau (phi (co.φ (psi k))) + b) atTop atTop := by
    apply tendsto_atTop.mpr
    intro C
    filter_upwards [htau.eventually_ge_atTop (C - b)] with k hk
    exact sub_le_iff_le_add.mp hk
  exact lintegral_poleEndpoint_redDensity_limit_eq_asymptoticReducedVolume_of_tendsto
    F hcar hreg b hbmem tau q hsigma Phi co kappa hancient p hbase hmono
    psi hpsi hselected ell hconv ht hcomplete

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
