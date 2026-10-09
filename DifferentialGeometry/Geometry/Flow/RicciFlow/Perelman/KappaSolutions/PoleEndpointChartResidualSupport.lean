import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartSourceResidual
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Separation.Regular
import DifferentialGeometry.Analysis.Integration.Integral.Prod

noncomputable section

open Set _root_.Manifold

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem exists_isOpen_chart_domain_containing_tsupport
    {P : Type*} [TopologicalSpace P]
    (α : M) {ψ : P × E → ℝ} {s : Set P}
    (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ s ×ˢ interior (extChartAt I α).target) :
    ∃ Ω : Set EuStd, IsOpen Ω ∧ IsCompact (closure Ω) ∧
      (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I α).target ∧
      tsupport ψ ⊆ s ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) := by
  let e := toEuclidean (E := E)
  let K : Set EuStd := (fun z : P × E => e z.2) '' tsupport ψ
  let U : Set EuStd := e.symm ⁻¹' interior (extChartAt I α).target
  have hK : IsCompact K := hψc.image (e.continuous.comp continuous_snd)
  have hU : IsOpen U := isOpen_interior.preimage e.symm.continuous
  have hKU : K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    change e.symm (e z.2) ∈ interior (extChartAt I α).target
    rw [e.symm_apply_apply]
    exact (hψs hz).2
  obtain ⟨Ω, hΩ, hKΩ, hΩU, hΩc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  refine ⟨Ω, hΩ, hΩc, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hΩU hy)
  · intro z hz
    exact ⟨(hψs hz).1, hKΩ ⟨z, hz, rfl⟩⟩

end DifferentialGeometry.Analysis.Sobolev.Chart


namespace DifferentialGeometry.Analysis

open Set Filter
open scoped _root_.Topology

private theorem time_spatial_derivatives_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ × E → ℝ) {z : ℝ × E} (hz : z ∉ tsupport ψ) :
    deriv (fun t => ψ (t, z.2)) z.1 = 0 ∧
      fderiv ℝ (fun y => ψ (z.1, y)) z.2 = 0 := by
  have ht : z.1 ∉ tsupport (fun t => ψ (t, z.2)) := by
    intro ht
    exact hz (tsupport_comp_subset_preimage ψ
      (continuous_id.prodMk continuous_const) ht)
  have hx : z.2 ∉ tsupport (fun y => ψ (z.1, y)) := by
    intro hx
    exact hz (tsupport_comp_subset_preimage ψ
      (continuous_const.prodMk continuous_id) hx)
  exact ⟨deriv_of_notMem_tsupport ht, fderiv_of_notMem_tsupport ℝ hx⟩

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter _root_.MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
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

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic

theorem integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_interval_of_ancient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (hb : b < 0) {kappa0 : ℝ}
    (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {a c A : ℝ} (ha : 1 < a)
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hescape : Tendsto tau atTop atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (hcompleteOn : ∀ t ∈ Icc a' c', MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)))
    (x : P.M) (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ interior (extChartAt I x).target) :
    let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
    let u : ℝ × E → ℝ := fun z => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    (∫ z in Ioo a' c' ×ˢ interior (extChartAt I x).target,
      chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume : Measure ℝ).prod (modelHaar (E := E))) = 0 := by
  intro f u
  obtain ⟨Ω, hΩ, hΩc, hΩt, hψΩ⟩ :=
    exists_isOpen_chart_domain_containing_tsupport x hψc hψsupp
  let W : Set E := (toEuclidean (E := E)) ⁻¹' Ω
  let r : ℝ × E → ℝ := fun z =>
    chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
      (deriv (fun t => ψ (t, z.2)) z.1 +
        chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
  have hrzero {z : ℝ × E} (hz : z ∉ tsupport ψ) : r z = 0 := by
    obtain ⟨ht, hx⟩ := DifferentialGeometry.Analysis.time_spatial_derivatives_eq_zero ψ hz
    simp only [r, ht, hx, map_zero, zero_add, mul_zero]
  have hzero := co.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
      hcomplete hboundary kappa hF hb hAncient p ha hbase hescape hphi
      psi hpsi ellC hconv ell hagree haa hac hcc hcompleteOn x hΩ hΩc hΩt
      ψ hψ hψc hψΩ
  calc
    (∫ z in Ioo a' c' ×ˢ interior (extChartAt I x).target,
        r z ∂(volume : Measure ℝ).prod (modelHaar (E := E))) =
        ∫ z, r z ∂(volume : Measure ℝ).prod (modelHaar (E := E)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      exact hrzero fun h => hz (hψsupp h)
    _ = ∫ z, r z ∂(volume.restrict (Ioc a' c')).prod
        ((modelHaar (E := E)).restrict W) := by
      apply integral_eq_integral_restrict_prod_of_support
      intro z hz
      apply hrzero
      intro hs
      exact hz ⟨⟨(hψΩ hs).1.1, (hψΩ hs).1.2.le⟩, (hψΩ hs).2⟩
    _ = 0 := hzero

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
