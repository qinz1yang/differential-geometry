import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiQuadratic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import DifferentialGeometry.Analysis.Integration.Integral.LipschitzIntegrationByParts


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
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

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem eventually_poleEndpoint_redLength_weak_hamilton_jacobi
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (ψ : E × ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψW : tsupport ψ ⊆ W ×ˢ Ioo a c) :
    ∀ᶠ k in atTop,
      let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
        (volume : Measure ℝ)
      let f := fun z : E × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2
      let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
      ∫ z, f z * fderiv ℝ ψ z (0, 1) ∂ν =
        ∫ z, ((1 / 2 : ℝ) *
          chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2)) x
            ((extChartAt I x).symm z.1) (d z) (d z) -
          (1 / 2 : ℝ) * ((Y).term (phi (co.φ k))).S.scalar (1 - z.2)
            (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) +
          f z / (2 * z.2)) * ψ z ∂ν := by
  have hlip := eventually_locallyLipschitzOn_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
    x hWt hWJ
  have hhj := eventually_ae_poleEndpoint_redLength_hamilton_jacobi_eq_chartGradientBilin
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
    x hW hWt hWJ
  filter_upwards [hlip, hhj] with k hkLip hkHJ
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (volume : Measure ℝ)
  let f := fun z : E × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
    (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2
  let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let H := fun z => (1 / 2 : ℝ) *
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ k) (1 - z.2)) x
        ((extChartAt I x).symm z.1) (d z) (d z) -
      (1 / 2 : ℝ) * ((Y).term (phi (co.φ k))).S.scalar (1 - z.2)
        (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) + f z / (2 * z.2)
  have hf : LocallyLipschitzOn (W ×ˢ Ioo a c) f :=
    hkLip.mono (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hibp := hf.integral_fderiv_mul_eq_neg_mul_fderiv (μ := ν)
    (hW.prod isOpen_Ioo) hψ hψc hψW (0, 1)
  have hnegative : (fun z => fderiv ℝ f z (0, 1) * ψ z) =ᵐ[ν]
      (fun z => -(H z * ψ z)) := by
    filter_upwards [hkHJ] with z hz
    by_cases hψz : ψ z = 0
    · simp only [hψz, mul_zero, neg_zero]
    · have hzw : z ∈ W ×ˢ Ioo a c := hψW (subset_tsupport ψ hψz)
      have heq : fderiv ℝ f z (0, 1) + H z = 0 := by
        have hsource := hz hzw
        dsimp only at hsource
        dsimp only [H, f, d]
        linarith only [hsource]
      have hd : fderiv ℝ f z (0, 1) = -H z := by linarith
      rw [hd, neg_mul]
  change (∫ z, f z * fderiv ℝ ψ z (0, 1) ∂ν) = ∫ z, H z * ψ z ∂ν
  have heq := integral_congr_ae hnegative
  rw [integral_neg] at heq
  linarith

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
