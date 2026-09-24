import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiTimeChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineGradientCoefficients
import DifferentialGeometry.Geometry.Operator.TimeLaplacian
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {φ : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private local instance covectorNormedAddCommGroupContinuity : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpaceContinuity : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroupContinuity :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpaceContinuity : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroupContinuity :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpaceContinuity :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem continuousOn_halfLine_hamilton_jacobi_residual
    (Phi : PointedCGHMaps X P φ) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hYreg : Iio (0 : ℝ) ⊆ X.D.regular) {a c : ℝ} (ha : 1 < a)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    {f : ℝ × E → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo a c ×ˢ W)) :
    ContinuousOn (fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1 +
      (1 / 2 : ℝ) * chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
        (fderiv ℝ (fun y : E => f (z.1, y)) z.2)
        (fderiv ℝ (fun y : E => f (z.1, y)) z.2) -
      (1 / 2 : ℝ) * metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2) +
      f z / (2 * z.1)) (Ioo a c ×ˢ W) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Ω : Set (ℝ × E) := Ioo a c ×ˢ W
  let d : ℝ × E → E →L[ℝ] ℝ :=
    fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E =>
    metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
  let HJ := fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1 +
    (1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z + f z / (2 * z.1)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hd : ContinuousOn d Ω :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => f (t, y)) isOpen_Ioo.uniqueDiffOn hW hf).continuousOn
  have hdt : ContinuousOn (fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1) Ω := by
    have hfd : ContinuousOn (fderiv ℝ f) Ω :=
      hf.continuousOn_fderiv_of_isOpen hΩ (by simp)
    apply (hfd.clm_apply (continuousOn_const (c := (1, (0 : E))))).congr
    intro z hz
    have hdiff := (hf.differentiableOn (by simp) z hz).differentiableAt (hΩ.mem_nhds hz)
    have htime := (hdiff.hasFDerivAt.comp z.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).hasDerivAt.deriv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using htime
  have hlag (z : ℝ × E) (hz : z ∈ Ω) : 1 - z.1 < 0 := by
    have ht : 1 < z.1 := ha.trans hz.1.1
    linarith
  have hB : ContinuousOn B Ω := by
    apply (co.continuousOn_chartGradientBilin (Φ := Phi) hYreg x).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    intro z hz
    exact ⟨hlag z hz, hWt hz.2⟩
  have hscalar : ContinuousOn (fun z : ℝ × P.M => metricScalarAt (co.gInf z.1) z.2)
      (Iio (0 : ℝ) ×ˢ univ) :=
    DifferentialGeometry.PDE.RicciFlow.scalarCont_of_joint co.gInf (Iio 0)
      isOpen_Iio.uniqueDiffOn
        (HalfLineMetricConvergenceData.gramSmooth (I := I) (Φ := Phi) co hYreg)
  have hS : ContinuousOn S Ω := by
    have hchart : ContinuousOn (fun z : ℝ × E => (extChartAt I x).symm z.2) Ω :=
      (continuousOn_extChartAt_symm (I := I) x).comp continuous_snd.continuousOn
        (fun z hz => hWt hz.2)
    let ψ : ℝ × E → ℝ × P.M := fun z => (1 - z.1, (extChartAt I x).symm z.2)
    have hψ : ContinuousOn ψ Ω :=
      (continuous_const.sub continuous_fst).continuousOn.prodMk hchart
    have hmaps : MapsTo ψ Ω (Iio (0 : ℝ) ×ˢ (univ : Set P.M)) :=
      fun z hz => ⟨hlag z hz, mem_univ _⟩
    have hcomp := hscalar.comp hψ hmaps
    simpa only [Function.comp_def, ψ, S] using hcomp
  have hquad : ContinuousOn (fun z => B z (d z) (d z)) Ω :=
    (hB.clm_apply hd).clm_apply hd
  have hH : ContinuousOn HJ Ω := by
    apply ((hdt.add (hquad.const_mul (1 / 2))).sub (hS.const_mul (1 / 2))).add
    exact hf.continuousOn.div (continuousOn_const.mul continuous_fst.continuousOn)
      (fun z hz => mul_ne_zero (by norm_num) (ne_of_gt ((zero_lt_one.trans ha).trans hz.1.1)))
  exact hH

end Continuity

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (hell : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => ell (z.2, z.1)) (Ioo a c ×ˢ univ)) :
    ∀ t ∈ Ioo a c, ∀ y ∈ W,
      2 * deriv (fun s => ell ((extChartAt I x).symm y, s)) t +
        (co.gInf (1 - t)).inner ((extChartAt I x).symm y)
          (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
            ((extChartAt I x).symm y))
          (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
            ((extChartAt I x).symm y)) -
        metricScalarAt (co.gInf (1 - t)) ((extChartAt I x).symm y) +
        ell ((extChartAt I x).symm y, t) / t = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let ν := (volume : Measure ℝ).prod (modelHaar (E := E))
  let Ω : Set (ℝ × E) := Ioo a c ×ˢ W
  let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
  let d : ℝ × E → E →L[ℝ] ℝ :=
    fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
  let B := fun z : ℝ × E => chartGradientBilin (co.gInf (1 - z.1)) x
    ((extChartAt I x).symm z.2)
  let S := fun z : ℝ × E =>
    metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
  let HJ := fun z : ℝ × E => deriv (fun s => f (s, z.2)) z.1 +
    (1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z + f z / (2 * z.1)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod hW
  have hYreg : Iio (0 : ℝ) ⊆ (Y).D.regular := by
    intro s hs
    change s ∈ ancientTimeInterval.regular
    simpa only [ancientTimeInterval_regular] using hs
  have hf : ContDiffOn ℝ ∞ f Ω := by
    have hchart := DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_prod
      (I := I) (f := fun t y => ell (y, t)) x hell
    exact hchart.mono (Set.prod_mono Subset.rfl hWt)
  have hH : ContinuousOn HJ Ω :=
    continuousOn_halfLine_hamilton_jacobi_residual Phi co hYreg ha x hW hWt hf
  have hae : ∀ᵐ z ∂ν, z ∈ Ω → HJ z = 0 :=
    ae_poleEndpoint_redLength_limit_hamilton_jacobi_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ
  have hzero : EqOn HJ (fun _ => (0 : ℝ)) Ω :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq
      ((ae_restrict_iff' hΩ.measurableSet).mpr hae) hΩ hH continuousOn_const
  intro t ht y hy
  have heq := hzero (x := (t, y)) ⟨ht, hy⟩
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun z => ell (z, t)) :=
    hell.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun z => ⟨ht, mem_univ z⟩)
  have hxsource : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x).map_target (hWt hy)
  have hgrad := grad_norm_sq_eq_chartGradientBilin (I := I) (co.gInf (1 - t)) x
    (hsmooth.mdifferentiable (by simp) _) hxsource
  rw [(extChartAt I x).right_inv (hWt hy)] at hgrad
  change (co.gInf (1 - t)).inner ((extChartAt I x).symm y)
      (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
        ((extChartAt I x).symm y))
      (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t))
        ((extChartAt I x).symm y)) = B (t, y) (d (t, y)) (d (t, y)) at hgrad
  rw [hgrad]
  dsimp only [HJ, f, S] at heq
  have htne : t ≠ 0 := (lt_trans (zero_lt_one.trans ha) ht.1).ne'
  field_simp [htne] at heq ⊢
  nlinarith

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
