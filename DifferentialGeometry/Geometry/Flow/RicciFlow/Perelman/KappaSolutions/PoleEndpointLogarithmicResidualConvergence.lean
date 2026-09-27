import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientBilinearConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLogarithmicZeroOrder

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

private local instance cotangentNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance cotangentNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance cotangentDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance cotangentDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance cotangentBilinearNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance cotangentBilinearNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

theorem integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual
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
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a' c'))
    (v : E × ℝ → E →L[ℝ] ℝ) (hv : ContinuousOn v (K ×ˢ Icc a' c')) :
    let ν := (modelHaar (E := E)).prod (volume : Measure ℝ)
    let f := fun k (z : E × ℝ) =>
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
    let f₀ := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
    let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let r := fun k (z : E × ℝ) =>
      chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let r₀ := fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let B := fun k (z : E × ℝ) =>
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let B₀ := fun z : E × ℝ =>
      chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let S := fun k (z : E × ℝ) =>
      ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
    let S₀ := fun z : E × ℝ =>
      metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
    let Q := fun k z => r k z *
      (((1 / 2 : ℝ) * B k z (d k z) (d k z) - (1 / 2 : ℝ) * S k z +
        ((Module.finrank ℝ E : ℝ) - f k z) / (2 * z.2)) * w z +
          B k z (d k z) (v z))
    let Q₀ := fun z => r₀ z *
      (((1 / 2 : ℝ) * B₀ z (d₀ z) (d₀ z) - (1 / 2 : ℝ) * S₀ z +
        ((Module.finrank ℝ E : ℝ) - f₀ z) / (2 * z.2)) * w z +
          B₀ z (d₀ z) (v z))
    (∀ᶠ k in atTop, IntegrableOn (Q k) (K ×ˢ Icc a' c') ν) ∧
      IntegrableOn Q₀ (K ×ˢ Icc a' c') ν ∧
      Tendsto (fun k => ∫ z in K ×ˢ Icc a' c', Q k z ∂ν) atTop
        (𝓝 (∫ z in K ×ˢ Icc a' c', Q₀ z ∂ν)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let ν := (modelHaar (E := E)).prod (volume : Measure ℝ)
  let C := K ×ˢ Icc a' c'
  let f := fun k (z : E × ℝ) =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
  let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let r := fun k (z : E × ℝ) =>
    chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let r₀ := fun z : E × ℝ =>
    chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let B := fun k (z : E × ℝ) =>
    chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let B₀ := fun z : E × ℝ =>
    chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let S := fun k (z : E × ℝ) =>
    ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
  let S₀ := fun z : E × ℝ =>
    metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
  let e := fun k z => (w z * r k z) * B k z (d k z) (d k z)
  let e₀ := fun z => (w z * r₀ z) * B₀ z (d₀ z) (d₀ z)
  let s := fun k z => w z * r k z * S k z
  let s₀ := fun z => w z * r₀ z * S₀ z
  let z₀ := fun k z => r k z * (w z / (2 * z.2)) *
    ((Module.finrank ℝ E : ℝ) - f k z)
  let zInf := fun z => r₀ z * (w z / (2 * z.2)) *
    ((Module.finrank ℝ E : ℝ) - f₀ z)
  let l := fun k z => r k z * B k z (d k z) (v z)
  let l₀ := fun z => r₀ z * B₀ z (d₀ z) (v z)
  have he := integrable_and_tendsto_integral_poleEndpoint_redLength_gradient_bilinear
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc w hw v hv
  have hl := integrable_and_tendsto_integral_poleEndpoint_redLength_gradient_bilinear
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc
    (fun _ => 1) continuousOn_const v hv
  have ha' : 1 ≤ a' := (ha.trans haa).le
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hs := integrableOn_and_tendsto_integral_poleEndpoint_chartDensity_mul_scalar
    F hcar hreg b hbmem tau q hsigma Phi R co (c := c') ha' rho hrho x hK hKt w hw
  have htime : ContinuousOn (fun z : E × ℝ => w z / (2 * z.2)) C :=
    hw.div (continuousOn_const.mul continuous_snd.continuousOn) (fun z hz =>
      mul_ne_zero (by norm_num) (ne_of_gt (zero_lt_one.trans_le (ha'.trans hz.2.1))))
  have hz := integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c') ha' hbase
    rho hrho ell
    (fun y hy t ht => hconv y hy t ⟨haa.le.trans ht.1, ht.2.trans hcc.le⟩)
    x hK hKt (fun y hy => hWJ (hKW hy)) (Module.finrank ℝ E : ℝ)
    (fun z => w z / (2 * z.2)) htime
  have heSrc : ∀ᶠ k in atTop, IntegrableOn (e k) C ν := by
    filter_upwards [he.1] with k hk
    simpa only [e, r, B, d, f, smul_apply, smul_eq_mul] using hk.2
  have heInf : IntegrableOn e₀ C ν := by
    simpa only [e₀, r₀, B₀, d₀, f₀, smul_apply, smul_eq_mul] using he.2.2.1
  have heConv : Tendsto (fun k => ∫ z in C, e k z ∂ν) atTop
      (𝓝 (∫ z in C, e₀ z ∂ν)) := by
    simpa only [e, e₀, r, r₀, B, B₀, d, d₀, f, f₀, smul_apply, smul_eq_mul] using he.2.2.2.2
  have hlSrc : ∀ᶠ k in atTop, IntegrableOn (l k) C ν := by
    filter_upwards [hl.1] with k hk
    simpa only [l, r, B, d, f, one_mul, smul_apply, smul_eq_mul] using hk.1
  have hlInf : IntegrableOn l₀ C ν := by
    simpa only [l₀, r₀, B₀, d₀, f₀, one_mul, smul_apply, smul_eq_mul] using hl.2.1
  have hlConv : Tendsto (fun k => ∫ z in C, l k z ∂ν) atTop
      (𝓝 (∫ z in C, l₀ z ∂ν)) := by
    simpa only [l, l₀, r, r₀, B, B₀, d, d₀, f, f₀, one_mul, smul_apply, smul_eq_mul]
      using hl.2.2.2.1
  have hsSrc : ∀ᶠ k in atTop, IntegrableOn (s k) C ν := hs.2.1
  have hsInf : IntegrableOn s₀ C ν := hs.1
  have hsConv : Tendsto (fun k => ∫ z in C, s k z ∂ν) atTop
      (𝓝 (∫ z in C, s₀ z ∂ν)) := hs.2.2
  have hzSrc : ∀ᶠ k in atTop, IntegrableOn (z₀ k) C ν := hz.1
  have hzInf : IntegrableOn zInf C ν := hz.2.1
  have hzConv : Tendsto (fun k => ∫ z in C, z₀ k z ∂ν) atTop
      (𝓝 (∫ z in C, zInf z ∂ν)) := hz.2.2
  let Q := fun k z => (1 / 2 : ℝ) * e k z - (1 / 2 : ℝ) * s k z + z₀ k z + l k z
  let Q₀ := fun z => (1 / 2 : ℝ) * e₀ z - (1 / 2 : ℝ) * s₀ z + zInf z + l₀ z
  have hQSrc : ∀ᶠ k in atTop, IntegrableOn (Q k) C ν := by
    filter_upwards [heSrc, hsSrc, hzSrc, hlSrc] with k hkE hkS hkZ hkL
    exact (((hkE.const_mul (1 / 2 : ℝ)).sub (hkS.const_mul (1 / 2 : ℝ))).add hkZ).add hkL
  have hQInf : IntegrableOn Q₀ C ν :=
    (((heInf.const_mul (1 / 2 : ℝ)).sub (hsInf.const_mul (1 / 2 : ℝ))).add hzInf).add hlInf
  have hQInt (k : ℕ) (hkE : IntegrableOn (e k) C ν) (hkS : IntegrableOn (s k) C ν)
      (hkZ : IntegrableOn (z₀ k) C ν) (hkL : IntegrableOn (l k) C ν) :
      (∫ z in C, Q k z ∂ν) =
        (1 / 2 : ℝ) * (∫ z in C, e k z ∂ν) - (1 / 2 : ℝ) * (∫ z in C, s k z ∂ν) +
          (∫ z in C, z₀ k z ∂ν) + ∫ z in C, l k z ∂ν := by
    dsimp only [Q]
    have hE := hkE.const_mul (1 / 2 : ℝ)
    have hS := hkS.const_mul (1 / 2 : ℝ)
    rw [integral_add
      (f := fun z => (1 / 2 : ℝ) * e k z - (1 / 2 : ℝ) * s k z + z₀ k z)
      (g := l k) ((hE.sub hS).add hkZ) hkL]
    rw [integral_add
      (f := fun z => (1 / 2 : ℝ) * e k z - (1 / 2 : ℝ) * s k z)
      (g := z₀ k) (hE.sub hS) hkZ]
    rw [integral_sub (f := fun z => (1 / 2 : ℝ) * e k z)
      (g := fun z => (1 / 2 : ℝ) * s k z) hE hS,
      integral_const_mul, integral_const_mul]
  have hQInt₀ : (∫ z in C, Q₀ z ∂ν) =
      (1 / 2 : ℝ) * (∫ z in C, e₀ z ∂ν) - (1 / 2 : ℝ) * (∫ z in C, s₀ z ∂ν) +
        (∫ z in C, zInf z ∂ν) + ∫ z in C, l₀ z ∂ν := by
    dsimp only [Q₀]
    have hE := heInf.const_mul (1 / 2 : ℝ)
    have hS := hsInf.const_mul (1 / 2 : ℝ)
    rw [integral_add
      (f := fun z => (1 / 2 : ℝ) * e₀ z - (1 / 2 : ℝ) * s₀ z + zInf z)
      (g := l₀) ((hE.sub hS).add hzInf) hlInf]
    rw [integral_add
      (f := fun z => (1 / 2 : ℝ) * e₀ z - (1 / 2 : ℝ) * s₀ z)
      (g := zInf) (hE.sub hS) hzInf]
    rw [integral_sub (f := fun z => (1 / 2 : ℝ) * e₀ z)
      (g := fun z => (1 / 2 : ℝ) * s₀ z) hE hS,
      integral_const_mul, integral_const_mul]
  have hQConv : Tendsto (fun k => ∫ z in C, Q k z ∂ν) atTop
      (𝓝 (∫ z in C, Q₀ z ∂ν)) := by
    rw [hQInt₀]
    apply ((((tendsto_const_nhds.mul heConv).sub
      (tendsto_const_nhds.mul hsConv)).add hzConv).add hlConv).congr'
    filter_upwards [heSrc, hsSrc, hzSrc, hlSrc] with k hkE hkS hkZ hkL
    exact (hQInt k hkE hkS hkZ hkL).symm
  have hQeq (k : ℕ) : Q k = fun z => r k z *
      (((1 / 2 : ℝ) * B k z (d k z) (d k z) - (1 / 2 : ℝ) * S k z +
        ((Module.finrank ℝ E : ℝ) - f k z) / (2 * z.2)) * w z +
          B k z (d k z) (v z)) := by
    funext z
    dsimp only [Q, e, s, z₀, l]
    simp only [div_eq_mul_inv]
    ring
  have hQeq₀ : Q₀ = fun z => r₀ z *
      (((1 / 2 : ℝ) * B₀ z (d₀ z) (d₀ z) - (1 / 2 : ℝ) * S₀ z +
        ((Module.finrank ℝ E : ℝ) - f₀ z) / (2 * z.2)) * w z +
          B₀ z (d₀ z) (v z)) := by
    funext z
    dsimp only [Q₀, e₀, s₀, zInf, l₀]
    simp only [div_eq_mul_inv]
    ring
  simpa only [hQeq, hQeq₀] using And.intro hQSrc (And.intro hQInf hQConv)

theorem integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities
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
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a' c'))
    (v : E × ℝ → E →L[ℝ] ℝ) (hv : ContinuousOn v (K ×ˢ Icc a' c')) :
    let ν := (modelHaar (E := E)).prod (volume : Measure ℝ)
    let f := fun k (z : E × ℝ) =>
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
    let f₀ := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
    let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let r := fun k (z : E × ℝ) =>
      chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let r₀ := fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let B := fun k (z : E × ℝ) =>
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let B₀ := fun z : E × ℝ =>
      chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let S := fun k (z : E × ℝ) =>
      ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
    let S₀ := fun z : E × ℝ =>
      metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
    let Q := fun k z => r k z *
      (((1 / 2 : ℝ) * B k z (d k z) (d k z) - (1 / 2 : ℝ) * S k z +
        ((Module.finrank ℝ E : ℝ) - f k z) / (2 * z.2)) * w z +
          B k z (d k z) (v z))
    let Q₀ := fun z => r₀ z *
      (((1 / 2 : ℝ) * B₀ z (d₀ z) (d₀ z) - (1 / 2 : ℝ) * S₀ z +
        ((Module.finrank ℝ E : ℝ) - f₀ z) / (2 * z.2)) * w z +
          B₀ z (d₀ z) (v z))
    (∀ᶠ k in atTop, 0 ≤ ∫ z in K ×ˢ Icc a' c', Q k z ∂ν) →
      IntegrableOn Q₀ (K ×ˢ Icc a' c') ν ∧
        0 ≤ ∫ z in K ×ˢ Icc a' c', Q₀ z ∂ν := by
  dsimp only
  intro hsource
  have h := integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc w hw v hv
  exact ⟨h.2.1, ge_of_tendsto h.2.2 hsource⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
