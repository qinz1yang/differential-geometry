import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointWeakHamiltonJacobiLimit
import DifferentialGeometry.Analysis.Calculus.Derivative.WeakIdentification
import Mathlib.Topology.Order.Compact

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

private theorem exists_compact_product_interval
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [LinearOrder T] [DenselyOrdered T] [ClosedIicTopology T] [ClosedIciTopology T]
    {C : Set (X × T)} {W : Set X} {a c : T}
    (hC : IsCompact C) (hne : C.Nonempty) (hCW : C ⊆ W ×ˢ Ioo a c) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ W ∧
      ∃ a' c' : T, a < a' ∧ a' < c' ∧ c' < c ∧ C ⊆ K ×ˢ Icc a' c' := by
  obtain ⟨zmin, hzmin, hmin⟩ := hC.exists_isMinOn hne continuous_snd.continuousOn
  obtain ⟨zmax, hzmax, hmax⟩ := hC.exists_isMaxOn hne continuous_snd.continuousOn
  obtain ⟨a', haa', ha'min⟩ := exists_between (hCW hzmin).2.1
  obtain ⟨c', hmaxc', hc'c⟩ := exists_between (hCW hzmax).2.2
  refine ⟨Prod.fst '' C, hC.image continuous_fst, ?_, a', c', haa', ?_, hc'c, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (hCW hz).1
  · exact (ha'min.trans_le (hmin hzmax)).trans hmaxc'
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, ha'min.le.trans (hmin hz),
      (hmax hz).trans hmaxc'.le⟩

namespace HalfLineMetricConvergenceData

theorem ae_poleEndpoint_redLength_limit_hamilton_jacobi
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
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    let f := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
    let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    ∀ᵐ z ∂ν, z ∈ W ×ˢ Ioo a c →
      fderiv ℝ f z (0, 1) + (1 / 2 : ℝ) *
        chartGradientBilin (co.gInf (1 - z.2)) x
          ((extChartAt I x).symm z.1) (d z) (d z) -
      (1 / 2 : ℝ) *
        metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1) +
      f z / (2 * z.2) = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (volume : Measure ℝ)
  let Ω : Set (E × ℝ) := W ×ˢ Ioo a c
  let f : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let Q := fun z => chartGradientBilin (co.gInf (1 - z.2)) x
    ((extChartAt I x).symm z.1) (d z) (d z)
  let S : E × ℝ → ℝ := fun z =>
    metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
  let G := fun z => (1 / 2 : ℝ) * Q z - (1 / 2 : ℝ) * S z + f z / (2 * z.2)
  have hΩ : IsOpen Ω := hW.prod isOpen_Ioo
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hQint {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
      (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
      IntegrableOn (fun z => w z * Q z) (K ×ˢ Icc a c) ν := by
    let _ : IsFiniteMeasure (ν.restrict (K ×ˢ Icc a c)) :=
      isFiniteMeasure_restrict.mpr (hK.prod isCompact_Icc).measure_ne_top
    have hi := integrableOn_poleEndpoint_redLength_limit_gradient_quadratic
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hW hK hKW hWt hWJ ν w hw
    simpa only [smul_apply, smul_eq_mul] using hi
  have hSint {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
      (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
      IntegrableOn (fun z => w z * S z) (K ×ˢ Icc a c) ν :=
    integrableOn_poleEndpoint_scalar_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R co ha.le x hK (hKW.trans hWt) w hw
  have hZint {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
      (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a c)) :
      IntegrableOn (fun z => w z / (2 * z.2) * f z) (K ×ˢ Icc a c) ν := by
    have hv : ContinuousOn (fun z : E × ℝ => w z / (2 * z.2)) (K ×ˢ Icc a c) :=
      hw.div (continuousOn_const.mul continuous_snd.continuousOn) (by
        intro z hz
        exact mul_ne_zero (by norm_num) (ha0.trans_le hz.2.1).ne')
    exact integrableOn_poleEndpoint_redLength_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha0 hbase
      rho hrho ell hconv x hK (hKW.trans hWt) (hWJ.mono_left hKW) _ hv
  have hG : LocallyIntegrableOn G Ω ν := by
    apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
    intro T hTΩ hT
    let K := Prod.fst '' T
    have hK : IsCompact K := hT.image continuous_fst
    have hKW : K ⊆ W := by
      rintro y ⟨z, hz, rfl⟩
      exact (hTΩ hz).1
    have hTC : T ⊆ K ×ˢ Icc a c := fun z hz =>
      ⟨mem_image_of_mem _ hz, (hTΩ hz).2.1.le, (hTΩ hz).2.2.le⟩
    have hQi : IntegrableOn Q (K ×ˢ Icc a c) ν := by
      simpa only [one_mul] using hQint hK hKW (fun _ => 1) continuousOn_const
    have hSi : IntegrableOn S (K ×ˢ Icc a c) ν := by
      simpa only [one_mul] using hSint hK hKW (fun _ => 1) continuousOn_const
    have hZi : IntegrableOn (fun z => f z / (2 * z.2)) (K ×ˢ Icc a c) ν := by
      have hi := hZint hK hKW (fun _ => 1) continuousOn_const
      convert hi using 1
      funext z
      ring
    have hi : IntegrableOn G (K ×ˢ Icc a c) ν :=
      ((hQi.const_mul (1 / 2 : ℝ)).sub (hSi.const_mul (1 / 2 : ℝ))).add hZi
    exact hi.mono_set hTC
  have hLip : LocallyLipschitzOn Ω f :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hWt hWJ).mono
        (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hweak : ∀ ψ : E × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ z, f z * fderiv ℝ ψ z (0, 1) ∂ν) = ∫ z, G z * ψ z ∂ν := by
    intro ψ hψ hψc hψΩ
    rcases (tsupport ψ).eq_empty_or_nonempty with hzero | hne
    · have hψzero : ψ = 0 := tsupport_eq_empty_iff.mp hzero
      subst ψ
      simp only [fderiv_zero, zero_apply, Pi.zero_apply, mul_zero, integral_zero]
    obtain ⟨K, hK, hKW, a', c', haa, _hac, hcc, hψC⟩ :=
      exists_compact_product_interval hψc hne hψΩ
    let C : Set (E × ℝ) := K ×ˢ Icc a' c'
    have hsub : C ⊆ K ×ˢ Icc a c := fun z hz =>
      ⟨hz.1, haa.le.trans hz.2.1, hz.2.2.trans hcc.le⟩
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have heq := poleEndpoint_redLength_limit_weak_hamilton_jacobi
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc
      ψ hψ1 hψc hψC
    have hQi : IntegrableOn (fun z => ψ z * Q z) C ν :=
      (hQint hK hKW ψ hψ.continuous.continuousOn).mono_set hsub
    have hSi : IntegrableOn (fun z => ψ z * S z) C ν :=
      (hSint hK hKW ψ hψ.continuous.continuousOn).mono_set hsub
    have hZi : IntegrableOn (fun z => ψ z / (2 * z.2) * f z) C ν :=
      (hZint hK hKW ψ hψ.continuous.continuousOn).mono_set hsub
    have hleft : (∫ z, f z * fderiv ℝ ψ z (0, 1) ∂ν) =
        ∫ z in C, f z * fderiv ℝ ψ z (0, 1) ∂ν := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hn : z ∉ tsupport ψ := fun h => hz (hψC h)
      simp only [fderiv_of_notMem_tsupport ℝ hn, zero_apply, mul_zero]
    have hright : (∫ z, G z * ψ z ∂ν) =
        (1 / 2 : ℝ) * (∫ z in C, ψ z * Q z ∂ν) -
        (1 / 2 : ℝ) * (∫ z in C, ψ z * S z ∂ν) +
        ∫ z in C, ψ z / (2 * z.2) * f z ∂ν := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C) (fun z hz => ?_)]
      · have hfun : (fun z => G z * ψ z) =
            fun z => (1 / 2 : ℝ) * (ψ z * Q z) -
              (1 / 2 : ℝ) * (ψ z * S z) + ψ z / (2 * z.2) * f z := by
          funext z
          dsimp only [G]
          ring
        have hQs : Integrable (fun z => (1 / 2 : ℝ) * (ψ z * Q z))
            (ν.restrict C) := hQi.const_mul _
        have hSs : Integrable (fun z => (1 / 2 : ℝ) * (ψ z * S z))
            (ν.restrict C) := hSi.const_mul _
        have hdiff : Integrable (fun z => (1 / 2 : ℝ) * (ψ z * Q z) -
            (1 / 2 : ℝ) * (ψ z * S z)) (ν.restrict C) := hQs.sub hSs
        rw [hfun, integral_add hdiff hZi, integral_sub hQs hSs,
          integral_const_mul, integral_const_mul]
      · have hn : z ∉ tsupport ψ := fun h => hz (hψC h)
        rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
    rw [hleft, hright]
    exact heq
  have hderiv := hLip.ae_fderiv_apply_eq_neg_of_integral_mul_fderiv_eq
    hΩ (μ := ν) hG (0, 1) hweak
  filter_upwards [hderiv] with z hz hzo
  have heq := hz hzo
  change fderiv ℝ f z (0, 1) + (1 / 2 : ℝ) * Q z -
    (1 / 2 : ℝ) * S z + f z / (2 * z.2) = 0
  dsimp only [G] at heq
  linarith only [heq]

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
