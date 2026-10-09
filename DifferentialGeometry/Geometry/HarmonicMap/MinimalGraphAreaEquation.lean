import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphEquation
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.MeanCurvatureReparametrization
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskTensionSmoothness
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The graph area integrand uses the original metric in the specified chart.
The fixed vector `N` need not be normal for the metric at the graph point. -/
def chartGraphAreaLagrangian (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a : M) (x₀ : E) (c : ℂ) (lift : ℂ → E) (N : E)
    (y : ℂ) (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  let B := chartMetricBilin g a (x₀ + lift (y - c) + t • N)
  let V := lift 1 + p.1 • N
  let W := lift Complex.I + p.2 • N
  Real.sqrt (B V V * B W W - (B V W) ^ 2)

/-- The two components of the actual derivative in the slope variables. -/
def chartGraphAreaFlux (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a : M) (x₀ : E) (c : ℂ) (lift : ℂ → E) (N : E)
    (y : ℂ) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let B := chartMetricBilin g a (x₀ + lift (y - c) + t • N)
  let V := lift 1 + p.1 • N
  let W := lift Complex.I + p.2 • N
  let J := chartGraphAreaLagrangian g a x₀ c lift N y t p
  ((B W W * B N V - B V W * B N W) / J,
   (B V V * B N W - B V W * B N V) / J)

/-- The height derivative of the same area integrand. It involves only the
position, first jet, and the original metric's chart Christoffel contraction. -/
def chartGraphAreaSource (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a : M) (x₀ : E) (c : ℂ) (lift : ℂ → E) (N : E)
    (y : ℂ) (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  let X := x₀ + lift (y - c) + t • N
  let B := chartMetricBilin g a X
  let V := lift 1 + p.1 • N
  let W := lift Complex.I + p.2 • N
  let CV := chartChristoffelContraction g a N V X
  let CW := chartChristoffelContraction g a N W X
  (B W W * B CV V + B V V * B CW W -
      B V W * (B CV W + B CW V)) /
    chartGraphAreaLagrangian g a x₀ c lift N y t p

omit [FiniteDimensional ℝ E] in
private theorem chartMetricBilin_symmetric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M) (x v w : E) :
    chartMetricBilin g a x v w = chartMetricBilin g a x w v :=
  g.symm _ _ _

omit [FiniteDimensional ℝ E] in
/-- The explicit inverse-Gram flux really is the full derivative in the two
slope variables; no equation or regularity of a graph is assumed here. -/
theorem hasFDerivAt_chartGraphAreaLagrangian_slope
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a : M) (x₀ : E) (c : ℂ) (lift : ℂ → E) (N : E)
    (y : ℂ) (t : ℝ) (p : ℝ × ℝ)
    (hdet : 0 <
      let B := chartMetricBilin g a (x₀ + lift (y - c) + t • N)
      let V := lift 1 + p.1 • N
      let W := lift Complex.I + p.2 • N
      B V V * B W W - (B V W) ^ 2) :
    HasFDerivAt (chartGraphAreaLagrangian g a x₀ c lift N y t)
      ((chartGraphAreaFlux g a x₀ c lift N y t p).1 •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (chartGraphAreaFlux g a x₀ c lift N y t p).2 •
          ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  let B := chartMetricBilin g a (x₀ + lift (y - c) + t • N)
  let V : ℝ × ℝ → E := fun q => lift 1 + q.1 • N
  let W : ℝ × ℝ → E := fun q => lift Complex.I + q.2 • N
  have hV : HasFDerivAt V ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight N) p := by
    simpa only [V, ContinuousLinearMap.coe_fst'] using
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).smul_const N).const_add (lift 1)
  have hW : HasFDerivAt W ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight N) p := by
    simpa only [W, ContinuousLinearMap.coe_snd'] using
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt).smul_const N).const_add
        (lift Complex.I)
  have hA := ((hasFDerivAt_const B p).clm_apply hV).clm_apply hV
  have hB := ((hasFDerivAt_const B p).clm_apply hV).clm_apply hW
  have hC := ((hasFDerivAt_const B p).clm_apply hW).clm_apply hW
  have hd := ((hA.mul hC).sub (hB.pow 2)).sqrt hdet.ne'
  change HasFDerivAt (chartGraphAreaLagrangian g a x₀ c lift N y t) _ p at hd
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  have hsymV : B (V p) N = B N (V p) := chartMetricBilin_symmetric g a _ _ _
  have hsymW : B (W p) N = B N (W p) := chartMetricBilin_symmetric g a _ _ _
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, map_smul, add_zero, smul_eq_mul,
    Nat.reduceSub, pow_one, hsymV, hsymW, Pi.mul_apply, Pi.sub_apply]
  change _ = (chartGraphAreaFlux g a x₀ c lift N y t p).1 * q.1 +
    (chartGraphAreaFlux g a x₀ c lift N y t p).2 * q.2
  dsimp only [chartGraphAreaFlux, chartGraphAreaLagrangian, B, V, W]
  ring

/-- The explicit first-order source is the actual derivative with respect to
height for the original chart metric. -/
theorem hasDerivAt_chartGraphAreaLagrangian_height
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a : M) (x₀ : E) (c : ℂ) (lift : ℂ → E) (N : E)
    (y : ℂ) (t : ℝ) (p : ℝ × ℝ)
    (hchart : x₀ + lift (y - c) + t • N ∈ (extChartAt 𝓘(ℝ, E) a).target)
    (hdet : 0 <
      let B := chartMetricBilin g a (x₀ + lift (y - c) + t • N)
      let V := lift 1 + p.1 • N
      let W := lift Complex.I + p.2 • N
      B V V * B W W - (B V W) ^ 2) :
    HasDerivAt (fun s => chartGraphAreaLagrangian g a x₀ c lift N y s p)
      (chartGraphAreaSource g a x₀ c lift N y t p) t := by
  let X : ℝ → E := fun s => x₀ + lift (y - c) + s • N
  let V := lift 1 + p.1 • N
  let W := lift Complex.I + p.2 • N
  have hX : HasDerivAt X N t := by
    simpa [X] using
      ((hasDerivAt_id t).smul_const N).const_add (x₀ + lift (y - c))
  have hA := chartMetricBilin_hasDerivAt g a hX
    (hasDerivAt_const t V) (hasDerivAt_const t V) hchart
  have hB := chartMetricBilin_hasDerivAt g a hX
    (hasDerivAt_const t V) (hasDerivAt_const t W) hchart
  have hC := chartMetricBilin_hasDerivAt g a hX
    (hasDerivAt_const t W) (hasDerivAt_const t W) hchart
  have hd := ((hA.mul hC).sub (hB.pow 2)).sqrt hdet.ne'
  change HasDerivAt (fun s => chartGraphAreaLagrangian g a x₀ c lift N y s p) _ t at hd
  apply hd.congr_deriv
  simp only [zero_add, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [chartMetricBilin_symmetric g a (X t) V
      (chartChristoffelContraction g a N V (X t)),
    chartMetricBilin_symmetric g a (X t) W
      (chartChristoffelContraction g a N W (X t)),
    chartMetricBilin_symmetric g a (X t) V
      (chartChristoffelContraction g a N W (X t))]
  dsimp only [chartGraphAreaSource, chartGraphAreaLagrangian, X, V, W,
    Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  ring

/-- The original harmonic disk supplies the zero mean trace of its actual
reparametrized immersed patch. This retains the same map and original metric. -/
theorem complexDivergence_flux_of_harmonic_reparametrization
    (O : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U F : ℂ → M) (ψ : ℂ → ℂ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : O => ψ q))
    (hmaps : Set.MapsTo ψ O (Metric.ball 0 1))
    (hbij : ∀ z : O, Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : O => ψ q) z))
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : O => F q))
    (hiF : ∀ z : O, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : O => F q) z))
    (heq : Set.EqOn F (U ∘ ψ) O)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U z = 0)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (F z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (F z) (W z)) (O : Set ℂ)) (z : O) :
    Analysis.complexDivergence (ImmersedDiskDivergence.fluxOne g F W)
      (ImmersedDiskDivergence.fluxI g F W) z =
      ImmersedDiskDivergence.immersedSectionDivergence g F W z := by
  apply ImmersedDiskDivergence.complexDivergence_flux_eq_immersedSectionDivergence_of_mean_zero
    O g F hF hiF hW z
  exact inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
    O g U F ψ hU hψ hmaps hbij hF hiF heq hconf htension z

private def graphCoordinateSection (a : M) (N : E) (F : ℂ → M)
    (z : ℂ) : TangentSpace 𝓘(ℝ, E) (F z) :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).symmL ℝ (F z) N

omit [FiniteDimensional ℝ E] in
private theorem contMDiffOn_graphCoordinateSection
    (a : M) (N : E) {F : ℂ → M} {s : Set ℂ}
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F s)
    (hchart : ∀ z ∈ s, F z ∈ (chartAt E a).source) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (F z) (graphCoordinateSection a N F z)) s := by
  apply ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).contMDiffOn_symmL_section N).comp hF
  intro z hz
  simpa only [TangentBundle.trivializationAt_baseSet, Set.mem_preimage] using hchart z hz

private theorem graphCoordinateSection_covariant_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M) (N : E)
    {F : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F s)
    (hchart : ∀ z ∈ s, F z ∈ (chartAt E a).source)
    {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).continuousLinearMapAt ℝ (F z)
      (sourceSectionCovariantDerivative g F (graphCoordinateSection a N F) z v) =
      chartChristoffelContraction g a N
        (fderiv ℝ (fun q => extChartAt 𝓘(ℝ, E) a (F q)) z v)
        (extChartAt 𝓘(ℝ, E) a (F z)) := by
  let line : ℝ → ℂ := fun t => z + t • v
  let γ : ℝ → M := fun t => F (line t)
  let W : ∀ t, TangentSpace 𝓘(ℝ, E) (γ t) :=
    fun t => graphCoordinateSection a N F (line t)
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) a
  let X : ℂ → E := fun q => extChartAt 𝓘(ℝ, E) a (F q)
  have hl0 : line 0 = z := by simp [line]
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hFz := hF.contMDiffAt (hs.mem_nhds hz)
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 := by
    have hF0 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F (line 0) := hl0.symm ▸ hFz
    exact (hF0.comp 0 hl.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hW0 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (γ t) (W t)) 0 := by
    have hw := (contMDiffOn_graphCoordinateSection a N hF hchart).contMDiffAt (hs.mem_nhds hz)
    have hw0 := hl0.symm ▸ hw
    exact hw0.comp 0 hl.contMDiff.contMDiffAt
  have hrep := (contDiffAt_chartRepAt_of_section hW0).differentiableAt (by simp)
  have ha : γ 0 ∈ (chartAt E a).source := by simpa [γ, hl0] using hchart z hz
  have hkey := covDeriv_chartAt g γ W 0 a hγ ha hrep
  have hbase : γ 0 ∈ T.baseSet := by
    simpa only [T, TangentBundle.trivializationAt_baseSet] using ha
  have hcoord : T.continuousLinearMapAt ℝ (γ 0) (covDerivAlong g γ W 0) =
      chartCovDerivAlong g a γ (chartRepAtBase a γ W) 0 := by
    rw [← hkey]
    exact T.continuousLinearMapAt_symmL hbase _
  have hconst : chartRepAtBase a γ W =ᶠ[𝓝 0] (fun _ => N) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds
      ((chartAt E a).open_source.mem_nhds ha)] with t ht
    change T.continuousLinearMapAt ℝ (γ t) (T.symmL ℝ (γ t) N) = N
    exact T.continuousLinearMapAt_symmL
      (by simpa only [T, TangentBundle.trivializationAt_baseSet, Set.mem_preimage] using ht) N
  have hX : DifferentiableAt ℝ X z :=
    (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z hFz).contDiffAt).differentiableAt (by simp)
  have hcurve : deriv (chartCurve (I := 𝓘(ℝ, E)) a γ) 0 = fderiv ℝ X z v := by
    change deriv (fun t : ℝ => X (z + t • v)) 0 = _
    exact deriv_comp_line hX
  have hcurve0 : chartCurve (I := 𝓘(ℝ, E)) a γ 0 =
      extChartAt 𝓘(ℝ, E) a (F z) := by
    simp only [chartCurve_def, γ, line, zero_smul, add_zero]
  have hLHS : T.continuousLinearMapAt ℝ (F z)
      (sourceSectionCovariantDerivative g F (graphCoordinateSection a N F) z v) =
      T.continuousLinearMapAt ℝ (γ 0) (covDerivAlong g γ W 0) := by
    have hγ0 : γ 0 = F z := by simp [γ, line]
    rw [← hγ0]
    congr 1
  rw [chartCovDerivAlong_def, hconst.deriv_eq, deriv_const, zero_add,
    hconst.eq_of_nhds, hcurve, hcurve0] at hcoord
  exact hLHS.trans (hcoord.trans (chartChristoffelContraction_symm g a _ _ _))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem fderiv_chart_graph
    (a : M) (x₀ : E) (c : ℂ) (L : ℂ →L[ℝ] E) (N : E)
    {F : ℂ → M} {h : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hgraph : ∀ y ∈ s, extChartAt 𝓘(ℝ, E) a (F y) =
      x₀ + L (y - c) + h y • N)
    {z : ℂ} (hz : z ∈ s) (hh : DifferentiableAt ℝ h z) (v : ℂ) :
    fderiv ℝ (fun q => extChartAt 𝓘(ℝ, E) a (F q)) z v =
      L v + (fderiv ℝ h z v) • N := by
  have hnear : (fun q => extChartAt 𝓘(ℝ, E) a (F q)) =ᶠ[𝓝 z]
      (fun q => x₀ + L (q - c) + h q • N) :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds hz) hgraph
  have hd := ((hasFDerivAt_const x₀ z).add
    (L.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c))).add
      (hh.hasFDerivAt.smul_const N)
  have hd' : HasFDerivAt (fun q => x₀ + L (q - c) + h q • N)
      (L + (fderiv ℝ h z).smulRight N) z := by
    refine (hd.congr_of_eventuallyEq ?_).congr_fderiv ?_
    · exact Filter.Eventually.of_forall (fun _ => rfl)
    · simp only [zero_add, ContinuousLinearMap.comp_id]
  rw [hnear.fderiv_eq, hd'.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]

private theorem chartGraphArea_coordinate_stress
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (a : M) (x₀ : E) (c : ℂ) (L : ℂ →L[ℝ] E) (N : E)
    {F : ℂ → M} {h : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F s)
    (hchart : ∀ y ∈ s, F y ∈ (chartAt E a).source)
    (hgraph : ∀ y ∈ s, extChartAt 𝓘(ℝ, E) a (F y) =
      x₀ + L (y - c) + h y • N)
    {z : ℂ} (hz : z ∈ s) (hh : DifferentiableAt ℝ h z) :
    (ImmersedDiskDivergence.fluxOne g F (graphCoordinateSection a N F) z,
      ImmersedDiskDivergence.fluxI g F (graphCoordinateSection a N F) z) =
        chartGraphAreaFlux g a x₀ c L N z (h z)
          (fderiv ℝ h z 1, fderiv ℝ h z Complex.I) ∧
    ImmersedDiskDivergence.immersedSectionDivergence g F
        (graphCoordinateSection a N F) z =
      chartGraphAreaSource g a x₀ c L N z (h z)
        (fderiv ℝ h z 1, fderiv ℝ h z Complex.I) := by
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) a
  let Z := x₀ + L (z - c) + h z • N
  let P : ℂ → E := fun v => L v + (fderiv ℝ h z v) • N
  have hpartial (v : ℂ) :
      T.continuousLinearMapAt ℝ (F z) (diskMapPartial F z v) = P v := by
    exact (diskMapPartial_trivAt_eq_fderiv v (hchart z hz)
      ((hF.contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp))).trans
        (fderiv_chart_graph a x₀ c L N hs hgraph hz hh v)
  have hpartial_mf (v : ℂ) : T.continuousLinearMapAt ℝ (F z)
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z) v) = P v := hpartial v
  have hsection : T.continuousLinearMapAt ℝ (F z)
      (graphCoordinateSection a N F z) = N := by
    exact T.continuousLinearMapAt_symmL
      (by simpa only [T, TangentBundle.trivializationAt_baseSet] using hchart z hz) N
  have hmetric (v w : TangentSpace 𝓘(ℝ, E) (F z)) :
      g.inner (F z) v w = chartMetricBilin g a Z
        (T.continuousLinearMapAt ℝ (F z) v)
        (T.continuousLinearMapAt ℝ (F z) w) := by
    dsimp only [Z]
    rw [← hgraph z hz]
    exact (chartMetricBilin_trivToE g a (F z) (hchart z hz) v w).symm
  have hcov (v : ℂ) : T.continuousLinearMapAt ℝ (F z)
      (sourceSectionCovariantDerivative g F (graphCoordinateSection a N F) z v) =
      chartChristoffelContraction g a N (P v) Z := by
    have hcov := graphCoordinateSection_covariant_chart g a N hs hF hchart hz v
    rw [fderiv_chart_graph a x₀ c L N hs hgraph hz hh v, hgraph z hz] at hcov
    exact hcov
  constructor
  · simp only [ImmersedDiskDivergence.fluxOne, ImmersedDiskDivergence.fluxI,
      ImmersedDiskDivergence.gramA, ImmersedDiskDivergence.gramB,
      ImmersedDiskDivergence.gramC, riemannianAreaDensity, tangentTwoJacobian,
      hmetric, hpartial, hpartial_mf, hsection]
    dsimp only [chartGraphAreaFlux, chartGraphAreaLagrangian, P, Z]
    congr 1 <;> ring
  · simp only [ImmersedDiskDivergence.immersedSectionDivergence,
      ImmersedDiskDivergence.gramA, ImmersedDiskDivergence.gramB,
      ImmersedDiskDivergence.gramC, riemannianAreaDensity, tangentTwoJacobian,
      hmetric, hpartial, hpartial_mf, hcov]
    rfl

/-- Off-center graph stress for the very same reparametrized harmonic disk.
The flux and source are the actual slope and height derivatives of the original
metric's graph area integrand. No smooth coefficient field is postulated. -/
theorem complexDivergence_chartGraphAreaFlux_of_harmonic_reparametrization
    (O : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U F : ℂ → M) (ψ : ℂ → ℂ)
    (a : M) (x₀ : E) (c : ℂ) (L : ℂ →L[ℝ] E) (N : E) (h : ℂ → ℝ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : O => ψ q))
    (hmaps : Set.MapsTo ψ O (Metric.ball 0 1))
    (hbij : ∀ z : O, Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : O => ψ q) z))
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : O => F q))
    (hiF : ∀ z : O, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : O => F q) z))
    (heq : Set.EqOn F (U ∘ ψ) O)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U z = 0)
    (hh : ContDiffOn ℝ ∞ h O)
    (hchart : ∀ z ∈ O, F z ∈ (chartAt E a).source)
    (hgraph : ∀ z ∈ O, extChartAt 𝓘(ℝ, E) a (F z) =
      x₀ + L (z - c) + h z • N) (z : O) :
    Analysis.complexDivergence
      (fun y => (chartGraphAreaFlux g a x₀ c L N y (h y)
        (fderiv ℝ h y 1, fderiv ℝ h y Complex.I)).1)
      (fun y => (chartGraphAreaFlux g a x₀ c L N y (h y)
        (fderiv ℝ h y 1, fderiv ℝ h y Complex.I)).2) z =
      chartGraphAreaSource g a x₀ c L N z (h z)
        (fderiv ℝ h z 1, fderiv ℝ h z Complex.I) := by
  have hFon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F (O : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hF.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hW := contMDiffOn_graphCoordinateSection a N hFon hchart
  have hdiv := complexDivergence_flux_of_harmonic_reparametrization O g U F ψ
    hU hψ hmaps hbij hF hiF heq hconf htension hW z
  have hid (q : ℂ) (hq : q ∈ O) := chartGraphArea_coordinate_stress
    g a x₀ c L N O.isOpen hFon hchart hgraph hq
      ((hh.contDiffAt (O.isOpen.mem_nhds hq)).differentiableAt (by simp))
  have hnear (k : ℝ × ℝ → ℝ) :
      (fun q => k (chartGraphAreaFlux g a x₀ c L N q (h q)
        (fderiv ℝ h q 1, fderiv ℝ h q Complex.I))) =ᶠ[𝓝 (z : ℂ)]
      (fun q => k (ImmersedDiskDivergence.fluxOne g F (graphCoordinateSection a N F) q,
        ImmersedDiskDivergence.fluxI g F (graphCoordinateSection a N F) q)) := by
    filter_upwards [O.isOpen.mem_nhds z.property] with q hq
    exact congrArg k (hid q hq).1.symm
  unfold Analysis.complexDivergence
  rw [(hnear Prod.fst).fderiv_eq, (hnear Prod.snd).fderiv_eq]
  exact hdiv.trans (hid z z.property).2

/-- The original leading-plane inverse germ supplies the area Euler--Lagrange
equation on its actual target. The lift agrees literally with the fixed lift
from the supplied original leading-plane data. -/
theorem chartLeadingPlaneProjection_graph_area_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hsdisk : s ⊆ Metric.ball (0 : ℂ) 1)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U z = 0)
    {a : ℂ} {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (N : E)
    (hunit : chartGramBilin g p (U a) N N = 1)
    (hprojN : chartLeadingPlaneProjection g p (U a) b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
          (fun i => (2 : ℝ) *
            (chartLeadingPlaneProjection g p (U a) b v * b i).re) +
        (chartGramBilin g p (U a) N v) • N)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hesource : e.source ⊆ s)
    (he : (e : ℂ → ℂ) = fun z => chartLeadingPlaneProjection g p (U a) b
      (extChartAt 𝓘(ℝ, E) p (U z)))
    (heinverse : ContDiffOn ℝ ∞ e.symm e.target)
    (y₀ : ℂ) (hy₀ : y₀ ∈ e.target) :
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) b
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
    ∃ L : ℂ →L[ℝ] E,
      (∀ w, L w = lift w) ∧ (∀ w, proj (L w) = w) ∧
      ContDiffOn ℝ ∞ h e.target ∧
      ∀ y ∈ e.target,
        Analysis.complexDivergence
          (fun q => (chartGraphAreaFlux g p (X a) (proj (X a)) L N q (h q)
            (fderiv ℝ h q 1, fderiv ℝ h q Complex.I)).1)
          (fun q => (chartGraphAreaFlux g p (X a) (proj (X a)) L N q (h q)
            (fderiv ℝ h q 1, fderiv ℝ h q Complex.I)).2) y =
          chartGraphAreaSource g p (X a) (proj (X a)) L N y (h y)
            (fderiv ℝ h y 1, fderiv ℝ h y Complex.I) := by
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) b
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * b i).re)
  let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
  let F : ℂ → M := fun y => U (e.symm y)
  let Xe : ℂ → E := fun y => X (e.symm y)
  let O : TopologicalSpace.Opens ℂ := ⟨e.target, e.open_target⟩
  have hdata := chartLeadingPlaneProjection_graph_equation g hs (hU.mono hsdisk)
    (fun z hz => hconf z (hsdisk hz)) (fun z hz => htension z (hsdisk hz))
    hchart N hunit hprojN hsplit e hesource he heinverse
  have hh : ContDiffOn ℝ ∞ h e.target := hdata.1
  have hgraph : ∀ y ∈ e.target,
      Xe y = X a + lift (y - proj (X a)) + h y • N := hdata.2.1
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)).comp z
      (hU.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsdisk hz)))).contDiffAt).contDiffWithinAt
  have hXe : ContDiffOn ℝ ∞ Xe e.target :=
    hX.comp heinverse (fun y hy => hesource (e.map_target hy))
  have hright (y : ℂ) (hy : y ∈ e.target) : proj (Xe y) = y := by
    change chartLeadingPlaneProjection g p (U a) b
      (extChartAt 𝓘(ℝ, E) p (U (e.symm y))) = y
    exact (congrFun he (e.symm y)).symm.trans (e.right_inv hy)
  have hprojD (y : ℂ) (hy : y ∈ e.target) :
      proj.comp (fderiv ℝ Xe y) = ContinuousLinearMap.id ℝ ℂ := by
    have hnear : proj ∘ Xe =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hy] with q hq using hright q hq
    have hd := proj.hasFDerivAt.comp y
      ((hXe.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    exact hd.fderiv.symm.trans (hnear.fderiv_eq.trans fderiv_id)
  let R : ℂ →L[ℝ] E := fderiv ℝ Xe y₀
  have hprojR (w : ℂ) : proj (R w) = w :=
    congrArg (fun D : ℂ →L[ℝ] ℂ => D w) (hprojD y₀ hy₀)
  let L : ℂ →L[ℝ] E := R - ((Q N).smulRight N).comp R
  have hL (w : ℂ) : L w = lift w := by
    have hsplitR := hsplit (R w)
    change R w = lift (proj (R w)) + Q N (R w) • N at hsplitR
    rw [hprojR] at hsplitR
    change R w - (Q N (R w)) • N = lift w
    exact sub_eq_iff_eq_add.mpr hsplitR
  have hprojL (w : ℂ) : proj (L w) = w := by
    change proj N = 0 at hprojN
    simp only [L, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, hprojN,
      smul_zero, sub_zero, hprojR]
  have hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : O => e.symm q) :=
    heinverse.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun q => q.property)
  have hmaps : Set.MapsTo e.symm O (Metric.ball (0 : ℂ) 1) :=
    fun q hq => hsdisk (hesource (e.map_target hq))
  have hFon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F (O : Set ℂ) :=
    hU.comp heinverse.contMDiffOn hmaps
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : O => F q) :=
    hFon.comp_contMDiff contMDiff_subtype_val (fun q => q.property)
  have hbij (q : O) : Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : O => e.symm y) q) := by
    rw [DifferentialGeometry.mfderiv_restrict_open e.symm O q, mfderiv_eq_fderiv]
    have hd : fderiv ℝ Xe q =
        (fderiv ℝ X (e.symm q)).comp (fderiv ℝ e.symm q) :=
      fderiv_comp (q : ℂ)
        ((hX.contDiffAt (hs.mem_nhds (hesource (e.map_target q.property)))).differentiableAt (by simp))
        ((heinverse.contDiffAt (e.open_target.mem_nhds q.property)).differentiableAt (by simp))
    have hinj : Function.Injective (fderiv ℝ e.symm q) := by
      intro v w hvw
      have h := congrArg (fun u => proj (fderiv ℝ X (e.symm q) u)) hvw
      have hcomp := hprojD q q.property
      rw [hd] at hcomp
      exact (congrArg (fun D : ℂ →L[ℝ] ℂ => D v = D w) hcomp).mp h
    exact ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (fderiv ℝ e.symm q).toLinearMap)).mp hinj⟩
  have hFchart (q : ℂ) (hq : q ∈ O) : F q ∈ (chartAt E p).source :=
    hchart _ (hesource (e.map_target hq))
  have hiF (q : O) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y : O => F y) q) := by
    rw [DifferentialGeometry.mfderiv_restrict_open F O q]
    intro v w hvw
    have h := congrArg (fun u => proj
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (F q) u)) hvw
    change proj ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (F q) (diskMapPartial F q v)) =
      proj ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (F q) (diskMapPartial F q w)) at h
    rw [diskMapPartial_trivAt_eq_fderiv v (hFchart q q.property)
        ((hFon.contMDiffAt (O.isOpen.mem_nhds q.property)).mdifferentiableAt (by simp)),
      diskMapPartial_trivAt_eq_fderiv w (hFchart q q.property)
        ((hFon.contMDiffAt (O.isOpen.mem_nhds q.property)).mdifferentiableAt (by simp))] at h
    change proj (fderiv ℝ Xe q v) = proj (fderiv ℝ Xe q w) at h
    exact (congrArg (fun D : ℂ →L[ℝ] ℂ => D v = D w) (hprojD q q.property)).mp h
  refine ⟨L, hL, hprojL, hh, ?_⟩
  intro y hy
  exact complexDivergence_chartGraphAreaFlux_of_harmonic_reparametrization
    O g U F e.symm p (X a) (proj (X a)) L N h hU hψ hmaps hbij hF hiF
    (fun _ _ => rfl) hconf htension hh hFchart
    (fun q hq => by simpa only [hL] using hgraph q hq) ⟨y, hy⟩

end DifferentialGeometry.Geometry
