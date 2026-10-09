import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowHamiltonJacobi
import Mathlib.Topology.Order.ProjIcc
import DifferentialGeometry.Topology.LocallyUniformConvergence
import DifferentialGeometry.Analysis.Viscosity.Stability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Viscosity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Functional
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthContinuity
import DifferentialGeometry.Geometry.Operator.Laplacian.Coordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHeatTestPullback
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff BigOperators _root_.Topology
universe u uE uH

private theorem linear_heat_operator_convergence
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]
    {l : Filter ι} {U : Set (ℝ × E)} (hU : ∀ z ∈ U, z.1 ≠ 0) (b : κ → E) (d : ℝ)
    {A : ι → (ℝ × E) → κ → κ → ℝ} {a : (ℝ × E) → κ → κ → ℝ}
    {B : ι → (ℝ × E) → κ → κ → κ → ℝ} {beta : (ℝ × E) → κ → κ → κ → ℝ}
    (hA : ∀ i j, TendstoLocallyUniformlyOn (fun n x => A n x i j) (fun x => a x i j) l U)
    (hB : ∀ i j k, TendstoLocallyUniformlyOn (fun n x => B n x i j k) (fun x => beta x i j k) l U)
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) U)
    (hb : ∀ i j k, ContinuousOn (fun x => beta x i j k) U) :
    ContinuousOn
      (fun z : (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) × ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) =>
        (d / 2 - z.2.1) / z.1.1 - z.2.2.1 (1, 0) -
          ∑ i, ∑ j, a z.1 i j * (z.2.2.2 (0, b i) (0, b j) -
            ∑ k, beta z.1 i j k * z.2.2.1 (0, b k))) (U ×ˢ univ) ∧
    TendstoLocallyUniformlyOn
      (fun n (z : (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) × ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ)) =>
        (d / 2 - z.2.1) / z.1.1 - z.2.2.1 (1, 0) -
          ∑ i, ∑ j, A n z.1 i j * (z.2.2.2 (0, b i) (0, b j) -
            ∑ k, B n z.1 i j k * z.2.2.1 (0, b k)))
      (fun z => (d / 2 - z.2.1) / z.1.1 - z.2.2.1 (1, 0) -
        ∑ i, ∑ j, a z.1 i j * (z.2.2.2 (0, b i) (0, b j) -
          ∑ k, beta z.1 i j k * z.2.2.1 (0, b k))) l (U ×ˢ univ) := by
  let _ : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let Z := (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) × ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ)
  have hAA : TendstoLocallyUniformlyOn A a l U :=
    tendstoLocallyUniformlyOn_pi.mpr fun i => tendstoLocallyUniformlyOn_pi.mpr (hA i)
  have hBB : TendstoLocallyUniformlyOn B beta l U :=
    tendstoLocallyUniformlyOn_pi.mpr fun i => tendstoLocallyUniformlyOn_pi.mpr fun j => tendstoLocallyUniformlyOn_pi.mpr (hB i j)
  have haa : ContinuousOn a U := continuousOn_pi.mpr fun i => continuousOn_pi.mpr (ha i)
  have hbb : ContinuousOn beta U := continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => continuousOn_pi.mpr (hb i j)
  have hAZ : TendstoLocallyUniformlyOn (fun n (z : Z) => A n z.1) (fun z => a z.1)
      l (U ×ˢ univ) := hAA.comp Prod.fst (fun _ hz => hz.1) continuous_fst.continuousOn
  have hBZ : TendstoLocallyUniformlyOn (fun n (z : Z) => B n z.1) (fun z => beta z.1)
      l (U ×ˢ univ) := hBB.comp Prod.fst (fun _ hz => hz.1) continuous_fst.continuousOn
  have hId : TendstoLocallyUniformlyOn (fun _ : ι => (id : Z → Z)) id l (U ×ˢ univ) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    intro V hV
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hV
  let H : ((κ → κ → ℝ) × (κ → κ → κ → ℝ)) × Z → ℝ := fun w =>
    (d / 2 - w.2.2.1) / w.2.1.1 - w.2.2.2.1 (1, 0) -
      ∑ i, ∑ j, w.1.1 i j * (w.2.2.2.2 (0, b i) (0, b j) -
        ∑ k, w.1.2 i j k * w.2.2.2.1 (0, b k))
  have hcoeff : ContinuousOn (fun z : Z => ((a z.1, beta z.1), z)) (U ×ˢ univ) :=
    ((haa.comp continuous_fst.continuousOn (fun _ hz => hz.1)).prodMk
      (hbb.comp continuous_fst.continuousOn (fun _ hz => hz.1))).prodMk continuousOn_id
  have hH (z : Z) (hz : z ∈ U ×ˢ univ) : ContinuousAt H ((a z.1, beta z.1), z) := by
    have ht := hU z.1 hz.1
    dsimp only [H, Z]
    fun_prop (disch := exact ht)
  exact ⟨fun z hz => (hH z hz).comp_continuousWithinAt
      (f := fun y : Z => ((a y.1, beta y.1), y)) (hcoeff z hz),
    ((hAZ.prodMk hBZ).prodMk hId).comp_of_continuousAt hcoeff hH⟩

section Pullback

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]

private theorem redLength_heat_lower_test_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ Φ.source) {x : M} (hx : x ∈ U)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ y ∈ U, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (a : M) (hxa : x ∈ (chartAt H' a).source)
    (phi : ℝ × E' → ℝ) (hphi : ContDiffAt ℝ 2 phi (theta, extChartAt J a x))
    (htest : IsLocalMin (fun z : ℝ × E' =>
      redLength F.S 0 p (Φ ((extChartAt J a).symm z.2)) (c * z.1) - phi z)
      (theta, extChartAt J a x)) :
    fderiv ℝ phi (theta, extChartAt J a x) (1, 0) +
      ∑ i : Fin (Module.finrank ℝ E'), ∑ j : Fin (Module.finrank ℝ E'),
        chartInvGramOnE (I := J) g a i j (extChartAt J a x) *
          (fderiv ℝ (fderiv ℝ phi) (theta, extChartAt J a x) (0, chartModelBasis E' i) (0, chartModelBasis E' j) -
            ∑ k : Fin (Module.finrank ℝ E'), chartChristoffel (I := J) g a i j k (extChartAt J a x) *
              fderiv ℝ phi (theta, extChartAt J a x) (0, chartModelBasis E' k)) ≤
      ((Module.finrank ℝ E' : ℝ) / 2 - redLength F.S 0 p (Φ x) (c * theta)) / theta := by
  have hxs : x ∈ (extChartAt J a).source := by
    simpa only [extChartAt_source] using hxa
  have hchart : ContMDiffAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × E') 2
      (fun z : ℝ × M => (z.1, extChartAt J a z.2)) (theta, x) :=
    (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst,
      (contMDiffAt_extChartAt' hxa).comp (theta, x) (f := Prod.snd) contMDiffAt_snd⟩
  have hphiM : ContMDiffAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) 2
      (fun z : ℝ × M => phi (z.1, extChartAt J a z.2)) (theta, x) :=
    hphi.contMDiffAt.comp (theta, x) hchart
  have htestM : IsLocalMin (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi (z.1, extChartAt J a z.2)) (theta, x) := by
    have hsrc : ∀ᶠ z : ℝ × M in 𝓝 (theta, x), z.2 ∈ (extChartAt J a).source :=
      continuous_snd.continuousAt.tendsto.eventually (by
        change (extChartAt J a).source ∈ 𝓝 x
        simpa only [extChartAt_source] using (chartAt H' a).open_source.mem_nhds hxa)
    filter_upwards [hchart.continuousAt.tendsto.eventually htest, hsrc] with z hz hzs
    simpa only [(extChartAt J a).left_inv hzs, (extChartAt J a).left_inv hxs] using hz
  have hlocal : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w) := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact hg y hy
  have hh := ancient_redLength_time_deriv_add_laplacian_lower_test_pullback
    F hF p Φ (hU hx) hc htheta g hlocal (fun z => phi (z.1, extChartAt J a z.2)) hphiM htestM
  have ht := (hphi.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt theta
    ((hasDerivAt_id theta).prodMk (hasDerivAt_const theta (extChartAt J a x)))
  have hdt : deriv (fun t => phi (t, extChartAt J a x)) theta =
      fderiv ℝ phi (theta, extChartAt J a x) (1, 0) := by
    simpa only [Function.comp_def, id_eq] using ht.deriv
  rwa [hdt, laplacian_time_slice_comp_extChartAt g a hxa phi hphi] at hh

private theorem redLength_heat_chart_limit
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (Phi : ℕ → PartialDiffeomorph J I M F.M ∞) (a : M)
    {V : Set (ℝ × E')} (hV : IsOpen V)
    (hVdomain : V ⊆ Ioi 0 ×ˢ (extChartAt J a).target)
    (G : ℕ → ℝ → SmoothRiemannianMetric J M) (g : ℝ → SmoothRiemannianMetric J M)
    (hG : ∀ᶠ n in atTop, ∃ U : TopologicalSpace.Opens M,
      (extChartAt J a).symm '' (Prod.snd '' V) ⊆ U ∧ (U : Set M) ⊆ (Phi n).source ∧
      ∀ theta : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace J x,
        (G n theta).inner x v w = (c n)⁻¹ * (F.S.base.metric (-(c n * theta))).inner (Phi n x)
          (mfderiv J I (Phi n) x v) (mfderiv J I (Phi n) x w))
    (hA : ∀ i j : Fin (Module.finrank ℝ E'), TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E') => chartInvGramOnE (I := J) (G n z.1) a i j z.2)
      (fun z => chartInvGramOnE (I := J) (g z.1) a i j z.2) atTop V)
    (hB : ∀ i j k : Fin (Module.finrank ℝ E'), TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E') => chartChristoffel (I := J) (G n z.1) a i j k z.2)
      (fun z => chartChristoffel (I := J) (g z.1) a i j k z.2) atTop V)
    (ha : ∀ i j : Fin (Module.finrank ℝ E'), ContinuousOn
      (fun z : ℝ × E' => chartInvGramOnE (I := J) (g z.1) a i j z.2) V)
    (hb : ∀ i j k : Fin (Module.finrank ℝ E'), ContinuousOn
      (fun z : ℝ × E' => chartChristoffel (I := J) (g z.1) a i j k z.2) V)
    (ell : ℝ × E' → ℝ)
    (hell : TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E') => redLength F.S 0 p (Phi n ((extChartAt J a).symm z.2)) (c n * z.1))
      ell atTop V) :
    ∀ z ∈ V, ∀ phi : ℝ × E' → ℝ, ContDiffAt ℝ 2 phi z →
      IsLocalMin (fun y => ell y - phi y) z →
        fderiv ℝ phi z (1, 0) +
          ∑ i : Fin (Module.finrank ℝ E'), ∑ j : Fin (Module.finrank ℝ E'),
            chartInvGramOnE (I := J) (g z.1) a i j z.2 *
              (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E' i) (0, chartModelBasis E' j) -
                ∑ k : Fin (Module.finrank ℝ E'), chartChristoffel (I := J) (g z.1) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E' k)) ≤
          ((Module.finrank ℝ E' : ℝ) / 2 - ell z) / z.1 := by
  let H := fun (g : ℝ → SmoothRiemannianMetric J M) (z : ℝ × E') (r : ℝ)
      (P : (ℝ × E') →L[ℝ] ℝ) (A : (ℝ × E') →L[ℝ] (ℝ × E') →L[ℝ] ℝ) =>
    ((Module.finrank ℝ E' : ℝ) / 2 - r) / z.1 - P (1, 0) -
      ∑ i : Fin (Module.finrank ℝ E'), ∑ j : Fin (Module.finrank ℝ E'),
        chartInvGramOnE (I := J) (g z.1) a i j z.2 *
          (A (0, chartModelBasis E' i) (0, chartModelBasis E' j) -
            ∑ k : Fin (Module.finrank ℝ E'), chartChristoffel (I := J) (g z.1) a i j k z.2 * P (0, chartModelBasis E' k))
  let f (n : ℕ) (z : ℝ × E') := redLength F.S 0 p (Phi n ((extChartAt J a).symm z.2)) (c n * z.1)
  obtain ⟨hH, hHconv⟩ := linear_heat_operator_convergence
    (fun z hz => (hVdomain hz).1.ne') (chartModelBasis E') (Module.finrank ℝ E') hA hB ha hb
  have hcont : ∀ᶠ n in atTop, ContinuousOn (f n) V := by
    filter_upwards [hG] with n hn
    obtain ⟨U, himage, hsource, _⟩ := hn
    intro z hz
    have hxU : (extChartAt J a).symm z.2 ∈ U := himage ⟨z.2, ⟨z, hz, rfl⟩, rfl⟩
    have hsp : ContinuousAt (fun y : E' => Phi n ((extChartAt J a).symm y)) z.2 :=
      ((Phi n).mdifferentiableAt (by simp) (hsource hxU)).continuousAt.comp
        (continuousAt_extChartAt_symm'' (hVdomain hz).2)
    have hmap : ContinuousAt (fun y : ℝ × E' => (c n * y.1, Phi n ((extChartAt J a).symm y.2))) z :=
      (continuous_const.mul continuous_fst).continuousAt.prodMk
        (hsp.comp continuous_snd.continuousAt)
    have hp : (c n * z.1, Phi n ((extChartAt J a).symm z.2)) ∈ Ioi 0 ×ˢ univ :=
      ⟨mul_pos (hc n) (hVdomain hz).1, mem_univ _⟩
    exact (((continuousOn_redLength_space_time_of_ancient F hF p).continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)).comp
        (f := fun y : ℝ × E' => (c n * y.1, Phi n ((extChartAt J a).symm y.2))) hmap).continuousWithinAt
  have htests : ∀ᶠ n in atTop, ∀ z ∈ V, ∀ phi : ℝ × E' → ℝ, ContDiffAt ℝ 2 phi z →
      IsLocalMin (fun y => f n y - phi y) z →
        0 ≤ H (G n) z (f n z) (fderiv ℝ phi z) (fderiv ℝ (fderiv ℝ phi) z) := by
    filter_upwards [hG] with n hn
    obtain ⟨U, himage, hsource, hinner⟩ := hn
    intro z hz phi hphi hmin
    have hxU : (extChartAt J a).symm z.2 ∈ U := himage ⟨z.2, ⟨z, hz, rfl⟩, rfl⟩
    have hxs : (extChartAt J a).symm z.2 ∈ (chartAt H' a).source := by
      simpa only [extChartAt_source] using (extChartAt J a).map_target (hVdomain hz).2
    have hright : extChartAt J a ((extChartAt J a).symm z.2) = z.2 :=
      (extChartAt J a).right_inv (hVdomain hz).2
    have hpd : ContDiffAt ℝ 2 phi (z.1, extChartAt J a ((extChartAt J a).symm z.2)) := by
      simpa only [hright, Prod.eta] using hphi
    have hm : IsLocalMin (fun y : ℝ × E' => f n y - phi y)
        (z.1, extChartAt J a ((extChartAt J a).symm z.2)) := by simpa only [hright, Prod.eta] using hmin
    have hh := redLength_heat_lower_test_in_chart F hF p (Phi n) U hsource hxU
      (hc n) (hVdomain hz).1 (G n z.1) (hinner z.1) a hxs phi hpd hm
    simp only [hright, Prod.eta] at hh
    exact sub_nonneg.mpr ((le_sub_iff_add_le').mpr hh)
  intro z hz phi hphi hmin
  have hh := DifferentialGeometry.Analysis.Viscosity.lower_test_ge_of_tendstoLocallyUniformlyOn
    (H := H g) (Hn := fun n => H (G n)) hV hcont hell hH hHconv htests hz phi hphi hmin
  exact (le_sub_iff_add_le').mp (sub_nonneg.mp hh)

end Pullback
section BackwardFlow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem backward_solution_heat_coefficients_continuous
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (a : L.M) :
    (∀ i j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun w : ℝ × E => chartInvGramOnE (I := I) (L.S.base.metric (1 - w.1)) a i j w.2)
      (Ioi 1 ×ˢ (extChartAt I a).target)) ∧
    (∀ i j k : Fin (Module.finrank ℝ E), ContinuousOn
      (fun w : ℝ × E => chartChristoffel (I := I) (L.S.base.metric (1 - w.1)) a i j k w.2)
      (Ioi 1 ×ˢ (extChartAt I a).target)) := by
  have hmap : Continuous (fun w : ℝ × E => (1 - w.1, w.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hmaps : MapsTo (fun w : ℝ × E => (1 - w.1, w.2))
      (Ioi 1 ×ˢ (extChartAt I a).target) (Iio 0 ×ˢ interior (extChartAt I a).target) := by
    intro w hw
    change 1 - w.1 < 0 ∧ w.2 ∈ interior (extChartAt I a).target
    exact ⟨sub_neg.mpr hw.1, by simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hw.2⟩
  constructor
  · intro i j
    have hh := (MetricFamilySmoothOn.chartInvGramOnE_continuousOn L.isSolution.smoothMetric
      (J := Iio 0) Subset.rfl a i j).comp hmap.continuousOn hmaps
    exact hh
  · intro i j k
    have hh := (MetricFamilySmoothOn.chartChristoffelOnE_continuousOn L.isSolution.smoothMetric
      (J := Iio 0) Subset.rfl (uniqueDiffOn_Iio 0) a i j k).comp hmap.continuousOn hmaps
    exact hh

theorem heat_lower_test_of_rescaled_reducedLength_limit_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (Phi : ℕ → PartialDiffeomorph I I L.M F.M ∞)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ (Phi n).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (c n)⁻¹ * (F.S.base.metric (c n * (t - 1))).inner (Phi n x)
            (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi n w.1) (c n * w.2)) ell atTop Q)
    (a : L.M) {z : ℝ × E} (hz : z ∈ Ioo 1 T ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    IsLocalMin (fun w => f w - phi w) z →
      fderiv ℝ phi z (1, 0) +
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k)) ≤
        ((Module.finrank ℝ E : ℝ) / 2 - f z) / z.1 := by
  obtain ⟨K, ⟨hKn, hK⟩, hKt⟩ := (compact_basis_nhds z.2).mem_iff.mp
    ((isOpen_extChartAt_target (I := I) a).mem_nhds hz.2)
  let V := Ioo (1 : ℝ) T ×ˢ interior K
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_interior
  have hzV : z ∈ V := ⟨hz.1, mem_interior_iff_mem_nhds.mpr hKn⟩
  have hVdomain : V ⊆ Ioi 0 ×ˢ (extChartAt I a).target :=
    fun w hw => ⟨zero_lt_one.trans hw.1.1, hKt (interior_subset hw.2)⟩
  let G' := fun n theta => G n (1 - theta)
  let g := fun theta => L.S.base.metric (1 - theta)
  let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
  have hcompact : IsCompact ((extChartAt I a).symm '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm a).mono hKt)
  have hlocal : ∀ᶠ n in atTop, ∃ U : TopologicalSpace.Opens L.M,
      (extChartAt I a).symm '' (Prod.snd '' V) ⊆ U ∧ (U : Set L.M) ⊆ (Phi n).source ∧
      ∀ theta : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (G' n theta).inner x v w = (c n)⁻¹ * (F.S.base.metric (-(c n * theta))).inner (Phi n x)
          (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w) := by
    filter_upwards [hG _ hcompact] with n hn
    obtain ⟨U, hU, hKU, hUsrc, hinner⟩ := hn
    refine ⟨⟨U, hU⟩, ?_, hUsrc, ?_⟩
    · rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact hKU ⟨w.2, interior_subset hw.2, rfl⟩
    · intro theta x hx v w
      have htime : c n * ((1 - theta) - 1) = -(c n * theta) := by ring
      simpa only [G', htime] using hinner (1 - theta) x hx v w
  have hinterval : Icc (1 - T) 0 ⊆ Iic (0 : ℝ) := fun _ ht => ht.2
  have hslab : Icc (-T) 0 ⊆ ancientTimeInterval.carrier := fun _ ht => ht.2
  have hreg : Ioo (-T) 0 ⊆ ancientTimeInterval.regular := fun _ ht => ht.2
  have hleft : -T < 1 - T := by linarith
  have hright : 1 - T < 0 := by linarith
  let P : ℝ × E → ℝ × E := fun w => (1 - w.1, w.2)
  have hP : Continuous P := (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hPV : MapsTo P V (Ioo (1 - T) 0 ×ˢ (extChartAt I a).target) := by
    intro w hw
    exact ⟨⟨by dsimp only [P]; linarith only [hw.1.2],
      by dsimp only [P]; linarith only [hw.1.1]⟩, hKt (interior_subset hw.2)⟩
  have hA (k j : Fin (Module.finrank ℝ E)) : TendstoLocallyUniformlyOn
      (fun n (w : ℝ × E) => chartInvGramOnE (I := I) (G' n w.1) a k j w.2)
      (fun w => chartInvGramOnE (I := I) (g w.1) a k j w.2) atTop V :=
    (chartInvGram_locally_uniform_of_metric_convergence L.S L.isSolution hleft hright
      hslab hreg G R (hmetric (1 - T) 0 hinterval) a k j).comp P hPV hP.continuousOn
  have hB (i j k : Fin (Module.finrank ℝ E)) : TendstoLocallyUniformlyOn
      (fun n (w : ℝ × E) => chartChristoffel (I := I) (G' n w.1) a i j k w.2)
      (fun w => chartChristoffel (I := I) (g w.1) a i j k w.2) atTop V :=
    (chartChristoffel_locally_uniform_of_metric_convergence L.S L.isSolution hleft hright
      hslab hreg G R (hmetric (1 - T) 0 hinterval) a i j k).comp P hPV hP.continuousOn
  have hVcont : V ⊆ Ioi 1 ×ˢ (extChartAt I a).target :=
    fun w hw => ⟨hw.1.1, (hVdomain hw).2⟩
  obtain ⟨hga, hgb⟩ := backward_solution_heat_coefficients_continuous L a
  have ha (k j : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun w : ℝ × E => chartInvGramOnE (I := I) (g w.1) a k j w.2) V := (hga k j).mono hVcont
  have hxcont : ContinuousOn (fun w : ℝ × E => (extChartAt I a).symm w.2) V :=
    (continuousOn_extChartAt_symm a).comp continuous_snd.continuousOn (fun _ hw => (hVdomain hw).2)
  have hb (i j k : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun w : ℝ × E => chartChristoffel (I := I) (g w.1) a i j k w.2) V := (hgb i j k).mono hVcont
  have hf : TendstoLocallyUniformlyOn
      (fun n (w : ℝ × E) => redLength F.S 0 p (Phi n ((extChartAt I a).symm w.2)) (c n * w.1)) f atTop V := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hV).mpr
    intro Q hQV hQ
    let B : ℝ × E → L.M × Icc (1 : ℝ) T :=
      fun w => ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    have hB : ContinuousOn B V := hxcont.prodMk (continuous_projIcc.comp continuous_fst).continuousOn
    have himage := hQ.image_of_continuousOn (hB.mono hQV)
    have hcQ := Metric.tendstoUniformlyOn_iff.mp (hell (B '' Q) himage)
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro epsilon hepsilon
    filter_upwards [hcQ epsilon hepsilon] with n hn
    intro w hw
    have ht : w.1 ∈ Icc (1 : ℝ) T := ⟨(hQV hw).1.1.le, (hQV hw).1.2.le⟩
    have hh := hn (B w) ⟨w, hw, rfl⟩
    simpa only [B, f, projIcc_of_mem hT.le ht] using hh
  exact redLength_heat_chart_limit F hF p c hc Phi a hV hVdomain
    G' g hlocal hA hB ha hb f hf z hzV phi hphi

theorem backward_flow_reducedLength_limit_heat_lower_test_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
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
    (a : L.M) {z : ℝ × E} (hz : z ∈ Ioo 1 T ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    IsLocalMin (fun w => f w - phi w) z →
      fderiv ℝ phi z (1, 0) +
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k)) ≤
        ((Module.finrank ℝ E : ℝ) / 2 - f z) / z.1 := by
  apply heat_lower_test_of_rescaled_reducedLength_limit_in_chart
    F hF p (fun n => tau (subseq n)) (fun n => htau (subseq n)) L Phi.partialDiffeomorph
    R G _ hmetric hT ell hell a hz phi hphi
  intro K hK
  filter_upwards [hG K hK] with n hn
  obtain ⟨U, hU, hKU, hsource, hinner⟩ := hn
  refine ⟨U, hU, hKU, hsource, ?_⟩
  intro t x hx v w
  let e : PartialDiffeomorph I I L.M F.M ∞ := Phi.partialDiffeomorph n
  have hh := hinner t x hx v w
  rw [backwardFlowSequence_metric] at hh
  change (G n t).inner x v w =
    (scaleMetric (tau (subseq n))⁻¹ (inv_pos.mpr (htau (subseq n)))
      (F.S.base.metric (tau (subseq n) * (t - 1)))).inner (e x)
        (mfderiv I I e x v) (mfderiv I I e x w) at hh
  rw [scaleMetric_inner] at hh
  exact hh


variable [NeZero (Module.finrank ℝ E)]

theorem conjugate_heat_lower_test_of_rescaled_reducedLength_limit_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (Phi : ℕ → PartialDiffeomorph I I L.M F.M ∞)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ (Phi n).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (c n)⁻¹ * (F.S.base.metric (c n * (t - 1))).inner (Phi n x)
            (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi n w.1) (c n * w.2)) ell atTop Q)
    (a : L.M) {z : ℝ × E} (hz : z ∈ Ioo 1 T ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    IsLocalMin (fun w => f w - phi w) z →
      0 ≤ fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        (∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a k j z.2 *
            fderiv ℝ phi z (0, chartModelBasis E j) * fderiv ℝ phi z (0, chartModelBasis E k)) -
        metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) +
        (Module.finrank ℝ E : ℝ) / (2 * z.1) := by
  dsimp only
  intro hmin
  have hheat := heat_lower_test_of_rescaled_reducedLength_limit_in_chart
    F hF p c hc L Phi R G hG hmetric hT ell hell a hz phi hphi hmin
  have hHJ := (hamilton_jacobi_tests_of_rescaled_reducedLength_limit_in_chart
    F hF p c hc L Phi R G hG hmetric hT ell hell a hz phi (hphi.of_le (by norm_num))).2 hmin
  dsimp only at hheat hHJ
  have halgebra : ((Module.finrank ℝ E : ℝ) / 2 - ell ((extChartAt I a).symm z.2, projIcc 1 T hT.le z.1)) / z.1 +
      2 * (ell ((extChartAt I a).symm z.2, projIcc 1 T hT.le z.1) / (2 * z.1)) =
      (Module.finrank ℝ E : ℝ) / (2 * z.1) := by ring
  nlinarith

theorem backward_flow_reducedLength_limit_conjugate_heat_lower_test_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
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
    (a : L.M) {z : ℝ × E} (hz : z ∈ Ioo 1 T ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    IsLocalMin (fun w => f w - phi w) z →
      0 ≤ fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        (∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a k j z.2 *
            fderiv ℝ phi z (0, chartModelBasis E j) * fderiv ℝ phi z (0, chartModelBasis E k)) -
        metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) +
        (Module.finrank ℝ E : ℝ) / (2 * z.1) := by
  apply conjugate_heat_lower_test_of_rescaled_reducedLength_limit_in_chart
    F hF p (fun n => tau (subseq n)) (fun n => htau (subseq n)) L Phi.partialDiffeomorph
    R G _ hmetric hT ell hell a hz phi hphi
  intro K hK
  filter_upwards [hG K hK] with n hn
  obtain ⟨U, hU, hKU, hsource, hinner⟩ := hn
  refine ⟨U, hU, hKU, hsource, ?_⟩
  intro t x hx v w
  let e : PartialDiffeomorph I I L.M F.M ∞ := Phi.partialDiffeomorph n
  have hh := hinner t x hx v w
  rw [backwardFlowSequence_metric] at hh
  change (G n t).inner x v w =
    (scaleMetric (tau (subseq n))⁻¹ (inv_pos.mpr (htau (subseq n)))
      (F.S.base.metric (tau (subseq n) * (t - 1)))).inner (e x)
        (mfderiv I I e x v) (mfderiv I I e x w) at hh
  rw [scaleMetric_inner] at hh
  exact hh


theorem perelmanDensity_upper_test_of_rescaled_reducedLength_limit_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (Phi : ℕ → PartialDiffeomorph I I L.M F.M ∞)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ (Phi n).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (c n)⁻¹ * (F.S.base.metric (c n * (t - 1))).inner (Phi n x)
            (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi n w.1) (c n * w.2)) ell atTop Q)
    (a : L.M) {z : ℝ × E} (hz : z ∈ Ioo 1 T ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    IsLocalMax (fun w => u w - phi w) z →
      fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) * u z ≤ 0 := by
  let n := Module.finrank ℝ E
  let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
  let A := fun i j => chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2
  let B := fun i j k => chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2
  let d : E := ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (A i j * B i j k) • chartModelBasis E k
  have htime : 0 < z.1 := zero_lt_one.trans hz.1.1
  have hD (P : (ℝ × E) →L[ℝ] ℝ) : P (1, d) = P (1, 0) +
      ∑ i : Fin n, ∑ j : Fin n, A i j * ∑ k : Fin n, B i j k * P (0, chartModelBasis E k) := by
    have heq : ((1 : ℝ), d) = (1, (0 : E)) + (0, d) := by ext <;> simp
    rw [heq, map_add]
    change P (1, 0) + P ((ContinuousLinearMap.inr ℝ ℝ E) d) = _
    simp only [d, map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.inr_apply, Finset.mul_sum, mul_assoc]
  have hop (P : (ℝ × E) →L[ℝ] ℝ) (C : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) :
      P (1, d) - (∑ i : Fin n, ∑ j : Fin n, A i j * C (0, chartModelBasis E i) (0, chartModelBasis E j)) =
        P (1, 0) - ∑ i : Fin n, ∑ j : Fin n, A i j *
          (C (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin n, B i j k * P (0, chartModelBasis E k)) := by
    rw [hD]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hquad (P : (ℝ × E) →L[ℝ] ℝ) :
      (∑ i : Fin n, ∑ j : Fin n, A i j * P (0, chartModelBasis E i) * P (0, chartModelBasis E j)) =
        ∑ i : Fin n, ∑ j : Fin n, A i j * P (0, chartModelBasis E j) * P (0, chartModelBasis E i) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  dsimp only
  intro hmax
  have hh := perelmanDensity_upper_test_of_conjugate_heat_lower_test n f htime d
    (chartModelBasis E) A (metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2))
    (fun psi hpsi hmin => ?_) phi hphi hmax
  · rw [hop] at hh
    exact hh
  · have h := conjugate_heat_lower_test_of_rescaled_reducedLength_limit_in_chart
      F hF p c hc L Phi R G hG hmetric hT ell hell a hz psi hpsi hmin
    rw [hop, hquad]
    exact h

theorem backward_flow_limit_perelmanDensity_upper_test_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
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
    (a : L.M) {z : ℝ × E} (hz : z ∈ Ioo 1 T ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    IsLocalMax (fun w => u w - phi w) z →
      fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) * u z ≤ 0 := by
  apply perelmanDensity_upper_test_of_rescaled_reducedLength_limit_in_chart
    F hF p (fun n => tau (subseq n)) (fun n => htau (subseq n)) L Phi.partialDiffeomorph
    R G _ hmetric hT ell hell a hz phi hphi
  intro K hK
  filter_upwards [hG K hK] with n hn
  obtain ⟨U, hU, hKU, hsource, hinner⟩ := hn
  refine ⟨U, hU, hKU, hsource, ?_⟩
  intro t x hx v w
  let e : PartialDiffeomorph I I L.M F.M ∞ := Phi.partialDiffeomorph n
  have hh := hinner t x hx v w
  rw [backwardFlowSequence_metric] at hh
  change (G n t).inner x v w =
    (scaleMetric (tau (subseq n))⁻¹ (inv_pos.mpr (htau (subseq n)))
      (F.S.base.metric (tau (subseq n) * (t - 1)))).inner (e x)
        (mfderiv I I e x v) (mfderiv I I e x w) at hh
  rw [scaleMetric_inner] at hh
  exact hh


end BackwardFlow
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
