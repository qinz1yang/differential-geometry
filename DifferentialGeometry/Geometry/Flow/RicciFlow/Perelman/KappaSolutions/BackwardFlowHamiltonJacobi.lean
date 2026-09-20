import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowSequence
import Mathlib.Topology.Order.ProjIcc
import DifferentialGeometry.Topology.LocallyUniformConvergence
import DifferentialGeometry.Analysis.HamiltonJacobi.Stability
import DifferentialGeometry.Analysis.HamiltonJacobi.Differentiability
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.Spacetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthContinuity
import DifferentialGeometry.Geometry.Operator.Gradient.Coordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobiPullback
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold ContDiff BigOperators _root_.Topology NNReal
universe u uE uH

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem hamilton_jacobi_test_in_chart
    (g : SmoothRiemannianMetric I M) (p : M) {t : ℝ} {x : M}
    (hx : x ∈ (chartAt H p).source)
    (hxint : extChartAt I p x ∈ interior (extChartAt I p).target)
    (phi : ℝ × E → ℝ) (hphi : DifferentiableAt ℝ phi (t, extChartAt I p x)) :
    deriv (fun s => phi (s, extChartAt I p x)) t +
      (1 / 2 : ℝ) * normGradSqFun g (fun y => phi (t, extChartAt I p y)) x =
    fderiv ℝ phi (t, extChartAt I p x) (1, 0) + (1 / 2 : ℝ) *
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g p k i (extChartAt I p x) *
          fderiv ℝ phi (t, extChartAt I p x) (0, chartModelBasis E i) *
          fderiv ℝ phi (t, extChartAt I p x) (0, chartModelBasis E k) := by
  have ht := hphi.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (extChartAt I p x)))
  have hs := hphi.hasFDerivAt.comp (extChartAt I p x)
    ((hasFDerivAt_const t (extChartAt I p x)).prodMk (hasFDerivAt_id (extChartAt I p x)))
  have hg := normGradSqFun_comp_extChartAt g p (f := phi ∘ Prod.mk t) hx hxint
  have hdt : deriv (fun s => phi (s, extChartAt I p x)) t =
      fderiv ℝ phi (t, extChartAt I p x) (1, 0) := by
    simpa only [Function.comp_def, id_eq] using ht.deriv
  rw [hs.fderiv] at hg
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, Function.comp_def] at hg
  rw [hdt, hg]


end Coordinates

private theorem quadratic_hamiltonian_convergence
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]
    {l : Filter ι} {U : Set (ℝ × E)} (hU : ∀ z ∈ U, z.1 ≠ 0) (b : κ → E)
    {A : ι → (ℝ × E) → κ → κ → ℝ} {a : (ℝ × E) → κ → κ → ℝ}
    {R : ι → (ℝ × E) → ℝ} {r : (ℝ × E) → ℝ}
    (hA : ∀ k j, TendstoLocallyUniformlyOn (fun n x => A n x k j) (fun x => a x k j) l U)
    (hR : TendstoLocallyUniformlyOn R r l U)
    (ha : ∀ k j, ContinuousOn (fun x => a x k j) U) (hr : ContinuousOn r U) :
    ContinuousOn
      (fun z : (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) =>
        z.2.2 (1, 0) + (1 / 2 : ℝ) * ∑ k, ∑ j,
          a z.1 k j * z.2.2 (0, b j) * z.2.2 (0, b k) -
        (1 / 2 : ℝ) * r z.1 + z.2.1 / (2 * z.1.1)) (U ×ˢ univ) ∧
    TendstoLocallyUniformlyOn
      (fun n (z : (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ)) =>
        z.2.2 (1, 0) + (1 / 2 : ℝ) * ∑ k, ∑ j,
          A n z.1 k j * z.2.2 (0, b j) * z.2.2 (0, b k) -
        (1 / 2 : ℝ) * R n z.1 + z.2.1 / (2 * z.1.1))
      (fun z => z.2.2 (1, 0) + (1 / 2 : ℝ) * ∑ k, ∑ j,
          a z.1 k j * z.2.2 (0, b j) * z.2.2 (0, b k) -
        (1 / 2 : ℝ) * r z.1 + z.2.1 / (2 * z.1.1)) l (U ×ˢ univ) := by
  let Z := (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ)
  have hAA : TendstoLocallyUniformlyOn A a l U :=
    tendstoLocallyUniformlyOn_pi.mpr fun k => tendstoLocallyUniformlyOn_pi.mpr (hA k)
  have haa : ContinuousOn a U := continuousOn_pi.mpr fun k => continuousOn_pi.mpr (ha k)
  have hAZ : TendstoLocallyUniformlyOn (fun n (z : Z) => A n z.1) (fun z => a z.1)
      l (U ×ˢ univ) := hAA.comp Prod.fst (fun _ hz => hz.1) continuous_fst.continuousOn
  have hRZ : TendstoLocallyUniformlyOn (fun n (z : Z) => R n z.1) (fun z => r z.1)
      l (U ×ˢ univ) := hR.comp Prod.fst (fun _ hz => hz.1) continuous_fst.continuousOn
  have hId : TendstoLocallyUniformlyOn (fun _ : ι => (id : Z → Z)) id l (U ×ˢ univ) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    intro V hV
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hV
  let H : ((κ → κ → ℝ) × ℝ) × Z → ℝ := fun w =>
    w.2.2.2 (1, 0) + (1 / 2 : ℝ) * ∑ k, ∑ j,
      w.1.1 k j * w.2.2.2 (0, b j) * w.2.2.2 (0, b k) -
    (1 / 2 : ℝ) * w.1.2 + w.2.2.1 / (2 * w.2.1.1)
  have hcoeff : ContinuousOn (fun z : Z => ((a z.1, r z.1), z)) (U ×ˢ univ) :=
    ((haa.comp continuous_fst.continuousOn (fun _ hz => hz.1)).prodMk
      (hr.comp continuous_fst.continuousOn (fun _ hz => hz.1))).prodMk continuousOn_id
  have hH (z : Z) (hz : z ∈ U ×ˢ univ) : ContinuousAt H ((a z.1, r z.1), z) := by
    have ht : 2 * z.1.1 ≠ 0 := mul_ne_zero two_ne_zero (hU z.1 hz.1)
    dsimp only [H, Z]
    fun_prop (disch := exact ht)
  exact ⟨fun z hz => (hH z hz).comp_continuousWithinAt
      (f := fun y : Z => ((a y.1, r y.1), y)) (hcoeff z hz),
    ((hAZ.prodMk hRZ).prodMk hId).comp_of_continuousAt hcoeff hH⟩

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

private theorem redLength_upper_test_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ Φ.source) {x : M} (hx : x ∈ U)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ y ∈ U, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (a : M) (hxa : x ∈ (chartAt H' a).source)
    (phi : ℝ × E' → ℝ) (hphi : DifferentiableAt ℝ phi (theta, extChartAt J a x))
    (htest : IsLocalMax (fun z : ℝ × E' =>
      redLength F.S 0 p (Φ ((extChartAt J a).symm z.2)) (c * z.1) - phi z)
      (theta, extChartAt J a x)) :
    fderiv ℝ phi (theta, extChartAt J a x) (1, 0) + (1 / 2 : ℝ) *
      ∑ k : Fin (Module.finrank ℝ E'), ∑ i : Fin (Module.finrank ℝ E'),
        chartInvGramOnE (I := J) g a k i (extChartAt J a x) *
          fderiv ℝ phi (theta, extChartAt J a x) (0, chartModelBasis E' i) *
          fderiv ℝ phi (theta, extChartAt J a x) (0, chartModelBasis E' k) -
      (1 / 2 : ℝ) * metricScalarAt g x +
      redLength F.S 0 p (Φ x) (c * theta) / (2 * theta) ≤ 0 := by
  have hxs : x ∈ (extChartAt J a).source := by
    simpa only [extChartAt_source] using hxa
  have hchart : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × E')
      (fun z : ℝ × M => (z.1, extChartAt J a z.2)) (theta, x) :=
    (mdifferentiableAt_prod_module_iff _).mpr ⟨mdifferentiableAt_fst,
      (mdifferentiableAt_extChartAt (I := J) hxa).comp (theta, x) (f := Prod.snd) mdifferentiableAt_snd⟩
  have hphiM : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi (z.1, extChartAt J a z.2)) (theta, x) :=
    hphi.mdifferentiableAt.comp (theta, x) hchart
  have htestM : IsLocalMax (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi (z.1, extChartAt J a z.2)) (theta, x) := by
    have hsrc : ∀ᶠ z : ℝ × M in 𝓝 (theta, x), z.2 ∈ (extChartAt J a).source :=
      continuous_snd.continuousAt.tendsto.eventually (by
        change (extChartAt J a).source ∈ 𝓝 x
        simpa only [extChartAt_source] using (chartAt H' a).open_source.mem_nhds hxa)
    filter_upwards [hchart.continuousAt.tendsto.eventually htest, hsrc] with z hz hzs
    simpa only [(extChartAt J a).left_inv hzs, (extChartAt J a).left_inv hxs] using hz
  have h := ancient_redLength_hamilton_jacobi_upper_test_of_local_pullback_metric
    F hF p Φ U hU hx hc htheta g hg (fun t y => phi (t, extChartAt J a y)) hphiM htestM
  have hxint : extChartAt J a x ∈ interior (extChartAt J a).target := by
    rw [(isOpen_extChartAt_target (I := J) a).interior_eq]
    exact (extChartAt J a).map_source hxs
  rwa [hamilton_jacobi_test_in_chart g a hxa hxint phi hphi] at h

private theorem redLength_lower_test_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ Φ.source) {x : M} (hx : x ∈ U)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ y ∈ U, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (a : M) (hxa : x ∈ (chartAt H' a).source)
    (phi : ℝ × E' → ℝ) (hphi : DifferentiableAt ℝ phi (theta, extChartAt J a x))
    (htest : IsLocalMin (fun z : ℝ × E' =>
      redLength F.S 0 p (Φ ((extChartAt J a).symm z.2)) (c * z.1) - phi z)
      (theta, extChartAt J a x)) :
    0 ≤ fderiv ℝ phi (theta, extChartAt J a x) (1, 0) + (1 / 2 : ℝ) *
      ∑ k : Fin (Module.finrank ℝ E'), ∑ i : Fin (Module.finrank ℝ E'),
        chartInvGramOnE (I := J) g a k i (extChartAt J a x) *
          fderiv ℝ phi (theta, extChartAt J a x) (0, chartModelBasis E' i) *
          fderiv ℝ phi (theta, extChartAt J a x) (0, chartModelBasis E' k) -
      (1 / 2 : ℝ) * metricScalarAt g x +
      redLength F.S 0 p (Φ x) (c * theta) / (2 * theta) := by
  have hxs : x ∈ (extChartAt J a).source := by
    simpa only [extChartAt_source] using hxa
  have hchart : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × E')
      (fun z : ℝ × M => (z.1, extChartAt J a z.2)) (theta, x) :=
    (mdifferentiableAt_prod_module_iff _).mpr ⟨mdifferentiableAt_fst,
      (mdifferentiableAt_extChartAt (I := J) hxa).comp (theta, x) (f := Prod.snd) mdifferentiableAt_snd⟩
  have hphiM : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi (z.1, extChartAt J a z.2)) (theta, x) :=
    hphi.mdifferentiableAt.comp (theta, x) hchart
  have htestM : IsLocalMin (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi (z.1, extChartAt J a z.2)) (theta, x) := by
    have hsrc : ∀ᶠ z : ℝ × M in 𝓝 (theta, x), z.2 ∈ (extChartAt J a).source :=
      continuous_snd.continuousAt.tendsto.eventually (by
        change (extChartAt J a).source ∈ 𝓝 x
        simpa only [extChartAt_source] using (chartAt H' a).open_source.mem_nhds hxa)
    filter_upwards [hchart.continuousAt.tendsto.eventually htest, hsrc] with z hz hzs
    simpa only [(extChartAt J a).left_inv hzs, (extChartAt J a).left_inv hxs] using hz
  have h := ancient_redLength_hamilton_jacobi_lower_test_of_local_pullback_metric
    F hF p Φ U hU hx hc htheta g hg (fun t y => phi (t, extChartAt J a y)) hphiM htestM
  have hxint : extChartAt J a x ∈ interior (extChartAt J a).target := by
    rw [(isOpen_extChartAt_target (I := J) a).interior_eq]
    exact (extChartAt J a).map_source hxs
  rwa [hamilton_jacobi_test_in_chart g a hxa hxint phi hphi] at h


private theorem redLength_hamilton_jacobi_chart_limit
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
    (hA : ∀ k j : Fin (Module.finrank ℝ E'), TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E') => chartInvGramOnE (I := J) (G n z.1) a k j z.2)
      (fun z => chartInvGramOnE (I := J) (g z.1) a k j z.2) atTop V)
    (hR : TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E') => metricScalarAt (G n z.1) ((extChartAt J a).symm z.2))
      (fun z => metricScalarAt (g z.1) ((extChartAt J a).symm z.2)) atTop V)
    (ha : ∀ k j : Fin (Module.finrank ℝ E'), ContinuousOn
      (fun z : ℝ × E' => chartInvGramOnE (I := J) (g z.1) a k j z.2) V)
    (hr : ContinuousOn (fun z : ℝ × E' => metricScalarAt (g z.1) ((extChartAt J a).symm z.2)) V)
    (ell : ℝ × E' → ℝ)
    (hell : TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E') => redLength F.S 0 p (Phi n ((extChartAt J a).symm z.2)) (c n * z.1))
      ell atTop V) :
    let H := fun (g : ℝ → SmoothRiemannianMetric J M) (z : ℝ × E') (r : ℝ)
        (P : (ℝ × E') →L[ℝ] ℝ) =>
      P (1, 0) + (1 / 2 : ℝ) * ∑ k : Fin (Module.finrank ℝ E'), ∑ j : Fin (Module.finrank ℝ E'),
        chartInvGramOnE (I := J) (g z.1) a k j z.2 * P (0, chartModelBasis E' j) * P (0, chartModelBasis E' k) -
      (1 / 2 : ℝ) * metricScalarAt (g z.1) ((extChartAt J a).symm z.2) + r / (2 * z.1)
    ∀ z ∈ V, ∀ phi : ℝ × E' → ℝ, ContDiffAt ℝ 1 phi z →
      (IsLocalMax (fun y => ell y - phi y) z → H g z (ell z) (fderiv ℝ phi z) ≤ 0) ∧
      (IsLocalMin (fun y => ell y - phi y) z → 0 ≤ H g z (ell z) (fderiv ℝ phi z)) := by
  let H := fun (g : ℝ → SmoothRiemannianMetric J M) (z : ℝ × E') (r : ℝ)
      (P : (ℝ × E') →L[ℝ] ℝ) =>
    P (1, 0) + (1 / 2 : ℝ) * ∑ k : Fin (Module.finrank ℝ E'), ∑ j : Fin (Module.finrank ℝ E'),
      chartInvGramOnE (I := J) (g z.1) a k j z.2 * P (0, chartModelBasis E' j) * P (0, chartModelBasis E' k) -
    (1 / 2 : ℝ) * metricScalarAt (g z.1) ((extChartAt J a).symm z.2) + r / (2 * z.1)
  let f (n : ℕ) (z : ℝ × E') := redLength F.S 0 p (Phi n ((extChartAt J a).symm z.2)) (c n * z.1)
  obtain ⟨hH, hHconv⟩ := quadratic_hamiltonian_convergence
    (fun z hz => (hVdomain hz).1.ne') (chartModelBasis E') hA hR ha hr
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
  have htests : ∀ᶠ n in atTop, ∀ z ∈ V, ∀ phi : ℝ × E' → ℝ, ContDiffAt ℝ 1 phi z →
      (IsLocalMax (fun y => f n y - phi y) z → H (G n) z (f n z) (fderiv ℝ phi z) ≤ 0) ∧
      (IsLocalMin (fun y => f n y - phi y) z → 0 ≤ H (G n) z (f n z) (fderiv ℝ phi z)) := by
    filter_upwards [hG] with n hn
    obtain ⟨U, himage, hsource, hinner⟩ := hn
    intro z hz phi hphi
    have hxU : (extChartAt J a).symm z.2 ∈ U := himage ⟨z.2, ⟨z, hz, rfl⟩, rfl⟩
    have hxs : (extChartAt J a).symm z.2 ∈ (chartAt H' a).source := by
      simpa only [extChartAt_source] using (extChartAt J a).map_target (hVdomain hz).2
    have hright : extChartAt J a ((extChartAt J a).symm z.2) = z.2 :=
      (extChartAt J a).right_inv (hVdomain hz).2
    have hpd : DifferentiableAt ℝ phi (z.1, extChartAt J a ((extChartAt J a).symm z.2)) := by
      rw [hright, Prod.eta]
      exact hphi.differentiableAt (by norm_num)
    constructor
    · intro hmax
      have hm : IsLocalMax (fun y : ℝ × E' => f n y - phi y)
          (z.1, extChartAt J a ((extChartAt J a).symm z.2)) := by simpa only [hright, Prod.eta] using hmax
      have hh := redLength_upper_test_in_chart F hF p (Phi n) U hsource hxU
        (hc n) (hVdomain hz).1 (G n z.1) (hinner z.1) a hxs phi hpd hm
      simpa only [hright, Prod.eta] using hh
    · intro hmin
      have hm : IsLocalMin (fun y : ℝ × E' => f n y - phi y)
          (z.1, extChartAt J a ((extChartAt J a).symm z.2)) := by simpa only [hright, Prod.eta] using hmin
      have hh := redLength_lower_test_in_chart F hF p (Phi n) U hsource hxU
        (hc n) (hVdomain hz).1 (G n z.1) (hinner z.1) a hxs phi hpd hm
      simpa only [hright, Prod.eta] using hh
  dsimp only
  intro z hz phi hphi
  exact ⟨fun hmax => DifferentialGeometry.Analysis.HamiltonJacobi.upper_test_le_of_tendstoLocallyUniformlyOn
      (H := H g) (Hn := fun n => H (G n)) hV hcont hell hH hHconv (htests.mono fun n hn z hz phi hp => (hn z hz phi hp).1) hz phi hphi hmax,
    fun hmin => DifferentialGeometry.Analysis.HamiltonJacobi.lower_test_ge_of_tendstoLocallyUniformlyOn
      (H := H g) (Hn := fun n => H (G n)) hV hcont hell hH hHconv (htests.mono fun n hn z hz phi hp => (hn z hz phi hp).2) hz phi hphi hmin⟩


end Pullback

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem metricScalar_locally_uniform_of_metric_convergence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b,
        metricDerivNormSupOn K r (g n t) (S.base.metric t) R < epsilon)
    (p : M) :
    TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E) => metricScalarAt (g n z.1) ((extChartAt I p).symm z.2))
      (fun z => metricScalarAt (S.base.metric z.1) ((extChartAt I p).symm z.2)) atTop
      (Ioo c b ×ˢ (extChartAt I p).target) := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) p))).mpr
  intro Q hQt hQ
  have hK : IsCompact (Prod.snd '' Q) := hQ.image continuous_snd
  have hKt : Prod.snd '' Q ⊆ (extChartAt I p).target := by
    rintro y ⟨z, hz, rfl⟩
    exact (hQt hz).2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := uniform_metricScalar_jets_of_metric_convergence_on_closed_interval
    S hS hac hcb hslab hreg g R isCompact_Icc Subset.rfl hconv p hK hKt 0
      (epsilon / 2) (half_pos hepsilon)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro z hz
  have hh := hN n hn z.1 ⟨(hQt hz).1.1.le, (hQt hz).1.2.le⟩ z.2 ⟨z, hz, rfl⟩
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] at hh
  rw [dist_comm, dist_eq_norm]
  exact hh.trans_lt (half_lt_self hepsilon)


end Metric

section BackwardFlow

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
private theorem backward_solution_chart_coefficients_continuous
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) (a : L.M) :
    (∀ k j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun w : ℝ × E => chartInvGramOnE (I := I) (L.S.base.metric (1 - w.1)) a k j w.2)
      (Ioi 1 ×ˢ (extChartAt I a).target)) ∧
    ContinuousOn (fun w : ℝ × E => metricScalarAt (L.S.base.metric (1 - w.1)) ((extChartAt I a).symm w.2))
      (Ioi 1 ×ˢ (extChartAt I a).target) := by
  constructor
  · intro k j
    have hh := MetricFamilySmoothOn.chartInvGramOnE_continuousOn L.isSolution.smoothMetric
      (J := Iio 0) Subset.rfl a k j
    apply hh.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    intro w hw
    refine ⟨?_, ?_⟩
    · change 1 - w.1 < 0
      exact sub_neg.mpr hw.1
    · rw [(isOpen_extChartAt_target (I := I) a).interior_eq]
      exact hw.2
  · have hxcont : ContinuousOn (fun w : ℝ × E => (extChartAt I a).symm w.2)
        (Ioi 1 ×ˢ (extChartAt I a).target) :=
      (continuousOn_extChartAt_symm a).comp continuous_snd.continuousOn (fun _ hw => hw.2)
    have hh : ContinuousOn (fun w : ℝ × L.M => metricScalarAt (L.S.base.metric w.1) w.2)
        (Iic 0 ×ˢ univ) := L.isSolution.scalarCont
    have hmap : ContinuousOn (fun w : ℝ × E => (1 - w.1, (extChartAt I a).symm w.2))
        (Ioi 1 ×ˢ (extChartAt I a).target) :=
      (continuous_const.sub continuous_fst).continuousOn.prodMk hxcont
    have hmaps : MapsTo (fun w : ℝ × E => (1 - w.1, (extChartAt I a).symm w.2))
        (Ioi 1 ×ˢ (extChartAt I a).target) (Iic 0 ×ˢ univ) := by
      intro w hw
      refine ⟨?_, mem_univ _⟩
      change 1 - w.1 ≤ 0
      exact sub_nonpos.mpr hw.1.le
    have hresult := hh.comp hmap hmaps
    exact hresult

theorem hamilton_jacobi_tests_of_rescaled_reducedLength_limit_in_chart
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
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 1 phi z) :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    let H := fderiv ℝ phi z (1, 0) + (1 / 2 : ℝ) *
      ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a k j z.2 *
          fderiv ℝ phi z (0, chartModelBasis E j) * fderiv ℝ phi z (0, chartModelBasis E k) -
      (1 / 2 : ℝ) * metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) +
      f z / (2 * z.1)
    (IsLocalMax (fun w => f w - phi w) z → H ≤ 0) ∧
      (IsLocalMin (fun w => f w - phi w) z → 0 ≤ H) := by
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
  have hR : TendstoLocallyUniformlyOn
      (fun n (w : ℝ × E) => metricScalarAt (G' n w.1) ((extChartAt I a).symm w.2))
      (fun w => metricScalarAt (g w.1) ((extChartAt I a).symm w.2)) atTop V :=
    (metricScalar_locally_uniform_of_metric_convergence L.S L.isSolution hleft hright
      hslab hreg G R (hmetric (1 - T) 0 hinterval) a).comp P hPV hP.continuousOn
  have hVcont : V ⊆ Ioi 1 ×ˢ (extChartAt I a).target :=
    fun w hw => ⟨hw.1.1, (hVdomain hw).2⟩
  obtain ⟨hga, hgr⟩ := backward_solution_chart_coefficients_continuous L a
  have ha (k j : Fin (Module.finrank ℝ E)) : ContinuousOn
      (fun w : ℝ × E => chartInvGramOnE (I := I) (g w.1) a k j w.2) V := (hga k j).mono hVcont
  have hxcont : ContinuousOn (fun w : ℝ × E => (extChartAt I a).symm w.2) V :=
    (continuousOn_extChartAt_symm a).comp continuous_snd.continuousOn (fun _ hw => (hVdomain hw).2)
  have hr : ContinuousOn (fun w : ℝ × E => metricScalarAt (g w.1) ((extChartAt I a).symm w.2)) V :=
    hgr.mono hVcont
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
  exact redLength_hamilton_jacobi_chart_limit F hF p c hc Phi a hV hVdomain
    G' g hlocal hA hR ha hr f hf z hzV phi hphi

theorem backward_flow_reducedLength_limit_hamilton_jacobi_tests_in_chart
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
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 1 phi z) :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    let H := fderiv ℝ phi z (1, 0) + (1 / 2 : ℝ) *
      ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a k j z.2 *
          fderiv ℝ phi z (0, chartModelBasis E j) * fderiv ℝ phi z (0, chartModelBasis E k) -
      (1 / 2 : ℝ) * metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) +
      f z / (2 * z.1)
    (IsLocalMax (fun w => f w - phi w) z → H ≤ 0) ∧
      (IsLocalMin (fun w => f w - phi w) z → 0 ≤ H) := by
  apply hamilton_jacobi_tests_of_rescaled_reducedLength_limit_in_chart
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


theorem backward_flow_reducedLength_limit_hamilton_jacobi_ae_in_chart
    [MeasurableSpace E] [BorelSpace E]
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
    (a : L.M) (μ : MeasureTheory.Measure (ℝ × E)) [μ.IsAddHaarMeasure] :
    let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
    ∀ᵐ z ∂μ.restrict (Ioo 1 T ×ˢ (extChartAt I a).target),
      fderiv ℝ f z (1, 0) + (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a k j z.2 *
            fderiv ℝ f z (0, chartModelBasis E j) * fderiv ℝ f z (0, chartModelBasis E k) -
        (1 / 2 : ℝ) * metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) +
        f z / (2 * z.1) = 0 := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let f := fun w : ℝ × E => ell ((extChartAt I a).symm w.2, projIcc 1 T hT.le w.1)
  let Ω := Ioo (1 : ℝ) T ×ˢ (extChartAt I a).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) a)
  have hf : LocallyLipschitzOn Ω f :=
    (Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip a).mono
      (fun _ hz => ⟨mem_univ _, hz.2⟩)
  let HJ : (ℝ × E) → ℝ → ((ℝ × E) →L[ℝ] ℝ) → ℝ := fun z r p =>
    p (1, 0) + (1 / 2 : ℝ) * ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a k j z.2 *
        p (0, chartModelBasis E j) * p (0, chartModelBasis E k) -
      (1 / 2 : ℝ) * metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) +
      r / (2 * z.1)
  apply DifferentialGeometry.Analysis.HamiltonJacobi.ae_eq_zero_of_tests_of_locallyLipschitzOn
    (H := HJ) hΩ hf
  · intro z hz φ hφ
    exact (backward_flow_reducedLength_limit_hamilton_jacobi_tests_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell a hz φ
        (hφ.of_le (by simp)).contDiffAt).1
  · intro z hz φ hφ
    exact (backward_flow_reducedLength_limit_hamilton_jacobi_tests_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell a hz φ
        (hφ.of_le (by simp)).contDiffAt).2
  · obtain ⟨hA, hR⟩ := backward_solution_chart_coefficients_continuous L a
    intro z hz
    have hz' : z.1 ∈ Ioi 1 ×ˢ (extChartAt I a).target := ⟨hz.1.1.1, hz.1.2⟩
    have hdom := (isOpen_Ioi.prod (isOpen_extChartAt_target (I := I) a)).mem_nhds hz'
    have hAc (k j : Fin (Module.finrank ℝ E)) : ContinuousAt
        (fun w : (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) =>
          chartInvGramOnE (I := I) (L.S.base.metric (1 - w.1.1)) a k j w.1.2) z :=
      ((hA k j z.1 hz').continuousAt hdom).comp continuousAt_fst
    have hRc : ContinuousAt
        (fun w : (ℝ × E) × ℝ × ((ℝ × E) →L[ℝ] ℝ) =>
          metricScalarAt (L.S.base.metric (1 - w.1.1)) ((extChartAt I a).symm w.1.2)) z :=
      ((hR z.1 hz').continuousAt hdom).comp continuousAt_fst
    have htime : 2 * z.1.1 ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt (zero_lt_one.trans hz.1.1.1))
    apply ContinuousAt.continuousWithinAt
    dsimp only [HJ]
    fun_prop (disch := exact htime)

end BackwardFlow
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
