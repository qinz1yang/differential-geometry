import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor0SBundle

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

theorem exists_uniform_window_flow_inner_bounds_of_local_curvature (K : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ζ : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1/2 → ∀ (J : RealTimeInterval) (θ : ℝ), θ ≤ τ →
      Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
      (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ < D →
        nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ < D →
      ∀ v : TangentSpace ThreeModel x,
        (1/4:ℝ)*metric.inner x.val v v ≤ (S.base.metric t).inner x v v ∧
        (S.base.metric t).inner x v v ≤ 4*metric.inner x.val v v := by
  let τ := Real.log 2/(18*Real.sqrt K+1)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 18*Real.sqrt K+1 := by positivity
  have hτ : 0 < τ := div_pos hlog hden
  have he : 18*Real.sqrt K*τ ≤ Real.log 2 := by
    have h := (le_div_iff₀ hden).mp (le_refl τ)
    change τ*(18*Real.sqrt K+1) ≤ Real.log 2 at h
    nlinarith
  have hexp : Real.exp (18*Real.sqrt K*τ) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
    exact Real.exp_le_exp.mpr he
  refine ⟨τ,hτ,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hζ J θ hθτ hcar hreg
    S hS hzero hcurv t ht x hx v
  have hsq : ∀ r ∈ Icc 0 θ, normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ K := by
    intro r hr
    simpa only [nablaKRm04NormSqIntrinsic,nablaKRm04Field_zero,Nat.add_zero] using hcurv r hr x hx
  have hb := metric_inner_exp_bounds_of_curvature_bound S hS hcar hreg x hsq ht
    ⟨le_rfl,ht.1.trans ht.2⟩ v
  rw [hzero,sub_zero,abs_of_nonneg ht.1] at hb
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ)=3 := by simp [ThreeSpace]
  rw [hdim] at hb
  have heq : 2*(3:ℝ)^2=18 := by norm_num
  simp only [heq] at hb
  have hinit := w.window_inner_bounds hζ hx v
  rw [standardCapMetric_eq_metric] at hinit
  change (1/2:ℝ)*metric.inner x.val v v ≤ w.windowMetric.inner x v v ∧
    w.windowMetric.inner x v v ≤ (3/2:ℝ)*metric.inner x.val v v at hinit
  have htarg : 18*Real.sqrt K*t ≤ 18*Real.sqrt K*τ :=
    mul_le_mul_of_nonneg_left (ht.2.trans hθτ) (by positivity)
  have hplus : Real.exp (18*Real.sqrt K*t) ≤ 2 := (Real.exp_le_exp.mpr htarg).trans hexp
  have hminus : (1/2:ℝ) ≤ Real.exp (-(18*Real.sqrt K*t)) := by
    rw [Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (Real.exp_pos _) hplus
  have hn := metric_inner_self_nonneg metric x.val v
  constructor
  · have hmul := mul_le_mul hminus hinit.1 (by positivity : 0 ≤ (1/2:ℝ)*metric.inner x.val v v)
      (Real.exp_nonneg _)
    nlinarith [hmul.trans hb.1]
  · have hmul := mul_le_mul hplus hinit.2 (metric_inner_self_nonneg w.windowMetric x v) (by norm_num)
    nlinarith [hb.2.trans hmul]

end DifferentialGeometry.PDE.RicciFlow.StandardCap
