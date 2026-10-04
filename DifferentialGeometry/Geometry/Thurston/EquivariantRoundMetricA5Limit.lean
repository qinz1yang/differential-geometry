import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5GaugeFlow
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionRate
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceShrinker
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Analysis.Elliptic.Poisson
import DifferentialGeometry.Analysis.Elliptic.PoissonStability
import DifferentialGeometry.Geometry.Metric.Convergence.IntegrableVelocity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropySquares
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Scaling
import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Geometry.Operator.Pullback

/-!
# The limit of the potential gauge has curvature two

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (design D18 (v)–(vi), review 18 §5).

* `scalar_eq_two_of_tracelessHess_eq_zero`: if `Δ_k f = R(k) − 2` and the traceless Hessian of `f`
  vanishes, then `k` is a gradient shrinking soliton with potential `−f` and `σ = 2`, so the surface
  classification `complete_surface_shrinker_compact_constant_scalar` gives `R(k) ≡ 2`.
* `tracelessHess_eq_zero_of_limit`: along a sequence `k j → kInf` in the fixed-background `C²` sense
  with mean-zero potentials, `∫ |M(k j, f j)|² → 0` forces `M(kInf, fInf) = 0`. The integrated
  Bochner identity `∫ |M|² = ½ ∫ (Δf)² − ½ ∫ R |∇f|²` is passed to the limit with the volume
  densities
  `dμ_{k j} / dμ_{kInf} → 1`, the uniform convergence of the scalar curvature
  (`exists_abs_metricScalarAt_sub_le`) and the strong `H¹` convergence of the potentials from
  `tendsto_meanZero_poisson_of_metric_tendsto`.
* `surfaceFlow_gauge_limit_round` (D18 (v)+(vi)): for the gauge `k t = ψ_t^* ĝ(t)` of the
  normalized flow, whose velocity `(T* − t)⁻¹ ψ_t^* M` has all intrinsic derivatives decaying,
  the integrable-velocity lemma `exists_metric_limit_of_exp_decay_velocity` is applied twice: in the
  normalized time `s` on `[t₁, T)` and in `σ` with `t = t₀ + (t₁ − t₀) e^{−σ}` on `(t₀, t₁]`
  (the gauge is smooth only on `(t₀, T)`). This gives a uniform lower bound and background bounds
  against `g(0)` on `[t₀, T)` and a smooth limit `kInf` with rate `(T* − t)^β`. The pulled-back
  potentials `f(t) ∘ ψ_t` solve `Δ_k f = R(k) − 2`, their traceless Hessians tend to `0` in `L²`,
  so `tracelessHess_eq_zero_of_limit` and `scalar_eq_two_of_tracelessHess_eq_zero` give
  `R(kInf) ≡ 2`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open Bundle MeasureTheory Filter Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance a5LimMeasurable : MeasurableSpace M := borel M
private local instance a5LimBorel : BorelSpace M := ⟨rfl⟩

theorem scalar_eq_two_of_tracelessHess_eq_zero (hdim : Module.finrank ℝ E = 2)
    (k : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (hf : ∀ x, ΔG k f x = metricScalarAt k x - 2)
    (hM : ∀ x, tracelessHessAt k f x = 0) (hpos : ∃ x, metricScalarAt k x ≠ 0) :
    ∀ x, metricScalarAt k x = 2 := by
  have hsol : gradientRicciSoliton (I := I) k (-f) 2 := by
    intro x v w
    have h1 := congrArg (fun A => A (vec2 v w)) (hM x)
    simp only [tracelessHessAt_vec2] at h1
    have hneg : hessFun (I := I) k (⇑(-f)) x v w = -hessFun (I := I) k f x v w := by
      have h2 : (⇑(-f) : M → ℝ) = (-1 : ℝ) • (⇑f : M → ℝ) := by
        funext y; simp
      rw [h2, hessFun_smul]
      simp
    rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two k hdim x v w, hneg]
    rw [hf x] at h1
    change hessFun (I := I) k f x v w - (metricScalarAt k x - 2) / 2 * k.inner x v w = 0 at h1
    linarith
  exact (complete_surface_shrinker_compact_constant_scalar k (-f) two_pos hdim
    (RiemannianMetricComplete.of_compact k) hsol hpos).2

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [ConnectedSpace M] in
theorem quadClose_of_metricDerivNorm_zero (h k kInf : SmoothRiemannianMetric I M)
    {lam : ℝ} (hlam : 0 < lam) (hlowInf : ∀ x (v : TangentSpace I x),
      lam * h.inner x v v ≤ kInf.inner x v v) (x : M) (v : TangentSpace I x) :
    |k.inner x v v - kInf.inner x v v| ≤
      (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 k kInf h x / lam *
        kInf.inner x v v := by
  have h1 := metricQuadFormDiff_le_metricDerivNorm (I := I) k kInf h x v
  have hfr : (Module.finrank ℝ (TangentSpace I x) : ℝ) = (Module.finrank ℝ E : ℝ) := rfl
  rw [hfr] at h1
  have hm : 0 ≤ (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 k kInf h x :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hh : h.inner x v v ≤ kInf.inner x v v / lam := by
    rw [le_div_iff₀ hlam, mul_comm]; exact hlowInf x v
  calc |k.inner x v v - kInf.inner x v v|
      ≤ (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 k kInf h x * h.inner x v v := h1
    _ ≤ (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 k kInf h x *
        (kInf.inner x v v / lam) := mul_le_mul_of_nonneg_left hh hm
    _ = _ := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem riemannianVolumeDensity_close (gInf : SmoothRiemannianMetric I M) (η : ℝ)
    (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ g' : SmoothRiemannianMetric I M,
      (∀ x : M, ∀ v : TangentSpace I x,
        |g'.inner x v v - gInf.inner x v v| ≤ δ * gInf.inner x v v) →
      ∀ x : M, |riemannianVolumeDensity gInf g' x - 1| ≤ η := by
  set φ : ℝ → ℝ := fun t => Real.sqrt ((1 + 2 * t) ^ Module.finrank ℝ E) with hφ
  have hφc : Continuous φ := by
    rw [hφ]; fun_prop
  have hφ0 : φ 0 = 1 := by simp [hφ]
  obtain ⟨δ₁, hδ₁, hδ₁φ⟩ := Metric.continuous_iff.1 hφc 0 η hη
  refine ⟨min (δ₁ / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _,
    fun g' hg' x => ?_⟩
  set δ := min (δ₁ / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ12 : δ ≤ 1 / 2 := min_le_right _ _
  have hφδ : φ δ < 1 + η := by
    have hd : dist δ 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
      exact (min_le_left _ _).trans_lt (by linarith)
    have := hδ₁φ δ hd
    rw [hφ0, Real.dist_eq] at this
    linarith [le_abs_self (φ δ - 1)]
  have hnn : ∀ (q : SmoothRiemannianMetric I M) (v : TangentSpace I x), 0 ≤ q.inner x v v := by
    intro q v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (q.pos x v hv).le
  have hQ : 0 < 1 + 2 * δ := by linarith
  have hup : ∀ v : TangentSpace I x, g'.inner x v v ≤ (1 + 2 * δ) * gInf.inner x v v := by
    intro v
    have := (abs_le.1 (hg' x v)).2
    nlinarith [hnn gInf v]
  have hdown : ∀ v : TangentSpace I x, gInf.inner x v v ≤ (1 + 2 * δ) * g'.inner x v v := by
    intro v
    have := (abs_le.1 (hg' x v)).1
    have h0 := hnn gInf v
    nlinarith [mul_nonneg (mul_nonneg hδ0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)) h0]
  have hd1 := riemannianVolumeDensity_le_of_inner_le (I := I) gInf g' hQ x hup
  have hd2 := riemannianVolumeDensity_le_of_inner_le (I := I) g' gInf hQ x hdown
  have hmul := riemannianVolumeDensity_mul (I := I) gInf g' gInf x
  rw [riemannianVolumeDensity_self] at hmul
  have hp1 := riemannianVolumeDensity_pos (I := I) gInf g' x
  change riemannianVolumeDensity gInf g' x ≤ φ δ at hd1
  change riemannianVolumeDensity g' gInf x ≤ φ δ at hd2
  rw [abs_le]
  constructor
  · have : 1 ≤ riemannianVolumeDensity gInf g' x * (1 + η) := by
      calc (1 : ℝ) = riemannianVolumeDensity gInf g' x * riemannianVolumeDensity g' gInf x :=
            hmul.symm
        _ ≤ riemannianVolumeDensity gInf g' x * (1 + η) :=
            mul_le_mul_of_nonneg_left (hd2.trans hφδ.le) hp1.le
    nlinarith
  · linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] in
theorem inner_gradFun_le_of_inner_le (g g₀ : SmoothRiemannianMetric I M) {Q : ℝ} (hQ : 0 ≤ Q)
    (f : M → ℝ) (x : M) (hcomp : ∀ v : TangentSpace I x, g.inner x v v ≤ Q * g₀.inner x v v) :
    g₀.inner x (gradFun (I := I) g₀ f x) (gradFun (I := I) g₀ f x) ≤
      Q * g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := by
  set X := gradFun (I := I) g₀ f x
  set Y := gradFun (I := I) g f x
  have hXX : g₀.inner x X X = g.inner x Y X := by
    rw [inner_gradFun (I := I) g₀ f x X, inner_gradFun (I := I) g f x X]
  have hnn : ∀ (q : SmoothRiemannianMetric I M) (v : TangentSpace I x), 0 ≤ q.inner x v v := by
    intro q v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (q.pos x v hv).le
  have hcs := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt (I := I) g x Y X
  set A := g₀.inner x X X
  set B := g.inner x Y Y
  have hA := hnn g₀ X
  have hB := hnn g Y
  have hXg : g.inner x X X ≤ Q * A := hcomp X
  have h1 : A ≤ Real.sqrt B * Real.sqrt (Q * A) := by
    calc A = g.inner x Y X := hXX
      _ ≤ |g.inner x Y X| := le_abs_self _
      _ ≤ Real.sqrt B * Real.sqrt (g.inner x X X) := hcs
      _ ≤ Real.sqrt B * Real.sqrt (Q * A) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hXg) (Real.sqrt_nonneg _)
  have h2 : A ^ 2 ≤ B * (Q * A) := by
    have := mul_self_le_mul_self hA h1
    rwa [mul_mul_mul_comm, Real.mul_self_sqrt hB, Real.mul_self_sqrt (mul_nonneg hQ hA),
      ← sq] at this
  by_cases hA0 : A = 0
  · rw [hA0]; exact mul_nonneg hQ hB
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem tendsto_integral_of_quadClose (k : ℕ → SmoothRiemannianMetric I M)
    (kInf : SmoothRiemannianMetric I M)
    (hclose : ∀ δ : ℝ, 0 < δ → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x (v : TangentSpace I x),
      |(k j).inner x v v - kInf.inner x v v| ≤ δ * kInf.inner x v v)
    (φ : ℕ → M → ℝ) (φInf : M → ℝ) (hφc : ∀ j, Continuous (φ j)) (hφInf : Continuous φInf)
    (hφ : ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x, |φ j x - φInf x| ≤ ε) :
    Tendsto (fun j => ∫ x, φ j x ∂riemannianVolumeMeasure I M (k j)) atTop
      (𝓝 (∫ x, φInf x ∂riemannianVolumeMeasure I M kInf)) := by
  classical
  set μI := riemannianVolumeMeasure I M kInf with hμI
  have hfmc : ∀ r : SmoothRiemannianMetric I M,
      IsFiniteMeasureOnCompacts (riemannianVolumeMeasure I M r) :=
    fun r => riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) r
  have hint : ∀ (r : SmoothRiemannianMetric I M) {G : M → ℝ}, Continuous G →
      Integrable G (riemannianVolumeMeasure I M r) :=
    fun r G hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set V := μI.real Set.univ with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set A := ∫ x, |φInf x| ∂μI with hA
  have hA0 : 0 ≤ A := integral_nonneg fun x => abs_nonneg _
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  set η₁ : ℝ := ε / (4 * (V + 1)) with hη₁
  have hη₁0 : 0 < η₁ := by positivity
  set η₂ : ℝ := min (1 / 2) (ε / (4 * (A + 1))) with hη₂
  have hη₂0 : 0 < η₂ := lt_min (by norm_num) (by positivity)
  obtain ⟨δ, hδ0, -, hδρ⟩ := riemannianVolumeDensity_close (I := I) kInf η₂ hη₂0
  obtain ⟨j₁, hj₁⟩ := hclose δ hδ0
  obtain ⟨j₂, hj₂⟩ := hφ η₁ hη₁0
  refine ⟨max j₁ j₂, fun j hj => ?_⟩
  have hρ := hδρ (k j) (hj₁ j ((le_max_left _ _).trans hj))
  have hφj := hj₂ j ((le_max_right _ _).trans hj)
  have hρcont : Continuous fun x => riemannianVolumeDensity kInf (k j) x :=
    (riemannianVolumeDensity_contMDiff (I := I) kInf (k j)).continuous
  have hvolj : (riemannianVolumeMeasure I M (k j)).real Set.univ ≤ 2 * V := by
    have h1 := integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (I := I) kInf
      (k j) (fun _ : M => (1 : ℝ))
    simp only [integral_const, smul_eq_mul, mul_one] at h1
    rw [h1]
    calc (∫ x, riemannianVolumeDensity kInf (k j) x ∂μI) ≤ ∫ _x, (2 : ℝ) ∂μI :=
          integral_mono (hint kInf hρcont) (integrable_const _) fun x => by
            have := (abs_le.1 (hρ x)).2
            have : η₂ ≤ 1 / 2 := min_le_left _ _
            linarith
      _ = 2 * V := by rw [integral_const, smul_eq_mul, mul_comm]
  have hfirst : |∫ x, (φ j x - φInf x) ∂riemannianVolumeMeasure I M (k j)| ≤ η₁ * (2 * V) := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc (∫ x, |φ j x - φInf x| ∂riemannianVolumeMeasure I M (k j)) ≤
        ∫ _x, η₁ ∂riemannianVolumeMeasure I M (k j) :=
          integral_mono (hint (k j) ((hφc j).sub hφInf).abs) (integrable_const _) hφj
      _ = η₁ * (riemannianVolumeMeasure I M (k j)).real Set.univ := by
          rw [integral_const, smul_eq_mul, mul_comm]
      _ ≤ η₁ * (2 * V) := mul_le_mul_of_nonneg_left hvolj hη₁0.le
  have hsecond : |(∫ x, φInf x ∂riemannianVolumeMeasure I M (k j)) - ∫ x, φInf x ∂μI| ≤
      η₂ * A := by
    have h1 : (∫ x, φInf x ∂riemannianVolumeMeasure I M (k j)) - ∫ x, φInf x ∂μI =
        ∫ x, (riemannianVolumeDensity kInf (k j) x - 1) * φInf x ∂μI := by
      have hI1 : Integrable (fun x => riemannianVolumeDensity kInf (k j) x * φInf x) μI :=
        hint kInf (hρcont.mul hφInf)
      have heq : (fun x => (riemannianVolumeDensity kInf (k j) x - 1) * φInf x) =
          fun x => riemannianVolumeDensity kInf (k j) x * φInf x - φInf x := by
        funext x; ring
      rw [heq, integral_sub hI1 (hint kInf hφInf),
        integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (I := I) kInf (k j)]
      simp only [smul_eq_mul]
      rfl
    rw [h1]
    refine (abs_integral_le_integral_abs).trans ?_
    calc (∫ x, |(riemannianVolumeDensity kInf (k j) x - 1) * φInf x| ∂μI) ≤
        ∫ x, η₂ * |φInf x| ∂μI := by
          refine integral_mono (hint kInf ((hρcont.sub continuous_const).mul hφInf).abs)
            (hint kInf (continuous_const.mul hφInf.abs)) fun x => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hρ x) (abs_nonneg _)
      _ = η₂ * A := by rw [integral_const_mul]
  have hsplit : (∫ x, φ j x ∂riemannianVolumeMeasure I M (k j)) - ∫ x, φInf x ∂μI =
      (∫ x, (φ j x - φInf x) ∂riemannianVolumeMeasure I M (k j)) +
        ((∫ x, φInf x ∂riemannianVolumeMeasure I M (k j)) - ∫ x, φInf x ∂μI) := by
    rw [integral_sub (hint (k j) (hφc j)) (hint (k j) hφInf)]; ring
  rw [Real.dist_eq, hsplit]
  have h3 : η₁ * (2 * V) < ε / 2 := by
    rw [hη₁, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have h4 : η₂ * A ≤ ε / 4 := by
    have : η₂ ≤ ε / (4 * (A + 1)) := min_le_right _ _
    calc η₂ * A ≤ ε / (4 * (A + 1)) * A := mul_le_mul_of_nonneg_right this hA0
      _ ≤ ε / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  calc |(∫ x, (φ j x - φInf x) ∂riemannianVolumeMeasure I M (k j)) +
        ((∫ x, φInf x ∂riemannianVolumeMeasure I M (k j)) - ∫ x, φInf x ∂μI)|
      ≤ |∫ x, (φ j x - φInf x) ∂riemannianVolumeMeasure I M (k j)| +
        |(∫ x, φInf x ∂riemannianVolumeMeasure I M (k j)) - ∫ x, φInf x ∂μI| := abs_add_le _ _
    _ < ε := by linarith

omit [CompactSpace M] [ConnectedSpace M] in
theorem tracelessHess_normSq_eq (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    normSq0S (I := I) g x 2 (tracelessHessAt g f x) =
      normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) - (ΔG (I := I) g f x) ^ 2 / 2 :=
  surfaceEntropy_traceFree_hessian_norm g hdim f x

omit [CompactSpace M] [ConnectedSpace M] in
private theorem hessian_normSq_pointwise (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) =
      (1 / 2 : ℝ) * ΔG (I := I) g
        ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩ x -
      (1 / 2 : ℝ) * (metricScalarAt (I := I) g x * normGradSqFun (I := I) g f x) -
      g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g (ΔG (I := I) g f) x) := by
  have hb := bochner_pointwise_half_grad_normSq_of_boundaryless (I := I) g f.contMDiff x
  rw [← surfaceEntropy_hessian_norm_eq_chart g f x,
    ricciTensor_apply_of_finrank_two g hdim] at hb
  change (1 / 2 : ℝ) * ΔG (I := I) g
      ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩ x =
    normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x) +
      (metricScalarAt (I := I) g x / 2) * normGradSqFun (I := I) g f x +
      g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g (ΔG (I := I) g f) x) at hb
  linarith

omit [CompactSpace M] [ConnectedSpace M] in
theorem hessian_normSq_continuous (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    Continuous (fun x : M => normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x)) := by
  let n : C^∞⟮I, M; ℝ⟯ :=
    ⟨normGradSqFun (I := I) g f, normGradSqFun_contMDiff g f.contMDiff⟩
  let d : C^∞⟮I, M; ℝ⟯ := ⟨ΔG (I := I) g f, Δ_g_contMDiff g f⟩
  have hgp : Continuous (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g d x)) :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g
      (gradG (I := I) g f) (gradG (I := I) g d)).continuous
  have hc := (((Δ_g_contMDiff g n).continuous.const_mul (1 / 2 : ℝ)).sub
    (((metricScalar_smooth g).continuous.mul
      (normGradSqFun_continuous g f.contMDiff)).const_mul (1 / 2 : ℝ))).sub hgp
  exact hc.congr (fun x => (hessian_normSq_pointwise hdim g f x).symm)

omit [CompactSpace M] [ConnectedSpace M] in
theorem tracelessHess_normSq_continuous (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    Continuous (fun x : M => normSq0S (I := I) g x 2 (tracelessHessAt g f x)) := by
  have hΔ : Continuous (fun x : M => ΔG (I := I) g f x) := (Δ_g_contMDiff g f).continuous
  exact ((hessian_normSq_continuous hdim g f).sub ((hΔ.pow 2).div_const 2)).congr
    fun x => (tracelessHess_normSq_eq hdim g f x).symm

omit [ConnectedSpace M] in
theorem integral_tracelessHess_normSq (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    (∫ x, normSq0S (I := I) g x 2 (tracelessHessAt g f x) ∂riemannianVolumeMeasure I M g) =
      (1 / 2 : ℝ) * (∫ x, (ΔG (I := I) g f x) ^ 2 ∂riemannianVolumeMeasure I M g) -
        (1 / 2 : ℝ) * ∫ x, metricScalarAt (I := I) g x * normGradSqFun (I := I) g f x
          ∂riemannianVolumeMeasure I M g := by
  have hfmc : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hint : ∀ {G : M → ℝ}, Continuous G → Integrable G (riemannianVolumeMeasure I M g) :=
    fun hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB := surfaceEntropy_integrated_bochner g hdim f
  simp only at hB
  have hΔ : Continuous (fun x : M => ΔG (I := I) g f x) := (Δ_g_contMDiff g f).continuous
  simp_rw [tracelessHess_normSq_eq hdim g f]
  have hI1 : Integrable (fun x => normSq0S (I := I) g x 2 (hessTensorAt (I := I) g f x))
      (riemannianVolumeMeasure I M g) := hint (hessian_normSq_continuous hdim g f)
  have hI2 : Integrable (fun x => ΔG (I := I) g f x ^ 2 / 2) (riemannianVolumeMeasure I M g) :=
    hint ((hΔ.pow 2).div_const 2)
  rw [integral_sub hI1 hI2, integral_div]
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [ConnectedSpace M] in
omit [T2Space M] in
theorem gradSq_close (g g₀ : SmoothRiemannianMetric I M) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hclose : ∀ x (v : TangentSpace I x), |g.inner x v v - g₀.inner x v v| ≤ δ * g₀.inner x v v)
    (u : M → ℝ) (x : M) :
    |normGradSqFun (I := I) g u x - normGradSqFun (I := I) g₀ u x| ≤
      2 * δ * normGradSqFun (I := I) g₀ u x := by
  have hnn : ∀ (q : SmoothRiemannianMetric I M) (v : TangentSpace I x), 0 ≤ q.inner x v v := by
    intro q v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (q.pos x v hv).le
  have hup : ∀ v : TangentSpace I x, g.inner x v v ≤ (1 + δ) * g₀.inner x v v := by
    intro v; have := (abs_le.1 (hclose x v)).2; linarith
  have hdown : ∀ v : TangentSpace I x, g₀.inner x v v ≤ (1 + 2 * δ) * g.inner x v v := by
    intro v
    have := (abs_le.1 (hclose x v)).1
    have h0 := hnn g₀ v
    nlinarith [mul_nonneg (mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)) h0]
  have h1 := inner_gradFun_le_of_inner_le (I := I) g g₀ (by linarith) u x hup
  have h2 := inner_gradFun_le_of_inner_le (I := I) g₀ g (by linarith) u x hdown
  simp only [normGradSqFun_def]
  have hG0 := hnn g₀ (gradFun (I := I) g₀ u x)
  have hG := hnn g (gradFun (I := I) g u x)
  rw [abs_le]
  constructor <;> nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem eventually_derivNorm_lt_of_iSup (k : ℕ → SmoothRiemannianMetric I M)
    (kInf h : SmoothRiemannianMetric I M) (q : ℕ)
    (hconv : Tendsto (fun j => ⨆ x, metricDerivNorm q (k j) kInf h x) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x, metricDerivNorm q (k j) kInf h x < ε := by
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := Metric.tendsto_atTop.1 hconv ε hε
  refine ⟨j₀, fun j hj x => ?_⟩
  have hb : BddAbove (Set.range fun x => metricDerivNorm q (k j) kInf h x) :=
    (isCompact_range (metricDerivNorm_cont (I := I) q (k j) kInf h)).bddAbove
  have h1 := le_ciSup hb x
  have h2 := hj₀ j hj
  rw [Real.dist_eq, sub_zero] at h2
  exact h1.trans_lt ((le_abs_self _).trans_lt h2)

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem limit_metric_data (h : SmoothRiemannianMetric I M) (k : ℕ → SmoothRiemannianMetric I M)
    (kInf : SmoothRiemannianMetric I M) {lam B : ℝ} (hlam : 0 < lam)
    (hlow : ∀ j x (v : TangentSpace I x), lam * h.inner x v v ≤ (k j).inner x v v)
    (hbdd : ∀ j x, ∀ q ≤ 2, metricCovDerivNorm q (k j) h x ≤ B)
    (hconv : ∀ q ≤ 2, Tendsto (fun j => ⨆ x, metricDerivNorm q (k j) kInf h x) atTop (𝓝 0)) :
    (∀ x (v : TangentSpace I x), lam * h.inner x v v ≤ kInf.inner x v v) ∧
    (∀ x, ∀ q ≤ 2, metricCovDerivNorm q kInf h x ≤ B + 1) ∧
    (∀ δ : ℝ, 0 < δ → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x (v : TangentSpace I x),
      |(k j).inner x v v - kInf.inner x v v| ≤ δ * kInf.inner x v v) ∧
    (∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x,
      |metricScalarAt (k j) x - metricScalarAt kInf x| ≤ ε) := by
  classical
  have hpt := fun q (hq : q ≤ 2) => eventually_derivNorm_lt_of_iSup (I := I) k kInf h q (hconv q hq)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hhnn : ∀ x (v : TangentSpace I x), 0 ≤ h.inner x v v := by
    intro x v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (h.pos x v hv).le
  have hlowInf : ∀ x (v : TangentSpace I x), lam * h.inner x v v ≤ kInf.inner x v v := by
    intro x v
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨j₀, hj₀⟩ := hpt 0 (by norm_num) (ε / ((n + 1) * (h.inner x v v + 1)))
      (by have := hhnn x v; positivity)
    have h1 := metricQuadFormDiff_le_metricDerivNorm (I := I) (k j₀) kInf h x v
    have hfr : (Module.finrank ℝ (TangentSpace I x) : ℝ) = n := rfl
    rw [hfr] at h1
    have h2 := hj₀ j₀ le_rfl x
    have hv := hhnn x v
    have h3 : n * metricDerivNorm (I := I) 0 (k j₀) kInf h x * h.inner x v v < ε := by
      have hm0 : 0 ≤ metricDerivNorm (I := I) 0 (k j₀) kInf h x := Real.sqrt_nonneg _
      calc n * metricDerivNorm (I := I) 0 (k j₀) kInf h x * h.inner x v v
          ≤ (n + 1) * metricDerivNorm (I := I) 0 (k j₀) kInf h x * (h.inner x v v + 1) := by
            gcongr <;> linarith
        _ < (n + 1) * (ε / ((n + 1) * (h.inner x v v + 1))) * (h.inner x v v + 1) := by
            gcongr
        _ = ε := by field_simp
    have h4 := (abs_le.1 h1).2
    have h5 := hlow j₀ x v
    linarith
  have hbddInf : ∀ x, ∀ q ≤ 2, metricCovDerivNorm q kInf h x ≤ B + 1 := by
    intro x q hq
    obtain ⟨j₀, hj₀⟩ := hpt q hq 1 one_pos
    have h1 := covNorm_le_add (I := I) q kInf (k j₀) h x
    rw [metricDerivNorm_symm] at h1
    linarith [hbdd j₀ x q hq, hj₀ j₀ le_rfl x]
  refine ⟨hlowInf, hbddInf, fun δ hδ => ?_, fun ε hε => ?_⟩
  · obtain ⟨j₀, hj₀⟩ := hpt 0 (by norm_num) (δ * lam / (n + 1)) (by positivity)
    refine ⟨j₀, fun j hj x v => ?_⟩
    have h1 := quadClose_of_metricDerivNorm_zero (I := I) h (k j) kInf hlam hlowInf x v
    have h2 := hj₀ j hj x
    have hk0 : 0 ≤ kInf.inner x v v := (mul_nonneg hlam.le (hhnn x v)).trans (hlowInf x v)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hk0)
    rw [div_le_iff₀ hlam]
    have hm0 : 0 ≤ metricDerivNorm (I := I) 0 (k j) kInf h x := Real.sqrt_nonneg _
    calc n * metricDerivNorm (I := I) 0 (k j) kInf h x
        ≤ (n + 1) * metricDerivNorm (I := I) 0 (k j) kInf h x := by nlinarith
      _ ≤ (n + 1) * (δ * lam / (n + 1)) := mul_le_mul_of_nonneg_left h2.le (by positivity)
      _ = δ * lam := by field_simp
  · obtain ⟨C, hC0, hC⟩ := exists_abs_metricScalarAt_sub_le (I := I) h isCompact_univ lam
      (B + 1) hlam
    have hex : ∀ q ∈ Finset.range 3, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x,
        metricDerivNorm q (k j) kInf h x < ε / (3 * C) := fun q hq =>
      hpt q (by simp at hq; omega) _ (by positivity)
    choose j₀ hj₀ using hex
    refine ⟨(Finset.range 3).attach.sup fun q => j₀ q.1 q.2, fun j hj x => ?_⟩
    have h1 := hC (k j) kInf (fun y _ ξ => hlow j y ξ) (fun y _ ξ => hlowInf y ξ)
      (fun y _ a ha => (hbdd j y a ha).trans (by linarith)) (fun y _ a ha => hbddInf y a ha)
      x (Set.mem_univ x)
    have h2 : ∑ q ∈ Finset.range 3, metricDerivNorm q (k j) kInf h x ≤
        ∑ _q ∈ Finset.range 3, ε / (3 * C) := by
      refine Finset.sum_le_sum fun q hq => (hj₀ q hq j ?_ x).le
      exact le_trans (Finset.le_sup (f := fun q : {q // q ∈ Finset.range 3} => j₀ q.1 q.2)
        (Finset.mem_attach _ ⟨q, hq⟩)) hj
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    calc |metricScalarAt (k j) x - metricScalarAt kInf x|
        ≤ C * ∑ q ∈ Finset.range 3, metricDerivNorm q (k j) kInf h x := h1
      _ ≤ C * ((3 : ℕ) * (ε / (3 * C))) := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = ε := by field_simp; ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] in
theorem abs_inner_add_sub_le (g : SmoothRiemannianMetric I M) (x : M) (X Y : TangentSpace I x)
    {ε : ℝ} (hε : 0 < ε) :
    |g.inner x (X + Y) (X + Y) - g.inner x Y Y| ≤
      (1 + 1 / ε) * g.inner x X X + ε * g.inner x Y Y := by
  have hnn : ∀ v : TangentSpace I x, 0 ≤ g.inner x v v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (g.pos x v hv).le
  have hexp : g.inner x (X + Y) (X + Y) - g.inner x Y Y = g.inner x X X + 2 * g.inner x X Y := by
    simp only [map_add, add_apply]
    rw [g.symm x Y X]; ring
  rw [hexp]
  have hcs := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt (I := I) g x X Y
  set a := Real.sqrt (g.inner x X X)
  set b := Real.sqrt (g.inner x Y Y)
  have ha2 : a ^ 2 = g.inner x X X := Real.sq_sqrt (hnn X)
  have hb2 : b ^ 2 = g.inner x Y Y := Real.sq_sqrt (hnn Y)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hyoung : 2 * (a * b) ≤ a ^ 2 / ε + ε * b ^ 2 := by
    rw [div_add' _ _ _ hε.ne', le_div_iff₀ hε]
    nlinarith [sq_nonneg (a - ε * b)]
  have hXX := hnn X
  rw [abs_le]
  constructor
  · have := (abs_le.1 hcs).1
    have h1 : 1 / ε * g.inner x X X = a ^ 2 / ε := by rw [ha2]; ring
    nlinarith
  · have := (abs_le.1 hcs).2
    have h1 : 1 / ε * g.inner x X X = a ^ 2 / ε := by rw [ha2]; ring
    nlinarith

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem tendsto_integral_scalar_gradSq_sub (k : ℕ → SmoothRiemannianMetric I M)
    (f : ℕ → C^∞⟮I, M; ℝ⟯) (fInf : C^∞⟮I, M; ℝ⟯) {K P : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hRb : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x, |metricScalarAt (k j) x| ≤ K)
    (hPb : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
      (∫ x, normGradSqFun (I := I) (k j) fInf x ∂riemannianVolumeMeasure I M (k j)) ≤ P)
    (hE : Tendsto (fun j => ∫ x, (k j).inner x
        ((gradG (I := I) (k j) (f j - fInf) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) (k j) (f j - fInf) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂riemannianVolumeMeasure I M (k j)) atTop (𝓝 0)) :
    Tendsto (fun j => (∫ x, metricScalarAt (k j) x * normGradSqFun (I := I) (k j) (f j) x
      ∂riemannianVolumeMeasure I M (k j)) - ∫ x, metricScalarAt (k j) x *
        normGradSqFun (I := I) (k j) fInf x ∂riemannianVolumeMeasure I M (k j)) atTop (𝓝 0) := by
  classical
  have hfmc : ∀ r : SmoothRiemannianMetric I M,
      IsFiniteMeasureOnCompacts (riemannianVolumeMeasure I M r) :=
    fun r => riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) r
  have hint : ∀ (r : SmoothRiemannianMetric I M) {G : M → ℝ}, Continuous G →
      Integrable G (riemannianVolumeMeasure I M r) :=
    fun r G hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRc : ∀ r : SmoothRiemannianMetric I M, Continuous fun x => metricScalarAt r x :=
    fun r => (metricScalar_smooth r).continuous
  have hGc : ∀ (r : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯),
      Continuous fun x => normGradSqFun (I := I) r u x :=
    fun r u => normGradSqFun_continuous r u.contMDiff
  have hGnn : ∀ (r : SmoothRiemannianMetric I M) (u : M → ℝ) x, 0 ≤ normGradSqFun (I := I) r u x :=
    fun r u x => by
      simp only [normGradSqFun_def]
      by_cases hv : gradFun (I := I) r u x = 0
      · rw [hv]; simp
      · exact (r.pos x _ hv).le
  obtain ⟨j₁, hj₁⟩ := hRb
  obtain ⟨j₂, hj₂⟩ := hPb
  refine Metric.tendsto_atTop.2 fun η hη => ?_
  set c : ℝ := η / (4 * (K + 1) * (P + 1)) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨j₃, hj₃⟩ := Metric.tendsto_atTop.1 hE (η / (2 * (K + 1) * (1 + 1 / c)))
    (by positivity)
  refine ⟨max j₁ (max j₂ j₃), fun j hj => ?_⟩
  have hj1 : j₁ ≤ j := (le_max_left _ _).trans hj
  have hj2 : j₂ ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hj3 : j₃ ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  set μj := riemannianVolumeMeasure I M (k j) with hμj
  set Fj := fun x => (k j).inner x
      ((gradG (I := I) (k j) (f j - fInf) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) (k j) (f j - fInf) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
    with hFj
  set Gj := fun x => normGradSqFun (I := I) (k j) fInf x with hGj
  have hFnn : ∀ x, 0 ≤ Fj x := fun x => by
    simp only [hFj]
    by_cases hv : (gradG (I := I) (k j) (f j - fInf) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x = 0
    · rw [hv]; simp
    · exact ((k j).pos x _ hv).le
  have hEj0 : 0 ≤ ∫ x, Fj x ∂μj := integral_nonneg hFnn
  have hEjlt : (∫ x, Fj x ∂μj) < η / (2 * (K + 1) * (1 + 1 / c)) := by
    have := hj₃ j hj3
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hEj0] at this
    exact this
  have hPj : (∫ x, Gj x ∂μj) ≤ P := hj₂ j hj2
  have hgrad : ∀ x, gradFun (I := I) (k j) (⇑(f j)) x =
      gradFun (I := I) (k j) (⇑(f j - fInf)) x + gradFun (I := I) (k j) (⇑fInf) x := by
    intro x
    have hfun : (⇑(f j) : M → ℝ) = ⇑(f j - fInf) + ⇑fInf := by
      funext y; simp
    rw [hfun]
    exact DifferentialGeometry.Geometry.Operator.gradFun_add (I := I) (k j)
      ((f j - fInf).contMDiff.mdifferentiableAt (by simp))
      (fInf.contMDiff.mdifferentiableAt (by simp))
  have hpt : ∀ x, |metricScalarAt (k j) x * normGradSqFun (I := I) (k j) (f j) x -
      metricScalarAt (k j) x * normGradSqFun (I := I) (k j) fInf x| ≤
      (K + 1) * ((1 + 1 / c) * Fj x + c * Gj x) := by
    intro x
    rw [← mul_sub, abs_mul]
    refine mul_le_mul ((hj₁ j hj1 x).trans (by linarith)) ?_ (abs_nonneg _) (by positivity)
    simp only [hFj, hGj, normGradSqFun_def, grad_g_apply]
    rw [hgrad x]
    exact abs_inner_add_sub_le (I := I) (k j) x _ _ hc0
  have hc1 : Continuous Fj := (contMDiff_g_inner_of_smooth_sections (I := I) (k j) _ _).continuous
  have hI1 : Integrable (fun x => metricScalarAt (k j) x *
      normGradSqFun (I := I) (k j) (f j) x) μj := hint (k j) ((hRc (k j)).mul (hGc (k j) (f j)))
  have hI2 : Integrable (fun x => metricScalarAt (k j) x *
      normGradSqFun (I := I) (k j) fInf x) μj := hint (k j) ((hRc (k j)).mul (hGc (k j) fInf))
  have hIF : Integrable (fun x => (1 + 1 / c) * Fj x) μj := hint (k j) (continuous_const.mul hc1)
  have hIG : Integrable (fun x => c * Gj x) μj :=
    hint (k j) (continuous_const.mul (hGc (k j) fInf))
  have hmono : (∫ x, |metricScalarAt (k j) x * normGradSqFun (I := I) (k j) (f j) x -
      metricScalarAt (k j) x * normGradSqFun (I := I) (k j) fInf x| ∂μj) ≤
      ∫ x, (K + 1) * ((1 + 1 / c) * Fj x + c * Gj x) ∂μj :=
    integral_mono (hI1.sub hI2).abs ((hIF.add hIG).const_mul _) hpt
  have hval : (∫ x, (K + 1) * ((1 + 1 / c) * Fj x + c * Gj x) ∂μj) =
      (K + 1) * ((1 + 1 / c) * (∫ x, Fj x ∂μj) + c * ∫ x, Gj x ∂μj) := by
    rw [integral_const_mul, integral_add hIF hIG, integral_const_mul, integral_const_mul]
  rw [Real.dist_eq, sub_zero, ← integral_sub hI1 hI2]
  refine (abs_integral_le_integral_abs).trans_lt (hmono.trans_lt ?_)
  rw [hval]
  have hG0 : 0 ≤ ∫ x, Gj x ∂μj := integral_nonneg fun x => hGnn _ _ x
  have h1 : (K + 1) * ((1 + 1 / c) * ∫ x, Fj x ∂μj) < η / 2 := by
    have hpos : 0 < (K + 1) * (1 + 1 / c) := by positivity
    calc (K + 1) * ((1 + 1 / c) * ∫ x, Fj x ∂μj) = ((K + 1) * (1 + 1 / c)) * ∫ x, Fj x ∂μj := by
          ring
      _ < ((K + 1) * (1 + 1 / c)) * (η / (2 * (K + 1) * (1 + 1 / c))) :=
          mul_lt_mul_of_pos_left hEjlt hpos
      _ = η / 2 := by field_simp
  have h2 : (K + 1) * (c * ∫ x, Gj x ∂μj) ≤ η / 4 := by
    calc (K + 1) * (c * ∫ x, Gj x ∂μj) ≤ (K + 1) * (c * (P + 1)) := by
          gcongr; linarith
      _ = η / 4 := by rw [hc]; field_simp
  nlinarith

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem tendsto_integral_scalar_gradSq_fixed (k : ℕ → SmoothRiemannianMetric I M)
    (kInf : SmoothRiemannianMetric I M)
    (hclose : ∀ δ : ℝ, 0 < δ → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x (v : TangentSpace I x),
      |(k j).inner x v v - kInf.inner x v v| ≤ δ * kInf.inner x v v)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x,
      |metricScalarAt (k j) x - metricScalarAt kInf x| ≤ ε)
    (fInf : C^∞⟮I, M; ℝ⟯) (w : ℝ) :
    Tendsto (fun j => ∫ x, (metricScalarAt (k j) x + w) * normGradSqFun (I := I) (k j) fInf x
        ∂riemannianVolumeMeasure I M (k j)) atTop
      (𝓝 (∫ x, (metricScalarAt kInf x + w) * normGradSqFun (I := I) kInf fInf x
        ∂riemannianVolumeMeasure I M kInf)) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : ∀ r : SmoothRiemannianMetric I M, riemannianVolumeMeasure I M r = 0 :=
      fun r => Measure.eq_zero_of_isEmpty _
    simp only [h0, integral_zero_measure]
    exact tendsto_const_nhds
  have hRc : ∀ r : SmoothRiemannianMetric I M, Continuous fun x => metricScalarAt r x :=
    fun r => (metricScalar_smooth r).continuous
  have hGc : ∀ (r : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯),
      Continuous fun x => normGradSqFun (I := I) r u x :=
    fun r u => normGradSqFun_continuous r u.contMDiff
  have hGnn : ∀ (r : SmoothRiemannianMetric I M) (u : M → ℝ) x, 0 ≤ normGradSqFun (I := I) r u x :=
    fun r u x => by
      simp only [normGradSqFun_def]
      by_cases hv : gradFun (I := I) r u x = 0
      · rw [hv]; simp
      · exact (r.pos x _ hv).le
  obtain ⟨KG, hKG⟩ := isCompact_univ.exists_bound_of_continuousOn (hGc kInf fInf).continuousOn
  obtain ⟨KR, hKR⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hRc kInf).add (continuous_const : Continuous fun _ : M => w)).continuousOn
  have hKG0 : 0 ≤ KG := (norm_nonneg _).trans (hKG (Classical.arbitrary M) (Set.mem_univ _))
  have hKR0 : 0 ≤ KR := (norm_nonneg _).trans (hKR (Classical.arbitrary M) (Set.mem_univ _))
  refine tendsto_integral_of_quadClose (I := I) k kInf hclose _ _
    (fun j => ((hRc (k j)).add continuous_const).mul (hGc (k j) fInf))
    (((hRc kInf).add continuous_const).mul (hGc kInf fInf)) fun ε hε => ?_
  obtain ⟨j₁, hj₁⟩ := hR (ε / (4 * KG + 1)) (by positivity)
  obtain ⟨j₂, hj₂⟩ := hclose (min (1 / 2) (ε / (4 * (KR + 1) * (KG + 1))))
    (lt_min (by norm_num) (by positivity))
  refine ⟨max j₁ j₂, fun j hj x => ?_⟩
  have h1 := hj₁ j ((le_max_left _ _).trans hj) x
  set δ := min (1 / 2 : ℝ) (ε / (4 * (KR + 1) * (KG + 1))) with hδ
  have hδ0 : 0 ≤ δ := (lt_min (by norm_num) (by positivity)).le
  have hδ12 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / (4 * (KR + 1) * (KG + 1)) := min_le_right _ _
  have h2 := gradSq_close (I := I) (k j) kInf hδ0 hδ12
    (hj₂ j ((le_max_right _ _).trans hj)) fInf x
  have hG : normGradSqFun (I := I) kInf fInf x ≤ KG :=
    (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hKG x (Set.mem_univ x))
  have hR' : |metricScalarAt kInf x + w| ≤ KR := (Real.norm_eq_abs _) ▸ hKR x (Set.mem_univ x)
  have hG0 := hGnn kInf fInf x
  have hGj0 := hGnn (k j) fInf x
  have hGj : normGradSqFun (I := I) (k j) fInf x ≤ 2 * KG := by
    have := (abs_le.1 h2).2
    nlinarith
  have hd2 : |normGradSqFun (I := I) (k j) fInf x - normGradSqFun (I := I) kInf fInf x| ≤
      ε / (2 * (KR + 1)) := by
    refine h2.trans ?_
    calc 2 * δ * normGradSqFun (I := I) kInf fInf x ≤
        2 * (ε / (4 * (KR + 1) * (KG + 1))) * (KG + 1) := by gcongr; linarith
      _ = ε / (2 * (KR + 1)) := by field_simp; ring
  have heq : (metricScalarAt (k j) x + w) * normGradSqFun (I := I) (k j) fInf x -
      (metricScalarAt kInf x + w) * normGradSqFun (I := I) kInf fInf x =
      (metricScalarAt (k j) x - metricScalarAt kInf x) * normGradSqFun (I := I) (k j) fInf x +
      (metricScalarAt kInf x + w) * (normGradSqFun (I := I) (k j) fInf x -
        normGradSqFun (I := I) kInf fInf x) := by ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hGj0]
  have e1 : |metricScalarAt (k j) x - metricScalarAt kInf x| *
      normGradSqFun (I := I) (k j) fInf x ≤ ε / (4 * KG + 1) * (2 * KG) :=
    mul_le_mul h1 hGj hGj0 (by positivity)
  have e2 : |metricScalarAt kInf x + w| * |normGradSqFun (I := I) (k j) fInf x -
      normGradSqFun (I := I) kInf fInf x| ≤ KR * (ε / (2 * (KR + 1))) :=
    mul_le_mul hR' hd2 (abs_nonneg _) hKR0
  have e3 : ε / (4 * KG + 1) * (2 * KG) ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e4 : KR * (ε / (2 * (KR + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem tendsto_integral_gradSq (k : ℕ → SmoothRiemannianMetric I M)
    (kInf : SmoothRiemannianMetric I M)
    (hclose : ∀ δ : ℝ, 0 < δ → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x (v : TangentSpace I x),
      |(k j).inner x v v - kInf.inner x v v| ≤ δ * kInf.inner x v v)
    (fInf : C^∞⟮I, M; ℝ⟯) :
    Tendsto (fun j => ∫ x, normGradSqFun (I := I) (k j) fInf x
        ∂riemannianVolumeMeasure I M (k j)) atTop
      (𝓝 (∫ x, normGradSqFun (I := I) kInf fInf x ∂riemannianVolumeMeasure I M kInf)) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : ∀ r : SmoothRiemannianMetric I M, riemannianVolumeMeasure I M r = 0 :=
      fun r => Measure.eq_zero_of_isEmpty _
    simp only [h0, integral_zero_measure]
    exact tendsto_const_nhds
  have hGc : ∀ (r : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯),
      Continuous fun x => normGradSqFun (I := I) r u x :=
    fun r u => normGradSqFun_continuous r u.contMDiff
  obtain ⟨KG, hKG⟩ := isCompact_univ.exists_bound_of_continuousOn (hGc kInf fInf).continuousOn
  have hKG0 : 0 ≤ KG := (norm_nonneg _).trans (hKG (Classical.arbitrary M) (Set.mem_univ _))
  refine tendsto_integral_of_quadClose (I := I) k kInf hclose _ _ (fun j => hGc (k j) fInf)
    (hGc kInf fInf) fun ε hε => ?_
  obtain ⟨j₀, hj₀⟩ := hclose (min (1 / 2) (ε / (2 * KG + 1))) (lt_min (by norm_num)
    (by positivity))
  refine ⟨j₀, fun j hj x => ?_⟩
  have hδ0 : 0 ≤ min (1 / 2 : ℝ) (ε / (2 * KG + 1)) := (lt_min (by norm_num) (by positivity)).le
  have h1 := gradSq_close (I := I) (k j) kInf hδ0 (min_le_left _ _) (hj₀ j hj) fInf x
  have hG : normGradSqFun (I := I) kInf fInf x ≤ KG :=
    (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hKG x (Set.mem_univ x))
  have hG0 : 0 ≤ normGradSqFun (I := I) kInf fInf x := by
    simp only [normGradSqFun_def]
    by_cases hv : gradFun (I := I) kInf fInf x = 0
    · rw [hv]; simp
    · exact (kInf.pos x _ hv).le
  refine h1.trans ?_
  have : min (1 / 2 : ℝ) (ε / (2 * KG + 1)) ≤ ε / (2 * KG + 1) := min_le_right _ _
  calc 2 * min (1 / 2) (ε / (2 * KG + 1)) * normGradSqFun (I := I) kInf fInf x
      ≤ 2 * (ε / (2 * KG + 1)) * KG := by gcongr
    _ ≤ ε := by
        rw [mul_comm 2, mul_assoc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem tracelessHess_eq_zero_of_limit (hdim : Module.finrank ℝ E = 2)
    (h : SmoothRiemannianMetric I M) (k : ℕ → SmoothRiemannianMetric I M)
    (kInf : SmoothRiemannianMetric I M) {lam B : ℝ} (hlam : 0 < lam)
    (hlow : ∀ j x (v : TangentSpace I x), lam * h.inner x v v ≤ (k j).inner x v v)
    (hbdd : ∀ j x, ∀ q ≤ 2, metricCovDerivNorm q (k j) h x ≤ B)
    (hconv : ∀ q ≤ 2, Tendsto (fun j => ⨆ x, metricDerivNorm q (k j) kInf h x) atTop (𝓝 0))
    (f : ℕ → C^∞⟮I, M; ℝ⟯) (fInf : C^∞⟮I, M; ℝ⟯)
    (hf : ∀ j, (∫ x, f j x ∂riemannianVolumeMeasure I M (k j)) = 0 ∧
      ∀ x, ΔG (k j) (f j) x = metricScalarAt (k j) x - 2)
    (hfInf : (∫ x, fInf x ∂riemannianVolumeMeasure I M kInf) = 0 ∧
      ∀ x, ΔG kInf fInf x = metricScalarAt kInf x - 2)
    (hM : Tendsto (fun j => ∫ x, normSq0S (k j) x 2 (tracelessHessAt (k j) (f j) x)
      ∂riemannianVolumeMeasure I M (k j)) atTop (𝓝 0)) :
    ∀ x, tracelessHessAt kInf fInf x = 0 := by
  classical
  rcases isEmpty_or_nonempty M with hM0 | hM0
  · intro x; exact isEmptyElim x
  obtain ⟨hlowInf, hbddInf, hclose, hR⟩ := limit_metric_data (I := I) h k kInf hlam hlow hbdd hconv
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  have hRc : ∀ r : SmoothRiemannianMetric I M, Continuous fun x => metricScalarAt r x :=
    fun r => (metricScalar_smooth r).continuous
  let q : ℕ → C^∞⟮I, M; ℝ⟯ := fun j =>
    ⟨fun x => metricScalarAt (k j) x - 2, (metricScalar_smooth (k j)).sub contMDiff_const⟩
  let qInf : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun x => metricScalarAt kInf x - 2, (metricScalar_smooth kInf).sub contMDiff_const⟩
  have hpt0 := eventually_derivNorm_lt_of_iSup (I := I) k kInf h 0 (hconv 0 (by norm_num))
  have hpt1 := eventually_derivNorm_lt_of_iSup (I := I) k kInf h 1 (hconv 1 (by norm_num))
  have hg : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j → ∀ a : ℕ, a ≤ 1 → ∀ x : M,
      metricDerivNorm (I := I) a (k j) kInf h x < ε := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := hpt0 ε hε
    obtain ⟨j₁, hj₁⟩ := hpt1 ε hε
    refine ⟨max j₀ j₁, fun j hj a ha x => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
    · exact hj₀ j ((le_max_left _ _).trans hj) x
    · exact hj₁ j ((le_max_right _ _).trans hj) x
  have hq : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j → ∀ x : M, |q j x - qInf x| < ε := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := hR (ε / 2) (by positivity)
    refine ⟨j₀, fun j hj x => ?_⟩
    have := hj₀ j hj x
    change |(metricScalarAt (k j) x - 2) - (metricScalarAt kInf x - 2)| < ε
    rw [sub_sub_sub_cancel_right]
    linarith
  obtain ⟨-, hE⟩ :=
    DifferentialGeometry.Analysis.Laplacian.tendsto_meanZero_poisson_of_metric_tendsto h kInf k
      hg q qInf hq f fInf (fun j => (hf j).1) (fun j x => (hf j).2 x) hfInf.1 hfInf.2
  have hfmc : ∀ r : SmoothRiemannianMetric I M,
      IsFiniteMeasureOnCompacts (riemannianVolumeMeasure I M r) :=
    fun r => riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) r
  have hint : ∀ (r : SmoothRiemannianMetric I M) {G : M → ℝ}, Continuous G →
      Integrable G (riemannianVolumeMeasure I M r) :=
    fun r G hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQ : ∀ (r : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; ℝ⟯),
      (∀ x, ΔG r u x = metricScalarAt r x - 2) →
      (∫ x, normSq0S r x 2 (tracelessHessAt r u x) ∂riemannianVolumeMeasure I M r) =
        (1 / 2 : ℝ) * (∫ x, (metricScalarAt r x - 2) ^ 2 ∂riemannianVolumeMeasure I M r) -
        (1 / 2 : ℝ) * ∫ x, metricScalarAt r x * normGradSqFun (I := I) r u x
          ∂riemannianVolumeMeasure I M r := by
    intro r u hu
    rw [integral_tracelessHess_normSq hdim r u]
    simp_rw [hu]
  obtain ⟨KR, hKR⟩ := isCompact_univ.exists_bound_of_continuousOn (hRc kInf).continuousOn
  have hKR0 : 0 ≤ KR := (norm_nonneg _).trans (hKR (Classical.arbitrary M) (Set.mem_univ _))
  have hA : Tendsto (fun j => ∫ x, (metricScalarAt (k j) x - 2) ^ 2
      ∂riemannianVolumeMeasure I M (k j)) atTop
      (𝓝 (∫ x, (metricScalarAt kInf x - 2) ^ 2 ∂riemannianVolumeMeasure I M kInf)) := by
    refine tendsto_integral_of_quadClose (I := I) k kInf hclose _ _
      (fun j => ((hRc (k j)).sub continuous_const).pow 2) (((hRc kInf).sub continuous_const).pow 2)
      fun ε hε => ?_
    obtain ⟨j₀, hj₀⟩ := hR (min 1 (ε / (2 * KR + 5))) (lt_min one_pos (by positivity))
    refine ⟨j₀, fun j hj x => ?_⟩
    have h1 := hj₀ j hj x
    have hR' : |metricScalarAt kInf x| ≤ KR := (Real.norm_eq_abs _) ▸ hKR x (Set.mem_univ x)
    have hm1 : min 1 (ε / (2 * KR + 5)) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (ε / (2 * KR + 5)) ≤ ε / (2 * KR + 5) := min_le_right _ _
    have heq : (metricScalarAt (k j) x - 2) ^ 2 - (metricScalarAt kInf x - 2) ^ 2 =
        (metricScalarAt (k j) x - metricScalarAt kInf x) *
          ((metricScalarAt (k j) x - metricScalarAt kInf x) + 2 * metricScalarAt kInf x - 4) := by
      ring
    rw [heq, abs_mul]
    have h2 : |(metricScalarAt (k j) x - metricScalarAt kInf x) + 2 * metricScalarAt kInf x - 4|
        ≤ 2 * KR + 5 := by
      calc _ ≤ |metricScalarAt (k j) x - metricScalarAt kInf x| + |2 * metricScalarAt kInf x| +
            |(4 : ℝ)| := abs_sub_le_iff.2 ⟨by
              have := abs_add_le (metricScalarAt (k j) x - metricScalarAt kInf x)
                (2 * metricScalarAt kInf x)
              linarith [le_abs_self (4 : ℝ), abs_nonneg (4 : ℝ),
                le_abs_self ((metricScalarAt (k j) x - metricScalarAt kInf x) +
                  2 * metricScalarAt kInf x)], by
              have := abs_add_le (metricScalarAt (k j) x - metricScalarAt kInf x)
                (2 * metricScalarAt kInf x)
              linarith [neg_abs_le ((metricScalarAt (k j) x - metricScalarAt kInf x) +
                  2 * metricScalarAt kInf x), abs_nonneg (4 : ℝ), le_abs_self (4 : ℝ)]⟩
        _ ≤ 1 + 2 * KR + 4 := by
            rw [abs_mul, abs_two]; norm_num; linarith
        _ = 2 * KR + 5 := by ring
    calc |metricScalarAt (k j) x - metricScalarAt kInf x| *
          |(metricScalarAt (k j) x - metricScalarAt kInf x) + 2 * metricScalarAt kInf x - 4|
        ≤ ε / (2 * KR + 5) * (2 * KR + 5) :=
          mul_le_mul (h1.trans hm2) h2 (abs_nonneg _) (by positivity)
      _ = ε := by field_simp
  have hfix := tendsto_integral_scalar_gradSq_fixed (I := I) k kInf hclose hR fInf 0
  simp only [add_zero] at hfix
  have hGI := tendsto_integral_gradSq (I := I) k kInf hclose fInf
  set GI := ∫ x, normGradSqFun (I := I) kInf fInf x ∂riemannianVolumeMeasure I M kInf with hGIdef
  have hRb : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ x, |metricScalarAt (k j) x| ≤ KR + 1 := by
    obtain ⟨j₀, hj₀⟩ := hR 1 one_pos
    refine ⟨j₀, fun j hj x => ?_⟩
    have h1 := hj₀ j hj x
    have h2 : |metricScalarAt kInf x| ≤ KR := (Real.norm_eq_abs _) ▸ hKR x (Set.mem_univ x)
    calc |metricScalarAt (k j) x| = |(metricScalarAt (k j) x - metricScalarAt kInf x) +
          metricScalarAt kInf x| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ 1 + KR := add_le_add h1 h2
      _ = KR + 1 := by ring
  have hPb : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
      (∫ x, normGradSqFun (I := I) (k j) fInf x ∂riemannianVolumeMeasure I M (k j)) ≤
        |GI| + 1 := by
    obtain ⟨j₀, hj₀⟩ := Metric.tendsto_atTop.1 hGI 1 one_pos
    refine ⟨j₀, fun j hj => ?_⟩
    have := hj₀ j hj
    rw [Real.dist_eq] at this
    linarith [le_abs_self GI, (abs_lt.1 this).2]
  have hsub := tendsto_integral_scalar_gradSq_sub (I := I) k f fInf (by linarith)
    (by positivity) hRb hPb hE
  have hB := hfix.add hsub
  simp only [add_sub_cancel, add_zero] at hB
  have hQj : (fun j => ∫ x, normSq0S (k j) x 2 (tracelessHessAt (k j) (f j) x)
      ∂riemannianVolumeMeasure I M (k j)) = fun j =>
      (1 / 2 : ℝ) * (∫ x, (metricScalarAt (k j) x - 2) ^ 2 ∂riemannianVolumeMeasure I M (k j)) -
        (1 / 2 : ℝ) * ∫ x, metricScalarAt (k j) x * normGradSqFun (I := I) (k j) (f j) x
          ∂riemannianVolumeMeasure I M (k j) := by
    funext j
    exact hQ (k j) (f j) (hf j).2
  have hlim := (hA.const_mul (1 / 2 : ℝ)).sub (hB.const_mul (1 / 2 : ℝ))
  rw [← hQj] at hlim
  have hzero := tendsto_nhds_unique hlim hM
  rw [← hQ kInf fInf hfInf.2] at hzero
  have hcont := tracelessHess_normSq_continuous hdim kInf fInf
  have hnn : ∀ x, 0 ≤ normSq0S kInf x 2 (tracelessHessAt kInf fInf x) :=
    fun x => normSq0S_nonneg (I := I) kInf x 2 _
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => hnn x) (hint kInf hcont)).1 hzero
  have := riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) kInf
  have heq := (Continuous.ae_eq_iff_eq (riemannianVolumeMeasure I M kInf) hcont
    continuous_const).1 hae
  intro x
  exact (normSq0S_eq_zero_iff (I := I) kInf x 2 _).1 (congrFun heq x)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] in
theorem pullbackFamily_inner_contMDiffAt (g : ℝ → SmoothRiemannianMetric I M) {U : Set ℝ}
    (hU : IsOpen U)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) (U ×ˢ univ))
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (U ×ˢ univ))
    (W0 W1 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {t : ℝ} (ht : t ∈ U) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => (g q.1).inner (ψ q.1 q.2) (mfderiv I I (ψ q.1) q.2 (W0 q.2))
        (mfderiv I I (ψ q.1) q.2 (W1 q.2))) (t, x) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hnhds : U ×ˢ (univ : Set M) ∈ 𝓝 (t, x) := (hU.prod isOpen_univ).mem_nhds ⟨ht, trivial⟩
  have hψa : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (Function.uncurry fun (s : ℝ) (y : M) => ψ s y) (t, x) := hψ.contMDiffAt hnhds
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1, ψ p.1 p.2)) (t, x) := contMDiffAt_fst.prodMk hψa
  have hnhds' : U ×ˢ (univ : Set M) ∈ 𝓝 (t, ψ t x) :=
    (hU.prod isOpen_univ).mem_nhds ⟨ht, trivial⟩
  have hmetric := (hg.contMDiffAt hnhds').comp (t, x) hmap
  have hvec : ∀ W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M => (⟨ψ p.1 p.2, mfderiv I I (ψ p.1) p.2 (W p.2)⟩ :
          TangentBundle I M)) (t, x) := by
    intro W
    have hw : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M => (⟨p.2, W p.2⟩ : TangentBundle I M)) (t, x) :=
      (W.contMDiff.contMDiffAt).comp (t, x) contMDiffAt_snd
    exact hψa.partial_mfderiv_apply hw le_rfl
  have happ := ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × M => ψ p.1 p.2)
    hmetric (hvec W0) (hvec W1)
  rw [Bundle.contMDiffAt_totalSpace] at happ
  exact happ.2

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem tensor02CovDerivNormWith_pullback_scale (g : SmoothRiemannianMetric I M) (c : ℝ)
    (hc : 0 < c) (ψ : M ≃ₘ⟮I, I⟯ M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (q : ℕ) (x : M) :
    tensor02CovDerivNormWith q (pullbackTensor02FieldCross ψ A)
        (Diffeomorph.pullbackMetric (scaleMetric c hc g) ψ)
        (Diffeomorph.pullbackMetric (scaleMetric c hc g) ψ) x =
      (Real.sqrt c)⁻¹ ^ (q + 2) *
        Real.sqrt (normSq0S g (ψ x) (2 + q) (iterCov g 2 A q (ψ x))) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    tensor02CovDerivNormWith_pullbackTensor02FieldCross,
    tensor02CovDerivNormWith_scaleMetric g g c c hc hc A q (ψ x)]
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g (ψ x)
  rw [tensor02CovDerivNormWith_eq_iterCov (I := I) A g q basis
    (Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON)]

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem exists_metric_limit_of_reparam (h : SmoothRiemannianMetric I M)
    (K : ℝ → SmoothRiemannianMetric I M)
    (W : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) {U : Set ℝ}
    (hKjoint : ∀ t ∈ U, ∀ x : M,
      ∀ W0 W1 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (K q.1).inner q.2 (W0 q.2) (W1 q.2)) (t, x))
    (hKderiv : ∀ t ∈ U, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (K r).inner x (v 0) (v 1)) (W t x v) t)
    (θ θ' : ℝ → ℝ) (σ₀ : ℝ) (hθ : ContDiff ℝ ∞ θ) (hθ' : ∀ σ, HasDerivAt θ (θ' σ) σ)
    (hθU : ∀ σ, σ₀ ≤ σ → θ σ ∈ U)
    (hbd : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ σ, σ₀ ≤ σ → ∀ x : M,
      |θ' σ| * tensor02CovDerivNormWith (I := I) q (W (θ σ)) (K (θ σ)) (K (θ σ)) x ≤
        C * Real.exp (-(γ * σ))) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
      (∀ σ, σ₀ ≤ σ → ∀ x : M, ∀ v : TangentSpace I x,
        lam * h.inner x v v ≤ (K (θ σ)).inner x v v) ∧
      (∀ x : M, ∀ v : TangentSpace I x, lam * h.inner x v v ≤ kInf.inner x v v) ∧
      (∀ q : ℕ, ∃ B : ℝ, ∀ x : M, metricCovDerivNorm (I := I) q kInf h x ≤ B ∧
        ∀ σ, σ₀ ≤ σ → metricCovDerivNorm (I := I) q (K (θ σ)) h x ≤ B) ∧
      (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ σ, σ₀ ≤ σ → ∀ q : ℕ, q ≤ N → ∀ x : M,
        metricDerivNorm (I := I) q (K (θ σ)) kInf h x ≤ B * Real.exp (-(β * σ))) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  choose C γ hγ hC using hbd
  refine exists_metric_limit_of_exp_decay_velocity (I := I) h (fun σ => K (θ σ))
    (fun σ => θ' σ • W (θ σ)) σ₀ C γ hγ ?_ ?_ ?_
  · intro σ hσ x Wv
    have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (θ q.1, q.2)) (σ, x) :=
      ((hθ.contMDiff.contMDiffAt).comp (σ, x) contMDiffAt_fst).prodMk contMDiffAt_snd
    exact (hKjoint (θ σ) (hθU σ hσ) x (Wv 0) (Wv 1)).comp (σ, x) hmap
  · intro σ hσ x v
    have h1 := (hKderiv (θ σ) (hθU σ hσ) x v).comp σ (hθ' σ)
    refine HasDerivAt.congr_deriv h1 ?_
    simp [mul_comm]
  · intro q σ hσ x
    rw [tensor02CovDerivNormWith_smul]
    exact hC q σ hσ x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
theorem sqrt_pow_eq {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : Real.sqrt a ^ n = Real.sqrt (a ^ n) := by
  rw [show a ^ n = (Real.sqrt a ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt ha],
    Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) n)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem normalizedFlowMetric_eq
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    {t : ℝ} (ht : t < flowExtinctionTime S) :
    normalizedFlowMetric S t = scaleMetric (1 / (2 * (flowExtinctionTime S - t)))
      (normalizedSurfaceMetric_pos ht) (S.family.metric t) := by
  unfold normalizedFlowMetric
  simp only [ht, ↓reduceDIte]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem gauge_velocity_bound
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) {A : Set ℝ} (q : ℕ) {C γ : ℝ}
    (hdec : ∀ t ∈ A, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + q) *
          normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
        C * (flowExtinctionTime S - t) ^ γ)
    {t : ℝ} (htA : t ∈ A) (ht : t < flowExtinctionTime S) (x : M) :
    tensor02CovDerivNormWith q
        ((1 / (flowExtinctionTime S - t)) • pullbackTensor02FieldCross (ψ t) (Mf t))
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t))
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) x ≤
      1 / (flowExtinctionTime S - t) *
        Real.sqrt (2 ^ (q + 2) * max C 0 * (flowExtinctionTime S - t) ^ γ) := by
  set τ := flowExtinctionTime S - t with hτ
  have hτ0 : 0 < τ := sub_pos.2 ht
  rw [tensor02CovDerivNormWith_smul, normalizedFlowMetric_eq S ht,
    tensor02CovDerivNormWith_pullback_scale, abs_of_pos (by positivity : (0 : ℝ) < 1 / τ)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set Nsq := normSq0S (S.family.metric t) (ψ t x) (2 + q)
    (iterCov (S.family.metric t) 2 (Mf t) q (ψ t x)) with hNsq
  have hN0 : 0 ≤ Nsq := normSq0S_nonneg (I := I) _ _ _ _
  have hd := hdec t htA (ψ t x)
  have hsq : (Real.sqrt (1 / (2 * τ)))⁻¹ = Real.sqrt (2 * τ) := by
    rw [← Real.sqrt_inv, one_div, inv_inv]
  rw [hsq, sqrt_pow_eq (by positivity), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hpow : (2 * τ) ^ (q + 2) = 2 ^ (q + 2) * τ ^ (2 + q) := by
    rw [mul_pow, add_comm q 2]
  rw [hpow]
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ0.le γ
  have h1 : τ ^ (2 + q) * Nsq ≤ max C 0 * τ ^ γ :=
    hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hτγ)
  calc 2 ^ (q + 2) * τ ^ (2 + q) * Nsq = 2 ^ (q + 2) * (τ ^ (2 + q) * Nsq) := by ring
    _ ≤ 2 ^ (q + 2) * (max C 0 * τ ^ γ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ (q + 2) * max C 0 * τ ^ γ := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem gauge_inner_eq (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (ψ : M ≃ₘ⟮I, I⟯ M) {t : ℝ} (ht : t < flowExtinctionTime S) (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ).inner x v w =
      1 / (2 * (flowExtinctionTime S - t)) *
        (Diffeomorph.pullbackMetric (S.family.metric t) ψ).inner x v w := by
  rw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner,
    normalizedFlowMetric_eq S ht, scaleMetric_inner]

omit [ConnectedSpace M] in
theorem gauge_hasDerivAt (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hTeq : T = flowExtinctionTime S) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψd : ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
    {t : ℝ} (ht : t ∈ Ioo t₀ T) (x : M) (v : Fin 2 → TangentSpace I x) :
    HasDerivAt (fun r => (Diffeomorph.pullbackMetric (normalizedFlowMetric S r) (ψ r)).inner x
        (v 0) (v 1))
      (((1 / (flowExtinctionTime S - t)) • pullbackTensor02FieldCross (ψ t) (Mf t)) x v) t := by
  have h1 := hψd t ht x (v 0) (v 1)
  have hev : (fun r => (Diffeomorph.pullbackMetric (normalizedFlowMetric S r) (ψ r)).inner x
      (v 0) (v 1)) =ᶠ[𝓝 t] fun s => 1 / (2 * (flowExtinctionTime S - s)) *
        (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x (v 0) (v 1) := by
    have hlt : t < flowExtinctionTime S := hTeq ▸ ht.2
    filter_upwards [Iio_mem_nhds hlt] with r hr
    exact gauge_inner_eq S (ψ r) hr x (v 0) (v 1)
  refine (h1.congr_of_eventuallyEq hev).congr_deriv ?_
  have hv : (fun j => mfderiv I I (ψ t) x (v j)) =
      vec2 (mfderiv I I (ψ t) x (v 0)) (mfderiv I I (ψ t) x (v 1)) := by
    funext j
    fin_cases j <;> rfl
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, smul_apply, smul_eq_mul,
    pullbackTensor02FieldCross_apply]
  rw [hM t ⟨ht₀.1.trans ht.1, ht.2⟩, hv]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] in
theorem gauge_joint (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (hTeq : T = flowExtinctionTime S) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ioo t₀ T) (x : M)
    (W0 W1 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun q : ℝ × M => (Diffeomorph.pullbackMetric (normalizedFlowMetric S q.1) (ψ q.1)).inner
        q.2 (W0 q.2) (W1 q.2)) (t, x) := by
  have hreg : Ioo t₀ T ⊆ (RealTimeInterval.closedOpen 0 T hT).regular :=
    fun r hr => (⟨ht₀.1.trans hr.1, hr.2⟩ : r ∈ Ioo 0 T)
  have hg := MetricFamilySmoothOn.metricCLMSection_contMDiffOn hS.smoothMetric hreg
  have hP := pullbackFamily_inner_contMDiffAt (I := I) (fun r => S.family.metric r) isOpen_Ioo hg
    ψ hψ W0 W1 ht x
  have hlt : t < flowExtinctionTime S := hTeq ▸ ht.2
  have hc : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => 1 / (2 * (flowExtinctionTime S - q.1))) (t, x) := by
    have h1 : ContDiffAt ℝ ∞ (fun r : ℝ => 1 / (2 * (flowExtinctionTime S - r))) t := by
      have hne : 2 * (flowExtinctionTime S - t) ≠ 0 := by
        have := sub_pos.2 hlt; positivity
      exact contDiffAt_const.div (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)) hne
    exact ContMDiffAt.comp (g := fun r : ℝ => 1 / (2 * (flowExtinctionTime S - r)))
      (f := Prod.fst) (t, x) h1.contMDiffAt contMDiffAt_fst
  refine (hc.mul hP).congr_of_eventuallyEq ?_
  have hnhds : Iio (flowExtinctionTime S) ×ˢ (univ : Set M) ∈ 𝓝 (t, x) :=
    (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hlt, trivial⟩
  filter_upwards [hnhds] with q hq
  rw [gauge_inner_eq S (ψ q.1) hq.1, Diffeomorph.pullbackMetric_inner]
  rfl

omit [ConnectedSpace M] in
theorem gauge_forward_limit (h : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hTeq : T = flowExtinctionTime S) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    (hdecay : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + q) *
          normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
        C * (flowExtinctionTime S - t) ^ γ)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ))
    (hψd : ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Ioo t₀ T) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
      (∀ σ, -(1 / 2) * Real.log (1 - t₁ / flowExtinctionTime S) ≤ σ → ∀ x : M,
        ∀ v : TangentSpace I x, lam * h.inner x v v ≤ (Diffeomorph.pullbackMetric
          (normalizedFlowMetric S (flowExtinctionTime S * (1 - Real.exp (-2 * σ))))
          (ψ (flowExtinctionTime S * (1 - Real.exp (-2 * σ))))).inner x v v) ∧
      (∀ x : M, ∀ v : TangentSpace I x, lam * h.inner x v v ≤ kInf.inner x v v) ∧
      (∀ q : ℕ, ∃ B : ℝ, ∀ x : M, metricCovDerivNorm (I := I) q kInf h x ≤ B ∧
        ∀ σ, -(1 / 2) * Real.log (1 - t₁ / flowExtinctionTime S) ≤ σ →
          metricCovDerivNorm (I := I) q (Diffeomorph.pullbackMetric
            (normalizedFlowMetric S (flowExtinctionTime S * (1 - Real.exp (-2 * σ))))
            (ψ (flowExtinctionTime S * (1 - Real.exp (-2 * σ))))) h x ≤ B) ∧
      (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ σ, -(1 / 2) * Real.log (1 - t₁ / flowExtinctionTime S) ≤ σ →
        ∀ q : ℕ, q ≤ N → ∀ x : M,
        metricDerivNorm (I := I) q (Diffeomorph.pullbackMetric
            (normalizedFlowMetric S (flowExtinctionTime S * (1 - Real.exp (-2 * σ))))
            (ψ (flowExtinctionTime S * (1 - Real.exp (-2 * σ))))) kInf h x ≤
          B * Real.exp (-(β * σ))) := by
  set Tst := flowExtinctionTime S with hTst
  have hTpos : 0 < Tst := hTeq ▸ hT
  have ht₁T : t₁ < Tst := hTeq ▸ ht₁.2
  set s₁ := -(1 / 2) * Real.log (1 - t₁ / Tst) with hs₁
  have harg : 0 < 1 - t₁ / Tst := by
    rw [sub_pos, div_lt_one hTpos]; exact ht₁T
  have hθs₁ : Real.exp (-2 * s₁) = 1 - t₁ / Tst := by
    rw [hs₁, show -2 * (-(1 / 2) * Real.log (1 - t₁ / Tst)) = Real.log (1 - t₁ / Tst) by ring,
      Real.exp_log harg]
  have hθU : ∀ σ, s₁ ≤ σ → Tst * (1 - Real.exp (-2 * σ)) ∈ Ioo t₀ T := by
    intro σ hσ
    have he : Real.exp (-2 * σ) ≤ Real.exp (-2 * s₁) := Real.exp_le_exp.2 (by linarith)
    have hepos := Real.exp_pos (-2 * σ)
    rw [hθs₁] at he
    constructor
    · have : t₁ ≤ Tst * (1 - Real.exp (-2 * σ)) := by
        have h2 : Tst * (t₁ / Tst) = t₁ := by field_simp
        nlinarith
      exact ht₁.1.trans_le this
    · rw [hTeq]; nlinarith
  refine exists_metric_limit_of_reparam (I := I) h
    (fun t => Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t))
    (fun t => (1 / (Tst - t)) • pullbackTensor02FieldCross (ψ t) (Mf t)) (U := Ioo t₀ T)
    (fun t ht x W0 W1 => gauge_joint S hS hTeq ht₀ ψ hψ ht x W0 W1)
    (fun t ht x v => gauge_hasDerivAt S hTeq f Mf hM ht₀ ψ hψd ht x v)
    (fun σ => Tst * (1 - Real.exp (-2 * σ))) (fun σ => Tst * (2 * Real.exp (-2 * σ))) s₁
    (by fun_prop) (fun σ => by
      have h1 : HasDerivAt (fun σ : ℝ => -2 * σ) (-2) σ := by
        simpa using (hasDerivAt_id σ).const_mul (-2)
      have h2 := (h1.exp.const_sub 1).const_mul Tst
      convert h2 using 1
      ring) hθU ?_
  intro q
  obtain ⟨C, γ, hγ, hC⟩ := hdecay q
  refine ⟨2 * Real.sqrt (2 ^ (q + 2) * max C 0 * Tst ^ γ), γ, hγ, fun σ hσ x => ?_⟩
  have hU := hθU σ hσ
  have hlt : Tst * (1 - Real.exp (-2 * σ)) < Tst := hTeq ▸ hU.2
  have hb := gauge_velocity_bound S Mf ψ q hC (t := Tst * (1 - Real.exp (-2 * σ)))
    ⟨hU.1.le, hU.2⟩ hlt x
  have hτ : Tst - Tst * (1 - Real.exp (-2 * σ)) = Tst * Real.exp (-2 * σ) := by ring
  rw [hτ] at hb
  have hepos := Real.exp_pos (-2 * σ)
  have hτpos : 0 < Tst * Real.exp (-2 * σ) := mul_pos hTpos hepos
  rw [abs_of_pos (by positivity : (0 : ℝ) < Tst * (2 * Real.exp (-2 * σ)))]
  calc Tst * (2 * Real.exp (-2 * σ)) * tensor02CovDerivNormWith q
        ((1 / (Tst - Tst * (1 - Real.exp (-2 * σ)))) •
          pullbackTensor02FieldCross (ψ (Tst * (1 - Real.exp (-2 * σ))))
            (Mf (Tst * (1 - Real.exp (-2 * σ)))))
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S (Tst * (1 - Real.exp (-2 * σ))))
          (ψ (Tst * (1 - Real.exp (-2 * σ)))))
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S (Tst * (1 - Real.exp (-2 * σ))))
          (ψ (Tst * (1 - Real.exp (-2 * σ))))) x
      ≤ Tst * (2 * Real.exp (-2 * σ)) * (1 / (Tst * Real.exp (-2 * σ)) *
          Real.sqrt (2 ^ (q + 2) * max C 0 * (Tst * Real.exp (-2 * σ)) ^ γ)) := by
        rw [hτ]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * Real.sqrt (2 ^ (q + 2) * max C 0 * (Tst * Real.exp (-2 * σ)) ^ γ) := by
        field_simp
    _ = 2 * Real.sqrt (2 ^ (q + 2) * max C 0 * Tst ^ γ) * Real.exp (-(γ * σ)) := by
        rw [Real.mul_rpow hTpos.le hepos.le, ← Real.exp_mul,
          show 2 ^ (q + 2) * max C 0 * (Tst ^ γ * Real.exp (-2 * σ * γ)) =
            (2 ^ (q + 2) * max C 0 * Tst ^ γ) * Real.exp (-(γ * σ)) ^ 2 by
              rw [← Real.exp_nat_mul]; ring_nf,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le]
        ring

omit [ConnectedSpace M] in
theorem gauge_backward_bounds (h : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hTeq : T = flowExtinctionTime S) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    (hdecay : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + q) *
          normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
        C * (flowExtinctionTime S - t) ^ γ)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ))
    (hψd : ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Ioo t₀ T) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ σ, 0 ≤ σ → ∀ x : M, ∀ v : TangentSpace I x, lam * h.inner x v v ≤
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S (t₀ + (t₁ - t₀) * Real.exp (-σ)))
          (ψ (t₀ + (t₁ - t₀) * Real.exp (-σ)))).inner x v v) ∧
      (∀ q : ℕ, ∃ B : ℝ, ∀ x : M, ∀ σ, 0 ≤ σ →
          metricCovDerivNorm (I := I) q (Diffeomorph.pullbackMetric
            (normalizedFlowMetric S (t₀ + (t₁ - t₀) * Real.exp (-σ)))
            (ψ (t₀ + (t₁ - t₀) * Real.exp (-σ)))) h x ≤ B) := by
  set Tst := flowExtinctionTime S with hTst
  have hd10 : 0 < t₁ - t₀ := sub_pos.2 ht₁.1
  have ht₁T : t₁ < Tst := hTeq ▸ ht₁.2
  have hθU : ∀ σ, 0 ≤ σ → t₀ + (t₁ - t₀) * Real.exp (-σ) ∈ Ioo t₀ T := by
    intro σ hσ
    have he1 : Real.exp (-σ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he0 := Real.exp_pos (-σ)
    constructor
    · nlinarith
    · nlinarith [ht₁.2]
  have hbdv : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ σ, 0 ≤ σ → ∀ x : M,
      |(fun σ => -((t₁ - t₀) * Real.exp (-σ))) σ| * tensor02CovDerivNormWith (I := I) q
        ((fun t => (1 / (Tst - t)) • pullbackTensor02FieldCross (ψ t) (Mf t))
          ((fun σ => t₀ + (t₁ - t₀) * Real.exp (-σ)) σ))
        ((fun t => Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t))
          ((fun σ => t₀ + (t₁ - t₀) * Real.exp (-σ)) σ))
        ((fun t => Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t))
          ((fun σ => t₀ + (t₁ - t₀) * Real.exp (-σ)) σ)) x ≤
        C * Real.exp (-(γ * σ)) := by
    intro q
    obtain ⟨C, γ, hγ, hC⟩ := hdecay q
    set τ₁ := Tst - t₁ with hτ₁
    set τ₀ := Tst - t₀ with hτ₀
    have hτ₁pos : 0 < τ₁ := sub_pos.2 ht₁T
    refine ⟨(t₁ - t₀) * (1 / τ₁ * Real.sqrt (2 ^ (q + 2) * max C 0 * τ₀ ^ γ)), 1, one_pos,
      fun σ hσ x => ?_⟩
    have hU := hθU σ hσ
    have hlt : t₀ + (t₁ - t₀) * Real.exp (-σ) < Tst := hTeq ▸ hU.2
    have hb := gauge_velocity_bound S Mf ψ q hC (t := t₀ + (t₁ - t₀) * Real.exp (-σ))
      ⟨hU.1.le, hU.2⟩ hlt x
    set τ := Tst - (t₀ + (t₁ - t₀) * Real.exp (-σ)) with hτ
    have he1 : Real.exp (-σ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he0 := Real.exp_pos (-σ)
    have hτ1 : τ₁ ≤ τ := by rw [hτ, hτ₁]; nlinarith
    have hτ0 : τ ≤ τ₀ := by rw [hτ, hτ₀]; nlinarith
    have hτpos : 0 < τ := hτ₁pos.trans_le hτ1
    have hb2 : 1 / τ * Real.sqrt (2 ^ (q + 2) * max C 0 * τ ^ γ) ≤
        1 / τ₁ * Real.sqrt (2 ^ (q + 2) * max C 0 * τ₀ ^ γ) := by
      refine mul_le_mul (one_div_le_one_div_of_le hτ₁pos hτ1) (Real.sqrt_le_sqrt ?_)
        (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hτpos.le hτ0 hγ.le) (by positivity)
    rw [abs_neg, abs_of_pos (mul_pos hd10 he0), show Real.exp (-(1 * σ)) = Real.exp (-σ) by
      rw [one_mul]]
    calc (t₁ - t₀) * Real.exp (-σ) * tensor02CovDerivNormWith q
          ((1 / (Tst - (t₀ + (t₁ - t₀) * Real.exp (-σ)))) •
            pullbackTensor02FieldCross (ψ (t₀ + (t₁ - t₀) * Real.exp (-σ)))
              (Mf (t₀ + (t₁ - t₀) * Real.exp (-σ))))
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S (t₀ + (t₁ - t₀) * Real.exp (-σ)))
            (ψ (t₀ + (t₁ - t₀) * Real.exp (-σ))))
          (Diffeomorph.pullbackMetric (normalizedFlowMetric S (t₀ + (t₁ - t₀) * Real.exp (-σ)))
            (ψ (t₀ + (t₁ - t₀) * Real.exp (-σ)))) x
        ≤ (t₁ - t₀) * Real.exp (-σ) *
            (1 / τ₁ * Real.sqrt (2 ^ (q + 2) * max C 0 * τ₀ ^ γ)) :=
          mul_le_mul_of_nonneg_left (hb.trans hb2) (by positivity)
      _ = _ := by ring
  obtain ⟨lam, hlam, _kInf, hlo, -, hbd, -⟩ := exists_metric_limit_of_reparam (I := I) h
    (fun t => Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t))
    (fun t => (1 / (Tst - t)) • pullbackTensor02FieldCross (ψ t) (Mf t)) (U := Ioo t₀ T)
    (fun t ht x W0 W1 => gauge_joint S hS hTeq ht₀ ψ hψ ht x W0 W1)
    (fun t ht x v => gauge_hasDerivAt S hTeq f Mf hM ht₀ ψ hψd ht x v)
    (fun σ => t₀ + (t₁ - t₀) * Real.exp (-σ)) (fun σ => -((t₁ - t₀) * Real.exp (-σ))) 0
    (by fun_prop) (fun σ => by
      have h2 := ((hasDerivAt_neg σ).exp.const_mul (t₁ - t₀)).const_add t₀
      convert h2 using 1
      ring) hθU hbdv
  exact ⟨lam, hlam, hlo, fun q => by
    obtain ⟨B, hB⟩ := hbd q
    exact ⟨B, fun x σ hσ => (hB x).2 σ hσ⟩⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [ConnectedSpace M] in
theorem ΔG_pullback_scale (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (ψ : M ≃ₘ⟮I, I⟯ M) (u : C^∞⟮I, M; ℝ⟯) (x : M) :
    ΔG (Diffeomorph.pullbackMetric (scaleMetric c hc g) ψ) (u.comp ψ.toContMDiffMap) x =
      c⁻¹ * ΔG g u (ψ x) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have h1 := laplacian_levi_eq (I := I) (Diffeomorph.pullbackMetric (scaleMetric c hc g) ψ)
    (u.comp ψ.toContMDiffMap).contMDiff x
  have h2 := laplacian_levi_eq (I := I) g u.contMDiff (ψ x)
  change ΔG (Diffeomorph.pullbackMetric (scaleMetric c hc g) ψ)
      ⟨_, (u.comp ψ.toContMDiffMap).contMDiff⟩ x = c⁻¹ * ΔG g ⟨_, u.contMDiff⟩ (ψ x)
  rw [← h1, ← h2, ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  have h3 := laplacian_pullbackCross (scaleMetric c hc g) ψ (f := ⇑u) (x := x)
    (u.contMDiff.contMDiffAt.of_le (by decide))
  change laplacian (LeviCivita (Diffeomorph.pullbackMetricCross (scaleMetric c hc g) ψ))
      (Diffeomorph.pullbackMetricCross (scaleMetric c hc g) ψ) (⇑u ∘ ⇑ψ) x = _
  rw [h3]
  have he : LeviCivita (I := I) (scaleMetric c hc g) = LeviCivita (I := I) g :=
    lcConn_scaleMetric c hc g
  rw [he]
  exact laplacian_scaleMetric c hc (LeviCivita (I := I) g) g
    ((gradFun_contMDiff_total (I := I) g u.contMDiff).mdifferentiableAt (by simp))

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] in
theorem gauge_potential_poisson
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (f : C^∞⟮I, M; ℝ⟯) (ψ : M ≃ₘ⟮I, I⟯ M) {t : ℝ} (ht : t < flowExtinctionTime S)
    (hfeq : (∫ x, f x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
      ∀ x, ΔG (S.family.metric t) f x = S.scalar t x - 1 / (flowExtinctionTime S - t)) :
    (∫ x, f.comp ψ.toContMDiffMap x ∂riemannianVolumeMeasure I M
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ)) = 0 ∧
      ∀ x, ΔG (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ)
        (f.comp ψ.toContMDiffMap) x =
        metricScalarAt (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ) x - 2 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  set τ := flowExtinctionTime S - t with hτ
  have hτ0 : 0 < τ := sub_pos.2 ht
  rw [normalizedFlowMetric_eq S ht]
  constructor
  · rw [riemannianVolumeMeasure_pullback, volume_scaleMetric]
    have hmeas : Measurable (ψ.symm : M → M) := ψ.symm.continuous.measurable
    rw [integral_map hmeas.aemeasurable
      (f.comp ψ.toContMDiffMap).contMDiff.continuous.aestronglyMeasurable]
    have heq : (fun y => f.comp ψ.toContMDiffMap (ψ.symm y)) = fun y => f y := by
      funext y
      simp
    rw [heq, integral_smul_measure, hfeq.1, smul_zero]
  · intro x
    rw [ΔG_pullback_scale, metricScalarAt_pullback, Curvature.metricScalarAt_scaleMetric, hfeq.2]
    change (1 / (2 * τ))⁻¹ * (S.scalar t (ψ x) - 1 / τ) =
      (1 / (2 * τ))⁻¹ * S.scalar t (ψ x) - 2
    field_simp

omit [CompactSpace M] [ConnectedSpace M] in
theorem tracelessHessAt_pullback_scale (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (ψ : M ≃ₘ⟮I, I⟯ M) (u : C^∞⟮I, M; ℝ⟯) (x : M) (v : Fin 2 → TangentSpace I x) :
    tracelessHessAt (Diffeomorph.pullbackMetric (scaleMetric c hc g) ψ) (u.comp ψ.toContMDiffMap)
        x v = tracelessHessAt g u (ψ x) (fun j => mfderiv I I ψ x (v j)) := by
  have hv : v = vec2 (v 0) (v 1) := by funext j; fin_cases j <;> rfl
  have hw : (fun j => mfderiv I I ψ x (v j)) =
      vec2 (mfderiv I I ψ x (v 0)) (mfderiv I I ψ x (v 1)) := by
    funext j; fin_cases j <;> rfl
  rw [hw, hv, tracelessHessAt_vec2, tracelessHessAt_vec2, ΔG_pullback_scale,
    ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, hessFun_pullbackCross,
    Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner, hessFun_scaleMetric]
  simp only [vec2, ↓reduceIte, show ¬((1 : Fin 2) = 0) from by decide]
  field_simp

omit [ConnectedSpace M] in
theorem gauge_tracelessHess_normSq_le
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (f : C^∞⟮I, M; ℝ⟯)
    (Mf : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {t : ℝ} (hM : ∀ x, Mf x = tracelessHessAt (S.family.metric t) f x)
    (ψ : M ≃ₘ⟮I, I⟯ M) (ht : t < flowExtinctionTime S) {C γ : ℝ}
    (hdec : ∀ x, (flowExtinctionTime S - t) ^ (2 + 0) *
        normSq0S (S.family.metric t) x (2 + 0) (iterCov (S.family.metric t) 2 Mf 0 x) ≤
        C * (flowExtinctionTime S - t) ^ γ) (x : M) :
    normSq0S (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ) x 2
        (tracelessHessAt (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ)
          (f.comp ψ.toContMDiffMap) x) ≤
      4 * max C 0 * (flowExtinctionTime S - t) ^ γ := by
  set τ := flowExtinctionTime S - t with hτ
  have hτ0 : 0 < τ := sub_pos.2 ht
  have hten : tracelessHessAt (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ)
      (f.comp ψ.toContMDiffMap) x = pullbackTensor02FieldCross ψ Mf x := by
    apply tensor0SSpace_ext 2 x
    intro v
    rw [pullbackTensor02FieldCross_apply, hM, normalizedFlowMetric_eq S ht,
      tracelessHessAt_pullback_scale]
  rw [hten]
  have hnorm := tensor02CovDerivNormWith_pullback_scale (S.family.metric t)
    (1 / (2 * τ)) (normalizedSurfaceMetric_pos ht) ψ Mf 0 x
  rw [← normalizedFlowMetric_eq S ht] at hnorm
  have hdef : tensor02CovDerivNormWith 0 (pullbackTensor02FieldCross ψ Mf)
      (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ)
      (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ) x =
      Real.sqrt (normSq0S (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ) x 2
        (pullbackTensor02FieldCross ψ Mf x)) := rfl
  rw [hdef] at hnorm
  have hN0 := normSq0S_nonneg (I := I) (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ)
    x 2 (pullbackTensor02FieldCross ψ Mf x)
  set Nsq := normSq0S (S.family.metric t) (ψ x) (2 + 0)
    (iterCov (S.family.metric t) 2 Mf 0 (ψ x)) with hNsq
  have hNsq0 : 0 ≤ Nsq := normSq0S_nonneg (I := I) _ _ _ _
  have hsq : (Real.sqrt (1 / (2 * τ)))⁻¹ = Real.sqrt (2 * τ) := by
    rw [← Real.sqrt_inv, one_div, inv_inv]
  rw [hsq] at hnorm
  have hval : normSq0S (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ) x 2
      (pullbackTensor02FieldCross ψ Mf x) = (2 * τ) ^ 2 * Nsq := by
    have h2 : Real.sqrt (normSq0S (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) ψ) x 2
        (pullbackTensor02FieldCross ψ Mf x)) ^ 2 =
        (Real.sqrt (2 * τ) ^ (0 + 2) * Real.sqrt Nsq) ^ 2 := by rw [hnorm]
    rw [Real.sq_sqrt hN0, mul_pow, ← pow_mul, Real.sq_sqrt hNsq0] at h2
    rw [h2, show (0 + 2) * 2 = 4 by norm_num]
    have : Real.sqrt (2 * τ) ^ 4 = (2 * τ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
    rw [this]
  rw [hval]
  have hd := hdec (ψ x)
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ0.le γ
  have h1 : τ ^ 2 * Nsq ≤ max C 0 * τ ^ γ :=
    hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hτγ)
  nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [ConnectedSpace M] in
theorem metricDerivNorm_le_covNorm_add (q : ℕ) (A B h : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) q A B h x ≤
      metricCovDerivNorm (I := I) q A h x + metricCovDerivNorm (I := I) q B h x := by
  simp only [metricCovDerivNorm, metricDerivNorm, metricDiffCovDerivAt]
  have htri := DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_add_le (I := I) h x (q + 2)
    (metricCovDeriv (I := I) A h q x) ((-1 : ℝ) • metricCovDeriv (I := I) B h q x)
  have hneg := DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_smul (I := I) h x (q + 2)
    (-1 : ℝ) (metricCovDeriv (I := I) B h q x)
  rw [hneg, abs_neg, abs_one, one_mul] at htri
  have heq : metricCovDeriv (I := I) A h q x + (-1 : ℝ) • metricCovDeriv (I := I) B h q x =
      metricCovDeriv (I := I) A h q x - metricCovDeriv (I := I) B h q x := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [heq] at htri
  exact htri

omit [ConnectedSpace M] in
theorem gauge_limit_bounds
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hTeq : T = flowExtinctionTime S) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    (hdecay : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + q) *
          normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
        C * (flowExtinctionTime S - t) ^ γ)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ))
    (hψd : ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
 :
    ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
      (∀ t ∈ Ico t₀ T, ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)).inner x v v) ∧
      (∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤ kInf.inner x v v) ∧
      (∀ q : ℕ, ∃ B : ℝ, (∀ x, metricCovDerivNorm q kInf (S.family.metric 0) x ≤ B) ∧
        ∀ t ∈ Ico t₀ T, ∀ x, metricCovDerivNorm q
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) (S.family.metric 0) x ≤ B) ∧
      (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ T, ∀ q ≤ N, ∀ x,
        metricDerivNorm q (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
          (S.family.metric 0) x ≤ B * (flowExtinctionTime S - t) ^ β) := by
  classical
  set h := S.family.metric 0 with hh
  set Tst := flowExtinctionTime S with hTst
  have hTpos : 0 < Tst := hTeq ▸ hT
  set t₁ := (t₀ + T) / 2 with ht₁def
  have ht₁ : t₁ ∈ Ioo t₀ T := ⟨by linarith [ht₀.2], by linarith [ht₀.2]⟩
  have ht₁T : t₁ < Tst := hTeq ▸ ht₁.2
  obtain ⟨lamA, hlamA, kInf, hloA, hloInf, hbdA, hrateA⟩ :=
    gauge_forward_limit h S hS hTeq f Mf hM ht₀ hdecay ψ hψ hψd ht₁
  obtain ⟨lamB, hlamB, hloB, hbdB⟩ :=
    gauge_backward_bounds h S hS hTeq f Mf hM ht₀ hdecay ψ hψ hψd ht₁
  set K : ℝ → SmoothRiemannianMetric I M :=
    fun t => Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t) with hK
  obtain ⟨C₀, hC₀⟩ := metricUniformEquivalentOn_of_compact (I := I) h (K t₀)
  have hC₀1 : 1 ≤ C₀ := hC₀.1
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀1
  have hfwd : ∀ t, t₁ ≤ t → t < T → ∃ σ, -(1 / 2) * Real.log (1 - t₁ / Tst) ≤ σ ∧
      Tst * (1 - Real.exp (-2 * σ)) = t ∧
      Real.exp (-2 * σ) = (Tst - t) / Tst := by
    intro t ht1 htT
    have htT' : t < Tst := hTeq ▸ htT
    have harg : 0 < 1 - t / Tst := by rw [sub_pos, div_lt_one hTpos]; exact htT'
    refine ⟨-(1 / 2) * Real.log (1 - t / Tst), ?_, ?_, ?_⟩
    · have hle : 1 - t / Tst ≤ 1 - t₁ / Tst := by
        have : t₁ / Tst ≤ t / Tst := div_le_div_of_nonneg_right ht1 hTpos.le
        linarith
      have := Real.log_le_log harg hle
      linarith
    · rw [show -2 * (-(1 / 2) * Real.log (1 - t / Tst)) = Real.log (1 - t / Tst) by ring,
        Real.exp_log harg]
      field_simp
      ring
    · rw [show -2 * (-(1 / 2) * Real.log (1 - t / Tst)) = Real.log (1 - t / Tst) by ring,
        Real.exp_log harg]
      field_simp
  have hbwd : ∀ t, t₀ < t → t ≤ t₁ → ∃ σ, 0 ≤ σ ∧ t₀ + (t₁ - t₀) * Real.exp (-σ) = t := by
    intro t ht0 ht1
    have hd : 0 < t₁ - t₀ := sub_pos.2 ht₁.1
    have hr0 : 0 < (t - t₀) / (t₁ - t₀) := div_pos (sub_pos.2 ht0) hd
    have hr1 : (t - t₀) / (t₁ - t₀) ≤ 1 := by rw [div_le_one hd]; linarith
    refine ⟨-Real.log ((t - t₀) / (t₁ - t₀)), ?_, ?_⟩
    · have := Real.log_nonpos hr0.le hr1; linarith
    · rw [neg_neg, Real.exp_log hr0]
      field_simp
      ring
  set lam := min (min lamA lamB) C₀⁻¹ with hlam
  have hlam0 : 0 < lam := lt_min (lt_min hlamA hlamB) (inv_pos.2 hC₀pos)
  have hhnn : ∀ x (v : TangentSpace I x), 0 ≤ h.inner x v v := by
    intro x v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (h.pos x v hv).le
  have hlowAll : ∀ t ∈ Ico t₀ T, ∀ x (v : TangentSpace I x), lam * h.inner x v v ≤
      (K t).inner x v v := by
    intro t ht x v
    have hv := hhnn x v
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      have := (hC₀.2 x (Set.mem_univ x) v).1
      have : lam ≤ C₀⁻¹ := min_le_right _ _
      nlinarith
    · rcases le_or_gt t t₁ with h1 | h1
      · obtain ⟨σ, hσ, rfl⟩ := hbwd t h0 h1
        have := hloB σ hσ x v
        have : lam ≤ lamB := (min_le_left _ _).trans (min_le_right _ _)
        nlinarith
      · obtain ⟨σ, hσ, hσt, -⟩ := hfwd t h1.le ht.2
        have h2 := hloA σ hσ x v
        rw [hσt] at h2
        have : lam ≤ lamA := (min_le_left _ _).trans (min_le_left _ _)
        nlinarith
  have hlowInf' : ∀ x (v : TangentSpace I x), lam * h.inner x v v ≤ kInf.inner x v v := by
    intro x v
    have := hloInf x v
    have hv := hhnn x v
    have : lam ≤ lamA := (min_le_left _ _).trans (min_le_left _ _)
    nlinarith
  have hbdAll : ∀ q : ℕ, ∃ B : ℝ, (∀ x, metricCovDerivNorm q kInf h x ≤ B) ∧
      ∀ t ∈ Ico t₀ T, ∀ x, metricCovDerivNorm q (K t) h x ≤ B := by
    intro q
    obtain ⟨BA, hBA⟩ := hbdA q
    obtain ⟨BB, hBB⟩ := hbdB q
    obtain ⟨B0, hB0⟩ := metricCovDerivNorm_bddOn (I := I) isCompact_univ q (K t₀) h
    refine ⟨max (max BA BB) B0, fun x => ((hBA x).1).trans (le_trans (le_max_left _ _)
      (le_max_left _ _)), fun t ht x => ?_⟩
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      exact (hB0 x (Set.mem_univ x)).trans (le_max_right _ _)
    · rcases le_or_gt t t₁ with h1 | h1
      · obtain ⟨σ, hσ, rfl⟩ := hbwd t h0 h1
        exact (hBB x σ hσ).trans ((le_max_right _ _).trans (le_max_left _ _))
      · obtain ⟨σ, hσ, hσt, -⟩ := hfwd t h1.le ht.2
        have := (hBA x).2 σ hσ
        rw [hσt] at this
        exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨lam, hlam0, kInf, hlowAll, hlowInf', hbdAll, fun N => ?_⟩
  obtain ⟨B, β, hβ, hB⟩ := hrateA N
  have hex : ∀ q ∈ Finset.range (N + 1), ∃ Bq : ℝ, (∀ x, metricCovDerivNorm q kInf h x ≤ Bq) ∧
      ∀ t ∈ Ico t₀ T, ∀ x, metricCovDerivNorm q (K t) h x ≤ Bq := fun q _ => hbdAll q
  choose Bq hBq using hex
  set D := ∑ q ∈ (Finset.range (N + 1)).attach, max (Bq q.1 q.2) 0 with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => le_max_right _ _
  set τ₁ := Tst - t₁ with hτ₁
  have hτ₁pos : 0 < τ₁ := sub_pos.2 ht₁T
  refine ⟨max (|B| / Tst ^ (β / 2)) (2 * D / τ₁ ^ (β / 2)), β / 2, by positivity,
    fun t ht q hq x => ?_⟩
  have htT' : t < Tst := hTeq ▸ ht.2
  have hτpos : 0 < Tst - t := sub_pos.2 htT'
  rcases lt_or_ge t t₁ with h1 | h1
  · have hqmem : q ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    have h2 := metricDerivNorm_le_covNorm_add (I := I) q (K t) kInf h x
    have hb1 := (hBq q hqmem).2 t ht x
    have hb2 := (hBq q hqmem).1 x
    have hBqD : max (Bq q hqmem) 0 ≤ D :=
      Finset.single_le_sum (f := fun q : {q // q ∈ Finset.range (N + 1)} => max (Bq q.1 q.2) 0)
        (fun _ _ => le_max_right _ _) (Finset.mem_attach _ ⟨q, hqmem⟩)
    have hτle : τ₁ ^ (β / 2) ≤ (Tst - t) ^ (β / 2) :=
      Real.rpow_le_rpow hτ₁pos.le (by linarith) (by positivity)
    have hτ₁β : 0 < τ₁ ^ (β / 2) := Real.rpow_pos_of_pos hτ₁pos _
    calc metricDerivNorm q (K t) kInf h x ≤ 2 * D := by
          linarith [le_max_left (Bq q hqmem) 0]
      _ = 2 * D / τ₁ ^ (β / 2) * τ₁ ^ (β / 2) := by field_simp
      _ ≤ 2 * D / τ₁ ^ (β / 2) * (Tst - t) ^ (β / 2) :=
          mul_le_mul_of_nonneg_left hτle (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · obtain ⟨σ, hσ, hσt, hexp⟩ := hfwd t h1 ht.2
    have h2 := hB σ hσ q hq x
    rw [hσt] at h2
    have hexpβ : Real.exp (-(β * σ)) = ((Tst - t) / Tst) ^ (β / 2) := by
      rw [← hexp, ← Real.exp_mul]
      congr 1
      ring
    rw [hexpβ, Real.div_rpow hτpos.le hTpos.le] at h2
    have hTβ : 0 < Tst ^ (β / 2) := Real.rpow_pos_of_pos hTpos _
    calc metricDerivNorm q (K t) kInf h x ≤ B * ((Tst - t) ^ (β / 2) / Tst ^ (β / 2)) := h2
      _ ≤ |B| / Tst ^ (β / 2) * (Tst - t) ^ (β / 2) := by
          rw [mul_div_assoc', div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)) hTβ.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem tendsto_rpow_sub_seq {T t₀ γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun j : ℕ => (T - (T - (T - t₀) / (j + 2))) ^ γ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun j : ℕ => (T - t₀) / ((j : ℝ) + 2)) atTop (𝓝 0) := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 this))
  have h2 : ContinuousAt (fun r : ℝ => r ^ γ) 0 := Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)
  have h3 := h2.tendsto.comp h1
  rw [Real.zero_rpow hγ.ne'] at h3
  refine h3.congr fun j => ?_
  simp only [Function.comp]
  ring_nf

theorem gauge_limit_round_scalar (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (hTeq : T = flowExtinctionTime S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hfeq : ∀ t ∈ Ico 0 T, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
      ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) {C₀ γ₀ : ℝ} (hγ₀ : 0 < γ₀)
    (hdec0 : ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + 0) *
          normSq0S (S.family.metric t) x (2 + 0) (iterCov (S.family.metric t) 2 (Mf t) 0 x) ≤
        C₀ * (flowExtinctionTime S - t) ^ γ₀)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ t ∈ Ico 0 T, ∀ x, c ≤ S.scalar t x * (2 * (flowExtinctionTime S - t)))
    {lam : ℝ} (hlam : 0 < lam) (kInf : SmoothRiemannianMetric I M)
    (hlo : ∀ t ∈ Ico t₀ T, ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
      (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)).inner x v v)
    (hbd : ∀ q : ℕ, ∃ B : ℝ, (∀ x, metricCovDerivNorm q kInf (S.family.metric 0) x ≤ B) ∧
      ∀ t ∈ Ico t₀ T, ∀ x, metricCovDerivNorm q
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) (S.family.metric 0) x ≤ B)
    (hrate : ∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ T, ∀ q ≤ N, ∀ x,
      metricDerivNorm q (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
        (S.family.metric 0) x ≤ B * (flowExtinctionTime S - t) ^ β) :
    ∀ x, metricScalarAt kInf x = 2 := by
  classical
  rcases isEmpty_or_nonempty M with hM0 | hM0
  · intro x; exact isEmptyElim x
  set h := S.family.metric 0 with hh
  set Tst := flowExtinctionTime S with hTst
  set tj : ℕ → ℝ := fun j => T - (T - t₀) / ((j : ℝ) + 2) with htj
  have hd : 0 < T - t₀ := sub_pos.2 ht₀.2
  have htjmem : ∀ j, tj j ∈ Ico t₀ T := by
    intro j
    have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have h1 : (T - t₀) / ((j : ℝ) + 2) ≤ (T - t₀) / 2 :=
      div_le_div_of_nonneg_left hd.le (by norm_num) (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
    have h2 : 0 < (T - t₀) / ((j : ℝ) + 2) := div_pos hd hj
    exact ⟨by simp only [htj]; linarith, by simp only [htj]; linarith⟩
  have htjlt : ∀ j, tj j < Tst := fun j => hTeq ▸ (htjmem j).2
  set k : ℕ → SmoothRiemannianMetric I M :=
    fun j => Diffeomorph.pullbackMetric (normalizedFlowMetric S (tj j)) (ψ (tj j)) with hk
  set fb : ℕ → C^∞⟮I, M; ℝ⟯ := fun j => (f (tj j)).comp (ψ (tj j)).toContMDiffMap with hfb
  have hτlim : ∀ γ : ℝ, 0 < γ → Tendsto (fun j => (Tst - tj j) ^ γ) atTop (𝓝 0) := by
    intro γ hγ
    have := tendsto_rpow_sub_seq (T := T) (t₀ := t₀) hγ
    rw [← hTeq]
    exact this
  obtain ⟨B0, hB0⟩ := hbd 0
  obtain ⟨B1, hB1⟩ := hbd 1
  obtain ⟨B2, hB2⟩ := hbd 2
  set B := max (max B0 B1) B2 with hB
  have hbddk : ∀ j x, ∀ q ≤ 2, metricCovDerivNorm q (k j) h x ≤ B := by
    intro j x q hq
    interval_cases q
    · exact ((hB0.2 (tj j) (htjmem j) x)).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact ((hB1.2 (tj j) (htjmem j) x)).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact ((hB2.2 (tj j) (htjmem j) x)).trans (le_max_right _ _)
  obtain ⟨Br, βr, hβr, hBr⟩ := hrate 2
  have hconv : ∀ q ≤ 2, Tendsto (fun j => ⨆ x, metricDerivNorm q (k j) kInf h x) atTop (𝓝 0) := by
    intro q hq
    have hup : ∀ j, (⨆ x, metricDerivNorm q (k j) kInf h x) ≤ Br * (Tst - tj j) ^ βr :=
      fun j => ciSup_le fun x => hBr (tj j) (htjmem j) q hq x
    have hlo0 : ∀ j, 0 ≤ ⨆ x, metricDerivNorm q (k j) kInf h x := fun j =>
      (Real.sqrt_nonneg _).trans (le_ciSup ((isCompact_range
        (metricDerivNorm_cont (I := I) q (k j) kInf h)).bddAbove) (Classical.arbitrary M))
    have hlim := (hτlim βr hβr).const_mul Br
    rw [mul_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo0 hup
  have hpois : ∀ j, (∫ x, fb j x ∂riemannianVolumeMeasure I M (k j)) = 0 ∧
      ∀ x, ΔG (k j) (fb j) x = metricScalarAt (k j) x - 2 := fun j =>
    gauge_potential_poisson S (f (tj j)) (ψ (tj j)) (htjlt j)
      (hfeq (tj j) ⟨ht₀.1.le.trans (htjmem j).1, (htjmem j).2⟩)
  obtain ⟨-, -, hclose, hR⟩ := limit_metric_data (I := I) h k kInf hlam
    (fun j x v => hlo (tj j) (htjmem j) x v) hbddk hconv
  have hRc : ∀ r : SmoothRiemannianMetric I M, Continuous fun x => metricScalarAt r x :=
    fun r => (metricScalar_smooth r).continuous
  have hmeanInf : (∫ x, (metricScalarAt kInf x - 2) ∂riemannianVolumeMeasure I M kInf) = 0 := by
    have hlimI := tendsto_integral_of_quadClose (I := I) k kInf hclose
      (fun j x => metricScalarAt (k j) x - 2) (fun x => metricScalarAt kInf x - 2)
      (fun j => (hRc (k j)).sub continuous_const) ((hRc kInf).sub continuous_const)
      (fun ε hε => by
        obtain ⟨j₀, hj₀⟩ := hR ε hε
        exact ⟨j₀, fun j hj x => by rw [sub_sub_sub_cancel_right]; exact hj₀ j hj x⟩)
    have hzero : ∀ j, (∫ x, (metricScalarAt (k j) x - 2) ∂riemannianVolumeMeasure I M (k j)) = 0 :=
      fun j => by
        have h1 : (fun x => metricScalarAt (k j) x - 2) = fun x => ΔG (k j) (fb j) x := by
          funext x; rw [(hpois j).2 x]
        rw [h1]
        exact integral_divergence_eq_zero_of_compact (I := I) (k j) (gradG (I := I) (k j) (fb j))
    simp only [hzero] at hlimI
    exact tendsto_nhds_unique hlimI tendsto_const_nhds
  obtain ⟨fInf, hfInf, -⟩ :=
    DifferentialGeometry.Analysis.Laplacian.existsUnique_meanZero_smooth_poisson
      kInf ⟨fun x => metricScalarAt kInf x - 2, (metricScalar_smooth kInf).sub contMDiff_const⟩
      hmeanInf
  have hMlim : Tendsto (fun j => ∫ x, normSq0S (k j) x 2 (tracelessHessAt (k j) (fb j) x)
      ∂riemannianVolumeMeasure I M (k j)) atTop (𝓝 0) := by
    have hvol : ∀ j, (riemannianVolumeMeasure I M (k j)).real Set.univ =
        totalScalarCurvature h / 2 := by
      intro j
      rw [hk, riemannianVolumeMeasure_pullback, measureReal_def,
        Measure.map_apply (ψ (tj j)).symm.continuous.measurable MeasurableSet.univ,
        Set.preimage_univ, ← measureReal_def, normalizedFlowMetric_eq S (htjlt j)]
      exact surfaceFlow_normalized_area hT S hS hdim hscal
        ⟨ht₀.1.le.trans (htjmem j).1, (htjmem j).2⟩
    have hfmc : ∀ r : SmoothRiemannianMetric I M,
        IsFiniteMeasureOnCompacts (riemannianVolumeMeasure I M r) :=
      fun r => riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) r
    have hup : ∀ j, (∫ x, normSq0S (k j) x 2 (tracelessHessAt (k j) (fb j) x)
        ∂riemannianVolumeMeasure I M (k j)) ≤
        4 * max C₀ 0 * (Tst - tj j) ^ γ₀ * (totalScalarCurvature h / 2) := by
      intro j
      calc (∫ x, normSq0S (k j) x 2 (tracelessHessAt (k j) (fb j) x)
            ∂riemannianVolumeMeasure I M (k j))
          ≤ ∫ _x, (4 * max C₀ 0 * (Tst - tj j) ^ γ₀) ∂riemannianVolumeMeasure I M (k j) := by
            refine integral_mono ((tracelessHess_normSq_continuous hdim (k j)
              (fb j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
              (integrable_const _) fun x => ?_
            exact gauge_tracelessHess_normSq_le S (f (tj j)) (Mf (tj j))
              (hM (tj j) ⟨ht₀.1.trans_le (htjmem j).1, (htjmem j).2⟩) (ψ (tj j)) (htjlt j)
              (hdec0 (tj j) (htjmem j)) x
        _ = _ := by rw [integral_const, smul_eq_mul, hvol j]; ring
    have hlo0 : ∀ j, 0 ≤ ∫ x, normSq0S (k j) x 2 (tracelessHessAt (k j) (fb j) x)
        ∂riemannianVolumeMeasure I M (k j) :=
      fun j => integral_nonneg fun x => normSq0S_nonneg (I := I) _ _ _ _
    have hlim := ((hτlim γ₀ hγ₀).const_mul (4 * max C₀ 0)).mul_const (totalScalarCurvature h / 2)
    rw [mul_zero, zero_mul] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo0 hup
  have hfInf' : (∫ x, fInf x ∂riemannianVolumeMeasure I M kInf) = 0 ∧
      ∀ x, ΔG kInf fInf x = metricScalarAt kInf x - 2 := ⟨hfInf.1, fun x => hfInf.2 x⟩
  have hMinf := tracelessHess_eq_zero_of_limit hdim h k kInf hlam
    (fun j x v => hlo (tj j) (htjmem j) x v) hbddk hconv fb fInf hpois hfInf' hMlim
  obtain ⟨x₀⟩ := hM0
  have hRk : ∀ j, c ≤ metricScalarAt (k j) x₀ := by
    intro j
    rw [hk, metricScalarAt_pullback, normalizedFlowMetric_eq S (htjlt j),
      Curvature.metricScalarAt_scaleMetric]
    have h1 := hlow (tj j) ⟨ht₀.1.le.trans (htjmem j).1, (htjmem j).2⟩ (ψ (tj j) x₀)
    have hτ : 0 < Tst - tj j := sub_pos.2 (htjlt j)
    rw [one_div, inv_inv]
    change c ≤ 2 * (Tst - tj j) * S.scalar (tj j) (ψ (tj j) x₀)
    calc c ≤ S.scalar (tj j) (ψ (tj j) x₀) * (2 * (Tst - tj j)) := h1
      _ = 2 * (Tst - tj j) * S.scalar (tj j) (ψ (tj j) x₀) := by ring
  obtain ⟨j₀, hj₀⟩ := hR (c / 2) (by positivity)
  have hpos : metricScalarAt kInf x₀ ≠ 0 := by
    have h1 := hj₀ j₀ le_rfl x₀
    have h2 := hRk j₀
    have h3 := (abs_le.1 h1).2
    intro h0
    linarith
  exact scalar_eq_two_of_tracelessHess_eq_zero hdim kInf fInf hfInf'.2 hMinf ⟨x₀, hpos⟩

theorem surfaceFlow_gauge_limit_round (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (hTeq : T = flowExtinctionTime S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hfeq : ∀ t ∈ Ico 0 T, (∫ x, f t x ∂riemannianVolumeMeasure I M (S.family.metric t)) = 0 ∧
      ∀ x, ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T)
    (hdecay : ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + q) *
          normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
        C * (flowExtinctionTime S - t) ^ γ)
    (ψ : ℝ → (M ≃ₘ⟮I, I⟯ M)) (hψ0 : ∀ x, ψ t₀ x = x)
    (hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ψ q.1 q.2) (Ioo t₀ T ×ˢ univ))
    (hψc : ∀ x, ContinuousWithinAt (fun s => ψ s x) (Ici t₀) t₀)
    (hψd : ∀ t ∈ Ioo t₀ T, ∀ x (v w : TangentSpace I x),
        HasDerivAt (fun s => 1 / (2 * (flowExtinctionTime S - s)) *
            (Diffeomorph.pullbackMetric (S.family.metric s) (ψ s)).inner x v w)
          (1 / (flowExtinctionTime S - t) *
            tracelessHessAt (S.family.metric t) (f t) (ψ t x)
              (vec2 (mfderiv I I (ψ t) x v) (mfderiv I I (ψ t) x w))) t)
    {c : ℝ} (hc : 0 < c)
    (hlow : ∀ t ∈ Ico 0 T, ∀ x, c ≤ S.scalar t x * (2 * (flowExtinctionTime S - t))) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
      (∀ t ∈ Ico t₀ T, ∀ x (v : TangentSpace I x), lam * (S.family.metric 0).inner x v v ≤
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)).inner x v v) ∧
      (∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ T, ∀ x, metricCovDerivNorm q
        (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) (S.family.metric 0) x ≤ B) ∧
      (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ T, ∀ q ≤ N, ∀ x,
        metricDerivNorm q (Diffeomorph.pullbackMetric (normalizedFlowMetric S t) (ψ t)) kInf
          (S.family.metric 0) x ≤ B * (flowExtinctionTime S - t) ^ β) ∧
      ∀ x, metricScalarAt kInf x = 2 := by
  refine (fun (_ : ∀ x, ψ t₀ x = x) (_ : ∀ x, ContinuousWithinAt (fun s => ψ s x) (Ici t₀) t₀)
    (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
      (Ioo 0 T ×ˢ univ)) => ?_) hψ0 hψc hf
  obtain ⟨lam, hlam, kInf, hlo, -, hbd, hrate⟩ :=
    gauge_limit_bounds S hS hTeq f Mf hM ht₀ hdecay ψ hψ hψd
  obtain ⟨C₀, γ₀, hγ₀, hC₀⟩ := hdecay 0
  have hR := gauge_limit_round_scalar hdim S hS hscal hTeq f hfeq Mf hM ht₀ hγ₀ hC₀ ψ hc hlow
    hlam kInf hlo hbd hrate
  refine ⟨lam, hlam, kInf, hlo, fun q => ?_, hrate, hR⟩
  obtain ⟨B, -, hB⟩ := hbd q
  exact ⟨B, hB⟩

end GC.Geometry
