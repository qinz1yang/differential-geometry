import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartSobolev
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakGradientClosed
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [T2Space M] [I.Boundaryless]

private lemma chart_norm_sub_le_errors {u : M → ℝ} {f : ℕ → M → ℝ}
    (hu : Chart.MemWkpChart (I := I) 1 2 u)
    (hf : ∀ n, ContMDiff I 𝓘(ℝ) ∞ (f n)) (n m : ℕ) :
    Chart.wkpNormChart (I := I) 1 2 (fun x => f n x - f m x) ≤
      Chart.wkpNormChart (I := I) 1 2 (fun x => u x - f n x) +
      Chart.wkpNormChart (I := I) 1 2 (fun x => u x - f m x) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hfn := Equivalence.MemWkpChart_of_contMDiff hp (hf n)
  have hfm := Equivalence.MemWkpChart_of_contMDiff hp (hf m)
  have hen := Chart.MemWkpChart_sub hp hu hfn
  have hem := Chart.MemWkpChart_sub hp hu hfm
  have hdecomp : (fun x => f n x - f m x) =
      fun x => -(u x - f n x) + (u x - f m x) := by funext x; ring
  rw [hdecomp]
  refine (Chart.wkpNormChart_add_le hp (Chart.MemWkpChart_neg hp hen) hem).trans ?_
  have hneg := Chart.wkpNormChart_const_smul hp (-1) hen
  simpa only [neg_one_mul, enorm_neg, enorm_one, one_mul] using
    (congrArg (fun a => a + Chart.wkpNormChart (I := I) 1 2 (fun x => u x - f m x)) hneg).le


theorem HasWeakRiemannianGradLp.exists_smooth_metricL2_approx
    [NeZero (Module.finrank ℝ E)] {g : SmoothRiemannianMetric I M}
    {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : MemLp u 2 (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g)) :
    ∃ f : ℕ → M → ℝ, (∀ n, ContMDiff I 𝓘(ℝ) ∞ (f n)) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2
        (riemannianVolumeMeasure I M g)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂riemannianVolumeMeasure I M g,
        Tendsto (fun n => gradFun g (f n) x) atTop (𝓝 (G x))) ∧
      Tendsto (fun n => eLpNorm (fun x => Real.sqrt
        (g.inner x (gradFun g (f n) x - G x) (gradFun g (f n) x - G x))) 2
        (riemannianVolumeMeasure I M g)) atTop (𝓝 0) := by
  classical
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let u₀ : M → ℝ := hu.aestronglyMeasurable.mk u
  have huu₀ : u =ᵐ[μ] u₀ := hu.aestronglyMeasurable.ae_eq_mk
  have hu₀ : MemLp u₀ 2 μ := hu.ae_eq huu₀
  have hu₀meas : Measurable u₀ := hu.aestronglyMeasurable.measurable_mk
  have hG₀ : HasWeakRiemannianGradLp g u₀ G := hG.congr_fun_ae huu₀
  have hu₀W : MemW1pIntrinsicLp g 2 u₀ := ⟨hu₀, G, hG₀, hGn⟩
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hu₀chart := hu₀W.memWkpChart hp
  let δ : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞)⁻¹ ^ n
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hδmono : Antitone δ := fun _ _ h =>
    pow_le_pow_of_le_one (by positivity) (by norm_num) h
  have hex (n : ℕ) : ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v ∧
      Chart.wkpNormChart (I := I) 1 2 (fun x => u₀ x - v x) ≤ δ n := by
    obtain ⟨v, hv, hbound⟩ := Chart.contMDiff_dense_in_WkpChart hp hp_top hu₀chart
      (show 0 < (2 : ℝ)⁻¹ ^ n by positivity)
    refine ⟨v, hv, ?_⟩
    simpa only [δ, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat] using hbound
  choose f hf herr using hex
  have hfn (n : ℕ) : MemLp (f n) 2 μ :=
    (MemW1pIntrinsicLp_of_contMDiff g 2 (hf n)).1
  obtain ⟨C₀, _hC₀, hscalarBound⟩ :=
    Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform g hp hp_top
  have hscalar : Tendsto (fun n => eLpNorm (fun x => f n x - u₀ x) 2 μ) atTop (𝓝 0) := by
    have hboundlim : Tendsto (fun n => ENNReal.ofReal C₀ * δ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hδlim (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim (fun _ => bot_le)
    intro n
    change eLpNorm (fun x => f n x - u₀ x) 2 μ ≤ ENNReal.ofReal C₀ * δ n
    have heq : eLpNorm (fun x => f n x - u₀ x) 2 μ =
        eLpNorm (fun x => u₀ x - f n x) 2 μ := eLpNorm_sub_comm (f n) u₀ 2 μ
    rw [heq]
    exact (hscalarBound (hu₀meas.sub (hf n).continuous.measurable)).trans (by
      gcongr
      exact herr n)
  let V (n : ℕ) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG g ⟨f n, hf n⟩
  have hV (n : ℕ) (x : M) : V n x = gradFun g (f n) x := grad_g_apply g ⟨f n, hf n⟩ x
  have hsub (n m : ℕ) (x : M) :
      V n x - V m x = gradFun g (fun y => f n y - f m y) x := by
    rw [hV, hV]
    exact (Geometry.Connection.gradFun_sub g
      ((hf n).mdifferentiable (by simp) x) ((hf m).mdifferentiable (by simp) x)).symm
  let d (n m : ℕ) : ℝ≥0∞ := eLpNorm (fun x => Real.sqrt
    (g.inner x (V n x - V m x) (V n x - V m x))) 2 μ
  obtain ⟨C, _hC, hgradientBound⟩ :=
    Equivalence.eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform g hp hp_top
  have hdbound (n m : ℕ) : d n m ≤ ENNReal.ofReal C * (δ n + δ m) := by
    dsimp only [d]
    simp_rw [hsub]
    exact (hgradientBound ((hf n).sub (hf m))).trans (by
      gcongr
      exact (chart_norm_sub_le_errors hu₀chart hf n m).trans (add_le_add (herr n) (herr m)))
  have hdmeas (n m : ℕ) : AEStronglyMeasurable (fun x => Real.sqrt
      (g.inner x (V n x - V m x) (V n x - V m x))) μ := by
    simp_rw [hsub]
    exact (Equivalence.continuous_g_norm_gradFun g ((hf n).sub (hf m))).aestronglyMeasurable
  let r : ℕ → ℝ≥0∞ := fun n => (ENNReal.ofReal C * 2) * δ n
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hδlim
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)))
  have hstep (n : ℕ) : d (n + 1) n ≤ r n := by
    calc
      d (n + 1) n ≤ ENNReal.ofReal C * (δ (n + 1) + δ n) := hdbound _ _
      _ ≤ ENNReal.ofReal C * (δ n + δ n) := by gcongr; exact hδmono (Nat.le_succ n)
      _ = r n := by dsimp only [r]; rw [← two_mul, mul_assoc]
  have hsum : (∑' n, d (n + 1) n) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hstep)
    dsimp only [r, δ]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)) (by norm_num)
  have htail (n : ℕ) : ∀ᶠ m in atTop, d n m ≤ r n := by
    filter_upwards [eventually_ge_atTop n] with m hm
    calc
      d n m ≤ ENNReal.ofReal C * (δ n + δ m) := hdbound _ _
      _ ≤ ENNReal.ofReal C * (δ n + δ n) := by gcongr; exact hδmono hm
      _ = r n := by dsimp only [r]; rw [← two_mul, mul_assoc]
  obtain ⟨G', hpoint, hmetric⟩ := exists_metricL2_limit_of_summable_steps g (fun n x => V n x)
    hdmeas hsum hr htail
  have hweak (n : ℕ) : HasWeakRiemannianGradLp g (f n) (fun x => V n x) := by
    simpa only [hV] using Equivalence.hasWeakRiemannianGradLp_gradFun g (hf n)
  have hG' : HasWeakRiemannianGradLp g u₀ G' :=
    HasWeakRiemannianGradLp.of_metricL2_limit V hfn hu₀ hweak hpoint hscalar hmetric
  have hG'n := memLp_metric_norm_of_smooth_limit g V hpoint hmetric
  have heq : G' =ᵐ[μ] G := hG'.ae_eq hG₀
    (hG'n.mono_exponent hp) (hGn.mono_exponent hp)
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · convert hscalar using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [huu₀] with x hx
    rw [hx]
  · filter_upwards [hpoint, heq] with x hx heqx
    simpa only [hV, heqx] using hx
  · convert hmetric using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [heq] with x hx
    rw [hV, hx]

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
