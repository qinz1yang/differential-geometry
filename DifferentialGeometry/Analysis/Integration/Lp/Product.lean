import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} [SFinite ν]
variable {p : ℝ≥0∞}

section ENorm

variable {E : Type*} [ENorm E]

theorem eLpNorm_eLpNorm {f : A × B → E}
    (hp : p ≠ (⊤ : ℝ≥0∞))
    (hf : AEMeasurable (fun z => ‖f z‖ₑ) (μ.prod ν)) :
    eLpNorm (fun a => eLpNorm (fun b => f (a, b)) p ν) p μ =
      eLpNorm f p (μ.prod ν) := by
  by_cases hp₀ : p = 0
  · simp [hp₀]
  have hp' : p.toReal ≠ 0 := (ENNReal.toReal_pos hp₀ hp).ne'
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, enorm_eq_self,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp', ENNReal.rpow_one]
  rw [← lintegral_prod _ (hf.pow_const p.toReal)]

end ENorm

section ContinuousENorm

variable {E : Type*} [TopologicalSpace E] [ContinuousENorm E]

theorem MemLp.prodMk_left {f : A × B → E}
    (hf : MemLp f p (μ.prod ν)) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    ∀ᵐ a ∂μ, MemLp (fun b => f (a, b)) p ν := by
  by_cases hp₀ : p = 0
  · subst p
    filter_upwards [hf.aestronglyMeasurable.prodMk_left] with a ha
    exact ⟨ha, by simp⟩
  have hnorm := eLpNorm_eLpNorm hp hf.aestronglyMeasurable.enorm
  have hfinite : (∫⁻ a, (eLpNorm (fun b => f (a, b)) p ν) ^ p.toReal ∂μ) < ⊤ := by
    apply (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr (ENNReal.toReal_pos hp₀ hp))).mp
    simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, enorm_eq_self] using
      (hnorm.trans_lt hf.2)
  have hmeas : AEMeasurable (fun a => (eLpNorm (fun b => f (a, b)) p ν) ^ p.toReal) μ := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, ← ENNReal.rpow_mul,
      one_div, inv_mul_cancel₀ (ENNReal.toReal_pos hp₀ hp).ne', ENNReal.rpow_one]
    exact (hf.aestronglyMeasurable.enorm.pow_const p.toReal).lintegral_prod_right'
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, ae_lt_top' hmeas hfinite.ne] with a ha₁ ha₂
  exact ⟨ha₁, (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp₀ hp)).mp ha₂⟩

theorem eLpNorm_eLpNorm_toReal {f : A × B → E}
    (hf : MemLp f p (μ.prod ν)) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (fun a => (eLpNorm (fun b => f (a, b)) p ν).toReal) p μ =
      eLpNorm f p (μ.prod ν) := by
  rw [← eLpNorm_eLpNorm hp hf.aestronglyMeasurable.enorm]
  apply eLpNorm_congr_enorm_ae
  filter_upwards [hf.prodMk_left hp] with a ha
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha.2.ne, enorm_eq_self]

theorem MemLp.eLpNorm_toReal {f : A × B → E}
    (hf : MemLp f p (μ.prod ν)) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    MemLp (fun a => (eLpNorm (fun b => f (a, b)) p ν).toReal) p μ := by
  by_cases hp₀ : p = 0
  · subst p
    simp only [eLpNorm_exponent_zero, ENNReal.toReal_zero]
    exact ⟨aestronglyMeasurable_const, by simp⟩
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]
    exact (((hf.aestronglyMeasurable.enorm.pow_const p.toReal).lintegral_prod_right').pow_const
      (1 / p.toReal)).ennreal_toReal
  · rw [eLpNorm_eLpNorm_toReal hf hp]
    exact hf.2

end ContinuousENorm

variable {E : Type*} [NormedAddCommGroup E]

theorem Lp.ext_curry {f g : Lp E p (μ.prod ν)}
    (h : ∀ᵐ a ∂μ, (fun b => f (a, b)) =ᵐ[ν] fun b => g (a, b)) : f = g := by
  apply Lp.ext
  exact (Measure.ae_prod_iff_ae_ae
    ((Lp.stronglyMeasurable f).measurableSet_eq_fun (Lp.stronglyMeasurable g))).mpr h

variable [Fact (1 ≤ p)]

private def uncurrySimple (f : SimpleFunc A (Lp E p ν)) : A × B → E :=
  fun z => f z.1 z.2

omit [SFinite ν] [Fact (1 ≤ p)] in
private theorem stronglyMeasurable_uncurrySimple (f : SimpleFunc A (Lp E p ν)) :
    StronglyMeasurable (uncurrySimple f) := by
  classical
  have h (v : Lp E p ν) : StronglyMeasurable
      ((Prod.fst ⁻¹' (f ⁻¹' {v})).indicator (fun z : A × B => v z.2)) :=
    ((Lp.stronglyMeasurable v).comp_measurable measurable_snd).indicator
      ((f.measurableSet_fiber v).preimage measurable_fst)
  convert Finset.stronglyMeasurable_sum f.range (fun v _ => h v) using 1
  funext z
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single (f z.1)]
  · simp only [Set.indicator_of_mem (show z ∈ Prod.fst ⁻¹' (f ⁻¹' {f z.1}) from rfl)]
    rfl
  · intro v _ hv
    exact Set.indicator_of_notMem
      (show z ∉ Prod.fst ⁻¹' (f ⁻¹' {v}) from fun h => hv (Eq.symm h)) _
  · intro hnot
    exact False.elim (hnot (f.mem_range_self z.1))

private theorem eLpNorm_uncurrySimple (f : SimpleFunc A (Lp E p ν))
    (hp : p ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (uncurrySimple f) p (μ.prod ν) = eLpNorm f p μ := by
  rw [← eLpNorm_eLpNorm hp (stronglyMeasurable_uncurrySimple f).enorm.aemeasurable]
  change eLpNorm (fun a => eLpNorm (f a) p ν) p μ = _
  simp_rw [← Lp.enorm_def]
  exact eLpNorm_enorm f

private theorem memLp_uncurrySimple {f : SimpleFunc A (Lp E p ν)}
    (hf : MemLp f p μ) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    MemLp (uncurrySimple f) p (μ.prod ν) := by
  refine ⟨(stronglyMeasurable_uncurrySimple f).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_uncurrySimple f hp]
  exact hf.2

private def uncurrySimpleLp (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (Lp E p ν) p μ) : Lp E p (μ.prod ν) :=
  (memLp_uncurrySimple (Lp.simpleFunc.memLp f) hp).toLp _

private theorem uncurrySimpleLp_coeFn (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (Lp E p ν) p μ) :
    ∀ᵐ a ∂μ, (fun b => uncurrySimpleLp hp f (a, b)) =ᵐ[ν]
      ((f : Lp (Lp E p ν) p μ) a : B → E) := by
  have h := Measure.ae_ae_of_ae_prod
    (MemLp.coeFn_toLp (memLp_uncurrySimple (Lp.simpleFunc.memLp f) hp))
  filter_upwards [h, Lp.simpleFunc.toSimpleFunc_eq_toFun f] with a ha₁ ha₂
  filter_upwards [ha₁] with b hb
  exact hb.trans (congrArg (fun v : Lp E p ν => v b) ha₂)

private theorem norm_uncurrySimpleLp (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (Lp E p ν) p μ) :
    ‖uncurrySimpleLp hp f‖ = ‖f‖ := by
  rw [uncurrySimpleLp, Lp.norm_toLp, eLpNorm_uncurrySimple _ hp]
  exact (Lp.simpleFunc.norm_toSimpleFunc f).symm

theorem Lp.exists_subseq_tendsto_eLpNorm_prodMk_left
    {f : ℕ → Lp E p (μ.prod ν)} {g : Lp E p (μ.prod ν)}
    (hp : p ≠ (⊤ : ℝ≥0∞)) (hfg : Tendsto f atTop (𝓝 g)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ a ∂μ,
      Tendsto (fun k => eLpNorm (fun b => f (s k) (a, b) - g (a, b)) p ν)
        atTop (𝓝 0) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  let ψ : ℕ → A → ℝ := fun k a =>
    (eLpNorm (fun b => f k (a, b) - g (a, b)) p ν).toReal
  have hmem (k : ℕ) : MemLp (fun z => f k z - g z) p (μ.prod ν) :=
    (Lp.memLp (f k)).sub (Lp.memLp g)
  have hψmem (k : ℕ) : MemLp (ψ k) p μ := (hmem k).eLpNorm_toReal hp
  have hψlim : Tendsto (fun k => eLpNorm (ψ k - 0) p μ) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).mp hfg
    apply h.congr'
    filter_upwards [] with k
    rw [sub_zero]
    exact (eLpNorm_eLpNorm_toReal (hmem k) hp).symm
  obtain ⟨s, hs, hslim⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp₀
    (fun k => (hψmem k).aestronglyMeasurable) aestronglyMeasurable_const hψlim).exists_seq_tendsto_ae
  refine ⟨s, hs, ?_⟩
  filter_upwards [hslim, ae_all_iff.mpr (fun k => (hmem k).prodMk_left hp)] with a ha hfinite
  exact (ENNReal.tendsto_toReal_zero_iff (fun k => (hfinite (s k)).2.ne)).mp ha

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

attribute [local instance] Lp.simpleFunc.module Lp.simpleFunc.normedSpace

private def uncurrySimpleLinear (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp.simpleFunc (Lp E p ν) p μ →ₗ[𝕜] Lp E p (μ.prod ν) where
  toFun := uncurrySimpleLp hp
  map_add' f g := by
    apply Lp.ext_curry
    filter_upwards [uncurrySimpleLp_coeFn hp (f + g), uncurrySimpleLp_coeFn hp f,
      uncurrySimpleLp_coeFn hp g,
      Lp.coeFn_add (f : Lp (Lp E p ν) p μ) (g : Lp (Lp E p ν) p μ),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_add (uncurrySimpleLp hp f) (uncurrySimpleLp hp g))]
      with a hfg hf hg ht hprod
    filter_upwards [hfg, hf, hg, hprod,
      Lp.coeFn_add ((f : Lp (Lp E p ν) p μ) a) ((g : Lp (Lp E p ν) p μ) a)]
      with b hfg' hf' hg' hprod' hab
    calc
      uncurrySimpleLp hp (f + g) (a, b) = ((f + g : Lp.simpleFunc (Lp E p ν) p μ) :
          Lp (Lp E p ν) p μ) a b := hfg'
      _ = (((f : Lp (Lp E p ν) p μ) a) + ((g : Lp (Lp E p ν) p μ) a)) b :=
        congrArg (fun v : Lp E p ν => v b) ht
      _ = (f : Lp (Lp E p ν) p μ) a b + (g : Lp (Lp E p ν) p μ) a b := hab
      _ = uncurrySimpleLp hp f (a, b) + uncurrySimpleLp hp g (a, b) := by rw [hf', hg']
      _ = (uncurrySimpleLp hp f + uncurrySimpleLp hp g) (a, b) := hprod'.symm
  map_smul' c f := by
    apply Lp.ext_curry
    filter_upwards [uncurrySimpleLp_coeFn hp (c • f), uncurrySimpleLp_coeFn hp f,
      Lp.coeFn_smul c (f : Lp (Lp E p ν) p μ),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c (uncurrySimpleLp hp f))]
      with a hcf hf ht hprod
    filter_upwards [hcf, hf, hprod, Lp.coeFn_smul c ((f : Lp (Lp E p ν) p μ) a)]
      with b hcf' hf' hprod' hcb
    calc
      uncurrySimpleLp hp (c • f) (a, b) = ((c • f : Lp.simpleFunc (Lp E p ν) p μ) :
          Lp (Lp E p ν) p μ) a b := hcf'
      _ = (c • ((f : Lp (Lp E p ν) p μ) a)) b := congrArg (fun v : Lp E p ν => v b) ht
      _ = c • (f : Lp (Lp E p ν) p μ) a b := hcb
      _ = c • uncurrySimpleLp hp f (a, b) := by rw [hf']
      _ = (c • uncurrySimpleLp hp f) (a, b) := hprod'.symm

private def uncurrySimpleIsometry (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp.simpleFunc (Lp E p ν) p μ →ₗᵢ[𝕜] Lp E p (μ.prod ν) where
  toLinearMap := uncurrySimpleLinear hp
  norm_map' := norm_uncurrySimpleLp hp

variable [CompleteSpace E]

private def uncurryLinear (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp (Lp E p ν) p μ →L[𝕜] Lp E p (μ.prod ν) :=
  (uncurrySimpleIsometry (𝕜 := 𝕜) hp).toContinuousLinearMap.extend
    (Lp.simpleFunc.coeToLp A (Lp E p ν) 𝕜)

private theorem uncurryLinear_simple (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (Lp E p ν) p μ) :
    uncurryLinear (𝕜 := 𝕜) hp (f : Lp (Lp E p ν) p μ) = uncurrySimpleLp hp f := by
  exact ContinuousLinearMap.extend_eq _ (Lp.simpleFunc.denseRange hp)
    Lp.simpleFunc.isUniformInducing f

variable (𝕜) in
def Lp.uncurry (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp (Lp E p ν) p μ →ₗᵢ[𝕜] Lp E p (μ.prod ν) where
  toLinearMap := (uncurryLinear hp).toLinearMap
  norm_map' f := by
    change ‖uncurryLinear (𝕜 := 𝕜) hp f‖ = ‖f‖
    refine (Lp.simpleFunc.denseRange (E := Lp E p ν) (μ := μ) hp).induction_on
      (p := fun v => ‖uncurryLinear (𝕜 := 𝕜) hp v‖ = ‖v‖) f ?_ ?_
    · exact isClosed_eq (uncurryLinear (𝕜 := 𝕜) hp).continuous.norm continuous_norm
    · intro s
      change ‖uncurryLinear (𝕜 := 𝕜) hp (s : Lp (Lp E p ν) p μ)‖ = _
      rw [uncurryLinear_simple hp]
      exact norm_uncurrySimpleLp hp s

private theorem uncurry_simple_coeFn (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (Lp E p ν) p μ) :
    ∀ᵐ a ∂μ, (fun b => Lp.uncurry 𝕜 hp (f : Lp (Lp E p ν) p μ) (a, b)) =ᵐ[ν]
      ((f : Lp (Lp E p ν) p μ) a : B → E) := by
  change ∀ᵐ a ∂μ, (fun b => uncurryLinear (𝕜 := 𝕜) hp
    (f : Lp (Lp E p ν) p μ) (a, b)) =ᵐ[ν] _
  rw [uncurryLinear_simple hp]
  exact uncurrySimpleLp_coeFn hp f

theorem Lp.uncurry_coeFn (hp : p ≠ (⊤ : ℝ≥0∞)) (f : Lp (Lp E p ν) p μ) :
    ∀ᵐ a ∂μ, (fun b => Lp.uncurry 𝕜 hp f (a, b)) =ᵐ[ν] (f a : B → E) := by
  classical
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    ((Lp.simpleFunc.denseRange (E := Lp E p ν) (μ := μ) hp) f)
  choose s hs using hv
  have hslim : Tendsto (fun k => (s k : Lp (Lp E p ν) p μ)) atTop (𝓝 f) := by
    simpa only [hs] using hvlim
  obtain ⟨σ, hσ, hσlim⟩ := (tendstoInMeasure_of_tendsto_Lp hslim).exists_seq_tendsto_ae
  have hprod : Tendsto (fun k => Lp.uncurry 𝕜 hp (s (σ k) : Lp (Lp E p ν) p μ))
      atTop (𝓝 (Lp.uncurry 𝕜 hp f)) :=
    (Lp.uncurry 𝕜 hp).continuous.continuousAt.tendsto.comp (hslim.comp hσ.tendsto_atTop)
  obtain ⟨τ, hτ, hτlim⟩ := Lp.exists_subseq_tendsto_eLpNorm_prodMk_left hp hprod
  have hslice := (Lp.memLp (Lp.uncurry 𝕜 hp f)).prodMk_left hp
  have heqs := ae_all_iff.mpr (fun k => uncurry_simple_coeFn (𝕜 := 𝕜) hp (s k))
  filter_upwards [hσlim, hτlim, hslice, heqs] with a ha₁ ha₂ ha₃ ha₄
  let w : Lp E p ν := ha₃.toLp (fun b => Lp.uncurry 𝕜 hp f (a, b))
  have hlim₁ : Tendsto (fun k => (s (σ (τ k)) : Lp (Lp E p ν) p μ) a) atTop (𝓝 (f a)) :=
    ha₁.comp hτ.tendsto_atTop
  have hlim₂ : Tendsto (fun k => (s (σ (τ k)) : Lp (Lp E p ν) p μ) a) atTop (𝓝 w) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ w).mpr
    apply ha₂.congr'
    filter_upwards [] with k
    apply eLpNorm_congr_ae
    filter_upwards [ha₄ (σ (τ k)), MemLp.coeFn_toLp ha₃] with b hb₁ hb₂
    simp only [Pi.sub_apply, hb₁, w, hb₂]
  have heq : f a = w := tendsto_nhds_unique hlim₁ hlim₂
  rw [heq]
  exact (MemLp.coeFn_toLp ha₃).symm

theorem Lp.uncurry_compLpL_coeFn {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hp : p ≠ ⊤) (L : F →L[𝕜] Lp E p ν) (f : Lp F p μ) :
    ∀ᵐ a ∂μ, (fun b => Lp.uncurry (μ := μ) (ν := ν) (E := E) 𝕜 hp (L.compLpL p μ f) (a, b)) =ᵐ[ν] (L (f a) : B → E) := by
  filter_upwards [Lp.uncurry_coeFn (μ := μ) (ν := ν) (E := E) (𝕜 := 𝕜) hp (L.compLpL p μ f), L.coeFn_compLpL f]
    with a ha₁ ha₂
  rw [ha₂] at ha₁
  exact ha₁

end MeasureTheory
