import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleContinuousComposition
import DifferentialGeometry.Analysis.Integration.Lp.BoundedConvergence
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTameComposition

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff BigOperators Topology ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem tendstoInMeasure_scalar_composition_of_order
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    {σ : ℝ} (hσ : σ = (k : ℝ) + 1)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u : ℕ → Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (u0 : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (v : ℕ → Ω → TensorHs g 0 0 σ)
    (v0 : Ω → TensorHs g 0 0 σ)
    (hu : TendstoInMeasure μ u atTop u0)
    (hv : ∀ n, AEStronglyMeasurable (v n) μ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    TendstoInMeasure μ v atTop v0 := by
  subst σ
  intro J P hRange hEval hEval0
  apply (exists_seq_tendstoInMeasure_atTop_iff hv).mpr
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hu.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hlim, hRange, hEval0, ae_all_iff.mpr hEval] with t ht hRt hEt hEnt
  exact tendsto_scalarHs_composition g k F hF hU
    (fun n => u (ns (ms n)) t) (u0 t)
    (fun n => v (ns (ms n)) t) (v0 t) ht hRt
    (Eventually.of_forall (fun n => hEnt (ns (ms n)))) hEt

theorem tendstoInMeasure_scalarHs_composition
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u : ℕ → Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (u0 : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (v : ℕ → Ω → TensorHs g 0 0 ((k : ℝ) + 1))
    (v0 : Ω → TensorHs g 0 0 ((k : ℝ) + 1))
    (hu : TendstoInMeasure μ u atTop u0)
    (hv : ∀ n, AEStronglyMeasurable (v n) μ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    TendstoInMeasure μ v atTop v0 := by
  exact tendstoInMeasure_scalar_composition_of_order μ g k rfl F hF hU u u0 v v0 hu hv

private theorem tendsto_lp_scalarHs_composition_seq_of_lower_order_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (⊤ : ℝ≥0∞))
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    (u : ℕ → Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (u0 : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (v : ℕ → Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (v0 : Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (hu : Tendsto u atTop (𝓝 u0)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ n, ∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u n t))) ⊆ K) →
    (∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, (∑ i, ‖L (u n t i)‖) ≤ R) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    Tendsto v atTop (𝓝 v0) := by
  intro J P L hRange hRange0 hBound hEval hEval0
  have hv : TendstoInMeasure μ (fun n => v n) atTop v0 := by
    exact tendstoInMeasure_scalar_composition_of_order μ g (k + 1)
      (by push_cast; ring : (k : ℝ) + 2 = ((k + 1 : ℕ) : ℝ) + 1)
      F hF hU (fun n => u n) u0 (fun n => v n) v0
      (tendstoInMeasure_of_tendsto_Lp hu) (fun n => Lp.aestronglyMeasurable (v n))
      hRange0 hEval hEval0
  obtain ⟨C, hC, hc⟩ := exists_scalarHs_composition_bound_of_lower_order_bound
    g k F hF hU hK hKU R
  let E := PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))
  let c : ℝ := Fintype.card ι
  let one : Lp ℝ p μ := (memLp_const (1 : ℝ)).toLp (fun _ : Ω => 1)
  let q : Lp E p μ → Lp ℝ p μ := lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : E)‖ = 0)
  let B : Lp E p μ → Lp ℝ p μ := fun w => C • (one + c • q w)
  have hq : Continuous q := lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : E)‖ = 0)
  have hB : Continuous B := (continuous_const.add (hq.const_smul c)).const_smul C
  have hBeval (w : Lp E p μ) : ∀ᵐ t ∂μ, B w t = C * (1 + c * ‖w t‖) := by
    filter_upwards [Lp.coeFn_smul C (one + c • q w), Lp.coeFn_add one (c • q w),
      (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) p μ).coeFn_toLp,
      Lp.coeFn_smul c (q w),
      lipschitzWith_one_norm.coeFn_compLp (norm_zero : ‖(0 : E)‖ = 0) w] with t h₁ h₂ h₃ h₄ h₅
    change (C • (one + c • q w)) t = _
    change one t = 1 at h₃
    change q w t = ‖w t‖ at h₅
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h₁ h₂ h₄
    rw [h₁, h₂, h₄, h₃, h₅]
  apply Lp.tendsto_of_tendstoInMeasure_of_ae_norm_le hp v v0
    (fun n => B (u n)) (B u0) (hB.tendsto u0 |>.comp hu) _ hv
  intro n
  filter_upwards [hRange n, hBound n, hEval n, hBeval (u n)] with t hRt hBt hEt hBwt
  obtain ⟨z, hz, hze⟩ := hc (u n t) hRt hBt
  have heq : v n t = z := by
    apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    apply scalarH1ToContinuous_injective g
    exact ContinuousMap.ext (fun x => (hEt x).trans (hze x).symm)
  have hsum : (∑ i, ‖u n t i‖) ≤ c * ‖u n t‖ := by
    calc
      _ ≤ ∑ _i : ι, ‖u n t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le (u n t) i)
      _ = _ := by simp [c]
  rw [heq, hBwt, Real.norm_eq_abs, abs_of_nonneg]
  · exact hz.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC)
  · exact mul_nonneg hC (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem tendsto_lp_scalarHs_composition_of_lower_order_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (⊤ : ℝ≥0∞))
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ)
    {X : Type*} {l : Filter X}
    (u : X → Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (u0 : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) p μ)
    (v : X → Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (v0 : Lp (TensorHs g 0 0 ((k : ℝ) + 2)) p μ)
    (hu : Tendsto u l (𝓝 u0)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let L := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    (∀ n, ∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u n t))) ⊆ K) →
    (∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u0 t))) ⊆ U) →
    (∀ n, ∀ᵐ t ∂μ, (∑ i, ‖L (u n t i)‖) ≤ R) →
    (∀ n, ∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v n t)) x =
      F (scalarH1PiToContinuous g (P (u n t)) x)) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (J (v0 t)) x =
      F (scalarH1PiToContinuous g (P (u0 t)) x)) →
    Tendsto v l (𝓝 v0) := by
  intro J P L hRange hRange0 hBound hEval hEval0
  have hv : Tendsto v (Filter.comap u (𝓝 u0)) (𝓝 v0) := by
    apply Filter.tendsto_of_seq_tendsto
    intro ns hns
    exact tendsto_lp_scalarHs_composition_seq_of_lower_order_bound μ hp g k F hF hU hK hKU R
      (fun n => u (ns n)) u0 (fun n => v (ns n)) v0
      (tendsto_comap_iff.mp hns) (fun n => hRange (ns n)) hRange0
      (fun n => hBound (ns n)) (fun n => hEval (ns n)) hEval0
  exact hv.mono_left hu.le_comap

end AddCircle
