import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Analysis.Integration.Holder.Weighted
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Integral.MeanInequalities
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Manifold MeasureTheory Set Filter Bundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Integral
section ScalarHolder

variable {α ι : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

private theorem holder_integral_prod_rpow_le_prod_integral_rpow_local
    (t : Finset ι) (f : ι → α → ℝ) (θ : ι → ℝ)
    (hf_int : ∀ i ∈ t, MeasureTheory.Integrable (f i) μ)
    (hf_nn : ∀ i ∈ t, 0 ≤ᵐ[μ] f i)
    (hθ : ∀ i ∈ t, 0 ≤ θ i) (hθ1 : ∑ i ∈ t, θ i = 1) :
    ∫ x, ∏ i ∈ t, f i x ^ θ i ∂μ ≤ ∏ i ∈ t, (∫ x, f i x ∂μ) ^ θ i := by
  classical
  have hae : ∀ᵐ x ∂μ, ∀ i ∈ t, 0 ≤ f i x :=
    (Filter.eventually_all_finset t).mpr fun i hi => hf_nn i hi
  have hmeas : ∀ i ∈ t, AEMeasurable (f i) μ := fun i hi => (hf_int i hi).aemeasurable
  have hF_meas : AEMeasurable (fun x => ∏ i ∈ t, f i x ^ θ i) μ :=
    Finset.aemeasurable_fun_prod t fun i hi => (hmeas i hi).pow_const (θ i)
  have hF_nn : 0 ≤ᵐ[μ] fun x => ∏ i ∈ t, f i x ^ θ i := by
    filter_upwards [hae] with x hx
    exact Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hx i hi) (θ i)
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hF_nn hF_meas.aestronglyMeasurable]
  have hoR : ∀ i ∈ t, AEMeasurable (fun x => ENNReal.ofReal (f i x)) μ :=
    fun i hi => ENNReal.measurable_ofReal.comp_aemeasurable (hmeas i hi)
  have hlin := ENNReal.lintegral_prod_norm_pow_le t hoR hθ1 hθ
  have hcongr : (∫⁻ x, ENNReal.ofReal (∏ i ∈ t, f i x ^ θ i) ∂μ) =
      ∫⁻ x, ∏ i ∈ t, ENNReal.ofReal (f i x) ^ θ i ∂μ := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [ENNReal.ofReal_prod_of_nonneg fun i hi => Real.rpow_nonneg (hx i hi) (θ i)]
    exact Finset.prod_congr rfl fun i hi =>
      (ENNReal.ofReal_rpow_of_nonneg (hx i hi) (hθ i hi)).symm
  have hfin : ∀ i ∈ t, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ≠ ⊤ :=
    fun i hi => (hf_int i hi).lintegral_lt_top.ne
  have hRfin : (∏ i ∈ t, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ^ θ i) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun i hi =>
      ENNReal.rpow_lt_top_of_nonneg (hθ i hi) (hfin i hi)).ne
  calc (∫⁻ x, ENNReal.ofReal (∏ i ∈ t, f i x ^ θ i) ∂μ).toReal
      ≤ (∏ i ∈ t, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ^ θ i).toReal := by
        refine ENNReal.toReal_mono hRfin ?_
        rw [hcongr]
        exact hlin
    _ = ∏ i ∈ t, (∫ x, f i x ∂μ) ^ θ i := by
        rw [ENNReal.toReal_prod]
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [← ENNReal.toReal_rpow,
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae (hf_nn i hi)
            (hf_int i hi).aestronglyMeasurable]

theorem lyapunov_pow_le (F : α → ℝ) (hF_nn : ∀ᵐ x ∂μ, 0 ≤ F x)
    {a b c lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hc : c = lam * a + (1 - lam) * b)
    (hFa : MeasureTheory.Integrable (fun x => F x ^ a) μ)
    (hFb : MeasureTheory.Integrable (fun x => F x ^ b) μ) :
    ∫ x, F x ^ c ∂μ ≤
      (∫ x, F x ^ a ∂μ) ^ lam * (∫ x, F x ^ b ∂μ) ^ (1 - lam) := by
  classical
  have hc_pos : 0 < c := by
    rcases eq_or_lt_of_le hlam0 with h | h
    · rw [hc, ← h]; simpa using hb
    · rcases eq_or_lt_of_le hlam1 with h' | h'
      · rw [hc, h']; simpa using ha
      · have h1 : 0 < lam * a := mul_pos h ha
        have h2 : 0 < (1 - lam) * b := mul_pos (by linarith) hb
        rw [hc]; linarith
  set f : Fin 2 → α → ℝ := ![fun x => F x ^ a, fun x => F x ^ b] with hf
  set θ : Fin 2 → ℝ := ![lam, 1 - lam] with hθ
  have hθ1 : ∑ i ∈ (Finset.univ : Finset (Fin 2)), θ i = 1 := by
    rw [Fin.sum_univ_two, hθ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hθ_nn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ θ i := by
    intro i _
    fin_cases i
    · simpa [hθ] using hlam0
    · simpa [hθ] using (by linarith : (0 : ℝ) ≤ 1 - lam)
  have hf_int : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      MeasureTheory.Integrable (f i) μ := by
    intro i _
    fin_cases i
    · simpa [hf] using hFa
    · simpa [hf] using hFb
  have hf_nn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), (0 : α → ℝ) ≤ᵐ[μ] f i := by
    intro i _
    fin_cases i
    · filter_upwards [hF_nn] with x hx
      simpa [hf] using Real.rpow_nonneg hx a
    · filter_upwards [hF_nn] with x hx
      simpa [hf] using Real.rpow_nonneg hx b
  have key := holder_integral_prod_rpow_le_prod_integral_rpow
    (Finset.univ : Finset (Fin 2)) f θ hf_int hf_nn hθ_nn hθ1
  have hpt : ∀ᵐ x ∂μ,
      F x ^ c = ∏ i ∈ (Finset.univ : Finset (Fin 2)), f i x ^ θ i := by
    filter_upwards [hF_nn] with x hx
    rw [Fin.prod_univ_two, hf, hθ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Real.rpow_mul hx, ← Real.rpow_mul hx,
      ← Real.rpow_add' hx (by
        rw [show a * lam + b * (1 - lam) = c by rw [hc]; ring]
        exact ne_of_gt hc_pos), hc]
    ring_nf
  rw [MeasureTheory.integral_congr_ae hpt]
  refine key.trans (le_of_eq ?_)
  rw [Fin.prod_univ_two, hf, hθ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

end ScalarHolder

namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem holder_integral_prod_riemannianFiberNormSq_le
    (g : SmoothRiemannianMetric I M) {ι : Type*} (t : Finset ι)
    (r s : ι → ℕ) (S : ∀ m, SmoothCcTensor g (r m) (s m)) (θ : ι → ℝ)
    (hθ : ∀ m ∈ t, 0 < θ m) (hθ1 : ∑ m ∈ t, θ m = 1) :
    (∫ x, ∏ m ∈ t,
        riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∏ m ∈ t,
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
            ^ (1 / θ m)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ θ m := by
  classical
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hcont : ∀ m : ι, Continuous (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)) := by
    intro m
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) (S m)
    refine hc.congr fun x => ?_
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g (r m) (s m) x
        ((S m).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) (S m) x]
  have hnn : ∀ (m : ι) (x : M), 0 ≤
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) :=
    fun m x => riemannianFiberNormSq_nonneg (I := I) (M := M) g (r m) (s m) x _
  have hF_cont : ∀ m ∈ t, Continuous (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
        ^ (1 / θ m)) :=
    fun m hm => (hcont m).rpow_const fun _ => Or.inr (one_div_nonneg.mpr (hθ m hm).le)
  have hF_int : ∀ m ∈ t, MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
        ^ (1 / θ m)) μ :=
    fun m hm => ((hF_cont m hm).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl
  have hF_nn : ∀ m ∈ t, (0 : M → ℝ) ≤ᵐ[μ] fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
        ^ (1 / θ m) :=
    fun m _ => Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hnn m x) _
  have hpt : ∀ x : M, (∏ m ∈ t,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)) =
      ∏ m ∈ t,
        (riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
          ^ (1 / θ m)) ^ θ m := by
    intro x
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [← Real.rpow_mul (hnn m x), one_div_mul_cancel (hθ m hm).ne', Real.rpow_one]
  calc (∫ x, ∏ m ∈ t,
        riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) ∂μ)
      = ∫ x, ∏ m ∈ t,
          (riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
            ^ (1 / θ m)) ^ θ m ∂μ :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ ≤ ∏ m ∈ t,
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
              ^ (1 / θ m) ∂μ) ^ θ m :=
        holder_integral_prod_rpow_le_prod_integral_rpow t
          (fun m x =>
            riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
              ^ (1 / θ m))
          θ hF_int hF_nn (fun m hm => (hθ m hm).le) hθ1

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound
    (g : SmoothRiemannianMetric I M) {ι : Type*} [DecidableEq ι]
    (t t₀ : Finset ι) (ht₀ : t₀ ⊆ t)
    (r s : ι → ℕ) (S : ∀ m, SmoothCcTensor g (r m) (s m))
    (Λ : ι → ℝ) (hΛ_nn : ∀ m ∈ t₀, 0 ≤ Λ m)
    (hΛ : ∀ m ∈ t₀, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) ≤ Λ m)
    (θ : ι → ℝ) (hθ : ∀ m ∈ t \ t₀, 0 < θ m) (hθ1 : ∑ m ∈ t \ t₀, θ m = 1) :
    (∫ x, ∏ m ∈ t,
        riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      (∏ m ∈ t₀, Λ m) *
        ∏ m ∈ t \ t₀,
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
              ^ (1 / θ m)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ θ m := by
  classical
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hcont : ∀ m : ι, Continuous (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)) := by
    intro m
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) (S m)
    refine hc.congr fun x => ?_
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g (r m) (s m) x
        ((S m).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) (S m) x]
  have hnn : ∀ (m : ι) (x : M), 0 ≤
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) :=
    fun m x => riemannianFiberNormSq_nonneg (I := I) (M := M) g (r m) (s m) x _
  have hmaj_cont : Continuous (fun x : M => (∏ m ∈ t₀, Λ m) * ∏ m ∈ t \ t₀,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)) :=
    continuous_const.mul (continuous_finset_prod _ fun m _ => hcont m)
  have hmaj_int : MeasureTheory.Integrable (fun x : M => (∏ m ∈ t₀, Λ m) * ∏ m ∈ t \ t₀,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)) μ :=
    (hmaj_cont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl
  have hptw : ∀ x : M, (∏ m ∈ t,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)) ≤
      (∏ m ∈ t₀, Λ m) * ∏ m ∈ t \ t₀,
        riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) := by
    intro x
    rw [← Finset.prod_sdiff ht₀ (f := fun m =>
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)),
      mul_comm (∏ m ∈ t₀, Λ m)]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun m _ => hnn m x)
    exact Finset.prod_le_prod (fun m _ => hnn m x) fun m hm => hΛ m hm x
  have h1 : (∫ x, ∏ m ∈ t,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) ∂μ) ≤
      ∫ x, (∏ m ∈ t₀, Λ m) * ∏ m ∈ t \ t₀,
        riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) ∂μ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun m _ => hnn m x)
      hmaj_int (Filter.Eventually.of_forall hptw)
  refine h1.trans ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (holder_integral_prod_riemannianFiberNormSq_le (I := I) (M := M) g (t \ t₀) r s S θ hθ hθ1)
    (Finset.prod_nonneg hΛ_nn)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem holder_integral_prod_riemannianFiberNormSq_natWeight_le_of_sup_bound
    (g : SmoothRiemannianMetric I M) {ι : Type*} (t : Finset ι)
    (r s : ι → ℕ) (S : ∀ m, SmoothCcTensor g (r m) (s m))
    (e : ι → ℕ) (k : ℕ) (hk : 0 < k) (he : ∑ m ∈ t, e m = k)
    (Λ : ι → ℝ) (hΛ_nn : ∀ m ∈ t, e m = 0 → 0 ≤ Λ m)
    (hΛ : ∀ m ∈ t, e m = 0 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) ≤ Λ m) :
    (∫ x, ∏ m ∈ t,
        riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      (∏ m ∈ t.filter (fun m => e m = 0), Λ m) *
        ∏ m ∈ t.filter (fun m => 0 < e m),
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x)
              ^ ((k : ℝ) / (e m : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ ((e m : ℝ) / (k : ℝ)) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  set t₀ : Finset ι := t.filter (fun m => e m = 0) with ht₀_def
  have ht₀ : t₀ ⊆ t := Finset.filter_subset _ t
  have hsdiff : t \ t₀ = t.filter (fun m => 0 < e m) := by
    rw [ht₀_def, ← Finset.filter_not]
    exact Finset.filter_congr fun m _ => by simp [Nat.pos_iff_ne_zero]
  have hθ : ∀ m ∈ t \ t₀, 0 < (e m : ℝ) / (k : ℝ) := by
    intro m hm
    rw [hsdiff, Finset.mem_filter] at hm
    exact div_pos (Nat.cast_pos.mpr hm.2) hkR
  have hθ1 : ∑ m ∈ t \ t₀, (e m : ℝ) / (k : ℝ) = 1 := by
    rw [← Finset.sum_div]
    have hsum : ∑ m ∈ t \ t₀, (e m : ℝ) = ∑ m ∈ t, (e m : ℝ) := by
      refine Finset.sum_subset (Finset.sdiff_subset) fun m hm hnot => ?_
      have : m ∈ t₀ := by
        by_contra h0
        exact hnot (Finset.mem_sdiff.mpr ⟨hm, h0⟩)
      rw [ht₀_def, Finset.mem_filter] at this
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) this.2
    rw [hsum, ← Nat.cast_sum, he, div_self hkR.ne']
  have hΛ_nn' : ∀ m ∈ t₀, 0 ≤ Λ m := by
    intro m hm
    rw [ht₀_def, Finset.mem_filter] at hm
    exact hΛ_nn m hm.1 hm.2
  have hΛ' : ∀ m ∈ t₀, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (r m) (s m) x ((S m).toSection x) ≤ Λ m := by
    intro m hm
    rw [ht₀_def, Finset.mem_filter] at hm
    exact hΛ m hm.1 hm.2
  have hmain := holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound (I := I) (M := M)
    g t t₀ ht₀ r s S Λ hΛ_nn' hΛ' (fun m => (e m : ℝ) / (k : ℝ)) hθ hθ1
  refine hmain.trans (le_of_eq ?_)
  rw [hsdiff]
  refine congrArg _ (Finset.prod_congr rfl fun m hm => ?_)
  rw [one_div_div]

end Connection

namespace L2

alias holder_integral_prod_riemannianFiberNormSq_le :=
  Connection.holder_integral_prod_riemannianFiberNormSq_le
alias holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound :=
  Connection.holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound
alias holder_integral_prod_riemannianFiberNormSq_natWeight_le_of_sup_bound :=
  Connection.holder_integral_prod_riemannianFiberNormSq_natWeight_le_of_sup_bound

end L2
end Integral
end DifferentialGeometry

end
