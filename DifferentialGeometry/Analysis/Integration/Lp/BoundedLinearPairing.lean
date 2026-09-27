import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul


noncomputable section

namespace MeasureTheory

open Filter
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable
  (clm_apply_of_apply_aestronglyMeasurable)
open scoped Topology

variable {X E F A : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrable_clm_apply_of_ae_norm_le
    (b : X → E →L[ℝ] F)
    (hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f : X → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ b x (f x)) μ := by
  have hmeas : AEStronglyMeasurable (fun x ↦ b x (f x)) μ :=
    clm_apply_of_apply_aestronglyMeasurable b hb f hf.aestronglyMeasurable
  refine (hf.norm.const_mul M).mono' hmeas ?_
  filter_upwards [hM] with x hx
  exact ((b x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

theorem norm_integral_clm_apply_sub_le
    (b : X → E →L[ℝ] F)
    (hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ‖(∫ x, b x (f x) ∂μ) - ∫ x, b x (g x) ∂μ‖ ≤
      M * ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← integral_sub (integrable_clm_apply_of_ae_norm_le b hb hM hf)
    (integrable_clm_apply_of_ae_norm_le b hb hM hg)]
  have heq : (fun x ↦ b x (f x) - b x (g x)) =
      fun x ↦ b x (f x - g x) := by
    funext x
    exact ((b x).map_sub (f x) (g x)).symm
  rw [heq]
  calc
    _ ≤ ∫ x, M * ‖f x - g x‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((hf.sub hg).norm.const_mul M)
      filter_upwards [hM] with x hx
      exact ((b x).le_opNorm (f x - g x)).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = M * ∫ x, ‖f x - g x‖ ∂μ := integral_const_mul _ _

theorem tendsto_integral_clm_apply_of_tendsto_integral_norm_sub
    {l : Filter A} (b : X → E →L[ℝ] F)
    (hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f : A → X → E} {g : X → E}
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : Integrable g μ)
    (hlim : Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, b x (f i x) ∂μ) l (𝓝 (∫ x, b x (g x) ∂μ)) := by
  have herr : Tendsto (fun i ↦ (∫ x, b x (f i x) ∂μ) - ∫ x, b x (g x) ∂μ)
      l (𝓝 0) := by
    apply squeeze_zero_norm'
      (hf.mono fun i hi ↦ norm_integral_clm_apply_sub_le b hb hM hi hg)
    simpa only [mul_zero] using hlim.const_mul M
  simpa only [sub_add_cancel, zero_add] using
    herr.add (tendsto_const_nhds (x := ∫ x, b x (g x) ∂μ))

theorem tendsto_integral_clm_apply_of_tendsto_l1
    {l : Filter A} (b : X → E →L[ℝ] F)
    (hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f : A → Lp E 1 μ} {g : Lp E 1 μ} (hlim : Tendsto f l (𝓝 g)) :
    Tendsto (fun i ↦ ∫ x, b x (f i x) ∂μ) l (𝓝 (∫ x, b x (g x) ∂μ)) := by
  apply tendsto_integral_clm_apply_of_tendsto_integral_norm_sub b hb hM
    (Eventually.of_forall fun i ↦ memLp_one_iff_integrable.mp (Lp.memLp (f i)))
    (memLp_one_iff_integrable.mp (Lp.memLp g))
  have hdist := hlim.dist (tendsto_const_nhds (x := g))
  simp only [dist_self] at hdist
  simp_rw [L1.dist_eq_integral_dist, dist_eq_norm] at hdist
  exact hdist

theorem tendsto_integral_mul_of_tendsto_integral_norm_sub
    {l : Filter A} (c : X → ℝ) (hc : AEStronglyMeasurable c μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖c x‖ ≤ M)
    {f : A → X → ℝ} {g : X → ℝ}
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : Integrable g μ)
    (hlim : Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, c x * f i x ∂μ) l (𝓝 (∫ x, c x * g x ∂μ)) := by
  let b : X → ℝ →L[ℝ] ℝ := fun x ↦ ContinuousLinearMap.lsmul ℝ ℝ (c x)
  have hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ := by
    intro v
    simpa only [b, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hc.mul_const v
  have hB : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := by
    filter_upwards [hM] with x hx
    exact (ContinuousLinearMap.opNorm_lsmul_apply_le (𝕜 := ℝ) (E := ℝ) (c x)).trans hx
  simpa only [b, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    tendsto_integral_clm_apply_of_tendsto_integral_norm_sub b hb hB hf hg hlim

theorem tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub
    {l : Filter A} (b : X → E →L[ℝ] ℝ) (c : X → ℝ)
    (hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ)
    (hc : AEStronglyMeasurable c μ)
    {M N : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (hN : ∀ᵐ x ∂μ, ‖c x‖ ≤ N)
    {u : A → X → E} {v : X → E} {f : A → X → ℝ} {g : X → ℝ}
    (hu : ∀ᶠ i in l, Integrable (u i) μ) (hv : Integrable v μ)
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : Integrable g μ)
    (hulim : Tendsto (fun i ↦ ∫ x, ‖u i x - v x‖ ∂μ) l (𝓝 0))
    (hflim : Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, b x (u i x) + c x * f i x ∂μ)
      l (𝓝 (∫ x, b x (v x) + c x * g x ∂μ)) := by
  have hsum :=
    (tendsto_integral_clm_apply_of_tendsto_integral_norm_sub b hb hM hu hv hulim).add
      (tendsto_integral_mul_of_tendsto_integral_norm_sub c hc hN hf hg hflim)
  rw [← integral_add (integrable_clm_apply_of_ae_norm_le b hb hM hv)
    (hg.bdd_mul hc hN)] at hsum
  refine hsum.congr' ?_
  filter_upwards [hu, hf] with i hui hfi
  exact (integral_add (integrable_clm_apply_of_ae_norm_le b hb hM hui)
    (hfi.bdd_mul hc hN)).symm

theorem integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub
    {l : Filter A} [NeBot l] (b : X → E →L[ℝ] ℝ) (c : X → ℝ)
    (hb : ∀ v, AEStronglyMeasurable (fun x ↦ b x v) μ)
    (hc : AEStronglyMeasurable c μ)
    {M N : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (hN : ∀ᵐ x ∂μ, ‖c x‖ ≤ N)
    {u : A → X → E} {v : X → E} {f : A → X → ℝ} {g : X → ℝ}
    (hu : ∀ᶠ i in l, Integrable (u i) μ) (hv : Integrable v μ)
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : Integrable g μ)
    (hulim : Tendsto (fun i ↦ ∫ x, ‖u i x - v x‖ ∂μ) l (𝓝 0))
    (hflim : Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0))
    (hnonneg : ∀ᶠ i in l, 0 ≤ ∫ x, b x (u i x) + c x * f i x ∂μ) :
    0 ≤ ∫ x, b x (v x) + c x * g x ∂μ := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub
      b c hb hc hM hN hu hv hf hg hulim hflim) hnonneg

end MeasureTheory
