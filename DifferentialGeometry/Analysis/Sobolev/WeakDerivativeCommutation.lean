import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Set E}

omit [MeasurableSpace E] in
private theorem fderiv_fderiv_apply_comm
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hc : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := (hc.differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  rw [fderiv_fun_const, fderiv_fun_const]
  simp only [add_apply, ContinuousLinearMap.comp_apply, Pi.zero_apply, zero_apply, map_zero, zero_add]
  exact hφ.contDiffAt.isSymmSndFDerivAt (by simpa only [minSmoothness_of_isRCLikeNormedField] using (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞) from by norm_cast)) w v

theorem integral_weak_deriv_fderiv_comm
    {U V R : E → ℝ} (v w : E)
    (hv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) = -∫ x, R x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, V x * fderiv ℝ φ x w ∂μ) = ∫ x, R x * fderiv ℝ φ x v ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have h₁ := hv (fun x => fderiv ℝ φ x w) (hd w) (hφc.fderiv_apply ℝ w)
    ((tsupport_fderiv_apply_subset ℝ w).trans hφs)
  have h₂ := hw (fun x => fderiv ℝ φ x v) (hd v) (hφc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφs)
  apply neg_injective
  rw [← h₁, ← h₂]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fderiv_fderiv_apply_comm hφ x w v]


variable [OpensMeasurableSpace E]

omit [NormedSpace ℝ E] in
private theorem integrable_mul_continuousOn_mul_test
    (hΩ : IsOpen Ω) {U c φ : E → ℝ}
    (hU : LocallyIntegrable U μ) (hc : ContinuousOn c Ω)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    Integrable (fun x => c x * U x * φ x) μ := by
  have hcφ : Continuous (fun x => c x * φ x) :=
    (hc.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  convert hU.integrable_smul_right_of_hasCompactSupport hcφ hφc.mul_left using 1
  ext x
  simp only [smul_eq_mul]
  ring

theorem integral_weak_product_deriv
    (hΩ : IsOpen Ω) {U V c : E → ℝ} (v : E)
    (hU : LocallyIntegrable U μ) (hV : LocallyIntegrable V μ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, c x * U x * fderiv ℝ φ x v ∂μ) =
      -∫ x, (c x * V x + fderiv ℝ c x v * U x) * φ x ∂μ := by
  let ψ := fun x => c x * φ x
  have hψs : tsupport ψ ⊆ Ω := tsupport_mul_subset_right.trans hφs
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (hc.mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ hψs
  have hdc : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ c x v) Ω :=
    (hc.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have heq : (fun x => U x * fderiv ℝ ψ x v) = fun x =>
      c x * U x * fderiv ℝ φ x v + fderiv ℝ c x v * U x * φ x := by
    ext x
    by_cases hx : x ∈ Ω
    · have hcd := (hc.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
      dsimp only [ψ]
      rw [fderiv_fun_mul hcd (hφ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · have hp : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
      have hdφ : fderiv ℝ φ x v = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ φ y v)
        (fun h => hx (hφs (tsupport_fderiv_apply_subset ℝ v h)))
      have hdψ : fderiv ℝ ψ x v = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ψ y v)
        (fun h => hx (hψs (tsupport_fderiv_apply_subset ℝ v h)))
      simp only [hp, hdφ, hdψ, mul_zero, zero_add]
  have hI := integrable_mul_continuousOn_mul_test hΩ hU hc.continuousOn
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hφs)
  have hJ := integrable_mul_continuousOn_mul_test hΩ hU hdc.continuousOn
    hφ.continuous hφc hφs
  have hK := integrable_mul_continuousOn_mul_test hΩ hV hc.continuousOn
    hφ.continuous hφc hφs
  have ht := hweak ψ hψ hψc hψs
  rw [heq, integral_add hI hJ] at ht
  have hright : (∫ x, V x * ψ x ∂μ) = ∫ x, c x * V x * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [ψ]
    ring
  rw [hright] at ht
  simp_rw [add_mul]
  rw [integral_add hK hJ]
  linarith


theorem integral_weak_deriv_weighted_divergence
    {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω)
    {U W R ρ L : E → ℝ} {V H A : ι → E → ℝ} (v w : E) (e : ι → E)
    (hU : LocallyIntegrable U μ) (hW : LocallyIntegrable W μ)
    (hR : LocallyIntegrable R μ)
    (hV : ∀ i ∈ s, LocallyIntegrable (V i) μ)
    (hH : ∀ i ∈ s, LocallyIntegrable (H i) μ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω)
    (hA : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (A i) Ω)
    (hspace : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x v ∂μ) = -∫ x, W x * ψ x ∂μ)
    (hsource : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, U x * fderiv ℝ ψ x w ∂μ) = -∫ x, R x * ψ x ∂μ)
    (hflux : ∀ i ∈ s, ∀ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, V i x * fderiv ℝ ψ x v ∂μ) = -∫ x, H i x * ψ x ∂μ)
    (hbase : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ x, ρ x * U x * fderiv ℝ ψ x w ∂μ) =
        (∑ i ∈ s, ∫ x, A i x * V i x * fderiv ℝ ψ x (e i) ∂μ) -
          ∫ x, L x * ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    (∫ x, ρ x * W x * fderiv ℝ φ x w ∂μ) =
      (∑ i ∈ s, ∫ x, (A i x * H i x + fderiv ℝ (A i) x v * V i x) *
        fderiv ℝ φ x (e i) ∂μ) + (∫ x, L x * fderiv ℝ φ x v ∂μ) +
        ∫ x, (fderiv ℝ ρ x v * R x +
          fderiv ℝ (fun y => fderiv ℝ ρ y v) x w * U x) * φ x ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hdc (z : E) : HasCompactSupport (fun x => fderiv ℝ φ x z) :=
    hφc.fderiv_apply ℝ z
  have hds (z : E) : tsupport (fun x => fderiv ℝ φ x z) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ z).trans hφs
  have hDρ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ρ x v) Ω :=
    (hρ.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hT := integral_weak_product_deriv hΩ v hU hW hρ hspace (hd w) (hdc w) (hds w)
  have hS := integral_weak_product_deriv hΩ w hU hR hDρ hsource hφ hφc hφs
  have hI := integrable_mul_continuousOn_mul_test hΩ hW hρ.continuousOn
    (hd w).continuous (hdc w) (hds w)
  have hJ := integrable_mul_continuousOn_mul_test hΩ hU hDρ.continuousOn
    (hd w).continuous (hdc w) (hds w)
  have hTcomm : (∫ x, ρ x * U x * fderiv ℝ (fun y => fderiv ℝ φ y w) x v ∂μ) =
      ∫ x, ρ x * U x * fderiv ℝ (fun y => fderiv ℝ φ y v) x w ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [fderiv_fderiv_apply_comm hφ x w v]
  rw [hTcomm] at hT
  simp_rw [add_mul] at hT
  rw [integral_add hI hJ, hS] at hT
  have hF (i : ι) (hi : i ∈ s) :
      (∫ x, A i x * V i x * fderiv ℝ (fun y => fderiv ℝ φ y v) x (e i) ∂μ) =
        -∫ x, (A i x * H i x + fderiv ℝ (A i) x v * V i x) *
          fderiv ℝ φ x (e i) ∂μ := by
    have h := integral_weak_product_deriv hΩ v (hV i hi) (hH i hi) (hA i hi)
      (hflux i hi) (hd (e i)) (hdc (e i)) (hds (e i))
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [fderiv_fderiv_apply_comm hφ x v (e i)]
  have hsum :
      (∑ i ∈ s, ∫ x, A i x * V i x * fderiv ℝ (fun y => fderiv ℝ φ y v) x (e i) ∂μ) =
        -(∑ i ∈ s, ∫ x, (A i x * H i x + fderiv ℝ (A i) x v * V i x) *
          fderiv ℝ φ x (e i) ∂μ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hF
  have hb := hbase (fun x => fderiv ℝ φ x v) (hd v) (hdc v) (hds v)
  rw [hsum] at hb
  linarith

end DifferentialGeometry.Analysis.Sobolev
