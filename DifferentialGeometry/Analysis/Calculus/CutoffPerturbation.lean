import DifferentialGeometry.Analysis.Calculus.BumpPerturbation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped Topology ContDiff
namespace Poincare.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_bumpPerturbation_of_ne_zero {f : E → E} {ρ : E → ℝ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hρ : DifferentiableAt ℝ ρ x)
    (hρx : ρ x ≠ 0) (hz : bumpPerturbation f ρ v x = 0) :
    fderiv ℝ (bumpPerturbation f ρ v) x =
      ρ x • fderiv ℝ (fun y => (ρ y)⁻¹ • f y) x := by
  let q : E → E := fun y => (ρ y)⁻¹ • f y
  have hq : DifferentiableAt ℝ q x := (hρ.inv hρx).smul hf
  have hfx : f x = ρ x • v := sub_eq_zero.mp hz
  have hqx : q x = v := by simp [q, hfx, smul_smul, hρx]
  have he : bumpPerturbation f ρ v =ᶠ[𝓝 x] fun y => ρ y • (q y - v) := by
    filter_upwards [hρ.continuousAt.eventually_ne hρx] with y hy
    simp [bumpPerturbation, q, smul_sub, smul_smul, hy]
  rw [he.fderiv_eq]
  simpa [hqx] using! (hρ.hasFDerivAt.smul (hq.hasFDerivAt.sub_const v)).fderiv


theorem fderiv_bumpPerturbation_of_eq_zero {f : E → E} {ρ : E → ℝ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hρ : DifferentiableAt ℝ ρ x)
    (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ ρ y) (hρx : ρ x = 0) :
    fderiv ℝ (bumpPerturbation f ρ v) x = fderiv ℝ f x := by
  have hmin : IsLocalMin ρ x := by simpa only [IsLocalMin, IsMinFilter, hρx] using hnonneg
  have hd : fderiv ℝ ρ x = 0 := hmin.fderiv_eq_zero
  simpa [bumpPerturbation, hd] using! (hf.hasFDerivAt.sub (hρ.hasFDerivAt.smul_const v)).fderiv

variable [FiniteDimensional ℝ E]

theorem exists_small_regular_cutoff_perturbation {f : E → E} {ρ : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) (hρ : DifferentiableOn ℝ ρ U)
    (hnonneg : ∀ x ∈ U, 0 ≤ ρ x)
    (hfixed : ∀ x ∈ U, ρ x = 0 → f x = 0 → (fderiv ℝ f x).det ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, ‖v‖ < ε ∧ ∀ x ∈ U, bumpPerturbation f ρ v x = 0 →
      (fderiv ℝ (bumpPerturbation f ρ v) x).det ≠ 0 := by
  let q : E → E := fun y => (ρ y)⁻¹ • f y
  obtain ⟨v, hv, hreg⟩ := exists_near_regular_value
    (f := q) (s := {x ∈ U | ρ x ≠ 0})
    (fun x hx => ((hρ x hx.1).differentiableAt (hU.mem_nhds hx.1)).inv hx.2 |>.smul
      ((hf x hx.1).differentiableAt (hU.mem_nhds hx.1))) 0 hε
  refine ⟨v, by simpa only [dist_zero_right] using hv, ?_⟩
  intro x hx hz
  have hfx := (hf x hx).differentiableAt (hU.mem_nhds hx)
  have hρx := (hρ x hx).differentiableAt (hU.mem_nhds hx)
  by_cases hzero : ρ x = 0
  · rw [fderiv_bumpPerturbation_of_eq_zero hfx hρx
      (Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => hnonneg y hy)) hzero]
    exact hfixed x hx hzero (by simpa [bumpPerturbation, hzero] using hz)
  · rw [fderiv_bumpPerturbation_of_ne_zero hfx hρx hzero hz]
    change (LinearMap.det (ρ x • (fderiv ℝ q x).toLinearMap)) ≠ 0
    rw [LinearMap.det_smul]
    apply mul_ne_zero (pow_ne_zero _ hzero)
    apply hreg x ⟨hx, hzero⟩
    have he : f x = ρ x • v := sub_eq_zero.mp hz
    simp [q, he, smul_smul, hzero]

theorem exists_small_regular_perturbation_fixed {f : E → E} {U Ω : Set E}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f U)
    (hfixed : ∀ x ∈ U, x ∉ Ω → f x = 0 → (fderiv ℝ f x).det ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → E, ContDiffOn ℝ ∞ g U ∧
      (∀ x, ‖g x - f x‖ < ε) ∧ EqOn g f Ωᶜ ∧
      (∀ x ∈ U, x ∉ Ω → fderiv ℝ g x = fderiv ℝ f x) ∧
      ∀ x ∈ U, g x = 0 → (fderiv ℝ g x).det ≠ 0 := by
  obtain ⟨ρ, hsupport, hρ, hrange⟩ := hΩ.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hn (x : E) : ρ x ∈ Icc (0 : ℝ) 1 := hrange ⟨x, rfl⟩
  have hzero (x : E) : ρ x = 0 ↔ x ∉ Ω := by
    rw [← hsupport]
    simp only [mem_support, not_not]
  obtain ⟨v, hv, hreg⟩ := exists_small_regular_cutoff_perturbation hU
    (hf.differentiableOn (by simp)) (hρ.differentiable (by simp)).differentiableOn
    (fun x _ => (hn x).1) (fun x hx hz => hfixed x hx ((hzero x).mp hz)) hε
  refine ⟨bumpPerturbation f ρ v, contDiffOn_bumpPerturbation hf hρ v,
    fun x => (norm_bumpPerturbation_sub_le f hn v x).trans_lt hv, ?_, ?_, hreg⟩
  · intro x hx
    simp only [bumpPerturbation, (hzero x).mpr hx, zero_smul, sub_zero]
  · intro x hx hxo
    exact fderiv_bumpPerturbation_of_eq_zero
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      (hρ.contDiffAt.differentiableAt (by simp)) (Eventually.of_forall (fun y => (hn y).1))
      ((hzero x).mpr hxo)

end Poincare.Calculus
