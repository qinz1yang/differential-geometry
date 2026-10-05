import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Support

/-!
# EDP01 kernel on a manifold: the blend `s = (1 − χ)ρ + χz` varies slowly

Frozen blueprint master207B, EDP01 (`lem:fibration-actual-adjusted-scale-derivative`, B:6666–6746):
"The actual blend is `s = (1−χ)ρ + χz_ρ`. … The product rule bounds its derivative by
`(1 + K₂ + K₁K₃)Λ`. Outside the closed support `s = ρ`." The normed-space form is
`EdgeDisk.adjustedScale_slow` (AdjustedScale.lean); here the same statement on a manifold `M`, with
the derivative `mvfderiv` applied to tangent vectors and an arbitrary pointwise size `n_x(v)` of
tangent vectors (for a Riemannian metric `n_x(v) = √g_x(v, v)`):

* `mvfderiv_blend_apply_GAFS`: `ds(v) = (1 − χ)dρ(v) + χ dz(v) + (z − ρ) dχ(v)`;
* `adjustedScale_slow_mfd_GAFS`: if `|dρ(v)| ≤ Λn(v)`, `0 ≤ χ ≤ 1`, and on the closed support of `χ`
  the functions `z, χ` are differentiable with `|z − ρ| ≤ K₁Λρ`, `|dz(v)| ≤ K₂Λn(v)` and
  `|dχ(v)| ≤ (K₃/ρ)n(v)`, then `s` is differentiable everywhere, `|s − ρ| ≤ K₁Λρ` and
  `|ds(v)| ≤ (1 + K₂ + K₁K₃)Λn(v)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Hm : Type*} [TopologicalSpace Hm]
  {I : ModelWithCorners ℝ E Hm} {M : Type*} [TopologicalSpace M] [ChartedSpace Hm M]

/-- The derivative of the blend `s = (1 − χ)ρ + χz` at a point where `ρ, z, χ` are differentiable:
`ds(v) = (1 − χ)dρ(v) + χ dz(v) + (z − ρ) dχ(v)`. -/
theorem mvfderiv_blend_apply_GAFS {ρ z χ : M → ℝ} {x : M}
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x) (hz : MDifferentiableAt I 𝓘(ℝ, ℝ) z x)
    (hχ : MDifferentiableAt I 𝓘(ℝ, ℝ) χ x) (v : TangentSpace I x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (1 - χ y) * ρ y + χ y * z y) x ∧
      mvfderiv I (fun y => (1 - χ y) * ρ y + χ y * z y) x v =
        (1 - χ x) * mvfderiv I ρ x v + χ x * mvfderiv I z x v +
          (z x - ρ x) * mvfderiv I χ x v := by
  have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => 1 - χ y) x :=
    mdifferentiableAt_const.sub hχ
  have hA : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (1 - χ y) * ρ y) x := h1.mul hρ
  have hB : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => χ y * z y) x := hχ.mul hz
  refine ⟨hA.add hB, ?_⟩
  rw [mvfderiv_fun_add hA hB, mvfderiv_fun_mul h1 hρ, mvfderiv_fun_mul hχ hz,
    mvfderiv_fun_sub mdifferentiableAt_const hχ, mvfderiv_const]
  simp only [add_apply, smul_apply, sub_apply, zero_apply, smul_eq_mul]
  ring

/-- **EDP01 kernel (SD) on a manifold.** Let `ρ > 0` be differentiable with `|dρ(v)| ≤ Λn(v)`
(`0 ≤ Λ`) and `0 ≤ χ ≤ 1`. If at every point of the closed support of `χ` the functions `z, χ`
are differentiable with `|z − ρ| ≤ K₁Λρ`, `|dz(v)| ≤ K₂Λn(v)` and `|dχ(v)| ≤ (K₃/ρ)n(v)`, then
`s = (1 − χ)ρ + χz` is differentiable everywhere with `|s − ρ| ≤ K₁Λρ` and
`|ds(v)| ≤ (1 + K₂ + K₁K₃)Λn(v)`. -/
theorem adjustedScale_slow_mfd_GAFS (n : ∀ x : M, TangentSpace I x → ℝ) {ρ z χ : M → ℝ}
    {Λ K₁ K₂ K₃ : ℝ} (hΛ : 0 ≤ Λ) (hK₁ : 0 ≤ K₁) (hK : 0 ≤ K₂ + K₁ * K₃)
    (hρ : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x) (hρpos : ∀ x, 0 < ρ x)
    (hρ' : ∀ x v, |mvfderiv I ρ x v| ≤ Λ * n x v) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : ∀ x ∈ tsupport χ, MDifferentiableAt I 𝓘(ℝ, ℝ) z x ∧
      MDifferentiableAt I 𝓘(ℝ, ℝ) χ x ∧ |z x - ρ x| ≤ K₁ * Λ * ρ x ∧
      (∀ v, |mvfderiv I z x v| ≤ K₂ * Λ * n x v) ∧ ∀ v, |mvfderiv I χ x v| ≤ K₃ / ρ x * n x v) :
    ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (1 - χ y) * ρ y + χ y * z y) x ∧
      |(1 - χ x) * ρ x + χ x * z x - ρ x| ≤ K₁ * Λ * ρ x ∧
      ∀ v, |mvfderiv I (fun y => (1 - χ y) * ρ y + χ y * z y) x v| ≤
        (1 + K₂ + K₁ * K₃) * Λ * n x v := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · obtain ⟨hzd, hχd, hzv, hz', hχ'⟩ := hsupp x hx
    obtain ⟨hχ0, hχ1⟩ := hχ01 x
    have hρx := hρpos x
    refine ⟨(mvfderiv_blend_apply_GAFS (hρ x) hzd hχd (0 : TangentSpace I x)).1, ?_, fun v => ?_⟩
    · have : (1 - χ x) * ρ x + χ x * z x - ρ x = χ x * (z x - ρ x) := by ring
      rw [this, abs_mul, abs_of_nonneg hχ0]
      calc χ x * |z x - ρ x| ≤ 1 * |z x - ρ x| := mul_le_mul_of_nonneg_right hχ1 (abs_nonneg _)
        _ ≤ K₁ * Λ * ρ x := by rw [one_mul]; exact hzv
    · rw [(mvfderiv_blend_apply_GAFS (hρ x) hzd hχd v).2]
      have hn1 : 0 ≤ Λ * n x v := (abs_nonneg _).trans (hρ' x v)
      have hn2 : 0 ≤ K₂ * Λ * n x v := (abs_nonneg _).trans (hz' v)
      have hn3 : 0 ≤ K₃ / ρ x * n x v := (abs_nonneg _).trans (hχ' v)
      have hterm3 : |z x - ρ x| * |mvfderiv I χ x v| ≤ K₁ * K₃ * Λ * n x v := by
        calc |z x - ρ x| * |mvfderiv I χ x v| ≤ (K₁ * Λ * ρ x) * (K₃ / ρ x * n x v) :=
              mul_le_mul hzv (hχ' v) (abs_nonneg _) ((abs_nonneg _).trans hzv)
          _ = K₁ * K₃ * Λ * n x v := by field_simp
      calc |(1 - χ x) * mvfderiv I ρ x v + χ x * mvfderiv I z x v +
            (z x - ρ x) * mvfderiv I χ x v|
          ≤ |(1 - χ x) * mvfderiv I ρ x v| + |χ x * mvfderiv I z x v| +
              |(z x - ρ x) * mvfderiv I χ x v| := abs_add_three _ _ _
        _ = (1 - χ x) * |mvfderiv I ρ x v| + χ x * |mvfderiv I z x v| +
              |z x - ρ x| * |mvfderiv I χ x v| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hχ1), abs_of_nonneg hχ0]
        _ ≤ (1 - χ x) * (Λ * n x v) + χ x * (K₂ * Λ * n x v) + K₁ * K₃ * Λ * n x v :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hρ' x v) (by linarith))
              (mul_le_mul_of_nonneg_left (hz' v) hχ0)) hterm3
        _ ≤ Λ * n x v + K₂ * Λ * n x v + K₁ * K₃ * Λ * n x v := by nlinarith
        _ = (1 + K₂ + K₁ * K₃) * Λ * n x v := by ring
  · have hev : χ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hχx : χ x = 0 := hev.eq_of_nhds
    have hseq : (fun y => (1 - χ y) * ρ y + χ y * z y) =ᶠ[𝓝 x] ρ := by
      filter_upwards [hev] with y hy
      rw [hy]
      ring
    have hρx := hρpos x
    refine ⟨(hρ x).congr_of_eventuallyEq hseq, ?_, fun v => ?_⟩
    · rw [hχx]
      simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, abs_zero]
      positivity
    · have hd : mvfderiv I (fun y => (1 - χ y) * ρ y + χ y * z y) x = mvfderiv I ρ x := by
        unfold mvfderiv
        rw [hseq.mfderiv_eq]
        rfl
      rw [hd]
      have hn1 : 0 ≤ Λ * n x v := (abs_nonneg _).trans (hρ' x v)
      calc |mvfderiv I ρ x v| ≤ Λ * n x v := hρ' x v
        _ ≤ (1 + K₂ + K₁ * K₃) * Λ * n x v := by nlinarith

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
