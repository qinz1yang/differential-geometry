import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Ring.Units

/-!
# CH12-S126 G1: smoothness of the local inverse of `id + u` (setup for `inverse_jets_S126`)

Context of `[FROZEN] CH12-O58 R-E`: `V W ⊆ E` open, `u` smooth on `V`,
`ApproximatesLinearOn (id + u) id V (1/2)`, `Φ` a right inverse of `id + u` on `W` with values in
`V`.  Pure ℝ-calculus on a complete normed space.

* `norm_fderiv_le_half_S126`: `‖Du‖ ≤ 1/2` on `V` (the `1/2`-Lipschitz bound),
* `injOn_id_add_S126`: `id + u` is injective on `V`,
* `exists_equiv_one_add_S126`: `‖A‖ ≤ 1/2 → ∃ e : E ≃L E, ↑e = 1 + A`,
* `contDiffOn_inverse_S126`: `Φ` is `C^∞` on `W` (inverse function theorem + injectivity),
* `fderiv_inverse_comp_S126`: `DΦ(x) ∘ (1 + Du(Φ x)) = 1` on `W` (chain rule).
-/

set_option autoImplicit false

open Set Filter Topology
open scoped ContDiff NNReal

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `‖(y + u y)‖`-difference identity used twice: the defect of `id + u` against `id` is `u`. -/
theorem approx_defect_S126 {u : E → E} (a b : E) :
    (fun y => y + u y) a - (fun y => y + u y) b -
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (a - b) = u a - u b := by
  have h : ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (a - b) = a - b := rfl
  change a + u a - (b + u b) -
    ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (a - b) = u a - u b
  rw [h]
  abel

/-- `u` is `1/2`-Lipschitz on `V`, hence `‖Du‖ ≤ 1/2` at interior points. -/
theorem norm_fderiv_le_half_S126 {u : E → E} {V : Set E} (hV : IsOpen V)
    (hA : ApproximatesLinearOn (fun y => y + u y)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0)) :
    ∀ y ∈ V, ‖fderiv ℝ u y‖ ≤ 1 / 2 := by
  intro y hy
  have hlip : LipschitzOnWith (1 / 2 : ℝ≥0) u V := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have h := hA a ha b hb
    rw [approx_defect_S126] at h
    simpa [dist_eq_norm] using h
  have := norm_fderiv_le_of_lipschitzOn ℝ (hV.mem_nhds hy) hlip
  simpa using this

/-- `id + u` is injective on `V`. -/
theorem injOn_id_add_S126 {u : E → E} {V : Set E}
    (hA : ApproximatesLinearOn (fun y => y + u y)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0)) :
    InjOn (fun y => y + u y) V := by
  intro a ha b hb hab
  have h := hA a ha b hb
  have h3 : (fun y => y + u y) a - (fun y => y + u y) b = 0 := sub_eq_zero.2 hab
  rw [h3, zero_sub, norm_neg] at h
  have hr : ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (a - b) = a - b := rfl
  rw [hr] at h
  have h8 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [h8] at h
  have h7 : ‖a - b‖ = 0 := by linarith [norm_nonneg (a - b)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h7)

/-- `1 + A` is a continuous linear equivalence when `‖A‖ ≤ 1/2`. -/
theorem exists_equiv_one_add_S126 [CompleteSpace E] (A : E →L[ℝ] E) (hA : ‖A‖ ≤ 1 / 2) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = 1 + A := by
  have h : ‖-A‖ < 1 := by rw [norm_neg]; linarith
  refine ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub (-A) h), ?_⟩
  ext x
  simp [ContinuousLinearEquiv.ofUnit]

/-- A right inverse `Φ` of `id + u` on an open `W` (values in the open set `V`) is `C^∞`. -/
theorem contDiffOn_inverse_S126 [CompleteSpace E] {u Φ : E → E} {V W : Set E} (hV : IsOpen V)
    (hW : IsOpen W) (hu : ContDiffOn ℝ ∞ u V)
    (hA : ApproximatesLinearOn (fun y => y + u y)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0))
    (hΦ : ∀ x ∈ W, Φ x ∈ V ∧ Φ x + u (Φ x) = x) : ContDiffOn ℝ ∞ Φ W := by
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨hy₀, hΨy₀⟩ := hΦ x₀ hx₀
  obtain ⟨y₀, hy₀eq⟩ : ∃ y₀, y₀ = Φ x₀ := ⟨_, rfl⟩
  rw [← hy₀eq] at hy₀ hΨy₀
  have hinj := injOn_id_add_S126 hA
  have hua : ContDiffAt ℝ ∞ u y₀ := hu.contDiffAt (hV.mem_nhds hy₀)
  have hΨ : ContDiffAt ℝ ∞ (fun y => y + u y) y₀ := contDiffAt_id.add hua
  obtain ⟨e, he⟩ := exists_equiv_one_add_S126 (fderiv ℝ u y₀)
    (norm_fderiv_le_half_S126 hV hA y₀ hy₀)
  have hf' : HasFDerivAt (fun y => y + u y) (e : E →L[ℝ] E) y₀ := by
    rw [he, ContinuousLinearMap.one_def]
    exact (hasFDerivAt_id y₀).add (hua.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hΨ.hasStrictFDerivAt' hf' hn
  have hg : ContDiffAt ℝ ∞ (hs.localInverse (fun y => y + u y) e y₀) (y₀ + u y₀) :=
    hΨ.to_localInverse hf' hn
  have hx₀' : y₀ + u y₀ = x₀ := hΨy₀
  rw [hx₀'] at hg
  have hcont : ContinuousAt (hs.localInverse (fun y => y + u y) e y₀) x₀ := by
    have := hs.localInverse_continuousAt
    rwa [hx₀'] at this
  have hgy : hs.localInverse (fun y => y + u y) e y₀ x₀ = y₀ := by
    have := hs.localInverse_apply_image
    rwa [hx₀'] at this
  have hright : ∀ᶠ x in 𝓝 x₀, hs.localInverse (fun y => y + u y) e y₀ x +
      u (hs.localInverse (fun y => y + u y) e y₀ x) = x := by
    have := hs.eventually_right_inverse
    rwa [hx₀'] at this
  have hVg : ∀ᶠ x in 𝓝 x₀, hs.localInverse (fun y => y + u y) e y₀ x ∈ V :=
    hcont.eventually_mem (by rw [hgy]; exact hV.mem_nhds hy₀)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [hW.mem_nhds hx₀, hright, hVg] with x hxW hxr hxV
  obtain ⟨hΦV, hΦx⟩ := hΦ x hxW
  exact hinj hΦV hxV (hΦx.trans hxr.symm)

/-- Chain rule: `DΦ(x) ∘ (1 + Du(Φ x)) = 1` on `W`. -/
theorem fderiv_inverse_comp_S126 [CompleteSpace E] {u Φ : E → E} {V W : Set E} (hV : IsOpen V)
    (hW : IsOpen W) (hu : ContDiffOn ℝ ∞ u V)
    (hA : ApproximatesLinearOn (fun y => y + u y)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0))
    (hΦ : ∀ x ∈ W, Φ x ∈ V ∧ Φ x + u (Φ x) = x) :
    ∀ x ∈ W, (fderiv ℝ Φ x).comp (1 + fderiv ℝ u (Φ x)) = 1 := by
  intro x hx
  obtain ⟨hy, hΨy⟩ := hΦ x hx
  have hinj := injOn_id_add_S126 hA
  have hΦc := contDiffOn_inverse_S126 hV hW hu hA hΦ
  have hΦd : DifferentiableAt ℝ Φ x :=
    (hΦc.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hud : DifferentiableAt ℝ u (Φ x) :=
    (hu.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ (fun y => y + u y) (Φ x) := differentiableAt_id.add hud
  have hcomp : Φ ∘ (fun y => y + u y) =ᶠ[𝓝 (Φ x)] id := by
    have hc : ContinuousAt (fun y => y + u y) (Φ x) := hΨd.continuousAt
    have h1 : ∀ᶠ z in 𝓝 (Φ x), (fun y => y + u y) z ∈ W :=
      hc.eventually_mem (by rw [hΨy]; exact hW.mem_nhds hx)
    filter_upwards [hV.mem_nhds hy, h1] with z hzV hzW
    obtain ⟨hΦV, hΦz⟩ := hΦ _ hzW
    exact hinj hΦV hzV (by simpa using hΦz)
  have hfd : fderiv ℝ (fun y => y + u y) (Φ x) = 1 + fderiv ℝ u (Φ x) := by
    have := ((hasFDerivAt_id (𝕜 := ℝ) (Φ x)).add hud.hasFDerivAt).fderiv
    rw [ContinuousLinearMap.one_def]; exact this
  have h := hcomp.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp (Φ x) (by rw [hΨy]; exact hΦd) hΨd, fderiv_id, hfd, hΨy] at h
  rwa [ContinuousLinearMap.one_def]

end GC.LongTime.Ch12
