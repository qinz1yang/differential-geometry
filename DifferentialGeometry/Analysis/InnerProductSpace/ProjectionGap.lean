import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem norm_starProjection_sub_le_of_one_sided_bound
    (P Q : Submodule 𝕜 H) [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 Q]
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 Q)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hbound : ∀ u ∈ P, ‖u - Q.starProjection u‖ ≤ b * ‖u‖) :
    ‖P.starProjection - Q.starProjection‖ ≤ b + b / (1 - b) := by
  let F : P →ₗ[𝕜] Q := Q.orthogonalProjectionOnto.toLinearMap.comp P.subtype
  have hlow (u : P) : (1 - b) * ‖(u : H)‖ ≤ ‖Q.starProjection u‖ := by
    have htriangle := norm_add_le ((u : H) - Q.starProjection u) (Q.starProjection u)
    rw [sub_add_cancel] at htriangle
    have h := hbound u u.property
    nlinarith
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro u hu
    have hz : Q.starProjection (u : H) = 0 :=
      congrArg (fun w : Q => (w : H)) (LinearMap.mem_ker.mp hu)
    have hl := hlow u
    rw [hz, norm_zero] at hl
    have hn : ‖(u : H)‖ = 0 := by nlinarith [norm_nonneg (u : H)]
    exact Subtype.ext (norm_eq_zero.mp hn)
  have hsurj : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let c : ℝ := b / (1 - b)
  have hc : 0 ≤ c := div_nonneg hb (sub_pos.mpr hb1).le
  have hreverse (w : H) (hw : w ∈ Q) : ‖w - P.starProjection w‖ ≤ c * ‖w‖ := by
    obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
    have huw : Q.starProjection (u : H) = w := congrArg (fun z : Q => (z : H)) hu
    have hu_norm : ‖(u : H)‖ ≤ ‖w‖ / (1 - b) := by
      apply (le_div_iff₀ (sub_pos.mpr hb1)).mpr
      have h := hlow u
      rw [huw] at h
      nlinarith
    calc
      ‖w - P.starProjection w‖ = Metric.infDist w (P : Set H) := by
        simpa only [dist_eq_norm] using P.dist_starProjection_eq_infDist w
      _ ≤ dist w (u : H) := Metric.infDist_le_dist_of_mem u.property
      _ = ‖(u : H) - Q.starProjection u‖ := by rw [dist_eq_norm, huw, norm_sub_rev]
      _ ≤ b * ‖(u : H)‖ := hbound u u.property
      _ ≤ b * (‖w‖ / (1 - b)) := mul_le_mul_of_nonneg_left hu_norm hb
      _ = c * ‖w‖ := by dsimp [c]; ring
  have hcomplement (x : H) :
      ‖Q.starProjection (x - P.starProjection x)‖ ≤ c * ‖x‖ := by
    let y : H := x - P.starProjection x
    let z : H := Q.starProjection y
    have hy : ‖y‖ ≤ ‖x‖ := by
      have h := Pᗮ.norm_starProjection_apply_le x
      simpa only [starProjection_orthogonal, sub_apply,
        ContinuousLinearMap.id_apply] using h
    have horth : inner 𝕜 (P.starProjection z) y = 0 := by
      apply inner_eq_zero_symm.mp
      exact P.starProjection_inner_eq_zero x (P.starProjection z) (P.starProjection_apply_mem z)
    have hsq : RCLike.re (inner 𝕜 z y) = ‖z‖ ^ 2 :=
      Q.re_inner_starProjection_eq_normSq y
    have hinner : RCLike.re (inner 𝕜 (z - P.starProjection z) y) = ‖z‖ ^ 2 := by
      rw [inner_sub_left, horth, sub_zero, hsq]
    have hzbound := hreverse z (Q.starProjection_apply_mem y)
    have hsquare : ‖z‖ ^ 2 ≤ (c * ‖y‖) * ‖z‖ := by
      have h := re_inner_le_norm (𝕜 := 𝕜) (z - P.starProjection z) y
      rw [hinner] at h
      have hmul := mul_le_mul_of_nonneg_right hzbound (norm_nonneg y)
      nlinarith
    have hz : ‖z‖ ≤ c * ‖y‖ := by
      by_cases hzero : ‖z‖ = 0
      · rw [hzero]
        positivity
      · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzero)
        exact (mul_le_mul_iff_left₀ hpos).mp (by simpa only [pow_two] using hsquare)
    exact hz.trans (mul_le_mul_of_nonneg_left hy hc)
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hb hc)
  intro x
  have hsplit : P.starProjection x - Q.starProjection x =
      (P.starProjection x - Q.starProjection (P.starProjection x)) -
        Q.starProjection (x - P.starProjection x) := by
    rw [map_sub]
    abel
  change ‖P.starProjection x - Q.starProjection x‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖P.starProjection x - Q.starProjection (P.starProjection x)‖ +
        ‖Q.starProjection (x - P.starProjection x)‖ := norm_sub_le _ _
    _ ≤ b * ‖P.starProjection x‖ + c * ‖x‖ :=
      add_le_add (hbound _ (P.starProjection_apply_mem x)) (hcomplement x)
    _ ≤ b * ‖x‖ + c * ‖x‖ := by
      gcongr
      exact P.norm_starProjection_apply_le x
    _ = (b + b / (1 - b)) * ‖x‖ := by dsimp [c]; ring

theorem norm_starProjection_sub_le_three_mul_of_one_sided_bound
    (P Q : Submodule 𝕜 H) [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 Q]
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 Q)
    {b : ℝ} (hb : 0 ≤ b) (hbhalf : b ≤ 1 / 2)
    (hbound : ∀ u ∈ P, ‖u - Q.starProjection u‖ ≤ b * ‖u‖) :
    ‖P.starProjection - Q.starProjection‖ ≤ 3 * b := by
  have hb1 : b < 1 := by linarith
  have hratio : b / (1 - b) ≤ 2 * b := by
    apply (div_le_iff₀ (sub_pos.mpr hb1)).mpr
    nlinarith
  exact (norm_starProjection_sub_le_of_one_sided_bound P Q hdim hb hb1 hbound).trans
    (by linarith)

end Submodule
