import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.WeakConvergence
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Basic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

private theorem timeOp_pos
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A t x) x) :
    (timeOp A hA C hC).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨?_, fun u ↦ timeQuad_nonneg A hA C hC hpos u⟩
  intro u v
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeOp_apply_ae A hA C hC u,
    timeOp_apply_ae A hA C hC v, hself] with t hu hv ht
  change inner ℝ ((timeOp A hA C hC u) t) (v t) =
    inner ℝ (u t) ((timeOp A hA C hC v) t)
  rw [hu, hv]
  exact ht.isSymmetric (u t) (v t)

theorem timeQuad_weak_lim
    (A : ℕ → ℝ → X →L[ℝ] X) (A_lim : ℝ → X →L[ℝ] X)
    (hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure T))
    (hA_lim : AEStronglyMeasurable A_lim (timeMeasure T))
    (C : ℕ → NNReal) (C_lim : NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (hC_lim : ∀ᵐ t ∂timeMeasure T, ‖A_lim t‖ ≤ (C_lim : ℝ))
    (ε : ℕ → NNReal) (hε : Tendsto ε atTop (nhds 0))
    (hconv : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t - A_lim t‖ ≤ (ε n : ℝ))
    (hself : ∀ n, ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A n t))
    (hpos : ∀ n, ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A n t x) x)
    (u : ℕ → timeL2 X T) (u_lim : timeL2 X T)
    (hu : ∀ z, Tendsto (fun n ↦ inner ℝ (u n) z) atTop
      (nhds (inner ℝ u_lim z))) :
    timeQuad A_lim hA_lim C_lim hC_lim u_lim ≤
      liminf (fun n ↦ timeQuad (A n) (hA n) (C n) (hC n) (u n)) atTop := by
  let L : timeL2 X T →L[ℝ] timeL2 X T := timeOp A_lim hA_lim C_lim hC_lim
  let Ln : ℕ → timeL2 X T →L[ℝ] timeL2 X T :=
    fun n ↦ timeOp (A n) (hA n) (C n) (hC n)
  let q : ℕ → ℝ := fun n ↦ inner ℝ (Ln n (u n)) (u n)
  let qlim : ℝ := inner ℝ (L u_lim) u_lim
  have hcross : Tendsto (fun n ↦ inner ℝ (Ln n (u n)) u_lim) atTop
      (nhds qlim) := by
    simpa only [Ln, L, qlim] using
      timeOp_weak_lim A A_lim hA hA_lim C C_lim hC hC_lim ε hε hconv
        u u_lim hu u_lim
  have hu_const : ∀ z, Tendsto (fun _n : ℕ ↦ inner ℝ u_lim z) atTop
      (nhds (inner ℝ u_lim z)) := fun z ↦ tendsto_const_nhds
  have hfixed : Tendsto (fun n ↦ inner ℝ (Ln n u_lim) u_lim) atTop
      (nhds qlim) := by
    simpa only [Ln, L, qlim] using
      timeOp_weak_lim A A_lim hA hA_lim C C_lim hC hC_lim ε hε hconv
        (fun _ ↦ u_lim) u_lim hu_const u_lim
  have hlower (n : ℕ) :
      2 * inner ℝ (Ln n (u n)) u_lim - inner ℝ (Ln n u_lim) u_lim ≤ q n := by
    have hLn := timeOp_pos (A n) (hA n) (C n) (hC n) (hself n) (hpos n)
    have hnonneg := hLn.inner_nonneg_left (u n - u_lim)
    have hsymm := hLn.inner_left_eq_inner_right (u n) u_lim
    have hsymm' : inner ℝ (Ln n (u n)) u_lim =
        inner ℝ (u n) (Ln n u_lim) := by
      simpa only [Ln] using hsymm
    have hcross' : inner ℝ (Ln n u_lim) (u n) =
        inner ℝ (Ln n (u n)) u_lim :=
      (real_inner_comm (u n) (Ln n u_lim)).trans hsymm'.symm
    change 0 ≤ inner ℝ (Ln n (u n - u_lim)) (u n - u_lim) at hnonneg
    simp only [map_sub, inner_sub_left, inner_sub_right] at hnonneg
    rw [hcross'] at hnonneg
    dsimp only [q]
    linarith
  have hrhs : Tendsto
      (fun n ↦ 2 * inner ℝ (Ln n (u n)) u_lim - inner ℝ (Ln n u_lim) u_lim)
      atTop (nhds qlim) := by
    convert (hcross.const_mul 2).sub hfixed using 1
    all_goals ring_nf
  obtain ⟨D, huD⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (u n)) fun z ↦ by
    simpa only [innerSL_apply_apply, forall_mem_range] using
      (isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto (fun n ↦ inner ℝ (u n) z) (hu z)))
  have hu_norm (n : ℕ) : ‖u n‖ ≤ D := by
    simpa only [innerSL_apply_norm] using huD n
  have hop (n : ℕ) : ‖Ln n - L‖ ≤ (ε n : ℝ) := by
    have heq : Ln n - L = timeOp (fun t ↦ A n t - A_lim t)
        ((hA n).sub hA_lim) (ε n) (hconv n) := by
      ext f
      filter_upwards [Lp.coeFn_sub (Ln n f) (L f),
        timeOp_apply_ae (A n) (hA n) (C n) (hC n) f,
        timeOp_apply_ae A_lim hA_lim C_lim hC_lim f,
        timeOp_apply_ae (fun t ↦ A n t - A_lim t)
          ((hA n).sub hA_lim) (ε n) (hconv n) f]
        with t hsub hAn hAlim hdiff
      change ((Ln n f - L f : timeL2 X T) : ℝ → X) t =
        (timeOp (fun t ↦ A n t - A_lim t) ((hA n).sub hA_lim)
          (ε n) (hconv n) f : ℝ → X) t
      rw [hsub, Pi.sub_apply, hAn, hAlim, hdiff,
        sub_apply]
    rw [heq]
    exact timeOp_norm_le _ _ _ _
  have hε_real : Tendsto (fun n ↦ (ε n : ℝ)) atTop (nhds 0) :=
    NNReal.tendsto_coe.2 hε
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1
    (Metric.isBounded_range_of_tendsto (fun n ↦ (ε n : ℝ)) hε_real)
  have hεK (n : ℕ) : (ε n : ℝ) ≤ K := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      hK (ε n : ℝ) ⟨n, rfl⟩
  have hLnorm : ‖L‖ ≤ (C_lim : ℝ) := timeOp_norm_le _ _ _ _
  have hLn_norm (n : ℕ) : ‖Ln n‖ ≤ K + (C_lim : ℝ) := by
    calc
      ‖Ln n‖ ≤ ‖Ln n - L‖ + ‖L‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Ln n - L) L
      _ ≤ K + (C_lim : ℝ) := add_le_add (hop n |>.trans (hεK n)) hLnorm
  have hD : 0 ≤ D := (norm_nonneg (u 0)).trans (hu_norm 0)
  have hOp : 0 ≤ K + (C_lim : ℝ) :=
    (norm_nonneg (Ln 0)).trans (hLn_norm 0)
  have hq_upper (n : ℕ) : q n ≤ (K + (C_lim : ℝ)) * D * D := by
    calc
      q n ≤ |inner ℝ (Ln n (u n)) (u n)| := le_abs_self _
      _ ≤ ‖Ln n (u n)‖ * ‖u n‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖Ln n‖ * ‖u n‖) * ‖u n‖ := by
        gcongr
        exact (Ln n).le_opNorm (u n)
      _ ≤ ((K + (C_lim : ℝ)) * ‖u n‖) * ‖u n‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hLn_norm n) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ((K + (C_lim : ℝ)) * D) * ‖u n‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hu_norm n) hOp)
          (norm_nonneg _)
      _ ≤ ((K + (C_lim : ℝ)) * D) * D := by
        exact mul_le_mul_of_nonneg_left (hu_norm n) (mul_nonneg hOp hD)
  have hcob : IsCoboundedUnder (· ≥ ·) atTop q :=
    isCoboundedUnder_ge_of_le atTop hq_upper
  have hliminf : qlim ≤ liminf q atTop := by
    apply le_of_forall_lt
    intro r hr
    let s : ℝ := (r + qlim) / 2
    have hrs : r < s := by dsimp only [s]; linarith
    have hslt : s < qlim := by dsimp only [s]; linarith
    have hevR : ∀ᶠ n in atTop,
        s < 2 * inner ℝ (Ln n (u n)) u_lim - inner ℝ (Ln n u_lim) u_lim :=
      (tendsto_order.1 hrhs).1 s hslt
    have hevQ : ∀ᶠ n in atTop, s ≤ q n :=
      hevR.mono fun n hn ↦ (le_of_lt hn).trans (hlower n)
    exact hrs.trans_le (le_liminf_of_le hcob hevQ)
  simpa only [q, qlim, timeQuad, Ln, L] using hliminf

theorem timeQuad_weak_unif
    (A : ℕ → ℝ → X →L[ℝ] X) (A_lim : ℝ → X →L[ℝ] X)
    (hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure T))
    (hA_lim : AEStronglyMeasurable A_lim (timeMeasure T))
    (C : ℕ → NNReal) (C_lim : NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (hC_lim : ∀ᵐ t ∂timeMeasure T, ‖A_lim t‖ ≤ (C_lim : ℝ))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ t ∂timeMeasure T, ‖A n t - A_lim t‖ ≤ δ)
    (hself : ∀ n, ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A n t))
    (hpos : ∀ n, ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A n t x) x)
    (u : ℕ → timeL2 X T) (u_lim : timeL2 X T)
    (hu : ∀ z, Tendsto (fun n ↦ inner ℝ (u n) z) atTop
      (nhds (inner ℝ u_lim z))) :
    timeQuad A_lim hA_lim C_lim hC_lim u_lim ≤
      liminf (fun n ↦ timeQuad (A n) (hA n) (C n) (hC n) (u n)) atTop := by
  let L : timeL2 X T →L[ℝ] timeL2 X T := timeOp A_lim hA_lim C_lim hC_lim
  let Ln : ℕ → timeL2 X T →L[ℝ] timeL2 X T :=
    fun n ↦ timeOp (A n) (hA n) (C n) (hC n)
  let q : ℕ → ℝ := fun n ↦ inner ℝ (Ln n (u n)) (u n)
  let qlim : ℝ := inner ℝ (L u_lim) u_lim
  have hcross : Tendsto (fun n ↦ inner ℝ (Ln n (u n)) u_lim) atTop
      (nhds qlim) := by
    simpa only [Ln, L, qlim] using
      timeOp_weak_unif A A_lim hA hA_lim C C_lim hC hC_lim hconv
        u u_lim hu u_lim
  have hu_const : ∀ z, Tendsto (fun _n : ℕ ↦ inner ℝ u_lim z) atTop
      (nhds (inner ℝ u_lim z)) := fun z ↦ tendsto_const_nhds
  have hfixed : Tendsto (fun n ↦ inner ℝ (Ln n u_lim) u_lim) atTop
      (nhds qlim) := by
    simpa only [Ln, L, qlim] using
      timeOp_weak_unif A A_lim hA hA_lim C C_lim hC hC_lim hconv
        (fun _ ↦ u_lim) u_lim hu_const u_lim
  have hlower (n : ℕ) :
      2 * inner ℝ (Ln n (u n)) u_lim - inner ℝ (Ln n u_lim) u_lim ≤ q n := by
    have hLn := timeOp_pos (A n) (hA n) (C n) (hC n) (hself n) (hpos n)
    have hnonneg := hLn.inner_nonneg_left (u n - u_lim)
    have hsymm := hLn.inner_left_eq_inner_right (u n) u_lim
    have hsymm' : inner ℝ (Ln n (u n)) u_lim =
        inner ℝ (u n) (Ln n u_lim) := by
      simpa only [Ln] using hsymm
    have hcross' : inner ℝ (Ln n u_lim) (u n) =
        inner ℝ (Ln n (u n)) u_lim :=
      (real_inner_comm (u n) (Ln n u_lim)).trans hsymm'.symm
    change 0 ≤ inner ℝ (Ln n (u n - u_lim)) (u n - u_lim) at hnonneg
    simp only [map_sub, inner_sub_left, inner_sub_right] at hnonneg
    rw [hcross'] at hnonneg
    dsimp only [q]
    linarith
  have hrhs : Tendsto
      (fun n ↦ 2 * inner ℝ (Ln n (u n)) u_lim - inner ℝ (Ln n u_lim) u_lim)
      atTop (nhds qlim) := by
    convert (hcross.const_mul 2).sub hfixed using 1
    all_goals ring_nf
  obtain ⟨D, huD⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (u n)) fun z ↦ by
    simpa only [innerSL_apply_apply, forall_mem_range] using
      (isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto (fun n ↦ inner ℝ (u n) z) (hu z)))
  have hu_norm (n : ℕ) : ‖u n‖ ≤ D := by
    simpa only [innerSL_apply_norm] using huD n
  have hD : 0 ≤ D := (norm_nonneg (u 0)).trans (hu_norm 0)
  have hLn_norm : ∀ᶠ n in atTop, ‖Ln n‖ ≤ 1 + (C_lim : ℝ) := by
    filter_upwards [hconv 1 zero_lt_one] with n hn
    have hop : ‖Ln n - L‖ ≤ 1 := by
      have heq : Ln n - L = timeOp (fun t ↦ A n t - A_lim t)
          ((hA n).sub hA_lim) 1 hn := by
        ext f
        filter_upwards [Lp.coeFn_sub (Ln n f) (L f),
          timeOp_apply_ae (A n) (hA n) (C n) (hC n) f,
          timeOp_apply_ae A_lim hA_lim C_lim hC_lim f,
          timeOp_apply_ae (fun t ↦ A n t - A_lim t)
            ((hA n).sub hA_lim) 1 hn f]
          with t hsub hAn hAlim hdiff
        change ((Ln n f - L f : timeL2 X T) : ℝ → X) t =
          (timeOp (fun t ↦ A n t - A_lim t) ((hA n).sub hA_lim)
            1 hn f : ℝ → X) t
        rw [hsub, Pi.sub_apply, hAn, hAlim, hdiff,
          sub_apply]
      rw [heq]
      simpa using timeOp_norm_le (fun t ↦ A n t - A_lim t)
        ((hA n).sub hA_lim) 1 hn
    calc
      ‖Ln n‖ ≤ ‖Ln n - L‖ + ‖L‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Ln n - L) L
      _ ≤ 1 + (C_lim : ℝ) := add_le_add hop (timeOp_norm_le _ _ _ _)
  have hOp : 0 ≤ 1 + (C_lim : ℝ) := by positivity
  have hq_upper : ∀ᶠ n in atTop, q n ≤ (1 + (C_lim : ℝ)) * D * D := by
    filter_upwards [hLn_norm] with n hn
    calc
      q n ≤ |inner ℝ (Ln n (u n)) (u n)| := le_abs_self _
      _ ≤ ‖Ln n (u n)‖ * ‖u n‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖Ln n‖ * ‖u n‖) * ‖u n‖ := by
        gcongr
        exact (Ln n).le_opNorm (u n)
      _ ≤ ((1 + (C_lim : ℝ)) * ‖u n‖) * ‖u n‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ((1 + (C_lim : ℝ)) * D) * ‖u n‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hu_norm n) hOp)
          (norm_nonneg _)
      _ ≤ ((1 + (C_lim : ℝ)) * D) * D := by
        exact mul_le_mul_of_nonneg_left (hu_norm n) (mul_nonneg hOp hD)
  have hcob : IsCoboundedUnder (· ≥ ·) atTop q :=
    isCoboundedUnder_ge_of_eventually_le atTop hq_upper
  have hliminf : qlim ≤ liminf q atTop := by
    apply le_of_forall_lt
    intro r hr
    let s : ℝ := (r + qlim) / 2
    have hrs : r < s := by dsimp only [s]; linarith
    have hslt : s < qlim := by dsimp only [s]; linarith
    have hevR : ∀ᶠ n in atTop,
        s < 2 * inner ℝ (Ln n (u n)) u_lim - inner ℝ (Ln n u_lim) u_lim :=
      (tendsto_order.1 hrhs).1 s hslt
    have hevQ : ∀ᶠ n in atTop, s ≤ q n :=
      hevR.mono fun n hn ↦ (le_of_lt hn).trans (hlower n)
    exact hrs.trans_le (le_liminf_of_le hcob hevQ)
  simpa only [q, qlim, timeQuad, Ln, L] using hliminf

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
