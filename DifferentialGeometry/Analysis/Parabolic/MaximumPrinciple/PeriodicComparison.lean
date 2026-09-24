import Mathlib.Analysis.Calculus.DerivativeTest

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic

theorem IsLocalMin.second_deriv_nonneg {f : ℝ → ℝ} {x₀ a b : ℝ}
    (hmin : IsLocalMin f x₀) (hf : HasDerivAt f b x₀) (h : HasDerivAt (deriv f) a x₀) :
    0 ≤ a := by
  have hb : b = 0 := hmin.hasDerivAt_eq_zero hf
  by_contra hneg
  push Not at hneg
  have h0 : deriv f x₀ = 0 := by rw [← hb]; exact hf.deriv
  have hslope : Tendsto (fun y => deriv f y / (y - x₀)) (𝓝[≠] x₀) (𝓝 a) := by
    have h' := (hasDerivAt_iff_tendsto_slope.mp h)
    change Tendsto (fun y => slope (deriv f) x₀ y) (𝓝[≠] x₀) (𝓝 a) at h'
    simpa only [slope_def_field, h0, sub_zero] using h'
  have hlt : ∀ᶠ y in 𝓝[≠] x₀, deriv f y / (y - x₀) < 0 :=
    hslope.eventually (eventually_lt_nhds hneg)
  have hleft : ∀ᶠ y in 𝓝[<] x₀, 0 < deriv f y := by
    filter_upwards [nhdsLT_le_nhdsNE _ hlt, self_mem_nhdsWithin] with y hy hyx
    have hyx' : y - x₀ < 0 := sub_neg.mpr hyx
    have hprod : 0 < (deriv f y / (y - x₀)) * (y - x₀) := mul_pos_of_neg_of_neg hy hyx'
    rwa [div_mul_cancel₀ _ (ne_of_lt hyx')] at hprod
  obtain ⟨δ, hδx, hδ⟩ := (nhdsLT_basis (x₀ : ℝ)).eventually_iff.mp hleft
  have hcont : ContinuousOn f (Ioc δ x₀) := by
    intro y hy
    rcases eq_or_lt_of_le hy.2 with hy' | hy'
    · subst hy'
      exact hf.continuousAt.continuousWithinAt
    · have hd : DifferentiableAt ℝ f y :=
        differentiableAt_of_deriv_ne_zero (ne_of_gt (hδ ⟨hy.1, hy'⟩))
      exact hd.continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Ioc δ x₀) :=
    strictMonoOn_of_deriv_pos (convex_Ioc δ x₀) hcont (by
      intro y hy
      rw [interior_Ioc] at hy
      exact hδ hy)
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hmin
  have hm : 0 < min (x₀ - δ) ε := lt_min (sub_pos.mpr hδx) hε
  have hy_mem : x₀ - min (x₀ - δ) ε / 2 ∈ Ioc δ x₀ :=
    ⟨by linarith [min_le_left (x₀ - δ) ε], by linarith⟩
  have hx_mem : x₀ ∈ Ioc δ x₀ := ⟨hδx, le_rfl⟩
  have hlt2 : f (x₀ - min (x₀ - δ) ε / 2) < f x₀ :=
    hmono hy_mem hx_mem (by linarith)
  have hclose : x₀ - min (x₀ - δ) ε / 2 ∈ Metric.ball x₀ ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith [min_le_right (x₀ - δ) ε]
  exact absurd (hε' hclose) (not_le.mpr hlt2)

theorem deriv_nonpos_of_eventually_le_left {f : ℝ → ℝ} {x : ℝ}
    (hdiff : DifferentiableAt ℝ f x) (hmin : ∀ᶠ y in 𝓝[<] x, f x ≤ f y) :
    deriv f x ≤ 0 := by
  have hslope : Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[≠] x) (𝓝 (deriv f x)) := by
    have h' := hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt
    change Tendsto (fun y => slope f x y) (𝓝[≠] x) (𝓝 (deriv f x)) at h'
    simpa only [slope_def_field] using h'
  have hle : ∀ᶠ y in 𝓝[<] x, (f y - f x) / (y - x) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin, hmin] with y hyx hy
    exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) (sub_neg.mpr hyx).le
  exact le_of_tendsto (hslope.mono_left (nhdsLT_le_nhdsNE x)) hle

theorem add_int_period {w : ℝ → ℝ → ℝ} (hper : ∀ x t, w (x + 1) t = w x t) :
    ∀ (n : ℤ) (x t : ℝ), w (x + ((n : ℤ) : ℝ)) t = w x t := by
  intro n
  induction n using Int.induction_on with
  | zero => intro x t; simp
  | succ k ih =>
      intro x t
      have h2 : x + (((k : ℤ) + 1 : ℤ) : ℝ) = (x + ((k : ℤ) : ℝ)) + 1 := by
        push_cast; ring
      rw [h2, hper, ih]
  | pred k ih =>
      intro x t
      have h2 : x + (((-(k : ℤ) - 1 : ℤ)) : ℝ) = (x + (((-(k : ℤ)) : ℤ) : ℝ)) - 1 := by
        push_cast; ring
      have hstep : w (x + (((-(k : ℤ)) : ℤ) : ℝ) - 1) t =
          w (x + (((-(k : ℤ)) : ℤ) : ℝ)) t := by
        have h := (hper (x + (((-(k : ℤ)) : ℤ) : ℝ) - 1) t).symm
        have h5 : x + (((-(k : ℤ)) : ℤ) : ℝ) - 1 + 1 =
            x + (((-(k : ℤ)) : ℤ) : ℝ) := by ring
        rwa [h5] at h
      rw [h2, hstep, ih]

theorem periodic_nonneg_of_nonnegative_minimum_derivative
    {w : ℝ → ℝ → ℝ} {s v : ℝ} (hsv : s < v)
    (hper : ∀ x t, w (x + 1) t = w x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, 0 ≤ w x s)
    (htdiff : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => w x τ) t)
    (hmin_deriv : ∀ x t, t ∈ Ioo s v → IsLocalMin (fun y => w y t) x →
      0 ≤ deriv (fun τ => w x τ) t) :
    ∀ x t, t ∈ Icc s v → 0 ≤ w x t := by
  have hslice : ∀ (z : ℝ), z ∈ Icc (0 : ℝ) 1 → ∀ T : ℝ,
      (∀ y ∈ Icc (0 : ℝ) 1, w z T ≤ w y T) → IsLocalMin (fun y => w y T) z := by
    intro z hz T hmin
    refine IsMinOn.isLocalMin ?_ (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 2))
    change ∀ y ∈ Metric.ball z (1 / 2), w z T ≤ w y T
    intro y hy
    have hdist : |y - z| < 1 / 2 := by
      have h1 := Metric.mem_ball.mp hy
      rwa [dist_eq_norm, Real.norm_eq_abs] at h1
    have hlt := abs_lt.mp hdist
    by_cases hy0 : y < 0
    · have hy1 : y + 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hlt.1, hz.1], by linarith⟩
      rw [(hper y T).symm]
      exact hmin (y + 1) hy1
    · push Not at hy0
      by_cases hy1 : y ≤ 1
      · exact hmin y ⟨hy0, hy1⟩
      · push Not at hy1
        have hy2 : y - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hlt.2, hz.2]⟩
        have heq : w y T = w (y - 1) T := by
          have h2 : w y T = w ((y - 1) + 1) T := by
            have h5 : (y - 1) + 1 = y := by ring
            rw [h5]
          exact h2.trans (hper (y - 1) T)
        rw [heq]
        exact hmin (y - 1) hy2
  have hcore : ∀ T ∈ Ioo s v, ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ w z T := by
    intro T hT z hz
    by_contra hneg
    push Not at hneg
    have hTs : 0 < T - s := sub_pos.mpr hT.1
    set eps : ℝ := -w z T / (2 * (T - s)) with heps
    have heps_pos : 0 < eps := by
      rw [heps]; exact div_pos (by linarith) (by linarith)
    have heps_mul : eps * (T - s) = -w z T / 2 := by
      rw [heps]
      field_simp
    have hkey : w z T + eps * (T - s) < 0 := by rw [heps_mul]; linarith
    set F : ℝ × ℝ → ℝ := fun p => w p.1 p.2 + eps * (p.2 - s) with hF
    have hcontF : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc s T) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc s T) :=
        hcont.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hT.2.le⟩)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => eps * (p.2 - s))
          (Icc (0 : ℝ) 1 ×ˢ Icc s T) :=
        (continuous_const.mul (continuous_snd.sub continuous_const)).continuousOn
      have hFeq : F = (fun p : ℝ × ℝ => w p.1 p.2) + fun p => eps * (p.2 - s) := by
        funext p
        simp only [hF, Pi.add_apply]
      rw [hFeq]
      exact h1.add h2
    have hne : (Icc (0 : ℝ) 1 ×ˢ Icc s T).Nonempty :=
      ⟨(0, s), ⟨⟨le_refl 0, zero_le_one⟩, ⟨le_refl s, hT.1.le⟩⟩⟩
    obtain ⟨p₀, hp₀K, hp₀min⟩ :=
      (isCompact_Icc.prod isCompact_Icc).exists_isMinOn hne hcontF
    obtain ⟨x₀, t₀⟩ := p₀
    have hpK : x₀ ∈ Icc (0 : ℝ) 1 ∧ t₀ ∈ Icc s T := by
      have h1 := hp₀K
      rwa [mem_prod] at h1
    have hminK : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc s T, F (x₀, t₀) ≤ F q := by
      have h1 := hp₀min
      rwa [IsMinOn, IsMinFilter, eventually_principal] at h1
    have hval : w x₀ t₀ + eps * (t₀ - s) ≤ w z T + eps * (T - s) := by
      have h1 := hminK (z, T) ⟨hz, hT.1.le, le_rfl⟩
      rwa [hF] at h1
    have hnegmin : w x₀ t₀ + eps * (t₀ - s) < 0 := lt_of_le_of_lt hval hkey
    have ht₀pos : s < t₀ := by
      rcases lt_or_eq_of_le hpK.2.1 with h | h
      · exact h
      · exfalso
        have h1 : w x₀ s < 0 := by
          have h2 := hnegmin
          rw [← h] at h2
          simpa using h2
        linarith [hinit x₀]
    have ht₀lt : t₀ < v := lt_of_le_of_lt hpK.2.2 hT.2
    have ht₀mem : t₀ ∈ Ioo s v := ⟨ht₀pos, ht₀lt⟩
    have hmin_x : IsLocalMin (fun y => w y t₀) x₀ :=
      hslice x₀ hpK.1 t₀ (fun y hy => by
        have h1 := hminK (y, t₀) ⟨hy, ht₀pos.le, hpK.2.2⟩
        rw [hF] at h1
        linarith)
    have hder : 0 ≤ deriv (fun τ => w x₀ τ) t₀ := hmin_deriv x₀ t₀ ht₀mem hmin_x
    have hleftmin : ∀ᶠ τ in 𝓝[<] t₀,
        (fun τ => w x₀ τ + eps * (τ - s)) t₀ ≤
          (fun τ => w x₀ τ + eps * (τ - s)) τ := by
      filter_upwards [Ioo_mem_nhdsLT ht₀pos] with τ hτ
      have h1 := hminK (x₀, τ) ⟨hpK.1, hτ.1.le, le_of_lt (lt_of_lt_of_le hτ.2 hpK.2.2)⟩
      rw [hF] at h1
      linarith
    have hd : HasDerivAt (fun τ => w x₀ τ + eps * (τ - s))
        (deriv (fun τ => w x₀ τ) t₀ + eps) t₀ :=
      ((htdiff x₀ t₀ ht₀mem).hasDerivAt).add
        (by simpa using ((hasDerivAt_id t₀).sub_const s).const_mul eps)
    have hle0 : deriv (fun τ => w x₀ τ + eps * (τ - s)) t₀ ≤ 0 :=
      deriv_nonpos_of_eventually_le_left hd.differentiableAt hleftmin
    rw [hd.deriv] at hle0
    linarith
  have hclosed : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ w z v := by
    intro z hz
    set T : ℕ → ℝ := fun n => v - (v - s) / (2 * ((n : ℝ) + 1)) with hTdef
    have hTmem : ∀ n : ℕ, T n ∈ Ioo s v := by
      intro n
      have hden : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        linarith
      have hle : (v - s) / (2 * ((n : ℝ) + 1)) ≤ (v - s) / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))]
        have h0 : (0 : ℝ) ≤ v - s := sub_nonneg.mpr hsv.le
        have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have h2 := mul_le_mul_of_nonneg_left h1 h0
        linarith
      have h1 : 0 < (v - s) / (2 * ((n : ℝ) + 1)) :=
        div_pos (sub_pos.mpr hsv) (by positivity)
      refine ⟨?_, ?_⟩ <;> simp only [hTdef]
      · linarith
      · linarith
    have hTlim : Tendsto T atTop (𝓝 v) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h3 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h1
      have h2 : Tendsto (fun n : ℕ => (v - s) / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop h3
      have h4 : Tendsto (fun n : ℕ => v - (v - s) / (2 * ((n : ℝ) + 1))) atTop (𝓝 v) := by
        simpa using tendsto_const_nhds.sub h2
      simpa only [hTdef] using h4
    have hTend : Tendsto (fun n : ℕ => (z, T n)) atTop
        (𝓝[Icc (0 : ℝ) 1 ×ˢ Icc s v] (z, v)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · rw [nhds_prod_eq]
        exact tendsto_const_nhds.prodMk hTlim
      · refine Eventually.of_forall fun n => ?_
        change z ∈ Icc (0 : ℝ) 1 ∧ T n ∈ Icc s v
        exact ⟨hz, (hTmem n).1.le, (hTmem n).2.le⟩
    have hcw : ContinuousWithinAt (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v)
        (z, v) := hcont (z, v) ⟨hz, hsv.le, le_rfl⟩
    have hcomp : Tendsto (fun n : ℕ => w z (T n)) atTop (𝓝 (w z v)) := hcw.tendsto.comp hTend
    have hnn : ∀ᶠ n : ℕ in atTop, 0 ≤ w z (T n) :=
      Eventually.of_forall fun n => hcore _ (hTmem n) z hz
    exact ge_of_tendsto hcomp hnn
  intro x t ht
  have hx1 : x - ((⌊x⌋ : ℤ) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le x), by have := Int.lt_floor_add_one x; linarith⟩
  have hper' : w x t = w (x - ((⌊x⌋ : ℤ) : ℝ)) t := by
    have h := add_int_period hper ⌊x⌋ (x - ((⌊x⌋ : ℤ) : ℝ)) t
    have h5 : x - ((⌊x⌋ : ℤ) : ℝ) + (((⌊x⌋ : ℤ)) : ℝ) = x := by ring
    rw [h5] at h
    exact h
  rw [hper']
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · rcases lt_or_eq_of_le ht.1 with hlt' | heq'
    · exact hcore t ⟨hlt', hlt⟩ _ hx1
    · rw [← heq']; exact hinit _
  · rw [heq]; exact hclosed _ hx1

end DifferentialGeometry.Analysis.Parabolic
