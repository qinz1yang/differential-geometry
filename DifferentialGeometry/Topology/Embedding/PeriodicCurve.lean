import DifferentialGeometry.Analysis.Calculus.CurveSubdivision

open Set Metric

namespace DifferentialGeometry.Topology.PeriodicCurve

theorem exists_uniform_separation
    {E : Type*} [NormedAddCommGroup E] {γ : ℝ → E}
    (hγ : Continuous γ) (hperiod : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      δ ≤ y - x → y - x ≤ 1 - δ → ε < dist (γ x) (γ y) := by
  let K : Set (ℝ × ℝ) := (Icc 0 1 ×ˢ Icc 0 1) ∩ {q | δ ≤ q.2 - q.1 ∧ q.2 - q.1 ≤ 1 - δ}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const (continuous_snd.sub continuous_fst)).inter
      (isClosed_le (continuous_snd.sub continuous_fst) continuous_const))
  have hne : ∀ q ∈ K, γ q.1 - γ q.2 ≠ 0 := by
    intro q hq heq
    have he := sub_eq_zero.mp heq
    have hxy : q.1 < q.2 := by linarith [hq.2.1]
    have hx : q.1 ∈ Ico (0 : ℝ) 1 := ⟨hq.1.1.1, hxy.trans_le hq.1.2.2⟩
    rcases lt_or_eq_of_le hq.1.2.2 with hy | hy
    · exact hxy.ne (hinj hx ⟨hq.1.2.1, hy⟩ he)
    · have hp : γ q.2 = γ 0 := by rw [hy]; simpa using hperiod 0
      have hx0 : q.1 = 0 := hinj hx (by constructor <;> norm_num) (he.trans hp)
      linarith [hq.2.2]
  obtain ⟨ε, hε, hbound⟩ := exists_pos_lt_norm_of_isCompact hK
    ((hγ.comp continuous_fst).sub (hγ.comp continuous_snd)).continuousOn hne
  exact ⟨ε, hε, fun x hx y hy hlow hhigh => by
    simpa only [dist_eq_norm, Pi.sub_apply, Function.comp_apply] using hbound (x, y) ⟨⟨hx, hy⟩, hlow, hhigh⟩⟩


private theorem exists_positive_projection_margin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E} (hv : ContinuousOn v (Icc 0 2))
    (hne : ∀ x ∈ Icc (0 : ℝ) 2, v x ≠ 0) :
    ∃ c > 0, ∃ δ > 0, δ ≤ 1 ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      ∃ L : E →L[ℝ] ℝ, ‖L‖ = 1 ∧ ∀ y ∈ Icc x (x + δ), c < L (v y) := by
  obtain ⟨c, hc, d, hd, hproj⟩ :=
    DifferentialGeometry.Analysis.exists_uniform_positive_functionals hv hne
  refine ⟨c, hc, min (d / 2) 1, lt_min (half_pos hd) zero_lt_one, min_le_right _ _, ?_⟩
  intro x hx
  obtain ⟨L, hL, hpos⟩ := hproj x ⟨hx.1, by linarith [hx.2]⟩
  refine ⟨L, hL, ?_⟩
  intro y hy
  apply hpos y
  · exact ⟨hx.1.trans hy.1, by linarith [hy.2, hx.2, min_le_right (d / 2) (1 : ℝ)]⟩
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.1)]
    linarith [hy.2, min_le_left (d / 2) (1 : ℝ)]

theorem exists_pos_forall_injOn_of_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ v : ℝ → E} (hv : Continuous v) (hd : ∀ x, HasDerivAt γ (v x) x)
    (hne : ∀ x, v x ≠ 0) (hperiod : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) :
    ∃ η > 0, ∀ {g w : ℝ → E}, (∀ x, HasDerivAt g (w x) x) → Function.Periodic g 1 →
      (∀ x, ‖g x - γ x‖ < η) → (∀ x, ‖w x - v x‖ < η) →
      InjOn g (Ico (0 : ℝ) 1) ∧ ∀ x ∈ Icc (0 : ℝ) 1, w x ≠ 0 := by
  have hγ : Continuous γ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  obtain ⟨c, hc, δ, hδ, hδ1, hproj⟩ :=
    exists_positive_projection_margin hv.continuousOn (fun x _ => hne x)
  obtain ⟨ε, hε, hsep⟩ := exists_uniform_separation hγ hperiod hinj (half_pos hδ)
  refine ⟨min (c / 2) (ε / 4), lt_min (half_pos hc) (by positivity), ?_⟩
  intro g w hgd hgperiod hclose hdclose
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
  have hprowg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ∃ L : E →L[ℝ] ℝ, ‖L‖ = 1 ∧ ∀ y ∈ Icc x (x + δ), 0 < L (w y) := by
    obtain ⟨L, hL, hpos⟩ := hproj x hx
    refine ⟨L, hL, ?_⟩
    intro y hy
    have hb := L.le_opNorm (v y - w y)
    rw [hL, one_mul, map_sub, Real.norm_eq_abs, norm_sub_rev] at hb
    have hb' := (le_abs_self (L (v y) - L (w y))).trans hb
    have hsmall := (hdclose y).trans_le (min_le_left _ _)
    linarith [hpos y hy]
  have hmono (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ∃ L : E →L[ℝ] ℝ, StrictMonoOn (fun y => L (g y)) (Icc x (x + δ)) := by
    obtain ⟨L, _, hpos⟩ := hprowg x hx
    refine ⟨L, strictMonoOn_of_deriv_pos (convex_Icc _ _) (L.continuous.comp hg).continuousOn ?_⟩
    intro y hy
    rw [interior_Icc] at hy
    change 0 < deriv (L ∘ g) y
    rw [(L.hasFDerivAt.comp_hasDerivAt y (hgd y)).deriv]
    exact hpos y (Ioo_subset_Icc_self hy)
  have hordered (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Ico (0 : ℝ) 1) (hxy : x < y) : g x ≠ g y := by
    intro heq
    by_cases hnear : y - x < δ / 2
    · obtain ⟨L, hm⟩ := hmono x ⟨hx.1, hx.2.le⟩
      have hlt := hm (show x ∈ Icc x (x + δ) from ⟨le_rfl, by linarith⟩)
        (show y ∈ Icc x (x + δ) from ⟨hxy.le, by linarith⟩) hxy
      exact hlt.ne (congrArg L heq)
    by_cases hwrap : 1 - δ / 2 < y - x
    · obtain ⟨L, hm⟩ := hmono y ⟨hy.1, hy.2.le⟩
      have hlt := hm (show y ∈ Icc y (y + δ) from ⟨le_rfl, by linarith⟩)
        (show x + 1 ∈ Icc y (y + δ) from ⟨by linarith [hx.1, hy.2], by linarith⟩)
        (by linarith [hx.1, hy.2])
      change L (g y) < L (g (x + 1)) at hlt
      rw [hgperiod x, heq] at hlt
      exact lt_irrefl _ hlt
    · have hdist := hsep x ⟨hx.1, hx.2.le⟩ y ⟨hy.1, hy.2.le⟩
        (le_of_not_gt hnear) (le_of_not_gt hwrap)
      have hxclose : dist (γ x) (g x) < ε / 4 := by
        rw [dist_comm, dist_eq_norm]
        exact (hclose x).trans_le (min_le_right _ _)
      have hyclose : dist (g y) (γ y) < ε / 4 := by
        rw [dist_eq_norm]
        exact (hclose y).trans_le (min_le_right _ _)
      have htri := dist_triangle (γ x) (g x) (γ y)
      rw [heq] at htri
      rw [heq] at hxclose
      linarith
  constructor
  · intro x hx y hy heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact hordered x hx y hy hxy heq
    · exact hordered y hy x hx hyx heq.symm
  · intro x hx
    obtain ⟨L, _, hpos⟩ := hprowg x hx
    have h := hpos x ⟨le_rfl, by linarith⟩
    intro heq
    simp only [heq, map_zero, lt_self_iff_false] at h

end DifferentialGeometry.Topology.PeriodicCurve
