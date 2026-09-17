import DifferentialGeometry.Topology.Handle.HalfBallCornerGraph

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Topology.Handle

private noncomputable def halfBallShearRawHeight (s : ℝ) : ℝ :=
  if s ≤ 1 then halfBallShearHeight s else 0

private theorem halfBallShearRawHeight_eq_max {s : ℝ}
    (hs : s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) :
    halfBallShearRawHeight s = max (halfBallShearHeight s) 0 := by
  have h1 := Icc_subset_halfBallShearHeight_domain (show (1 : ℝ) ∈ Icc 0 1 by simp)
  by_cases hh : s ≤ 1
  · rw [halfBallShearRawHeight, if_pos hh, max_eq_left]
    rw [← halfBallShearHeight_one]
    exact strictAntiOn_halfBallShearHeight.antitoneOn hs h1 hh
  · rw [halfBallShearRawHeight, if_neg hh, max_eq_right]
    rw [← halfBallShearHeight_one]
    exact strictAntiOn_halfBallShearHeight.antitoneOn h1 hs (le_of_not_ge hh)

private theorem halfBallShearRawHeight_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ halfBallShearRawHeight s := by
  by_cases hh : s ≤ 1
  · rw [halfBallShearRawHeight, if_pos hh]
    exact (halfBallShearHeight_mem_Icc ⟨hs, hh⟩).1
  · simp only [halfBallShearRawHeight, if_neg hh, le_refl]

private theorem continuousOn_halfBallShearRawHeight : ContinuousOn halfBallShearRawHeight
    (Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) := by
  have hc : ContinuousOn (fun s => max (halfBallShearHeight s) 0)
      (Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) := by
    intro s hs
    have hc' : ContinuousAt (fun s => max (halfBallShearHeight s) 0) s :=
      (contDiffOn_halfBallShearHeight.contDiffAt (isOpen_Ioo.mem_nhds hs)).continuousAt.max
        (continuousAt_const (y := (0 : ℝ)))
    exact hc'.continuousWithinAt
  apply hc.congr
  intro s hs
  exact halfBallShearRawHeight_eq_max hs

private theorem halfBallShearCorner_roof_separation_pos {s : ℝ} (hs : 0 ≤ s)
    (hdom : s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))))
    (hne : s ≠ 1) :
    0 < |(halfBallShearCornerCoordinates s (halfBallShearRawHeight s)).1 +
      (halfBallShearCornerCoordinates s (halfBallShearRawHeight s)).2| := by
  have h1 := Icc_subset_halfBallShearHeight_domain (show (1 : ℝ) ∈ Icc 0 1 by simp)
  rw [abs_pos]
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hg : 0 < halfBallShearHeight s := by
      simpa only [halfBallShearHeight_one] using strictAntiOn_halfBallShearHeight hdom h1 hh
    have ht := halfBallShearHeight_mem_Icc ⟨hs, hh.le⟩
    rw [halfBallShearRawHeight, if_pos hh.le]
    have hd : 0 < s + (1 - halfBallShearHeight s / 2) ^ 2 * (halfBallShearHeight s + 1) ^ 2 := by
      have hb : 0 < 1 - halfBallShearHeight s / 2 := by linarith [ht.2]
      have hb' : 0 < halfBallShearHeight s + 1 := by linarith
      exact add_pos_of_nonneg_of_pos hs (mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hb'))
    dsimp [halfBallShearCornerCoordinates]
    rw [halfBallShearRadiusSq_height hdom, sub_self, zero_div, add_zero]
    exact (div_pos (mul_pos (mul_pos (by norm_num) hg)
      (sq_pos_of_pos (by linarith [ht.2]))) hd).ne'
  · rw [halfBallShearRawHeight, if_neg (not_le.mpr hh)]
    norm_num only [halfBallShearCornerCoordinates, halfBallShearRadiusSq, zero_div,
      sub_zero, zero_mul, mul_zero, one_pow, zero_pow (by decide : 2 ≠ 0),
      add_zero, zero_add, mul_one]
    exact (div_neg_of_neg_of_pos (by linarith) (by linarith)).ne

private theorem continuousAt_halfBallShearCorner_pos {s t : ℝ} (hs : 0 < s) :
    ContinuousAt (fun p : ℝ × ℝ => halfBallShearCornerCoordinates p.1 p.2) (s, t) := by
  have hd : s + (1 - t / 2) ^ 2 * (t + 1) ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg hs (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne'
  unfold halfBallShearCornerCoordinates halfBallShearRadiusSq
  fun_prop (disch := exact hd)

private theorem max_halfBallShearCorner_neg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 4)) :
    max (-(halfBallShearCornerCoordinates 1 t).1) (halfBallShearCornerCoordinates 1 t).2 < 0 := by
  have hd : 0 < 1 + (1 - t / 2) ^ 2 * (t + 1) ^ 2 :=
    add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hq : halfBallShearRadiusSq t < 1 := by
    have hh := strictAntiOn_halfBallShearRadiusSq (show (0 : ℝ) ∈ Ioo (-(1 / 4)) (5 / 4) by norm_num)
      (show t ∈ Ioo (-(1 / 4)) (5 / 4) by constructor <;> linarith [ht.1, ht.2]) ht.1
    simpa only [halfBallShearRadiusSq, zero_div, sub_zero, one_pow, zero_pow (by decide : 2 ≠ 0), mul_one] using hh
  rw [max_lt_iff]
  constructor
  · exact neg_neg_of_pos (div_pos (mul_pos (mul_pos (by norm_num) ht.1)
      (sq_pos_of_pos (by linarith [ht.2]))) hd)
  · exact div_neg_of_neg_of_pos (sub_neg.mpr hq) hd

private theorem exists_roundedHalfBallShearCorner_graph_control
    {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ r ∈ Ioo 0 (min ρ (1 / 16)), ∃ a < 0, ∃ b > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ g : ℝ → ℝ,
        ContDiffOn ℝ ∞ g (Ioo (1 - 2 * r) (1 + 2 * r)) ∧
        (∀ s ∈ Ioo (1 - 2 * r) (1 + 2 * r),
          halfBallShearRawHeight s ≤ g s ∧ g s ≤ halfBallShearRawHeight s + η) ∧
        (∀ s ∈ Ioo (1 - 2 * r) (1 + 2 * r), g s ∈ Ioo a b ∧
          roundedHalfBallShearCorner ε s (g s) = 0) ∧
        (∀ s ∈ Ioo (1 - 2 * r) (1 + 2 * r), r / 2 ≤ |s - 1| → g s = halfBallShearRawHeight s) ∧
        ∀ s ∈ Ioo (1 - 2 * r) (1 + 2 * r), ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε s t = 0 ↔ t = g s) ∧
          (0 ≤ roundedHalfBallShearCorner ε s t ↔ t ≤ g s) ∧
          (0 < roundedHalfBallShearCorner ε s t ↔ t < g s) := by
  obtain ⟨R, hR, a, ha, b, hb, δ₀, hδ₀, hgraph⟩ := exists_roundedHalfBallShearCorner_graph
  let v := min b (min η (1 / 4)) / 2
  have hv : 0 < v := by dsimp [v]; positivity
  have hvb : v < b := by dsimp [v]; have := min_le_left b (min η (1 / 4)); linarith
  have hvη : v < η := by dsimp [v]; have := (min_le_right b (min η (1 / 4))).trans (min_le_left η (1 / 4)); linarith
  have hvq : v < 1 / 4 := by dsimp [v]; have := (min_le_right b (min η (1 / 4))).trans (min_le_right η (1 / 4)); linarith
  let M : ℝ → ℝ := fun s => max (-(halfBallShearCornerCoordinates s v).1)
    (halfBallShearCornerCoordinates s v).2
  have hM : ContinuousAt M 1 := by
    have hc := (continuousAt_halfBallShearCorner_pos (t := v) (by norm_num : (0 : ℝ) < 1)).comp
      (f := fun s : ℝ => (s, v)) (continuousAt_id.prodMk continuousAt_const)
    exact hc.fst.neg.max hc.snd
  have hMneg : M 1 < 0 := max_halfBallShearCorner_neg ⟨hv, hvq⟩
  let κ := -M 1 / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  let V := Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))
  have h1V : (1 : ℝ) ∈ V := Icc_subset_halfBallShearHeight_domain ⟨by norm_num, le_rfl⟩
  have hraw : ContinuousAt halfBallShearRawHeight 1 :=
    continuousOn_halfBallShearRawHeight.continuousAt (isOpen_Ioo.mem_nhds h1V)
  have hraw1 : halfBallShearRawHeight 1 = 0 := by simp [halfBallShearRawHeight]
  have hnear : ∀ᶠ s in 𝓝 (1 : ℝ),
      s ∈ Ioo (1 - R) (1 + R) ∧ 0 < s ∧ s ∈ V ∧ halfBallShearRawHeight s < v ∧ M s < -κ := by
    have hU : ∀ᶠ s in 𝓝 (1 : ℝ), s ∈ Ioo (1 - R) (1 + R) := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hpos : ∀ᶠ s in 𝓝 (1 : ℝ), 0 < s := isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)
    have hV : ∀ᶠ s in 𝓝 (1 : ℝ), s ∈ V := isOpen_Ioo.mem_nhds h1V
    have hrawlt := hraw.eventually (isOpen_Iio.mem_nhds (show halfBallShearRawHeight 1 < v by rwa [hraw1]))
    have hMlt := hM.eventually (isOpen_Iio.mem_nhds (show M 1 < -κ by dsimp [κ]; linarith))
    exact hU.and (hpos.and (hV.and (hrawlt.and hMlt)))
  obtain ⟨d, hd, hdsub⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min (min d ρ) (1 / 16) / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : 2 * r < d := by dsimp [r]; have := (min_le_left (min d ρ) (1 / 16)).trans (min_le_left d ρ); linarith
  have hrρ : r < ρ := by dsimp [r]; have := (min_le_left (min d ρ) (1 / 16)).trans (min_le_right d ρ); linarith
  have hrq : r < 1 / 16 := by dsimp [r]; have := min_le_right (min d ρ) (1 / 16); linarith
  have hdata (s : ℝ) (hs : s ∈ Icc (1 - 2 * r) (1 + 2 * r)) :
      s ∈ Ioo (1 - R) (1 + R) ∧ 0 < s ∧ s ∈ V ∧ halfBallShearRawHeight s < v ∧ M s < -κ := by
    apply hdsub
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  let S := Icc (1 - 2 * r) (1 + 2 * r) ∩ {s : ℝ | r / 2 ≤ |s - 1|}
  let sep : ℝ → ℝ := fun s => |(halfBallShearCornerCoordinates s (halfBallShearRawHeight s)).1 +
    (halfBallShearCornerCoordinates s (halfBallShearRawHeight s)).2|
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).abs))
  have hsep : ContinuousOn sep S := by
    intro s hs
    have hd := hdata s hs.1
    have hc := (continuousAt_halfBallShearCorner_pos hd.2.1).comp
      (f := fun s : ℝ => (s, halfBallShearRawHeight s))
      (continuousAt_id.prodMk (continuousOn_halfBallShearRawHeight.continuousAt
        (isOpen_Ioo.mem_nhds hd.2.2.1)))
    exact (hc.fst.add hc.snd).abs.continuousWithinAt
  obtain ⟨ζ, hζ, hζle⟩ := hS.exists_forall_le' hsep (a := (0 : ℝ)) (by
    intro s hs
    have hd := hdata s hs.1
    apply halfBallShearCorner_roof_separation_pos hd.2.1.le hd.2.2.1
    intro heq
    have haway : r / 2 ≤ |s - 1| := hs.2
    rw [heq, sub_self, abs_zero] at haway
    linarith)
  refine ⟨r, ⟨hr, lt_min hrρ hrq⟩, a, ha, b, hb, min δ₀ (min κ ζ), by positivity, ?_⟩
  intro ε hε
  obtain ⟨g, hg, hroot, hsign⟩ := hgraph ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hεκ : ε < κ := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ : ε < ζ := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall (s : ℝ) (hs : s ∈ Ioo (1 - 2 * r) (1 + 2 * r)) := hdata s (Ioo_subset_Icc_self hs)
  refine ⟨g, hg.mono (fun s hs => (hsmall s hs).1), ?_,
    (fun s hs => hroot s (hsmall s hs).1), ?_, ?_⟩
  · intro s hs
    have hh := hsmall s hs
    have ht : halfBallShearRawHeight s ∈ Icc a b :=
      ⟨ha.le.trans (halfBallShearRawHeight_nonneg hh.2.1.le), hh.2.2.2.1.le.trans hvb.le⟩
    have hzero : max (-(halfBallShearCornerCoordinates s (halfBallShearRawHeight s)).1)
        (halfBallShearCornerCoordinates s (halfBallShearRawHeight s)).2 = 0 := by
      rw [halfBallShearRawHeight_eq_max hh.2.2.1]
      exact max_halfBallShearCornerCoordinates_roof hh.2.1.le hh.2.2.1
    have hlo : halfBallShearRawHeight s ≤ g s := (hsign s hh.1 _ ht).2.1.mp (by
      change 0 ≤ Real.smoothMax ε _ _
      rw [← hzero]
      exact Real.smoothMax.max_le hε.1 _ _)
    have hu : roundedHalfBallShearCorner ε s v < 0 := by
      have hle := Real.smoothMax.le_max_add hε.1 (-(halfBallShearCornerCoordinates s v).1)
        (halfBallShearCornerCoordinates s v).2
      change roundedHalfBallShearCorner ε s v ≤ M s + ε at hle
      linarith [hh.2.2.2.2]
    have hgv : g s < v := lt_of_not_ge (fun h => hu.not_ge
      ((hsign s hh.1 v ⟨ha.le.trans hv.le, hvb.le⟩).2.1.mpr h))
    exact ⟨hlo, by linarith [halfBallShearRawHeight_nonneg hh.2.1.le]⟩
  · intro s hs haway
    have hh := hsmall s hs
    apply ((hsign s hh.1 (halfBallShearRawHeight s)
      ⟨ha.le.trans (halfBallShearRawHeight_nonneg hh.2.1.le), hh.2.2.2.1.le.trans hvb.le⟩).1.mp _).symm
    rw [halfBallShearRawHeight_eq_max hh.2.2.1]
    apply roundedHalfBallShearCorner_eq_zero_of_le hε.1 hh.2.1.le hh.2.2.1
    have hbound := hεζ.le.trans (hζle s ⟨Ioo_subset_Icc_self hs, haway⟩)
    simpa only [sep, halfBallShearRawHeight_eq_max hh.2.2.1] using hbound
  · intro s hs t ht
    exact hsign s (hsmall s hs).1 t ht

private theorem contDiffAt_halfBallShearRawHeight {s : ℝ} (hs : 0 ≤ s) (hne : s ≠ 1) :
    ContDiffAt ℝ ∞ halfBallShearRawHeight s := by
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hg := contDiffOn_halfBallShearHeight.contDiffAt (isOpen_Ioo.mem_nhds
      (Icc_subset_halfBallShearHeight_domain ⟨hs, hh.le⟩))
    apply hg.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hh] with y hy
    exact if_pos hy.le
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hh] with y hy
    exact if_neg (not_le.mpr hy)

theorem exists_roundedHalfBallCornerRoof_graph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ r ∈ Ioo 0 (min ρ (1 / 16)), ∃ a < 0, ∃ b > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
        (∀ x, halfBallShearRoof x ≤ f x ∧ f x ≤ halfBallShearRoof x + η) ∧
        (∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) →
          f x ∈ Ioo a b ∧ roundedHalfBallShearCorner ε (‖x‖ ^ 2) (f x) = 0) ∧
        (∀ x, ‖x‖ ^ 2 ∉ Ioo (1 - r) (1 + r) → f x = halfBallShearRoof x) ∧
        (∀ x, 1 + r ≤ ‖x‖ ^ 2 → f x = 0) ∧
        ∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) → ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε (‖x‖ ^ 2) t = 0 ↔ t = f x) ∧
          (0 ≤ roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t ≤ f x) ∧
          (0 < roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t < f x) := by
  classical
  obtain ⟨r, hr, a, ha, b, hb, δ, hδ, hgraph⟩ :=
    exists_roundedHalfBallShearCorner_graph_control hρ hη
  refine ⟨r, hr, a, ha, b, hb, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨g, hg, hbounds, hroot, heq, hsign⟩ := hgraph ε hε
  let f : E → ℝ := fun x => if ‖x‖ ^ 2 ∈ Ioo (1 - r) (1 + r) then g (‖x‖ ^ 2)
    else halfBallShearRawHeight (‖x‖ ^ 2)
  have hsub : Ioo (1 - r) (1 + r) ⊆ Ioo (1 - 2 * r) (1 + 2 * r) := by
    intro s hs
    exact ⟨by linarith [hs.1, hr.1], by linarith [hs.2, hr.1]⟩
  have hraw (x : E) : halfBallShearRawHeight (‖x‖ ^ 2) = halfBallShearRoof x := rfl
  have hfar (x : E) (hx : r / 2 ≤ |‖x‖ ^ 2 - 1|) : f x = halfBallShearRawHeight (‖x‖ ^ 2) := by
    by_cases hh : ‖x‖ ^ 2 ∈ Ioo (1 - r) (1 + r)
    · exact (if_pos hh).trans (heq _ (hsub hh) hx)
    · exact if_neg hh
  have hfg (x : E) (hx : ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r)) :
      f x = g (‖x‖ ^ 2) := by
    by_cases hh : ‖x‖ ^ 2 ∈ Ioo (1 - r) (1 + r)
    · exact if_pos hh
    · have haway : r / 2 ≤ |‖x‖ ^ 2 - 1| := by
        have hh' : r ≤ |‖x‖ ^ 2 - 1| := by
          by_contra h
          have hlt := abs_lt.mp (lt_of_not_ge h)
          exact hh ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
        linarith [hr.1]
      exact (if_neg hh).trans (heq _ hx haway).symm
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : ‖x‖ ^ 2 ∈ Ioo (1 - r) (1 + r)
    · have hgc := hg.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))
      apply (hgc.comp x (contDiff_norm_sq ℝ).contDiffAt).congr_of_eventuallyEq
      filter_upwards [((continuous_norm.pow 2).isOpen_preimage _ isOpen_Ioo).mem_nhds hx] with y hy
      exact if_pos hy
    · have haway : r / 2 < |‖x‖ ^ 2 - 1| := by
        have hh : r ≤ |‖x‖ ^ 2 - 1| := by
          by_contra h
          have hlt := abs_lt.mp (lt_of_not_ge h)
          exact hx ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
        linarith [hr.1]
      have hne : ‖x‖ ^ 2 ≠ 1 := by intro hh; rw [hh, sub_self, abs_zero] at haway; linarith [hr.1]
      have hc := (contDiffAt_halfBallShearRawHeight (sq_nonneg ‖x‖) hne).comp x
        (contDiff_norm_sq ℝ).contDiffAt
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const (((continuous_norm.pow 2).sub continuous_const).abs)).mem_nhds haway]
        with y hy
      exact hfar y hy.le
  · intro x
    by_cases hx : ‖x‖ ^ 2 ∈ Ioo (1 - r) (1 + r)
    · simpa only [f, if_pos hx, hraw] using hbounds _ (hsub hx)
    · simp only [f, if_neg hx, hraw, le_refl, true_and]
      linarith
  · intro x hx
    rw [hfg x hx]
    exact hroot _ hx
  · intro x hx
    exact if_neg hx
  · intro x hx
    have hnot : ‖x‖ ^ 2 ∉ Ioo (1 - r) (1 + r) := fun hh => not_lt_of_ge hx hh.2
    rw [show f x = halfBallShearRawHeight (‖x‖ ^ 2) from if_neg hnot]
    exact if_neg (by linarith [hr.1])
  · intro x hx t ht
    simpa only [hfg x hx] using hsign _ hx t ht

theorem exists_roundedHalfBallCornerRoof
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ r ∈ Ioo 0 (min ρ (1 / 16)), ∃ a < 0, ∃ b > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
        (∀ x, halfBallShearRoof x ≤ f x ∧ f x ≤ halfBallShearRoof x + η) ∧
        (∀ x, ‖x‖ ^ 2 ∉ Ioo (1 - r) (1 + r) → f x = halfBallShearRoof x) ∧
        (∀ x, 1 + r ≤ ‖x‖ ^ 2 → f x = 0) ∧
        ∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) → ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε (‖x‖ ^ 2) t = 0 ↔ t = f x) ∧
          (0 ≤ roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t ≤ f x) ∧
          (0 < roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t < f x) := by
  obtain ⟨r, hr, a, ha, b, hb, δ, hδ, hroof⟩ := exists_roundedHalfBallCornerRoof_graph (E := E) hρ hη
  refine ⟨r, hr, a, ha, b, hb, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨f, hf, hbounds, _, heq, hzero, hsign⟩ := hroof ε hε
  exact ⟨f, hf, hbounds, heq, hzero, hsign⟩

theorem exists_roundedHalfBallCornerRoof_graph_in_open
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (hP : PartialDiffeomorph.halfBallShear ''
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ O)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r ∈ Ioo 0 (min ρ (1 / 16)), ∃ a < 0, ∃ b > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        (∀ x, halfBallShearRoof x ≤ f x) ∧
        (∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) →
          f x ∈ Ioo a b ∧ roundedHalfBallShearCorner ε (‖x‖ ^ 2) (f x) = 0) ∧
        (∀ x, ‖x‖ ^ 2 ∉ Ioo (1 - r) (1 + r) → f x = halfBallShearRoof x) ∧
        (∀ x, 1 + r ≤ ‖x‖ ^ 2 → f x = 0) ∧
        ({p : E × ℝ | ‖p.1‖ ^ 2 ≤ 1 + r ∧ p.2 ∈ Icc 0 (f p.1)} ⊆ O) ∧
        ∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) → ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε (‖x‖ ^ 2) t = 0 ↔ t = f x) ∧
          (0 ≤ roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t ≤ f x) ∧
          (0 < roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t < f x) := by
  obtain ⟨η, hη, hband⟩ := exists_halfBallShearRoof_band_subset hO hP
  obtain ⟨r, hr, a, ha, b, hb, δ, hδ, hroof⟩ :=
    exists_roundedHalfBallCornerRoof_graph (E := E) (lt_min hρ hη) hη
  have hrρ : r < ρ := (hr.2.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hrη : r < η := (hr.2.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  refine ⟨r, ⟨hr.1, lt_min hrρ (hr.2.trans_le (min_le_right _ _))⟩,
    a, ha, b, hb, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨f, hf, hbounds, hroot, heq, hzero, hsign⟩ := hroof ε hε
  have hsupport : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) 2)
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra hh
    have hn : 2 < ‖x‖ := lt_of_not_ge hh
    have hlow : 1 + r ≤ ‖x‖ ^ 2 := by
      have hh := hr.2.trans_le (min_le_right _ _)
      nlinarith
    exact hx (hzero x hlow)
  refine ⟨f, hf, hsupport, fun x => (hbounds x).1, hroot, heq, hzero, ?_, hsign⟩
  intro p hp
  apply hband
  exact ⟨by linarith [hp.1], hp.2.1, hp.2.2.trans (hbounds p.1).2⟩

theorem exists_roundedHalfBallCornerRoof_in_open
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (hP : PartialDiffeomorph.halfBallShear ''
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ O)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r ∈ Ioo 0 (min ρ (1 / 16)), ∃ a < 0, ∃ b > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        (∀ x, halfBallShearRoof x ≤ f x) ∧
        (∀ x, ‖x‖ ^ 2 ∉ Ioo (1 - r) (1 + r) → f x = halfBallShearRoof x) ∧
        (∀ x, 1 + r ≤ ‖x‖ ^ 2 → f x = 0) ∧
        ({p : E × ℝ | ‖p.1‖ ^ 2 ≤ 1 + r ∧ p.2 ∈ Icc 0 (f p.1)} ⊆ O) ∧
        ∀ x, ‖x‖ ^ 2 ∈ Ioo (1 - 2 * r) (1 + 2 * r) → ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε (‖x‖ ^ 2) t = 0 ↔ t = f x) ∧
          (0 ≤ roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t ≤ f x) ∧
          (0 < roundedHalfBallShearCorner ε (‖x‖ ^ 2) t ↔ t < f x) := by
  obtain ⟨r, hr, a, ha, b, hb, δ, hδ, hroof⟩ :=
    exists_roundedHalfBallCornerRoof_graph_in_open hO hP hρ
  refine ⟨r, hr, a, ha, b, hb, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨f, hf, hsupport, hbounds, _, heq, hzero, hband, hsign⟩ := hroof ε hε
  exact ⟨f, hf, hsupport, hbounds, heq, hzero, hband, hsign⟩

end DifferentialGeometry.Topology.Handle
