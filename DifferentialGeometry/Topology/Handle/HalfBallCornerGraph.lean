import DifferentialGeometry.Topology.Handle.HalfBallShear
import DifferentialGeometry.Topology.Handle.HalfBallInversion
import DifferentialGeometry.Analysis.Calculus.Inverse.MonotoneGraph

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable def halfBallShearCornerCoordinates (s t : ℝ) : ℝ × ℝ :=
  (4 * t * (1 - t / 2) ^ 2 / (s + (1 - t / 2) ^ 2 * (t + 1) ^ 2),
    (halfBallShearRadiusSq t - s) / (s + (1 - t / 2) ^ 2 * (t + 1) ^ 2))

private noncomputable def halfBallShearCornerDenom (s t : ℝ) : ℝ :=
  s + (1 - t / 2) ^ 2 * (t + 1) ^ 2

private noncomputable def halfBallShearCornerDenomDeriv (t : ℝ) : ℝ :=
  -(1 - t / 2) * (t + 1) ^ 2 + 2 * (1 - t / 2) ^ 2 * (t + 1)

private noncomputable def halfBallShearCornerDeriv (s t : ℝ) : ℝ × ℝ :=
  (((4 * (1 - t / 2) ^ 2 - 4 * t * (1 - t / 2)) * halfBallShearCornerDenom s t -
      4 * t * (1 - t / 2) ^ 2 * halfBallShearCornerDenomDeriv t) /
      (halfBallShearCornerDenom s t) ^ 2,
    (-(1 - t / 2) * (1 + 2 * t - 2 * t ^ 2) * halfBallShearCornerDenom s t -
      (halfBallShearRadiusSq t - s) * halfBallShearCornerDenomDeriv t) /
      (halfBallShearCornerDenom s t) ^ 2)

private theorem hasDerivAt_halfBallShearCornerDenom (s t : ℝ) :
    HasDerivAt (halfBallShearCornerDenom s) (halfBallShearCornerDenomDeriv t) t := by
  have hb := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const 2)
  have h := (((hb.pow 2).mul (((hasDerivAt_id t).add_const 1).pow 2)).const_add s)
  convert! h using 1
  norm_num [halfBallShearCornerDenom, halfBallShearCornerDenomDeriv]
  ring

private theorem hasDerivAt_halfBallShearCornerCoordinates {s t : ℝ}
    (h : halfBallShearCornerDenom s t ≠ 0) :
    HasDerivAt (fun r => (halfBallShearCornerCoordinates s r).1)
      (halfBallShearCornerDeriv s t).1 t ∧
    HasDerivAt (fun r => (halfBallShearCornerCoordinates s r).2)
      (halfBallShearCornerDeriv s t).2 t := by
  have hb := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const 2)
  have hn := (((hasDerivAt_id t).const_mul 4).mul (hb.pow 2))
  have hd := hasDerivAt_halfBallShearCornerDenom s t
  constructor
  · convert! hn.div hd h using 1
    norm_num [halfBallShearCornerCoordinates, halfBallShearCornerDeriv]
    ring
  · exact ((hasDerivAt_halfBallShearRadiusSq t).sub_const s).div hd h

private theorem contDiffOn_halfBallShearCornerCoordinates :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => halfBallShearCornerCoordinates p.1 p.2)
      {p | halfBallShearCornerDenom p.1 p.2 ≠ 0} := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => halfBallShearCornerDenom p.1 p.2) := by
    unfold halfBallShearCornerDenom
    fun_prop
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 4 * p.2 * (1 - p.2 / 2) ^ 2) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => halfBallShearRadiusSq p.2 - p.1) :=
    (contDiff_halfBallShearRadiusSq.comp contDiff_snd).sub contDiff_fst
  exact (h1.contDiffOn.div hd.contDiffOn (fun _ h => h)).prodMk
    (h2.contDiffOn.div hd.contDiffOn (fun _ h => h))

private theorem continuousAt_halfBallShearCornerDeriv :
    ContinuousAt (fun p : ℝ × ℝ => halfBallShearCornerDeriv p.1 p.2) (1, 0) := by
  unfold halfBallShearCornerDeriv halfBallShearCornerDenom halfBallShearCornerDenomDeriv
    halfBallShearRadiusSq
  fun_prop (disch := norm_num)

private theorem exists_halfBallShearCornerCoordinates_deriv :
    ∃ r > 0, r < 1 ∧ ∀ s ∈ Ioo (1 - r) (1 + r), ∀ t ∈ Ioo (-r) r,
      0 < halfBallShearCornerDenom s t ∧
      0 < (halfBallShearCornerDeriv s t).1 ∧
      (halfBallShearCornerDeriv s t).2 < 0 := by
  have hd : Continuous (fun p : ℝ × ℝ => halfBallShearCornerDenom p.1 p.2) := by
    unfold halfBallShearCornerDenom
    fun_prop
  have hnh : ∀ᶠ p : ℝ × ℝ in 𝓝 (1, 0),
      0 < halfBallShearCornerDenom p.1 p.2 ∧
      0 < (halfBallShearCornerDeriv p.1 p.2).1 ∧
      (halfBallShearCornerDeriv p.1 p.2).2 < 0 := by
    have h1 := (hd.continuousAt (x := (1, 0))).eventually (isOpen_Ioi.mem_nhds
      (show 0 < halfBallShearCornerDenom 1 0 by norm_num [halfBallShearCornerDenom]))
    have h2 := continuousAt_halfBallShearCornerDeriv.fst.eventually (isOpen_Ioi.mem_nhds
      (show 0 < (halfBallShearCornerDeriv 1 0).1 by
        norm_num [halfBallShearCornerDeriv, halfBallShearCornerDenom, halfBallShearCornerDenomDeriv]))
    have h3 := continuousAt_halfBallShearCornerDeriv.snd.eventually (isOpen_Iio.mem_nhds
      (show (halfBallShearCornerDeriv 1 0).2 < 0 by
        norm_num [halfBallShearCornerDeriv, halfBallShearCornerDenom, halfBallShearCornerDenomDeriv,
          halfBallShearRadiusSq]))
    exact h1.and (h2.and h3)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnh
  refine ⟨min r 1 / 2, by positivity, by have := min_le_right r 1; linarith, ?_⟩
  intro s hs t ht
  apply hball (y := (s, t))
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero]
  constructor
  · rw [abs_lt]
    have := min_le_left r 1
    constructor <;> linarith [hs.1, hs.2]
  · rw [abs_lt]
    have := min_le_left r 1
    constructor <;> linarith [ht.1, ht.2]

noncomputable def roundedHalfBallShearCorner (ε s t : ℝ) : ℝ :=
  Real.smoothMax ε (-(halfBallShearCornerCoordinates s t).1)
    (halfBallShearCornerCoordinates s t).2

theorem roundedHalfBallShearCorner_nonpos_iff {ε : ℝ} (hε : ε ≠ 0) (s t : ℝ) :
    roundedHalfBallShearCorner ε s t ≤ 0 ↔
      Real.smoothAbs ε ((halfBallShearCornerCoordinates s t).1 +
        (halfBallShearCornerCoordinates s t).2) ≤
      (halfBallShearCornerCoordinates s t).1 - (halfBallShearCornerCoordinates s t).2 := by
  unfold roundedHalfBallShearCorner Real.smoothMax
  rw [show -(halfBallShearCornerCoordinates s t).1 - (halfBallShearCornerCoordinates s t).2 =
    -((halfBallShearCornerCoordinates s t).1 + (halfBallShearCornerCoordinates s t).2) by ring,
    Real.smoothAbs.neg hε]
  constructor <;> intro h <;> linarith

theorem roundedHalfBallShearCorner_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) (s t : ℝ) :
    roundedHalfBallShearCorner ε s t = 0 ↔
      Real.smoothAbs ε ((halfBallShearCornerCoordinates s t).1 +
        (halfBallShearCornerCoordinates s t).2) =
      (halfBallShearCornerCoordinates s t).1 - (halfBallShearCornerCoordinates s t).2 := by
  unfold roundedHalfBallShearCorner Real.smoothMax
  rw [show -(halfBallShearCornerCoordinates s t).1 - (halfBallShearCornerCoordinates s t).2 =
    -((halfBallShearCornerCoordinates s t).1 + (halfBallShearCornerCoordinates s t).2) by ring,
    Real.smoothAbs.neg hε]
  constructor <;> intro h <;> linarith

private theorem contDiffOn_roundedHalfBallShearCorner (ε : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => roundedHalfBallShearCorner ε p.1 p.2)
      {p | halfBallShearCornerDenom p.1 p.2 ≠ 0} := by
  exact (Real.smoothMax.contDiff ε).comp_contDiffOn
    (contDiffOn_halfBallShearCornerCoordinates.fst.neg.prodMk
      contDiffOn_halfBallShearCornerCoordinates.snd)

private theorem deriv_roundedHalfBallShearCorner_neg {s t : ℝ}
    (hd : halfBallShearCornerDenom s t ≠ 0)
    (h1 : 0 < (halfBallShearCornerDeriv s t).1)
    (h2 : (halfBallShearCornerDeriv s t).2 < 0) (ε : ℝ) :
    deriv (roundedHalfBallShearCorner ε s) t < 0 := by
  obtain ⟨hu, hv⟩ := hasDerivAt_halfBallShearCornerCoordinates hd
  exact Real.smoothMax.deriv_comp_neg hu.neg.differentiableAt hv.differentiableAt
    (by rw [hu.neg.deriv]; exact neg_neg_of_pos h1) (by rwa [hv.deriv]) ε

private theorem halfBallShearCornerCoordinates_continuousAt {s t : ℝ}
    (h : halfBallShearCornerDenom s t ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => halfBallShearCornerCoordinates p.1 p.2) (s, t) := by
  unfold halfBallShearCornerCoordinates halfBallShearRadiusSq
  unfold halfBallShearCornerDenom at h
  fun_prop (disch := exact h)

theorem exists_roundedHalfBallShearCorner_graph :
    ∃ r > 0, ∃ a < 0, ∃ b > 0, ∃ δ > 0,
      ∀ ε ∈ Ioo 0 δ, ∃ g : ℝ → ℝ,
        ContDiffOn ℝ ∞ g (Ioo (1 - r) (1 + r)) ∧
        (∀ s ∈ Ioo (1 - r) (1 + r), g s ∈ Ioo a b ∧
          roundedHalfBallShearCorner ε s (g s) = 0) ∧
        ∀ s ∈ Ioo (1 - r) (1 + r), ∀ t ∈ Icc a b,
          (roundedHalfBallShearCorner ε s t = 0 ↔ t = g s) ∧
          (0 ≤ roundedHalfBallShearCorner ε s t ↔ t ≤ g s) ∧
          (0 < roundedHalfBallShearCorner ε s t ↔ t < g s) := by
  obtain ⟨r, hr, hr1, hderiv⟩ := exists_halfBallShearCornerCoordinates_deriv
  let a := -r / 2
  let b := r / 2
  have ha : a ∈ Ioo (-r) r := ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  have hb : b ∈ Ioo (-r) r := ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  have ha0 : a < 0 := by dsimp [a]; linarith
  have hb0 : 0 < b := by dsimp [b]; linarith
  have h10 : (1 : ℝ) ∈ Ioo (1 - r) (1 + r) := ⟨by linarith, by linarith⟩
  have h00 : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hanti1 : StrictAntiOn (fun t => -(halfBallShearCornerCoordinates 1 t).1)
      (Ioo (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro t ht
      exact ((hasDerivAt_halfBallShearCornerCoordinates
        (hderiv 1 h10 t ht).1.ne').1.neg.continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      change deriv (-(fun t => (halfBallShearCornerCoordinates 1 t).1)) t < 0
      rw [(hasDerivAt_halfBallShearCornerCoordinates (hderiv 1 h10 t ht).1.ne').1.neg.deriv]
      exact neg_neg_of_pos (hderiv 1 h10 t ht).2.1
  have hanti2 : StrictAntiOn (fun t => (halfBallShearCornerCoordinates 1 t).2)
      (Ioo (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro t ht
      exact ((hasDerivAt_halfBallShearCornerCoordinates
        (hderiv 1 h10 t ht).1.ne').2.continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hasDerivAt_halfBallShearCornerCoordinates (hderiv 1 h10 t ht).1.ne').2.deriv]
      exact (hderiv 1 h10 t ht).2.2
  have hzero : halfBallShearCornerCoordinates 1 0 = (0, 0) := by
    norm_num [halfBallShearCornerCoordinates, halfBallShearRadiusSq]
  let M : ℝ × ℝ → ℝ := fun p =>
    max (-(halfBallShearCornerCoordinates p.1 p.2).1) (halfBallShearCornerCoordinates p.1 p.2).2
  have hMa : 0 < M (1, a) := by
    have hh := hanti1 ha h00 ha0
    simpa only [hzero, neg_zero] using hh.trans_le (le_max_left _ _)
  have hMb : M (1, b) < 0 := by
    have h1 := hanti1 h00 hb hb0
    have h2 := hanti2 h00 hb hb0
    dsimp [M]
    rw [max_lt_iff]
    simpa only [hzero, neg_zero] using And.intro h1 h2
  have hcont (t : ℝ) (ht : t ∈ Ioo (-r) r) : ContinuousAt (fun s => M (s, t)) 1 := by
    have hc := (halfBallShearCornerCoordinates_continuousAt
      (hderiv 1 h10 t ht).1.ne').comp (f := fun s : ℝ => (s, t))
        (continuousAt_id.prodMk continuousAt_const)
    exact hc.fst.neg.max hc.snd
  let δ := -M (1, b) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hevent : ∀ᶠ s in 𝓝 (1 : ℝ), 0 < M (s, a) ∧ M (s, b) < -δ := by
    exact ((hcont a ha).eventually (isOpen_Ioi.mem_nhds hMa)).and
      ((hcont b hb).eventually (isOpen_Iio.mem_nhds (show M (1, b) < -δ by dsimp [δ]; linarith)))
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.mp hevent
  let R := min ρ r / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRρ : R < ρ := by dsimp [R]; have := min_le_left ρ r; linarith
  have hRr : R < r := by dsimp [R]; have := min_le_right ρ r; linarith
  have hsub : Ioo (1 - R) (1 + R) ⊆ Ioo (1 - r) (1 + r) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsubt : Icc a b ⊆ Ioo (-r) r := by
    intro t ht
    exact ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  refine ⟨R, hR, a, ha0, b, hb0, δ, hδ, ?_⟩
  intro ε hε
  apply DifferentialGeometry.Analysis.exists_contDiffOn_implicit_graph_of_deriv_neg
    (F := fun p => roundedHalfBallShearCorner ε p.1 p.2)
    (U := Ioo (1 - R) (1 + R)) (by simp : (∞ : ℕ∞ω) ≠ 0) isOpen_Ioo (lt_trans ha0 hb0)
  · apply (contDiffOn_roundedHalfBallShearCorner ε).mono
    intro p hp
    exact (hderiv p.1 (hsub hp.1) p.2 (hsubt (Ioo_subset_Icc_self hp.2))).1.ne'
  · intro s hs t ht
    have hd := (hderiv s (hsub hs) t (hsubt ht)).1.ne'
    have hc : ContinuousAt (fun t => halfBallShearCornerCoordinates s t) t :=
      (halfBallShearCornerCoordinates_continuousAt hd).comp (f := fun t : ℝ => (s, t))
        (continuousAt_const.prodMk continuousAt_id)
    exact (((Real.smoothMax.contDiff ε).continuous.continuousAt).comp
      (hc.fst.neg.prodMk hc.snd)).continuousWithinAt
  · intro s hs t ht
    exact deriv_roundedHalfBallShearCorner_neg
      (hderiv s (hsub hs) t (hsubt (Ioo_subset_Icc_self ht))).1.ne'
      (hderiv s (hsub hs) t (hsubt (Ioo_subset_Icc_self ht))).2.1
      (hderiv s (hsub hs) t (hsubt (Ioo_subset_Icc_self ht))).2.2 ε
  · intro s hs
    have hdist : dist s 1 < ρ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
    exact (hρball hdist).1.trans_le (Real.smoothMax.max_le hε.1 _ _)
  · intro s hs
    have hdist : dist s 1 < ρ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
    have hh := Real.smoothMax.le_max_add hε.1
      (-(halfBallShearCornerCoordinates s b).1) (halfBallShearCornerCoordinates s b).2
    have hm := (hρball hdist).2
    change roundedHalfBallShearCorner ε s b < 0
    dsimp [roundedHalfBallShearCorner]
    dsimp [M] at hm
    linarith [hε.2]

theorem max_halfBallShearCornerCoordinates_roof {s : ℝ} (hs : 0 ≤ s)
    (hdom : s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) :
    let t := max (halfBallShearHeight s) 0
    max (-(halfBallShearCornerCoordinates s t).1) (halfBallShearCornerCoordinates s t).2 = 0 := by
  have h1 : (1 : ℝ) ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))) :=
    Icc_subset_halfBallShearHeight_domain ⟨by norm_num, le_rfl⟩
  by_cases hs1 : s ≤ 1
  · have hg : 0 ≤ halfBallShearHeight s := by
      rw [← halfBallShearHeight_one]
      exact strictAntiOn_halfBallShearHeight.antitoneOn hdom h1 hs1
    dsimp only
    rw [max_eq_left hg]
    have hq := halfBallShearRadiusSq_height hdom
    have ht := halfBallShearHeight_mem_Icc ⟨hs, hs1⟩
    have hd : 0 < s + (1 - halfBallShearHeight s / 2) ^ 2 * (halfBallShearHeight s + 1) ^ 2 := by
      have hb : 0 < 1 - halfBallShearHeight s / 2 := by linarith [ht.2]
      have hb' : 0 < halfBallShearHeight s + 1 := by linarith
      exact add_pos_of_nonneg_of_pos hs (mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hb'))
    dsimp [halfBallShearCornerCoordinates]
    rw [hq, sub_self, zero_div, max_eq_right]
    exact neg_nonpos.mpr (div_nonneg (by positivity) hd.le)
  · have hg : halfBallShearHeight s ≤ 0 := by
      rw [← halfBallShearHeight_one]
      exact strictAntiOn_halfBallShearHeight.antitoneOn h1 hdom (le_of_not_ge hs1)
    dsimp only
    rw [max_eq_right hg]
    norm_num only [halfBallShearCornerCoordinates, halfBallShearRadiusSq, div_zero,
      zero_div, sub_zero, zero_mul, mul_zero, one_pow, zero_pow (by decide : 2 ≠ 0),
      add_zero, zero_add, mul_one, neg_zero]
    apply max_eq_left
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem roundedHalfBallShearCorner_eq_zero_of_le {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s)
    (hdom : s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))))
    (hsep : ε ≤ |(halfBallShearCornerCoordinates s (max (halfBallShearHeight s) 0)).1 +
      (halfBallShearCornerCoordinates s (max (halfBallShearHeight s) 0)).2|) :
    roundedHalfBallShearCorner ε s (max (halfBallShearHeight s) 0) = 0 := by
  unfold roundedHalfBallShearCorner
  rw [Real.smoothMax.eq_max_of_le hε]
  · exact max_halfBallShearCornerCoordinates_roof hs hdom
  · rwa [show -(halfBallShearCornerCoordinates s (max (halfBallShearHeight s) 0)).1 -
      (halfBallShearCornerCoordinates s (max (halfBallShearHeight s) 0)).2 =
      -((halfBallShearCornerCoordinates s (max (halfBallShearHeight s) 0)).1 +
      (halfBallShearCornerCoordinates s (max (halfBallShearHeight s) 0)).2) by ring, abs_neg]

theorem halfBallShearCornerCoordinates_eq_inversion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : E × ℝ} (hp : p.2 < 2)
    (hJ : (PartialDiffeomorph.halfBallShear (E := E)).symm p ∈
      (PartialDiffeomorph.halfBallInversion 1 (by norm_num : (1 : ℝ) ≠ 0)).source) :
    let q := PartialDiffeomorph.halfBallInversion 1 (by norm_num : (1 : ℝ) ≠ 0)
      ((PartialDiffeomorph.halfBallShear (E := E)).symm p)
    halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2 =
      (1 - ‖q.1‖ ^ 2 - q.2 ^ 2, q.2) := by
  let z := (PartialDiffeomorph.halfBallShear (E := E)).symm p
  let q := PartialDiffeomorph.halfBallInversion 1 (by norm_num : (1 : ℝ) ≠ 0) z
  have hB : 1 - p.2 / 2 ≠ 0 := by linarith
  have h2 : 2 - p.2 ≠ 0 := by linarith
  have hz : ‖z.1‖ ^ 2 = ‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 := by
    simp only [z, PartialDiffeomorph.halfBallShear_symm_apply, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    ring
  have hzt : z.2 = p.2 := rfl
  have hnorm := PartialDiffeomorph.norm_sq_halfBallInversion 1 (by norm_num : (1 : ℝ) ≠ 0) hJ
  have hsnd := PartialDiffeomorph.halfBallInversion_snd 1 (by norm_num : (1 : ℝ) ≠ 0) hJ
  change ‖q.1‖ ^ 2 + q.2 ^ 2 - 1 ^ 2 = -4 * 1 ^ 3 * z.2 / (‖z.1‖ ^ 2 + (z.2 + 1) ^ 2) at hnorm
  change q.2 = 1 * (1 ^ 2 - (‖z.1‖ ^ 2 + z.2 ^ 2)) / (‖z.1‖ ^ 2 + (z.2 + 1) ^ 2) at hsnd
  rw [hz, hzt] at hnorm hsnd
  have hd : 0 < ‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 + (p.2 + 1) ^ 2 := by
    have h0 : 0 ≤ ‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    by_contra hh
    have ht : p.2 = -1 := by nlinarith [sq_nonneg (p.2 + 1)]
    have hx : ‖p.1‖ ^ 2 = 0 := by
      have heq : ‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.2 + 1)]
      exact (div_eq_zero_iff.mp heq).resolve_right (pow_ne_zero 2 hB)
    have hx0 : p.1 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
    apply hJ
    exact Prod.ext (by
      change (1 - p.2 / 2)⁻¹ • p.1 = 0
      rw [hx0, smul_zero]) (by exact ht)
  have hd' : ‖p.1‖ ^ 2 + (1 - p.2 / 2) ^ 2 * (p.2 + 1) ^ 2 ≠ 0 := by
    have h := mul_pos hd (sq_pos_of_ne_zero hB)
    have heq : (‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 + (p.2 + 1) ^ 2) * (1 - p.2 / 2) ^ 2 =
        ‖p.1‖ ^ 2 + (1 - p.2 / 2) ^ 2 * (p.2 + 1) ^ 2 := by
      rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hB)]
      ring
    rw [heq] at h
    exact h.ne'
  apply Prod.ext
  · change (halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).1 = 1 - ‖q.1‖ ^ 2 - q.2 ^ 2
    have heq : (halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).1 =
        4 * p.2 / (‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 + (p.2 + 1) ^ 2) := by
      dsimp [halfBallShearCornerCoordinates]
      field_simp [hB, h2, hd.ne', hd']
    rw [heq]
    norm_num only [one_pow, mul_one] at hnorm
    rw [neg_mul, neg_div] at hnorm
    linarith
  · change (halfBallShearCornerCoordinates (‖p.1‖ ^ 2) p.2).2 = q.2
    rw [hsnd]
    dsimp [halfBallShearCornerCoordinates, halfBallShearRadiusSq]
    field_simp [hB, h2, hd.ne', hd']
    ring

end DifferentialGeometry.Topology.Handle
