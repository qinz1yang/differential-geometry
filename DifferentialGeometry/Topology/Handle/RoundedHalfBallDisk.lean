import DifferentialGeometry.Topology.Handle.HalfBallRounding
import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Embedding.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus
import DifferentialGeometry.Topology.Handle.RoundedHalfBall
import DifferentialGeometry.Topology.Manifold.SphereLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

private noncomputable def diskRoundingHeight {E : Type*} [NormedAddCommGroup E]
    (r ε : ℝ) (x : E) : ℝ := (Real.smoothAbs ε (r ^ 2 - ‖x‖ ^ 2) - (r ^ 2 - ‖x‖ ^ 2)) / 2

private noncomputable def diskRoundingRadiusSq {E : Type*} [NormedAddCommGroup E]
    (r ε : ℝ) (x : E) : ℝ :=
  r ^ 2 - (r ^ 2 - ‖x‖ ^ 2 + Real.smoothAbs ε (r ^ 2 - ‖x‖ ^ 2)) / 2 -
    diskRoundingHeight r ε x ^ 2

private theorem diskRoundingRadiusSq_add_height {E : Type*} [NormedAddCommGroup E]
    (r ε : ℝ) (x : E) :
    diskRoundingRadiusSq r ε x + diskRoundingHeight r ε x ^ 2 + diskRoundingHeight r ε x = ‖x‖ ^ 2 := by
  unfold diskRoundingRadiusSq diskRoundingHeight
  ring

private theorem contDiff_diskRoundingHeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r ε : ℝ) : ContDiff ℝ ∞ (diskRoundingHeight (E := E) r ε) :=
  (((Real.smoothAbs.contDiff ε).comp (contDiff_const.sub (contDiff_norm_sq ℝ))).sub
    (contDiff_const.sub (contDiff_norm_sq ℝ))).div_const 2

private theorem contDiff_diskRoundingRadiusSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r ε : ℝ) : ContDiff ℝ ∞ (diskRoundingRadiusSq (E := E) r ε) :=
  (contDiff_const.sub (((contDiff_const.sub (contDiff_norm_sq ℝ)).add
    ((Real.smoothAbs.contDiff ε).comp (contDiff_const.sub (contDiff_norm_sq ℝ)))).div_const 2)).sub
      ((contDiff_diskRoundingHeight r ε).pow 2)

private theorem halfBallRounding_zero_snd_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r ε : ℝ) {x : E} (hx : x ≠ 0) :
    halfBallRounding r ε (x, 0) =
      ((Real.sqrt (diskRoundingRadiusSq r ε x) / ‖x‖) • x, diskRoundingHeight r ε x) := by
  simp [halfBallRounding, hx, diskRoundingRadiusSq, diskRoundingHeight]

private theorem contDiffOn_halfBallRounding_zero_snd {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r ε : ℝ) :
    ContDiffOn ℝ ∞ (fun x : E => halfBallRounding r ε (x, 0))
      {x | x ≠ 0 ∧ 0 < diskRoundingRadiusSq r ε x} := by
  have hnorm : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) {x | x ≠ 0 ∧ 0 < diskRoundingRadiusSq r ε x} :=
    fun x hx => (contDiffAt_norm ℝ hx.1).contDiffWithinAt
  have h := ((((contDiff_diskRoundingRadiusSq (E := E) r ε).contDiffOn.sqrt
    (fun x hx => hx.2.ne')).div hnorm (fun x hx => norm_ne_zero_iff.mpr hx.1)).smul
      contDiffOn_id).prodMk (contDiff_diskRoundingHeight r ε).contDiffOn
  exact h.congr (fun x hx => halfBallRounding_zero_snd_eq r ε hx.1)

private noncomputable def diskRoundingInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × ℝ) : E := (Real.sqrt (‖p.1‖ ^ 2 + p.2 ^ 2 + p.2) / ‖p.1‖) • p.1

private theorem norm_halfBallRounding_zero_snd {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r ε : ℝ) {x : E} (hx : x ≠ 0) :
    ‖(halfBallRounding r ε (x, 0)).1‖ = Real.sqrt (diskRoundingRadiusSq r ε x) := by
  rw [halfBallRounding_zero_snd_eq r ε hx]
  simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

private theorem diskRoundingInverse_left_inv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r ε : ℝ) {x : E}
    (hx : x ≠ 0) (hpos : 0 < diskRoundingRadiusSq r ε x) :
    diskRoundingInverse (halfBallRounding r ε (x, 0)) = x := by
  have hn := norm_halfBallRounding_zero_snd r ε hx
  have hb : (halfBallRounding r ε (x, 0)).2 = diskRoundingHeight r ε x := by
    rw [halfBallRounding_zero_snd_eq r ε hx]
  unfold diskRoundingInverse
  rw [hn, hb, Real.sq_sqrt hpos.le, diskRoundingRadiusSq_add_height, Real.sqrt_sq (norm_nonneg _)]
  rw [halfBallRounding_zero_snd_eq r ε hx]
  dsimp
  rw [smul_smul, div_mul_div_cancel₀ (Real.sqrt_pos.mpr hpos).ne',
    div_self (norm_ne_zero_iff.mpr hx), one_smul]

private theorem contDiffAt_diskRoundingInverse {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : E × ℝ} (hp : p.1 ≠ 0)
    (hpos : 0 < ‖p.1‖ ^ 2 + p.2 ^ 2 + p.2) :
    ContDiffAt ℝ ∞ (diskRoundingInverse (E := E)) p := by
  have hs : ContDiff ℝ ∞ (fun q : E × ℝ => ‖q.1‖ ^ 2 + q.2 ^ 2 + q.2) :=
    (((contDiff_norm_sq ℝ).comp contDiff_fst).add (contDiff_snd.pow 2)).add contDiff_snd
  exact ((hs.contDiffAt.sqrt hpos.ne').div
    ((contDiffAt_norm ℝ hp).comp p contDiffAt_fst) (norm_ne_zero_iff.mpr hp)).smul contDiffAt_fst

private theorem injective_fderiv_halfBallRounding_zero_snd_of_pos {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r ε : ℝ) {x : E}
    (hx : x ≠ 0) (hpos : 0 < diskRoundingRadiusSq r ε x) :
    Function.Injective (fderiv ℝ (fun y : E => halfBallRounding r ε (y, 0)) x) := by
  let f : E → E × ℝ := fun y => halfBallRounding r ε (y, 0)
  let U : Set E := {y | y ≠ 0 ∧ 0 < diskRoundingRadiusSq r ε y}
  have hU : IsOpen U := isOpen_compl_singleton.inter
    (isOpen_lt continuous_const (contDiff_diskRoundingRadiusSq r ε).continuous)
  have hfx : (f x).1 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_halfBallRounding_zero_snd r ε hx]
    exact (Real.sqrt_pos.mpr hpos).ne'
  have hb : (f x).2 = diskRoundingHeight r ε x := by
    change (halfBallRounding r ε (x, 0)).2 = _
    rw [halfBallRounding_zero_snd_eq r ε hx]
  have hrec : ‖(f x).1‖ ^ 2 + (f x).2 ^ 2 + (f x).2 = ‖x‖ ^ 2 := by
    rw [norm_halfBallRounding_zero_snd r ε hx, hb, Real.sq_sqrt hpos.le,
      diskRoundingRadiusSq_add_height]
  have hK := (contDiffAt_diskRoundingInverse hfx
    (by rw [hrec]; exact sq_pos_of_pos (norm_pos_iff.mpr hx))).differentiableAt (by simp)
  have hf := ((contDiffOn_halfBallRounding_zero_snd r ε).contDiffAt
    (hU.mem_nhds ⟨hx, hpos⟩)).differentiableAt (by simp)
  have hc := hK.hasFDerivAt.comp x hf.hasFDerivAt
  have hid : HasFDerivAt (diskRoundingInverse ∘ f) (ContinuousLinearMap.id ℝ E) x := by
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds ⟨hx, hpos⟩] with y hy
    exact diskRoundingInverse_left_inv r ε hy.1 hy.2
  have hder := hc.unique hid
  have hinj : Function.Injective ((fderiv ℝ diskRoundingInverse (f x)).comp (fderiv ℝ f x)) := by
    rw [hder]
    exact Function.injective_id
  exact Function.Injective.of_comp hinj

private theorem diskRoundingRadiusSq_pos {E : Type*}
    [NormedAddCommGroup E] {r ε : ℝ} (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2))
    {x : E} (hx : x ≠ 0) (hxr : ‖x‖ ^ 2 ≤ r ^ 2) :
    0 < diskRoundingRadiusSq r ε x := by
  by_cases h : ε ≤ r ^ 2 - ‖x‖ ^ 2
  · simp only [diskRoundingRadiusSq, diskRoundingHeight,
      Real.smoothAbs.eq_self_of_le hε h]
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hx)]
  · let p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
      ⟨(r ^ 2 - ‖x‖ ^ 2, 0), sub_nonneg.mpr hxr, le_rfl⟩
    have hn := Homeomorph.smoothAbsQuadrant_nonneg hε p
    have hs := Homeomorph.smoothAbsQuadrant_sum_le hε p (by dsimp [p]; linarith)
    simp only [Homeomorph.smoothAbsQuadrant_apply, p, sub_zero, add_zero] at hn hs
    have hb : 0 ≤ diskRoundingHeight r ε x := hn.2
    have hb1 : diskRoundingHeight r ε x ≤ 1 := by
      dsimp [diskRoundingHeight]
      linarith [hn.1, (lt_min_iff.mp hsmall).1]
    have hb2 : diskRoundingHeight r ε x ^ 2 ≤ diskRoundingHeight r ε x :=
      by nlinarith
    dsimp [diskRoundingRadiusSq, diskRoundingHeight]
    dsimp [diskRoundingHeight] at hb2
    linarith [(lt_min_iff.mp hsmall).2]

private theorem halfBallRounding_zero_snd_eqOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r ε : ℝ} (hε : 0 < ε) :
    EqOn (fun x : E => halfBallRounding r ε (x, 0)) (fun x => (x, 0))
      {x | ε < r ^ 2 - ‖x‖ ^ 2} := by
  intro x hx
  apply halfBallRounding_eq_self r hε
  simpa using hx.le

private theorem exists_contDiffOn_halfBallRounding_zero_snd {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2))
    {x : E} (hxr : ‖x‖ ^ 2 ≤ r ^ 2) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ContDiffOn ℝ ∞ (fun y : E => halfBallRounding r ε (y, 0)) U ∧
      Function.Injective (fderiv ℝ (fun y : E => halfBallRounding r ε (y, 0)) x) := by
  by_cases hx : x = 0
  · let U : Set E := {y | ε < r ^ 2 - ‖y‖ ^ 2}
    have hU : IsOpen U := isOpen_lt continuous_const
      (continuous_const.sub (continuous_norm.pow 2))
    have hxU : x ∈ U := by simpa [U, hx] using (lt_min_iff.mp hsmall).2
    have heq := halfBallRounding_zero_snd_eqOn (E := E) (r := r) hε
    have hf : ContDiffOn ℝ ∞ (fun y : E => halfBallRounding r ε (y, 0)) U :=
      (contDiff_id.prodMk contDiff_const).contDiffOn.congr heq
    refine ⟨U, hU, hxU, hf, ?_⟩
    have hder : HasFDerivAt (fun y : E => halfBallRounding r ε (y, 0))
        (ContinuousLinearMap.id ℝ E |>.prod 0) x :=
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (0 : ℝ) x)).congr_of_eventuallyEq
        (by
          filter_upwards [hU.mem_nhds hxU] with y hy
          exact heq hy)
    rw [hder.fderiv]
    intro y z h
    exact congrArg Prod.fst h
  · let U : Set E := {y | y ≠ 0 ∧ 0 < diskRoundingRadiusSq r ε y}
    have hU : IsOpen U := isOpen_compl_singleton.inter
      (isOpen_lt continuous_const (contDiff_diskRoundingRadiusSq r ε).continuous)
    have hpos := diskRoundingRadiusSq_pos hε hsmall hx hxr
    exact ⟨U, hU, ⟨hx, hpos⟩, contDiffOn_halfBallRounding_zero_snd r ε,
      injective_fderiv_halfBallRounding_zero_snd_of_pos r ε hx hpos⟩

private theorem isImmersionAt_halfBallRounding_zero_snd {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {r ε : ℝ} (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2))
    {x : E} (hxr : ‖x‖ ^ 2 ≤ r ^ 2) :
    _root_.Manifold.IsImmersionAt 𝓘(ℝ, E) 𝓘(ℝ, E × ℝ) ∞
      (fun y : E => halfBallRounding r ε (y, 0)) x := by
  obtain ⟨U, hU, hxU, hf, hinj⟩ := exists_contDiffOn_halfBallRounding_zero_snd hε hsmall hxr
  exact Manifold.isImmersionAt_of_injective_hasFDerivAt (by simp) hU hxU hf
    ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt hinj

theorem contDiffOn_halfBallRounding_disk {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) :
    ContDiffOn ℝ ∞ (fun x : E => halfBallRounding r ε (x, 0)) {x | ‖x‖ ^ 2 ≤ r ^ 2} := by
  intro x hx
  obtain ⟨U, hU, hxU, hf, _⟩ := exists_contDiffOn_halfBallRounding_zero_snd hε hsmall hx
  exact (hf.contDiffAt (hU.mem_nhds hxU)).contDiffWithinAt

private theorem halfBallRounding_zero_snd_mem_level_of_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r ε : ℝ}
    (hε : 0 < ε) {x : E} (hx0 : x ≠ 0) (hpos : 0 < diskRoundingRadiusSq r ε x) :
    Real.smoothMax ε (‖(halfBallRounding r ε (x, 0)).1‖ ^ 2 +
      (halfBallRounding r ε (x, 0)).2 ^ 2 - r ^ 2)
        (-(halfBallRounding r ε (x, 0)).2) = 0 := by
  rw [norm_halfBallRounding_zero_snd r ε hx0, Real.sq_sqrt hpos.le,
    halfBallRounding_zero_snd_eq r ε hx0]
  dsimp only
  unfold diskRoundingRadiusSq diskRoundingHeight Real.smoothMax
  rw [show r ^ 2 - (r ^ 2 - ‖x‖ ^ 2 + Real.smoothAbs ε (r ^ 2 - ‖x‖ ^ 2)) / 2 -
      ((Real.smoothAbs ε (r ^ 2 - ‖x‖ ^ 2) - (r ^ 2 - ‖x‖ ^ 2)) / 2) ^ 2 +
      ((Real.smoothAbs ε (r ^ 2 - ‖x‖ ^ 2) - (r ^ 2 - ‖x‖ ^ 2)) / 2) ^ 2 - r ^ 2 -
      -((Real.smoothAbs ε (r ^ 2 - ‖x‖ ^ 2) - (r ^ 2 - ‖x‖ ^ 2)) / 2) =
      -(r ^ 2 - ‖x‖ ^ 2) by ring, Real.smoothAbs.neg hε.ne']
  ring


theorem halfBallRounding_disk_mem_level {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) {x : E} (hx : ‖x‖ ^ 2 ≤ r ^ 2) :
    Real.smoothMax ε (‖(halfBallRounding r ε (x, 0)).1‖ ^ 2 +
      (halfBallRounding r ε (x, 0)).2 ^ 2 - r ^ 2)
        (-(halfBallRounding r ε (x, 0)).2) = 0 := by
  by_cases hx0 : x = 0
  · subst x
    simp only [halfBallRounding_zero_fst, norm_zero, zero_pow two_ne_zero, add_zero, zero_sub,
      neg_zero]
    rw [Real.smoothMax.eq_max_of_le hε]
    · exact max_eq_right (neg_nonpos.mpr (sq_nonneg r))
    · simpa only [sub_zero, abs_neg, abs_of_nonneg (sq_nonneg r)] using
        (hsmall.trans_le (min_le_right _ _)).le
  · exact halfBallRounding_zero_snd_mem_level_of_pos hε hx0
      (diskRoundingRadiusSq_pos hε hsmall hx0 hx)

theorem halfBallRounding_disk_boundary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} (hr : 0 < r)
    (ε : ℝ) {x : E} (hx : ‖x‖ = r) :
    halfBallRounding r ε (x, 0) =
      ((Real.sqrt (r ^ 2 - Real.smoothAbs ε 0 / 2 - (Real.smoothAbs ε 0 / 2) ^ 2) / r) • x,
        Real.smoothAbs ε 0 / 2) := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne hr.ne')
  rw [halfBallRounding_zero_snd_eq r ε hx0]
  simp only [diskRoundingRadiusSq, diskRoundingHeight, hx, sub_self, zero_add, sub_zero]

theorem exists_open_halfBallRounding_disk {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) :
    ∃ U : Set E, IsOpen U ∧ {x | ‖x‖ ^ 2 ≤ r ^ 2} ⊆ U ∧
      ContDiffOn ℝ ∞ (fun x : E => halfBallRounding r ε (x, 0)) U ∧
      (∀ x ∈ U, Function.Injective
        (fderiv ℝ (fun y : E => halfBallRounding r ε (y, 0)) x)) ∧
      (∀ x ∈ U, Real.smoothMax ε (‖(halfBallRounding r ε (x, 0)).1‖ ^ 2 +
        (halfBallRounding r ε (x, 0)).2 ^ 2 - r ^ 2)
          (-(halfBallRounding r ε (x, 0)).2) = 0) ∧
      InjOn (fun x : E => halfBallRounding r ε (x, 0)) U := by
  let U₀ : Set E := {x | ε < r ^ 2 - ‖x‖ ^ 2}
  let U₁ : Set E := {x | x ≠ 0 ∧ 0 < diskRoundingRadiusSq r ε x}
  have hU₀ : IsOpen U₀ := isOpen_lt continuous_const
    (continuous_const.sub (continuous_norm.pow 2))
  have hU₁ : IsOpen U₁ := isOpen_compl_singleton.inter
    (isOpen_lt continuous_const (contDiff_diskRoundingRadiusSq r ε).continuous)
  have heq := halfBallRounding_zero_snd_eqOn (E := E) (r := r) hε
  have h₀ : ContDiffOn ℝ ∞ (fun x : E => halfBallRounding r ε (x, 0)) U₀ :=
    (contDiff_id.prodMk contDiff_const).contDiffOn.congr heq
  refine ⟨U₀ ∪ U₁, hU₀.union hU₁, ?_,
    h₀.union_of_isOpen (contDiffOn_halfBallRounding_zero_snd r ε) hU₀ hU₁, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · left
      simpa [U₀, hx0] using (hsmall.trans_le (min_le_right _ _))
    · exact Or.inr ⟨hx0, diskRoundingRadiusSq_pos hε hsmall hx0 hx⟩
  · intro x hx
    rcases hx with hx | hx
    · have hder : HasFDerivAt (fun y : E => halfBallRounding r ε (y, 0))
          ((ContinuousLinearMap.id ℝ E).prod 0) x :=
        ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (0 : ℝ) x)).congr_of_eventuallyEq
          (by filter_upwards [hU₀.mem_nhds hx] with y hy; exact heq hy)
      rw [hder.fderiv]
      intro y z h
      exact congrArg Prod.fst h
    · exact injective_fderiv_halfBallRounding_zero_snd_of_pos r ε hx.1 hx.2
  · intro x hx
    rcases hx with hx | hx
    · have hxid : halfBallRounding r ε (x, 0) = (x, 0) := heq hx
      rw [hxid]
      simp only [zero_pow two_ne_zero, add_zero, neg_zero]
      rw [Real.smoothMax.eq_max_of_le hε]
      · apply max_eq_right
        linarith [show ε < r ^ 2 - ‖x‖ ^ 2 from hx]
      · rw [sub_zero, abs_of_nonpos (by linarith [show ε < r ^ 2 - ‖x‖ ^ 2 from hx])]
        linarith [show ε < r ^ 2 - ‖x‖ ^ 2 from hx]
    · exact halfBallRounding_zero_snd_mem_level_of_pos hε hx.1 hx.2
  · have hleft : LeftInvOn (diskRoundingInverse (E := E))
        (fun x : E => halfBallRounding r ε (x, 0)) (U₀ ∪ U₁) := by
      intro x hx
      rcases hx with hx | hx
      · have hxid : halfBallRounding r ε (x, 0) = (x, 0) := heq hx
        change diskRoundingInverse (halfBallRounding r ε (x, 0)) = x
        rw [hxid]
        by_cases hx0 : x = 0
        · simp [diskRoundingInverse, hx0]
        · simp [diskRoundingInverse, Real.sqrt_sq (norm_nonneg x),
            div_self (norm_ne_zero_iff.mpr hx0)]
      · exact diskRoundingInverse_left_inv r ε hx.1 hx.2
    exact hleft.injOn

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem isSmoothEmbedding_halfBallRounding_disk (m : ℕ) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) :
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)) × ℝ) ∞
      (fun x : ClosedCell (m + 1) => halfBallRounding r ε (r • x.val, 0)) := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 r hr.ne')
  have hb := (closedCellInclusion_isSmoothEmbedding m).continuousLinearEquiv_comp L
  have hnorm (x : ClosedCell (m + 1)) : ‖r • x.val‖ ^ 2 ≤ r ^ 2 := by
    have hx : ‖x.val‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using x.property
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith [norm_nonneg x.val, sq_nonneg (r * ‖x.val‖ - r)]
  have hi : _root_.Manifold.IsImmersion (𝓡∂ (m + 1)) 𝓘(ℝ, E × ℝ) ∞
      (fun x : ClosedCell (m + 1) => halfBallRounding r ε (r • x.val, 0)) := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt
    intro x
    let hf := hb.isImmersion.isImmersionAt x
    let hg := isImmersionAt_halfBallRounding_zero_snd hε hsmall (hnorm x)
    let : CompleteSpace hf.complement :=
      _root_.Manifold.completeSpace_of_continuousLinearEquiv_prod hf.equiv
    let : CompleteSpace hg.complement :=
      _root_.Manifold.completeSpace_of_continuousLinearEquiv_prod hg.equiv
    exact (hf.isImmersionAtOfComplement_complement.comp_of_smoothBoundary
      hg.isImmersionAtOfComplement_complement).isImmersionAt
  refine ⟨hi, hi.contMDiff.continuous.isClosedEmbedding ?_ |>.isEmbedding⟩
  obtain ⟨H, hH⟩ := exists_homeomorph_halfBallRounding (E := E) r hε hsmall
  intro x y hxy
  let px : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} :=
    ⟨(r • x.val, 0), by simpa using And.intro (hnorm x) (le_refl (0 : ℝ))⟩
  let py : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} :=
    ⟨(r • y.val, 0), by simpa using And.intro (hnorm y) (le_refl (0 : ℝ))⟩
  have heq : H px = H py := Subtype.ext (by simpa only [hH] using hxy)
  have hp := congrArg (fun p => p.val.1) (H.injective heq)
  apply Subtype.ext
  exact (smul_right_injective E hr.ne') hp

theorem exists_partialDiffeomorph_roundedHalfBall_disk (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2) :
    ∃ (D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1))))
      (ψ : PartialDiffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace ℝ (Fin n))
        (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∞),
      D '' closedBall 0 1 = {z | roundedHalfBallFunction n ε 0 z ≤ 0} ∧
      D '' sphere 0 1 = {z | roundedHalfBallFunction n ε 0 z = 0} ∧
      closedBall 0 1 ⊆ ψ.source ∧
      ∀ x ∈ ψ.source, D (ψ x) = (EuclideanSpace.equivProdLast n).symm
        (halfBallRounding 1 ε (x, 0)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin (n + 1))
  let : Fact (Module.finrank ℝ F = n + 1) := ⟨by simp [F]⟩
  obtain ⟨D, _, hDb, _, hDs⟩ := exists_diffeomorph_roundedHalfBall_zero n hε hsmall
  obtain ⟨U, hU, hball, hη, hdη, hlevel, hinj⟩ :=
    exists_open_halfBallRounding_disk (E := E) hε (r := 1) (by norm_num; linarith)
  let η : E → E × ℝ := fun x => halfBallRounding 1 ε (x, 0)
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  let T : (E × ℝ) ≃ₘ[ℝ] F := L.symm.toDiffeomorph.trans D.symm
  let f : E → F := T ∘ η
  have hf : ContDiffOn ℝ ∞ f U := T.contDiff.comp_contDiffOn hη
  have hnorm (x : E) (hx : x ∈ U) : ‖f x‖ = 1 := by
    have hlev : L.symm (η x) ∈ {z | roundedHalfBallFunction n ε 0 z = 0} := by
      change Real.smoothMax ε (‖L.symm (η x)‖ ^ 2 - 1)
        (-(L (L.symm (η x))).2 - 0) = 0
      rw [L.apply_symm_apply, sub_zero, EuclideanSpace.norm_sq_equivProdLast_symm]
      simpa only [η, one_pow, Real.norm_eq_abs, sq_abs] using hlevel x hx
    rw [← hDs] at hlev
    obtain ⟨y, hy, hyeq⟩ := hlev
    change ‖D.symm (L.symm (η x))‖ = 1
    rw [← hyeq, D.symm_apply_apply]
    exact mem_sphere_zero_iff_norm.mp hy
  have hd (x : E) (hx : x ∈ U) : Function.Injective (fderiv ℝ f x) := by
    have hT : Function.Injective (fderiv ℝ T (η x)) := by
      have h : Function.Injective (mfderiv 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) T (η x)) :=
        ((T.isLocalDiffeomorph (η x)).mfderivToContinuousLinearEquiv (by simp)).injective
      simp only [mfderiv_eq_fderiv, TangentSpace] at h
      convert! h using 1
    rw [show f = T ∘ η from rfl, fderiv_comp x
      (T.contDiff.contDiffAt.differentiableAt (by simp))
      ((hη.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    exact hT.comp (hdη x hx)
  obtain ⟨v, hv⟩ := NormedSpace.sphere_nonempty (E := F) (x := 0) (r := 1) |>.mpr zero_le_one
  let p : sphere (0 : F) 1 := ⟨v, hv⟩
  let g := Manifold.sphereDirection p ∘ f
  have hg := Manifold.isLocalDiffeomorphOn_sphereDirection_comp_of_norm_eq_one
    (n := n) p hU hf hnorm hd (by simp [E])
  have hgeq (x : E) (hx : x ∈ U) : (g x : F) = f x := by
    change (Manifold.sphereDirection p (f x) : F) = f x
    rw [Manifold.coe_sphereDirection p
      (norm_ne_zero_iff.mp ((hnorm x hx).trans_ne one_ne_zero)), hnorm x hx, inv_one, one_smul]
  have hginj : InjOn g U := by
    intro x hx y hy hxy
    apply hinj hx hy
    apply T.injective
    exact (hgeq x hx).symm.trans ((congrArg Subtype.val hxy).trans (hgeq y hy))
  have hzero : (0 : E) ∈ U := hball (by change ‖(0 : E)‖ ^ 2 ≤ (1 : ℝ) ^ 2; simp)
  obtain ⟨ψ, hψs, _, hψ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hg hU ⟨0, hzero⟩ hginj
  refine ⟨D, ψ, hDb, hDs, ?_, ?_⟩
  · rw [hψs]
    intro x hx
    apply hball
    have hnormx := mem_closedBall_zero_iff.mp hx
    change ‖x‖ ^ 2 ≤ (1 : ℝ) ^ 2
    nlinarith [norm_nonneg x]
  · intro x hx
    have hxU : x ∈ U := hψs ▸ hx
    change D (ψ.toFun x).val = _
    rw [hψ, hgeq x hxU]
    exact D.apply_symm_apply _

theorem exists_diffeomorph_roundedHalfBall_disk (m : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2) :
    ∃ (D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
      (u : ClosedCell (m + 1) →
        sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1),
      D '' closedBall 0 1 = {z | roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} ∧
      D '' sphere 0 1 = {z | roundedHalfBallFunction (m + 1) ε 0 z = 0} ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u ∧
      ∀ x, D (u x) = (EuclideanSpace.equivProdLast (m + 1)).symm
        (halfBallRounding 1 ε (x.val, 0)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + 1))) = (m + 1) + 1) :=
    ⟨by simp⟩
  obtain ⟨D, ψ, hDb, hDs, hs, hψ⟩ := exists_partialDiffeomorph_roundedHalfBall_disk (m + 1) hε hsmall
  let u : ClosedCell (m + 1) → sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 :=
    fun x => ψ x.val
  have hxsource (x : ClosedCell (m + 1)) : x.val ∈ ψ.source :=
    hs (mem_closedBall_zero_iff.mpr x.property)
  have hi : _root_.Manifold.IsImmersion (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u := by
    apply (closedCellInclusion_isSmoothEmbedding m).isImmersion.isLocalDiffeomorphOn_comp
    intro y
    obtain ⟨x, hx⟩ := y.property
    exact ψ.isLocalDiffeomorphAt _ _ _ (hx ▸ hxsource x)
  refine ⟨D, u, hDb, hDs, ⟨hi, ?_⟩, fun x => hψ x.val (hxsource x)⟩
  apply (hi.contMDiff.continuous.isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  exact Subtype.ext (ψ.injOn (hxsource x) (hxsource y) hxy)

end DifferentialGeometry.Topology.Handle
