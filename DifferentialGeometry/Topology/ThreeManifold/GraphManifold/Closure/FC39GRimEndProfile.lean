import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# FC39 GROUP G, RIMBOX R3 kernel: the inward end profile

External draft 58 §三 R3, disposition D58-4 (lane FC39-G-RIMBOX). At an end of a handle the
horizontal coordinate read along the axial parameter `s` is a function `q` smooth near `0` with
`q 0 = 0` and `q' 0 > 0` (from `descended_regular` and the inward sign). For a target square of
half-width `a` and every small corner scale `l`, there is a GLOBALLY smooth profile `τ : ℝ → ℝ` with
`τ 0 = 0`, `q (τ y) = l y`, `τ' > 0` and `τ` inside the domain of `q` on `[-a, a]`
(`exists_endProfile_GRIM`; 1-D inverse function theorem `OpenPartialHomeomorph.contDiffAt_symm_deriv`
on a restriction where `q' > 0`, then a `ContDiffBump` cut-off equal to `1` near `[-a, a]`). The
rim-product form `exists_endProfile_rim_GRIM` adds `0 ≤ τ y < 1` on `[0, a]` (domain `(-δ, δ)`,
`δ ≤ 1`), so the product equation of `RimProductAt` is never vacuous.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The inward end profile (R3 kernel).** -/
theorem exists_endProfile_GRIM {q : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hq : ContDiffOn ℝ ∞ q (Ioo (-δ) δ)) (hq0 : q 0 = 0) (hd : 0 < deriv q 0) {a : ℝ}
    (ha : 0 < a) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l, 0 < l → l ≤ l₀ → ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧
      ∀ y ∈ Icc (-a) a, q (τ y) = l * y ∧ 0 < deriv τ y ∧ τ y ∈ Ioo (-δ) δ := by
  have hmem : ∀ s ∈ Ioo (-δ) δ, Ioo (-δ) δ ∈ 𝓝 s := fun s hs => isOpen_Ioo.mem_nhds hs
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hcd : ∀ s ∈ Ioo (-δ) δ, ContDiffAt ℝ ∞ q s := fun s hs => hq.contDiffAt (hmem s hs)
  have hcont : ContinuousOn (deriv q) (Ioo (-δ) δ) :=
    hq.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  -- positivity of the derivative near 0
  obtain ⟨ε₁, hε₁, hpos⟩ : ∃ ε₁ > 0, ∀ s, |s| < ε₁ → 0 < deriv q s := by
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < deriv q s :=
      (hcont.continuousAt (hmem 0 h0)).eventually (lt_mem_nhds hd)
    obtain ⟨ε₁, hε₁, h⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨ε₁, hε₁, fun s hs => h (by rw [Real.dist_eq, sub_zero]; exact hs)⟩
  set σ := min ε₁ δ with hσ
  have hσ0 : 0 < σ := lt_min hε₁ hδ
  have hσδ : Ioo (-σ) σ ⊆ Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1, min_le_right ε₁ δ], lt_of_lt_of_le hs.2 (min_le_right ε₁ δ)⟩
  have hσpos : ∀ s ∈ Ioo (-σ) σ, 0 < deriv q s := fun s hs =>
    hpos s (abs_lt.mpr ⟨by linarith [hs.1, min_le_left ε₁ δ],
      lt_of_lt_of_le hs.2 (min_le_left ε₁ δ)⟩)
  -- the local homeomorphism
  have hstrict : HasStrictDerivAt q (deriv q 0) 0 :=
    (hcd 0 h0).hasStrictDerivAt (by simp)
  let F₀ := (hstrict.hasStrictFDerivAt_equiv hd.ne').toOpenPartialHomeomorph q
  let F := F₀.restrOpen (Ioo (-σ) σ) isOpen_Ioo
  have hF0src : (0 : ℝ) ∈ F.source :=
    ⟨(hstrict.hasStrictFDerivAt_equiv hd.ne').mem_toOpenPartialHomeomorph_source,
      ⟨by linarith, hσ0⟩⟩
  have hFapp : ∀ x, F x = q x := fun _ => rfl
  have hF0tgt : (0 : ℝ) ∈ F.target := by
    have := F.map_source hF0src
    rwa [hFapp, hq0] at this
  have hsrcσ : ∀ x ∈ F.source, x ∈ Ioo (-σ) σ := fun x hx => hx.2
  -- smoothness and derivative of the inverse on the target
  have hsymm_deriv : ∀ z ∈ F.target, HasDerivAt F.symm (deriv q (F.symm z))⁻¹ z := by
    intro z hz
    have hs := F.map_target hz
    have hne : deriv q (F.symm z) ≠ 0 := (hσpos _ (hsrcσ _ hs)).ne'
    refine F.hasDerivAt_symm hz hne ?_
    exact ((hcd _ (hσδ (hsrcσ _ hs))).differentiableAt (by simp)).hasDerivAt
  have hsymm_cd : ∀ z ∈ F.target, ContDiffAt ℝ ∞ F.symm z := by
    intro z hz
    have hs := F.map_target hz
    have hne : deriv q (F.symm z) ≠ 0 := (hσpos _ (hsrcσ _ hs)).ne'
    exact F.contDiffAt_symm_deriv hne hz
      (((hcd _ (hσδ (hsrcσ _ hs))).differentiableAt (by simp)).hasDerivAt)
      (hcd _ (hσδ (hsrcσ _ hs)))
  -- a ball in the target
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp F.open_target 0 hF0tgt
  refine ⟨ε / (4 * a), div_pos hε (by positivity), fun l hl hll => ?_⟩
  have hlin : ∀ y, |y| < 4 * a → l * y ∈ F.target := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul, abs_of_pos hl]
    calc l * |y| ≤ ε / (4 * a) * |y| := mul_le_mul_of_nonneg_right hll (abs_nonneg y)
      _ < ε / (4 * a) * (4 * a) := mul_lt_mul_of_pos_left hy (div_pos hε (by positivity))
      _ = ε := by field_simp
  let φ : ContDiffBump (0 : ℝ) := ⟨3 * a / 2, 2 * a, by positivity, by linarith⟩
  let g : ℝ → ℝ := fun y => F.symm (l * y)
  have hg : ∀ y, |y| < 4 * a → ContDiffAt ℝ ∞ g y := fun y hy =>
    ContDiffAt.comp (g := F.symm) (f := fun y => l * y) y (hsymm_cd _ (hlin y hy)) (by fun_prop)
  refine ⟨fun y => φ y * g y, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : |y| < 4 * a
    · exact φ.contDiff.contDiffAt.mul (hg y hy)
    · have hyt : y ∉ tsupport φ := by
        rw [φ.tsupport_eq]
        intro hy'
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hy'
        exact hy (by linarith)
      have hev : (fun y => φ y * g y) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyt] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · change φ 0 * F.symm (l * 0) = 0
    rw [mul_zero, φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
    have := F.left_inv hF0src
    rwa [hFapp, hq0] at this
  · intro y hy
    have hya : |y| ≤ a := abs_le.mpr hy
    have hev : (fun y => φ y * g y) =ᶠ[𝓝 y] g := by
      have hb : Metric.ball (0 : ℝ) (3 * a / 2) ∈ 𝓝 y :=
        Metric.isOpen_ball.mem_nhds (by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
      filter_upwards [hb] with z hz
      rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_mul]
    have hyt : l * y ∈ F.target := hlin y (by linarith)
    refine ⟨?_, ?_, ?_⟩
    · change q (φ y * F.symm (l * y)) = l * y
      rw [show φ y = 1 from φ.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; change |y| ≤ 3 * a / 2; linarith), one_mul, ← hFapp]
      exact F.right_inv hyt
    · rw [hev.deriv_eq]
      have hgd : HasDerivAt g ((deriv q (F.symm (l * y)))⁻¹ * l) y :=
        (hsymm_deriv _ hyt).comp y ((hasDerivAt_id y).const_mul l |>.congr_deriv (by simp))
      rw [hgd.deriv]
      exact mul_pos (inv_pos.mpr (hσpos _ (hsrcσ _ (F.map_target hyt)))) hl
    · change φ y * F.symm (l * y) ∈ Ioo (-δ) δ
      rw [show φ y = 1 from φ.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; change |y| ≤ 3 * a / 2; linarith), one_mul]
      exact hσδ (hsrcσ _ (F.map_target hyt))

/-- **The rim-product form of the end profile**: on `[0, a]` the profile takes values in `[0, 1)`
(for a domain `(-δ, δ)` with `δ ≤ 1`), its derivative is positive on `[0, a)`. -/
theorem exists_endProfile_rim_GRIM {q : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hq : ContDiffOn ℝ ∞ q (Ioo (-δ) δ)) (hq0 : q 0 = 0) (hd : 0 < deriv q 0) {a : ℝ}
    (ha : 0 < a) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l, 0 < l → l ≤ l₀ → ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧
      (∀ y ∈ Ico 0 a, 0 < deriv τ y) ∧
      ∀ y ∈ Icc 0 a, q (τ y) = l * y ∧ 0 ≤ τ y ∧ τ y < 1 := by
  obtain ⟨l₀, hl₀, h⟩ := exists_endProfile_GRIM hδ hq hq0 hd ha
  refine ⟨l₀, hl₀, fun l hl hll => ?_⟩
  obtain ⟨τ, hτ, hτ0, hτy⟩ := h l hl hll
  have hmono : MonotoneOn τ (Icc 0 a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hτ.continuous.continuousOn
      (hτ.differentiable (by simp)).differentiableOn fun y hy => ?_
    rw [interior_Icc] at hy
    exact (hτy y ⟨by linarith [hy.1], hy.2.le⟩).2.1.le
  refine ⟨τ, hτ, hτ0, fun y hy => (hτy y ⟨by linarith [hy.1], hy.2.le⟩).2.1, fun y hy => ?_⟩
  have hy' : y ∈ Icc (-a) a := ⟨by linarith [hy.1], hy.2⟩
  refine ⟨(hτy y hy').1, ?_, lt_of_lt_of_le (hτy y hy').2.2.2 hδ1⟩
  have := hmono ⟨le_rfl, ha.le⟩ hy hy.1
  rwa [hτ0] at this

end GC.GraphManifold.Assembly.FC39P0
