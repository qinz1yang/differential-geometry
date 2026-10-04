import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeSublevelProfile
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# LFR24 kernel: the smooth edge-model core `h = ψ ∘ F`

Blueprint LFR24 (master207A:26862). Its proof takes LFR02's smoothed distance `F` (smooth near the
compact annulus `3/4 ≤ r ≤ 9.1`, `|F - r| < μ`) and puts `h = ψ ∘ F` with the fixed sublevel
profile `ψ = edgeSublevelProfile` (zero on `(-∞,1]`, the identity on `[2,∞)`, values in `[0,2]`
below two). This file proves every clause of LFR24 that follows from those properties of `F`, for
an arbitrary radius function `r` on a manifold (so the physical scale `Δ⁻¹ Z` is the case
`r = dist z₀ · / Δ`):

* `contMDiffOn_edgeModelCore`: `h` is smooth on an open set containing `{r ≤ 9}`;
* `edgeModelCore_eqOn_zero`, `edgeModelCore_mem_Icc`: `h = 0` near `{r ≤ 1/2}`, `0 ≤ h ≤ 2` on `r ≤ 1`;
* `edgeModelCore_eventuallyEq`, `abs_edgeModelCore_sub_lt`, `mvfderiv_edgeModelCore_eq`: on
  `r ≥ 2.1`, `h` agrees with `F` near the point (so LFR24.1's value and gradient clauses are those of `F`);
* `edgeCoreSublevel_eq` and companions: for `s ∈ [3,6]` the WHOLE sublevel
  `D_s = {r < 9, h ≤ s}` equals `{F ≤ s}`, is closed, contains `{r ≤ s - μ}`, lies in `{r < s + μ}`;
* `edgeModelCore_field`: a field with `dF(V) > 1/2` on the collar has `dh(V) > 1/2` there, so every
  level `h = s`, `s ∈ [3,6]`, is regular;
* `three_quarters_sub_two_mul_lt_inner`: the pointwise algebra `dF(V) > 3/4 - 2ε` of the blueprint;
* `edgeModelCore_product_enclosure`: the scaled product enclosure (LFR24.2);
* `edgeModelCore_dist_isCompact` (metric binding): `D_s` is compact in a proper space.

Not proved here: LFR02 itself (lane W4-F7a), LFR23's field and topological disk, and the smooth
recognition of `D_s` as a closed disk (Hirsch 9.3.7) — see `build-logs/resume/sheet-W4-F7c.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

section Algebra

variable {Z : Type*}

/-- LFR24's core function `h = ψ ∘ F`, with `ψ` the fixed sublevel profile. -/
def edgeModelCore (F : Z → ℝ) : Z → ℝ := fun x => edgeSublevelProfile (F x)

/-- LFR24's sublevel `D_s = {x ∈ B(z₀, 9) : h x ≤ s}`, for a radius function `r`. -/
def edgeCoreSublevel (r F : Z → ℝ) (s : ℝ) : Set Z := {x | r x < 9 ∧ edgeModelCore F x ≤ s}

variable {r F : Z → ℝ} {μ : ℝ}

theorem lt_one_of_lt_three_quarters (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {x : Z}
    (hx : r x < 3 / 4) : F x < 1 := by
  have := (abs_lt.mp (hFr x)).2
  linarith

theorem two_lt_of_le_twentyOne (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {x : Z}
    (hx : 21 / 10 ≤ r x) : 2 < F x := by
  have := (abs_lt.mp (hFr x)).1
  linarith

/-- **LFR24, `0 ≤ h ≤ 2` where `r ≤ 1`.** -/
theorem edgeModelCore_mem_Icc (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {x : Z}
    (hx : r x ≤ 1) : edgeModelCore F x ∈ Icc 0 2 := by
  have := (abs_lt.mp (hFr x)).2
  exact ⟨edgeSublevelProfile_nonneg _, edgeSublevelProfile_le_two (by linarith)⟩

/-- **LFR24.1, value clause.** `|h - r| < μ` on `r ≥ 2.1`. -/
theorem abs_edgeModelCore_sub_lt (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {x : Z}
    (hx : 21 / 10 ≤ r x) : |edgeModelCore F x - r x| < μ := by
  have h2 := two_lt_of_le_twentyOne hμ hFr hx
  simpa only [edgeModelCore, edgeSublevelProfile_eq_self (le_of_lt h2)] using hFr x

theorem edgeModelCore_le_iff {s : ℝ} (hs : 2 ≤ s) {x : Z} :
    edgeModelCore F x ≤ s ↔ F x ≤ s :=
  edgeSublevelProfile_le_iff hs

theorem edgeModelCore_eq_iff {s : ℝ} (hs : 2 < s) {x : Z} :
    edgeModelCore F x = s ↔ F x = s := by
  constructor
  · intro h
    rcases le_total 2 (F x) with h2 | h2
    · rwa [edgeModelCore, edgeSublevelProfile_eq_self h2] at h
    · have := edgeSublevelProfile_le_two h2
      simp only [edgeModelCore] at h
      linarith
  · intro h
    simp only [edgeModelCore, h, edgeSublevelProfile_eq_self (le_of_lt hs)]

/-- **LFR24, the whole sublevel.** For `s ∈ [3,6]`, `D_s = {F ≤ s}`. -/
theorem edgeCoreSublevel_eq (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) 6) : edgeCoreSublevel r F s = {x | F x ≤ s} := by
  ext x
  simp only [edgeCoreSublevel, mem_ofPred_eq,
    edgeModelCore_le_iff (by linarith [hs.1] : (2 : ℝ) ≤ s)]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have := (abs_lt.mp (hFr x)).1
  linarith [hs.2]

/-- **LFR24, the whole level.** For `s ∈ [3,6]`, `{r < 9, h = s} = {F = s}`. -/
theorem edgeCoreLevel_eq (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) 6) : {x | r x < 9 ∧ edgeModelCore F x = s} = {x | F x = s} := by
  ext x
  simp only [mem_ofPred_eq, edgeModelCore_eq_iff (by linarith [hs.1] : (2 : ℝ) < s)]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have := (abs_lt.mp (hFr x)).1
  linarith [hs.2]

/-- **LFR24, the two ball inclusions (inner).** `{r ≤ s - μ} ⊆ D_s` for `s ∈ [3,6]`. -/
theorem subset_edgeCoreSublevel (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) 6) : {x | r x ≤ s - μ} ⊆ edgeCoreSublevel r F s := by
  rw [edgeCoreSublevel_eq hμ hFr hs]
  intro x hx
  have := (abs_lt.mp (hFr x)).2
  simp only [mem_ofPred_eq] at hx ⊢
  linarith

/-- **LFR24, the two ball inclusions (outer).** `D_s ⊆ {r < s + μ}` for `s ∈ [3,6]`. -/
theorem edgeCoreSublevel_subset (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) 6) : edgeCoreSublevel r F s ⊆ {x | r x < s + μ} := by
  rw [edgeCoreSublevel_eq hμ hFr hs]
  intro x hx
  have := (abs_lt.mp (hFr x)).1
  simp only [mem_ofPred_eq] at hx ⊢
  linarith

end Algebra

section Topology

variable {Z : Type*} [TopologicalSpace Z] {r F : Z → ℝ} {μ : ℝ}

theorem edgeModelCore_eventuallyEq_zero (hF : Continuous F) {x : Z} (hx : F x < 1) :
    edgeModelCore F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
  filter_upwards [(isOpen_lt hF continuous_const).mem_nhds hx] with y hy
  exact edgeSublevelProfile_eq_zero (le_of_lt hy)

theorem edgeModelCore_eventuallyEq_self (hF : Continuous F) {x : Z} (hx : 2 < F x) :
    edgeModelCore F =ᶠ[𝓝 x] F := by
  filter_upwards [(isOpen_lt continuous_const hF).mem_nhds hx] with y hy
  exact edgeSublevelProfile_eq_self (le_of_lt hy)

/-- **LFR24, the constant core.** `h = 0` on an open set containing `{r ≤ 1/2}`. -/
theorem edgeModelCore_eqOn_zero (hF : Continuous F) (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - r x| < μ) :
    ∃ O : Set Z, IsOpen O ∧ {x | r x ≤ 1 / 2} ⊆ O ∧ EqOn (edgeModelCore F) 0 O := by
  refine ⟨{x | F x < 1}, isOpen_lt hF continuous_const, fun x hx => ?_, fun x hx => ?_⟩
  · exact lt_one_of_lt_three_quarters hμ hFr (lt_of_le_of_lt hx (by norm_num))
  · exact edgeSublevelProfile_eq_zero (le_of_lt hx)

/-- **LFR24, the collar.** On `r ≥ 2.1`, `h` coincides with `F` near the point. -/
theorem edgeModelCore_eventuallyEq (hF : Continuous F) (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - r x| < μ) {x : Z} (hx : 21 / 10 ≤ r x) : edgeModelCore F =ᶠ[𝓝 x] F :=
  edgeModelCore_eventuallyEq_self hF (two_lt_of_le_twentyOne hμ hFr hx)

/-- **LFR24, `D_s` is closed** (so compact inside a compact ball). -/
theorem isClosed_edgeCoreSublevel (hF : Continuous F) (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - r x| < μ) {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 6) :
    IsClosed (edgeCoreSublevel r F s) := by
  rw [edgeCoreSublevel_eq hμ hFr hs]
  exact isClosed_le hF continuous_const

/-- **LFR24.2, the scaled product enclosure.** On `(-6Δ,6Δ) × {r < 9}`, the ENTIRE inverse image of
`[-4Δ,4Δ] × (-∞,4Δ]` under `(t,z) ↦ (t, Δ h z)` is `[-4Δ,4Δ] × D_4`, and it lies in the interior of
`Q = [-4.5Δ,4.5Δ] × {r ≤ 5}`. -/
theorem edgeModelCore_product_enclosure {Δ : ℝ} (hΔ : 0 < Δ) (hr : Continuous r)
    (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) :
    {p : ℝ × Z | p.1 ∈ Ioo (-(6 * Δ)) (6 * Δ) ∧ r p.2 < 9 ∧
        (p.1, Δ * edgeModelCore F p.2) ∈ Icc (-(4 * Δ)) (4 * Δ) ×ˢ Iic (4 * Δ)} =
      Icc (-(4 * Δ)) (4 * Δ) ×ˢ edgeCoreSublevel r F 4 ∧
    Icc (-(4 * Δ)) (4 * Δ) ×ˢ edgeCoreSublevel r F 4 ⊆
      interior (Icc (-(9 / 2 * Δ)) (9 / 2 * Δ) ×ˢ {z | r z ≤ 5}) := by
  have h4 : (4 : ℝ) ∈ Icc (3 : ℝ) 6 := ⟨by norm_num, by norm_num⟩
  constructor
  · ext ⟨t, z⟩
    simp only [mem_ofPred_eq, mem_prod, mem_Icc, mem_Ioo, mem_Iic, edgeCoreSublevel]
    have hmul : Δ * edgeModelCore F z ≤ 4 * Δ ↔ edgeModelCore F z ≤ 4 := by
      rw [mul_comm Δ]
      exact mul_le_mul_iff_left₀ hΔ
    rw [hmul]
    constructor
    · rintro ⟨-, hr9, ht, hh⟩
      exact ⟨ht, hr9, hh⟩
    · rintro ⟨ht, hr9, hh⟩
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hr9, ht, hh⟩
  · rw [interior_prod_eq, interior_Icc]
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have hlt : z ∈ {z | r z < 5} := by
      have := edgeCoreSublevel_subset hμ hFr h4 hz
      simp only [mem_ofPred_eq] at this ⊢
      linarith
    exact interior_maximal (fun y hy => le_of_lt hy) (isOpen_lt hr continuous_const) hlt

end Topology

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] {r F : Z → ℝ} {μ : ℝ}

/-- **LFR24, smoothness.** `h` is smooth on the open set `U ∪ {F < 1}`, which contains the whole
closed ball `{r ≤ 9}`: where `F` may fail to be smooth (`r < 3/4`) it is below one, so `h` is
locally constant there. -/
theorem contMDiffOn_edgeModelCore {U : Set Z} (hF : Continuous F) (hU : IsOpen U)
    (hFU : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F U) (hA : ∀ x, 3 / 4 ≤ r x → r x ≤ 9 → x ∈ U)
    (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - r x| < μ) :
    ∃ W : Set Z, IsOpen W ∧ {x | r x ≤ 9} ⊆ W ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (edgeModelCore F) W := by
  refine ⟨U ∪ {x | F x < 1}, hU.union (isOpen_lt hF continuous_const), ?_, ?_⟩
  · intro x hx
    by_cases h34 : 3 / 4 ≤ r x
    · exact Or.inl (hA x h34 hx)
    · exact Or.inr (lt_one_of_lt_three_quarters hμ hFr (not_le.mp h34))
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    rcases hx with hxU | hxF
    · exact ((contDiff_edgeSublevelProfile.contMDiff.comp_contMDiffOn hFU).contMDiffAt
        (hU.mem_nhds hxU))
    · exact contMDiffAt_const.congr_of_eventuallyEq (edgeModelCore_eventuallyEq_zero hF hxF)

/-- **LFR24.1, gradient clause.** On `r ≥ 2.1` the differential of `h` is that of `F`. -/
theorem mvfderiv_edgeModelCore_eq (hF : Continuous F) (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - r x| < μ) {x : Z} (hx : 21 / 10 ≤ r x) :
    mvfderiv I (edgeModelCore F) x = mvfderiv I F x := by
  have hev := edgeModelCore_eventuallyEq hF hμ hFr hx
  ext v
  simp only [mvfderiv, hev.mfderiv_eq]
  rfl

/-- **LFR24, the outward field.** A field `V` with `dF(V) > 1/2` on the collar `2.1 ≤ r ≤ 8` has
`dh(V) > 1/2` there (LFR23's field and LFR02's gradient clause give `dF(V) > 3/4 - 2ε`, see
`three_quarters_sub_two_mul_lt_inner`). -/
theorem edgeModelCore_field (hF : Continuous F) (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - r x| < μ) (V : (x : Z) → TangentSpace I x)
    (hV : ∀ x, 21 / 10 ≤ r x → r x ≤ 8 → 1 / 2 < mvfderiv I F x (V x)) {x : Z}
    (hx₁ : 21 / 10 ≤ r x) (hx₂ : r x ≤ 8) : 1 / 2 < mvfderiv I (edgeModelCore F) x (V x) := by
  rw [mvfderiv_edgeModelCore_eq hF hμ hFr hx₁]
  exact hV x hx₁ hx₂

/-- **LFR24, regular levels.** Under the field hypothesis every level `h = s`, `s ∈ [3,6]`, inside
`{r < 9}` is regular. -/
theorem mvfderiv_edgeModelCore_ne_zero (hF : Continuous F) (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - r x| < μ) (V : (x : Z) → TangentSpace I x)
    (hV : ∀ x, 21 / 10 ≤ r x → r x ≤ 8 → 1 / 2 < mvfderiv I F x (V x)) {s : ℝ}
    (hs : s ∈ Icc (3 : ℝ) 6) {x : Z} (hx : r x < 9) (hxs : edgeModelCore F x = s) :
    mvfderiv I (edgeModelCore F) x ≠ 0 := by
  have hFx : F x = s := (edgeCoreLevel_eq hμ hFr hs).subset (show x ∈ {x | r x < 9 ∧
    edgeModelCore F x = s} from ⟨hx, hxs⟩)
  have habs := abs_lt.mp (hFr x)
  have hx₁ : 21 / 10 ≤ r x := by linarith [hs.1, habs.2]
  have hx₂ : r x ≤ 8 := by linarith [hs.2, habs.1]
  intro h0
  have := edgeModelCore_field hF hμ hFr V hV hx₁ hx₂
  rw [h0] at this
  simp only [zero_apply] at this
  linarith

end Manifold

/-- **The pointwise algebra of LFR24.** If `‖G + v‖ < ε`, `‖V‖ < 2` and `⟪V, v⟫ < -3/4`, then
`⟪G, V⟫ > 3/4 - 2ε` (with `G = ∇F`, `v` an inward direction and `V` LFR23's outward field). -/
theorem three_quarters_sub_two_mul_lt_inner {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace ℝ F'] {G v V : F'} {ε : ℝ} (hG : ‖G + v‖ < ε) (hV : ‖V‖ < 2)
    (hvV : inner ℝ V v < -(3 / 4)) : 3 / 4 - 2 * ε < inner ℝ G V := by
  have hsplit : inner ℝ G V = inner ℝ (G + v) V - inner ℝ v V := by
    rw [inner_add_left]
    ring
  have hcs : -(‖G + v‖ * ‖V‖) ≤ inner ℝ (G + v) V :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hprod : ‖G + v‖ * ‖V‖ ≤ ‖G + v‖ * 2 :=
    mul_le_mul_of_nonneg_left (le_of_lt hV) (norm_nonneg _)
  rw [hsplit, real_inner_comm V v]
  linarith

section Metric

variable {Z : Type*} [MetricSpace Z] [ProperSpace Z]

/-- **LFR24, metric binding at scale `Δ`.** With `r = d(z₀,·)/Δ` on a proper metric space, every
`D_s`, `s ∈ [3,6]`, is compact, contains `B̄(z₀,(s-μ)Δ)` and lies in `B(z₀,(s+μ)Δ)`. -/
theorem edgeModelCore_dist_isCompact {z₀ : Z} {F : Z → ℝ} {μ Δ s : ℝ} (hΔ : 0 < Δ)
    (hF : Continuous F) (hμ : μ ≤ 1 / 100) (hFr : ∀ x, |F x - dist x z₀ / Δ| < μ)
    (hs : s ∈ Icc (3 : ℝ) 6) :
    IsCompact (edgeCoreSublevel (fun x => dist x z₀ / Δ) F s) ∧
      Metric.closedBall z₀ ((s - μ) * Δ) ⊆ edgeCoreSublevel (fun x => dist x z₀ / Δ) F s ∧
      edgeCoreSublevel (fun x => dist x z₀ / Δ) F s ⊆ Metric.ball z₀ ((s + μ) * Δ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (isCompact_closedBall z₀ ((s + μ) * Δ)).of_isClosed_subset
      (isClosed_edgeCoreSublevel hF hμ hFr hs) (fun x hx => ?_)
    have := edgeCoreSublevel_subset hμ hFr hs hx
    simp only [mem_ofPred_eq] at this
    rw [Metric.mem_closedBall]
    exact le_of_lt ((div_lt_iff₀ hΔ).mp this)
  · intro x hx
    apply subset_edgeCoreSublevel hμ hFr hs
    rw [Metric.mem_closedBall] at hx
    exact (div_le_iff₀ hΔ).mpr hx
  · intro x hx
    have := edgeCoreSublevel_subset hμ hFr hs hx
    simp only [mem_ofPred_eq] at this
    exact Metric.mem_ball.mpr ((div_lt_iff₀ hΔ).mp this)

end Metric

end DifferentialGeometry.Geometry.Collapse
