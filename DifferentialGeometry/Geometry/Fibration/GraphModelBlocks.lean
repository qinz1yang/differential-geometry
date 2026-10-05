import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartCutoffProfiles
import DifferentialGeometry.Analysis.Calculus.Cutoff.GraphPacketProfiles
import DifferentialGeometry.Analysis.Calculus.AnnularCutoff
import DifferentialGeometry.Analysis.Calculus.CompositionBounds
import DifferentialGeometry.Analysis.Calculus.SecondDerivativeComposition

/-!
# The shared model blocks of SGP04 and EGP06 (slim and zero blocks)

Blueprint `master207B.tex`, SGP04 (B:4602) and EGP06 (B:5088): the model graph `Φ_i` has, for a
listed slim chart `j`, the block `(λ f(λ/(sℓ)), s f(λ/(sℓ)))` with the slim profile `f` and
`ℓ = 10⁵Δ`, and for the possible zero block FC05's `F_{s₀}(λ) = (λ Φ(λ/s₀), s₀ Φ(λ/s₀))` with the
annular cutoff `Φ`. The actual slim cutoff is LC87's `slimCutoffProfile_LC87` (plateau `[−8, 8]`,
support in `[−8.9, 8.9]`; CGP01 deviation (1)), so the slim model block uses THAT profile; the
actual zero cutoff is LC31's `annularCutoff cutoffProfile ∘ radial`. Shared module (lead's decision
2026-10-05): SGP04 (C14-SGP3) and EGP06 (C14-KC3) both import it; names and signatures are those
frozen in `sheet-C14-SGP.md` / `state-C14-SGP2.md`.

* `sgpProfile ℓ z = slimCutoffProfile_LC87 (z/ℓ)`, its early `C²` constant `sgpProfileBound ≥ 1`
  and `sgpProfile_bounds` (values in `[0, 1]`, support in `[−9ℓ, 9ℓ]`, derivatives `≤ P/ℓ, P/ℓ²`).
* `sgpModelBlock ℓ s = scaledCutoffBlock s (sgpProfile ℓ)`, `sgpModelBlock_derivative_bounds`
  (`≤ 50(P + 1)` for `ℓ ≥ 1`, `s ≥ 99/100`), `sgpModelBlock_c1_comp_sub_le` (`≤ 200(P + 1)θ`).
* `zeroModelBlock s = scaledCutoffBlock s (annularCutoff cutoffProfile)`, `zeroProfileBound`,
  `zeroModelBlock_derivative_bounds` (`≤ 50(P₀ + 1)` for `s ≥ 1`), `zeroModelBlock_c1_comp_sub_le`.
* `modelBlock_pointwise_c1_sub_le`: the pointwise (directional) form of the composition error, for
  derivatives along one tangent vector of a manifold source (`du = dU(w)`, `dv = dV(w)`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

section Pointwise

/-- **The directional composition error of a model block.** If `W : ℝ → ℝ × ℝ` has first and
second derivatives at most `B`, then for reals `u, v, du, dv` with `|u − v| ≤ θ`,
`|du − dv| ≤ θ`, `|dv| ≤ 2` and `θ ≤ 1`: `‖W u − W v‖ ≤ 4Bθ` and
`‖W'(u) du − W'(v) dv‖ ≤ 4Bθ`. -/
theorem modelBlock_pointwise_c1_sub_le {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W)
    {B θ u v du dv : ℝ} (hB : 0 ≤ B) (hfirst : ∀ y, ‖fderiv ℝ W y‖ ≤ B)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) (hθ1 : θ ≤ 1) (huv : |u - v| ≤ θ)
    (hd : |du - dv| ≤ θ) (hdv : |dv| ≤ 2) :
    ‖W u - W v‖ ≤ 4 * B * θ ∧ ‖fderiv ℝ W u du - fderiv ℝ W v dv‖ ≤ 4 * B * θ := by
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans huv
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hDW : Differentiable ℝ (fderiv ℝ W) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hW).2.2.differentiable (by norm_num)
  have hv := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hWd y) (fun y _ => hfirst y) (Set.mem_univ v) (Set.mem_univ u)
  have hdd := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hDW y) (fun y _ => hsecond y) (Set.mem_univ v) (Set.mem_univ u)
  rw [Real.norm_eq_abs] at hv hdd
  have hdu : |du| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub du dv
    linarith
  constructor
  · calc ‖W u - W v‖ ≤ B * |u - v| := hv
      _ ≤ B * θ := mul_le_mul_of_nonneg_left huv hB
      _ ≤ 4 * B * θ := by nlinarith
  · have hsplit : fderiv ℝ W u du - fderiv ℝ W v dv =
        (fderiv ℝ W u - fderiv ℝ W v) du + fderiv ℝ W v (du - dv) := by
      rw [sub_apply, map_sub]
      abel
    rw [hsplit]
    have h1 : ‖(fderiv ℝ W u - fderiv ℝ W v) du‖ ≤ B * |u - v| * |du| := by
      refine ((fderiv ℝ W u - fderiv ℝ W v).le_opNorm du).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hdd (abs_nonneg _)
    have h2 : ‖fderiv ℝ W v (du - dv)‖ ≤ B * |du - dv| := by
      refine ((fderiv ℝ W v).le_opNorm (du - dv)).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hfirst v) (abs_nonneg _)
    have h3 : B * |u - v| * |du| ≤ B * θ * 3 :=
      mul_le_mul (mul_le_mul_of_nonneg_left huv hB) hdu (abs_nonneg _)
        (mul_nonneg hB hθ0)
    have h4 : B * |du - dv| ≤ B * θ := mul_le_mul_of_nonneg_left hd hB
    calc _ ≤ ‖(fderiv ℝ W u - fderiv ℝ W v) du‖ + ‖fderiv ℝ W v (du - dv)‖ := norm_add_le _ _
      _ ≤ 4 * B * θ := by linarith

end Pointwise

section Slim

/-- The early `C²` constant of LC87's slim profile exists (flat tails). -/
theorem exists_sgpProfileBound : ∃ P : ℝ, 1 ≤ P ∧
    (∀ t, ‖fderiv ℝ slimCutoffProfile_LC87 t‖ ≤ P) ∧
      ∀ t, ‖fderiv ℝ (fderiv ℝ slimCutoffProfile_LC87) t‖ ≤ P :=
  exists_derivative_bounds_of_constant_tails
    ((contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).of_le (by simp) :
      ContDiff ℝ 2 slimCutoffProfile_LC87)
    (fun x hx => intervalPlateauProfile_zero_left (a := (-89 / 10 : ℝ)) (b := -8) (c := 8)
      (d := 89 / 10) (by norm_num) hx)
    (fun x hx => intervalPlateauProfile_zero_right (a := (-89 / 10 : ℝ)) (b := -8) (c := 8)
      (d := 89 / 10) (by norm_num) hx)

/-- `P_*`: the early `C²` constant of LC87's slim profile (`≥ 1`). -/
def sgpProfileBound : ℝ := Classical.choose exists_sgpProfileBound

theorem sgpProfileBound_spec : 1 ≤ sgpProfileBound ∧
    (∀ t, ‖fderiv ℝ slimCutoffProfile_LC87 t‖ ≤ sgpProfileBound) ∧
      ∀ t, ‖fderiv ℝ (fderiv ℝ slimCutoffProfile_LC87) t‖ ≤ sgpProfileBound :=
  Classical.choose_spec exists_sgpProfileBound

/-- The slim tangential profile `z ↦ f(z/ℓ)` at scale `ℓ` (LC87's profile `f`). -/
def sgpProfile (ℓ z : ℝ) : ℝ := slimCutoffProfile_LC87 (z / ℓ)

theorem sgpProfile_eq_comp (ℓ : ℝ) :
    sgpProfile ℓ = slimCutoffProfile_LC87 ∘ (ℓ⁻¹ • ContinuousLinearMap.id ℝ ℝ) := by
  funext z
  simp [sgpProfile, div_eq_inv_mul]

theorem contDiff_sgpProfile (ℓ : ℝ) : ContDiff ℝ ∞ (sgpProfile ℓ) := by
  rw [sgpProfile_eq_comp]
  exact (contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).comp
    (ContinuousLinearMap.contDiff _)

/-- The slim profile is one on its plateau `|z| ≤ 8ℓ`. -/
theorem sgpProfile_eq_one {ℓ z : ℝ} (hℓ : 0 < ℓ) (hz : |z| ≤ 8 * ℓ) : sgpProfile ℓ z = 1 := by
  have h : |z / ℓ| ≤ 8 := by
    rw [abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
    exact hz
  exact intervalPlateauProfile_one (by norm_num) (by norm_num)
    ⟨by linarith [neg_abs_le (z / ℓ)], by linarith [le_abs_self (z / ℓ)]⟩

/-- Bounds of the slim profile at scale `ℓ`: values in `[0, 1]`, support in `[−9ℓ, 9ℓ]`,
first and second derivatives at most `P/ℓ` and `P/ℓ²`. -/
theorem sgpProfile_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ x, sgpProfile ℓ x ∈ Icc 0 1) ∧
    tsupport (sgpProfile ℓ) ⊆ Metric.closedBall 0 (9 * ℓ) ∧
    (∀ x, ‖fderiv ℝ (sgpProfile ℓ) x‖ ≤ sgpProfileBound * ℓ⁻¹) ∧
    ∀ x, ‖fderiv ℝ (fderiv ℝ (sgpProfile ℓ)) x‖ ≤ sgpProfileBound * ℓ⁻¹ ^ 2 := by
  obtain ⟨hP, hf1, hf2⟩ := sgpProfileBound_spec
  have hL : ‖(ℓ⁻¹ • ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ)‖ ≤ ℓ⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
      (inv_nonneg.mpr hℓ.le)).trans_eq (mul_one _)
  have hd (x : ℝ) := linear_precomp_derivative_bounds (ℓ⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    ((contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).of_le (by simp) :
      ContDiff ℝ 2 slimCutoffProfile_LC87) (inv_nonneg.mpr hℓ.le) (by linarith)
    (by linarith) hL hf1 hf2 x
  refine ⟨fun x => intervalPlateauProfile_mem_Icc _ _ _ _ _, ?_, ?_, ?_⟩
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h
    apply hx
    have hx' : 9 < |x / ℓ| := by
      rw [abs_div, abs_of_pos hℓ, lt_div_iff₀ hℓ]
      exact lt_of_not_ge h
    rcases lt_abs.mp hx' with h1 | h1
    · exact intervalPlateauProfile_zero_right (by norm_num) (by linarith)
    · exact intervalPlateauProfile_zero_left (by norm_num) (by linarith)
  · intro x
    rw [sgpProfile_eq_comp]
    exact (hd x).1
  · intro x
    rw [sgpProfile_eq_comp]
    exact (hd x).2

/-- The slim model block `(λ f(λ/(sℓ)), s f(λ/(sℓ)))` of SGP04 / EGP06 (LC87's slim profile). -/
def sgpModelBlock (ℓ s : ℝ) : ℝ → WithLp 2 (ℝ × ℝ) :=
  scaledCutoffBlock s (sgpProfile ℓ)

theorem sgpModelBlock_apply (ℓ s x : ℝ) :
    sgpModelBlock ℓ s x =
      WithLp.toLp 2 (slimCutoffProfile_LC87 (x / (s * ℓ)) * x,
        s * slimCutoffProfile_LC87 (x / (s * ℓ))) := by
  have h : x / (s * ℓ) = s⁻¹ * x / ℓ := by ring
  rw [h]
  rfl

theorem contDiff_sgpModelBlock (ℓ s : ℝ) : ContDiff ℝ ∞ (sgpModelBlock ℓ s) :=
  contDiff_scaledCutoffBlock (contDiff_sgpProfile ℓ) s

/-- SGP04 / EGP06: the slim model block has first and second derivatives at most `50(P + 1)`
for `ℓ ≥ 1` and `s ≥ 99/100`. -/
theorem sgpModelBlock_derivative_bounds {ℓ s : ℝ} (hℓ : 1 ≤ ℓ) (hs : 99 / 100 ≤ s) (x : ℝ) :
    ‖fderiv ℝ (sgpModelBlock ℓ s) x‖ ≤ 50 * (sgpProfileBound + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (sgpModelBlock ℓ s)) x‖ ≤ 50 * (sgpProfileBound + 1) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < s := by linarith
  have hP := sgpProfileBound_spec.1
  set P := sgpProfileBound
  obtain ⟨hval, hsupp, hfirst, hsecond⟩ := sgpProfile_bounds hℓ0
  have hinv : ℓ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓ
  have hinv0 : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ0.le
  have h := scaledCutoffBlock_derivative_bounds
    ((contDiff_sgpProfile ℓ).of_le (by simp)) hs0 (by positivity)
    (by positivity) (by positivity) hval hsupp hfirst hsecond x
  have hmul : ℓ * ℓ⁻¹ = 1 := mul_inv_cancel₀ hℓ0.ne'
  constructor
  · refine h.1.trans ?_
    have : (9 * ℓ + 1) * (P * ℓ⁻¹) = 9 * P + P * ℓ⁻¹ := by
      rw [add_mul, mul_comm P, ← mul_assoc, mul_assoc 9, hmul]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hinv (by linarith : (0 : ℝ) ≤ P)]
  · refine h.2.trans ?_
    rw [div_le_iff₀ hs0]
    have : 2 * (P * ℓ⁻¹) + (9 * ℓ + 1) * (P * ℓ⁻¹ ^ 2) = 11 * P * ℓ⁻¹ + P * ℓ⁻¹ ^ 2 := by
      have : ℓ * ℓ⁻¹ ^ 2 = ℓ⁻¹ := by rw [sq, ← mul_assoc, hmul, one_mul]
      calc 2 * (P * ℓ⁻¹) + (9 * ℓ + 1) * (P * ℓ⁻¹ ^ 2)
          = 2 * (P * ℓ⁻¹) + 9 * P * (ℓ * ℓ⁻¹ ^ 2) + P * ℓ⁻¹ ^ 2 := by ring
        _ = 11 * P * ℓ⁻¹ + P * ℓ⁻¹ ^ 2 := by rw [this]; ring
    rw [this]
    have h1 : P * ℓ⁻¹ ≤ P := by nlinarith
    have h2 : P * ℓ⁻¹ ^ 2 ≤ P := by
      nlinarith [mul_le_mul hinv hinv hinv0 (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith

/-- SGP04 / EGP06: per-block `C¹` composition error of the slim model block: if the actual and
affine inputs are `θ`-close in `C¹` at `x` and the affine input has derivative at most two, the
model blocks differ by at most `200(P + 1)θ` in value and derivative. -/
theorem sgpModelBlock_c1_comp_sub_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ℓ s : ℝ} (hℓ : 1 ≤ ℓ) (hs : 99 / 100 ≤ s) {U V : X → ℝ} {x : X}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ‖U x - V x‖ ≤ θ) (hDclose : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ θ)
    (hDV : ‖fderiv ℝ V x‖ ≤ 2) :
    max ‖sgpModelBlock ℓ s (U x) - sgpModelBlock ℓ s (V x)‖
      ‖fderiv ℝ (sgpModelBlock ℓ s ∘ U) x - fderiv ℝ (sgpModelBlock ℓ s ∘ V) x‖ ≤
      200 * (sgpProfileBound + 1) * θ := by
  have hP := sgpProfileBound_spec.1
  have hW := contDiff_sgpModelBlock ℓ s
  have hDW : Differentiable ℝ (fderiv ℝ (sgpModelBlock ℓ s)) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp (hW.of_le (by simp))).2.2.differentiable
      (by norm_num)
  have hb (y : ℝ) := sgpModelBlock_derivative_bounds hℓ hs y
  refine (c1_comp_sub_le_of_derivative_bounds (hW.differentiable (by simp))
    hDW hU hV (by linarith) (by linarith) (by norm_num) hθ
    (fun y => (hb y).1) (fun y => (hb y).2) hclose hDclose hDV).trans ?_
  nlinarith

end Slim

section Zero

/-- The early `C²` constant of LC31's annular cutoff exists (flat tails). -/
theorem exists_zeroProfileBound : ∃ P : ℝ, 1 ≤ P ∧
    (∀ t, ‖fderiv ℝ (annularCutoff cutoffProfile) t‖ ≤ P) ∧
      ∀ t, ‖fderiv ℝ (fderiv ℝ (annularCutoff cutoffProfile)) t‖ ≤ P :=
  exists_derivative_bounds_of_constant_tails (a := 1 / 5) (b := 9 / 10)
    ((annularCutoff_contDiff cutoffProfile_contDiff).of_le (by simp))
    (fun x hx => annularCutoff_eq_zero_of_le (fun t ht => cutoffProfile_eq_zero ht) hx)
    (fun x hx => annularCutoff_eq_zero_of_ge (fun t ht => cutoffProfile_eq_zero ht) hx)

/-- The early `C²` constant of LC31's annular cutoff (`≥ 1`). -/
def zeroProfileBound : ℝ := Classical.choose exists_zeroProfileBound

theorem zeroProfileBound_spec : 1 ≤ zeroProfileBound ∧
    (∀ t, ‖fderiv ℝ (annularCutoff cutoffProfile) t‖ ≤ zeroProfileBound) ∧
      ∀ t, ‖fderiv ℝ (fderiv ℝ (annularCutoff cutoffProfile)) t‖ ≤ zeroProfileBound :=
  Classical.choose_spec exists_zeroProfileBound

/-- The support of LC31's annular cutoff lies in the unit ball. -/
theorem tsupport_annularCutoff_subset_closedBall :
    tsupport (annularCutoff cutoffProfile) ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  apply hx
  rcases lt_abs.mp (lt_of_not_ge h) with h1 | h1
  · exact annularCutoff_eq_zero_of_ge (fun t ht => cutoffProfile_eq_zero ht) (by linarith)
  · exact annularCutoff_eq_zero_of_le (fun t ht => cutoffProfile_eq_zero ht) (by linarith)

/-- FC05's zero model block `F_s(λ) = (λ Φ(λ/s), s Φ(λ/s))` with LC31's annular cutoff `Φ`. -/
def zeroModelBlock (s : ℝ) : ℝ → WithLp 2 (ℝ × ℝ) :=
  scaledCutoffBlock s (annularCutoff cutoffProfile)

theorem zeroModelBlock_apply (s x : ℝ) :
    zeroModelBlock s x =
      WithLp.toLp 2 (annularCutoff cutoffProfile (s⁻¹ * x) * x,
        s * annularCutoff cutoffProfile (s⁻¹ * x)) :=
  rfl

theorem contDiff_zeroModelBlock (s : ℝ) : ContDiff ℝ ∞ (zeroModelBlock s) :=
  contDiff_scaledCutoffBlock (annularCutoff_contDiff cutoffProfile_contDiff) s

/-- FC05 / SGP04 / EGP06: the zero model block has first and second derivatives at most
`50(P₀ + 1)` for `s ≥ 1` (its Hessian bound only improves as `s` grows). -/
theorem zeroModelBlock_derivative_bounds {s : ℝ} (hs : 1 ≤ s) (x : ℝ) :
    ‖fderiv ℝ (zeroModelBlock s) x‖ ≤ 50 * (zeroProfileBound + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (zeroModelBlock s)) x‖ ≤ 50 * (zeroProfileBound + 1) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨hP, hf1, hf2⟩ := zeroProfileBound_spec
  have h := scaledCutoffBlock_derivative_bounds
    ((annularCutoff_contDiff cutoffProfile_contDiff).of_le (by simp)) hs0 zero_le_one
    (by linarith) (by linarith)
    (annularCutoff_mem_Icc cutoffProfile_mem_Icc) tsupport_annularCutoff_subset_closedBall hf1 hf2
    x
  constructor
  · refine h.1.trans ?_
    linarith
  · refine h.2.trans ?_
    rw [div_le_iff₀ hs0]
    nlinarith

/-- FC05 / SGP04 / EGP06: per-block `C¹` composition error of the zero model block (`s ≥ 1`):
at most `200(P₀ + 1)θ` in value and derivative. -/
theorem zeroModelBlock_c1_comp_sub_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : ℝ} (hs : 1 ≤ s) {U V : X → ℝ} {x : X}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ‖U x - V x‖ ≤ θ) (hDclose : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ θ)
    (hDV : ‖fderiv ℝ V x‖ ≤ 2) :
    max ‖zeroModelBlock s (U x) - zeroModelBlock s (V x)‖
      ‖fderiv ℝ (zeroModelBlock s ∘ U) x - fderiv ℝ (zeroModelBlock s ∘ V) x‖ ≤
      200 * (zeroProfileBound + 1) * θ := by
  have hP := zeroProfileBound_spec.1
  have hW := contDiff_zeroModelBlock s
  have hDW : Differentiable ℝ (fderiv ℝ (zeroModelBlock s)) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp (hW.of_le (by simp))).2.2.differentiable
      (by norm_num)
  have hb (y : ℝ) := zeroModelBlock_derivative_bounds hs y
  refine (c1_comp_sub_le_of_derivative_bounds (hW.differentiable (by simp))
    hDW hU hV (by linarith) (by linarith) (by norm_num) hθ
    (fun y => (hb y).1) (fun y => (hb y).2) hclose hDclose hDV).trans ?_
  nlinarith

end Zero

end DifferentialGeometry.Geometry.Collapse
