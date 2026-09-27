import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

open Set Metric Filter
open scoped Topology RealInnerProductSpace

namespace HasFDerivAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {L : E →L[ℝ] ℝ} {x c : E} {r : ℝ}

private theorem apply_eq_zero_of_isLocalMaxOn_closedBall
    (hf : HasFDerivAt f L x) (hr : 0 < r) (hx : ‖x - c‖ = r)
    (hmax : IsLocalMaxOn f (closedBall c r) x) {v : E} (hv : ⟪x - c, v⟫ = 0) : L v = 0 := by
  have hg : HasDerivAt (fun t : ℝ => x - c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (x - c)
  have hgnorm : HasDerivAt (fun t : ℝ => ‖x - c + t • v‖) 0 0 := by
    simpa [hv] using hg.norm_sq.sqrt (by simpa [hx] using pow_ne_zero 2 hr.ne')
  have hscale : HasDerivAt (fun t : ℝ => r / ‖x - c + t • v‖) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) r).div hgnorm (by simpa [hx] using hr.ne') using 1
    simp
  let γ : ℝ → E := fun t => c + (r / ‖x - c + t • v‖) • (x - c + t • v)
  have hγ : HasDerivAt γ v 0 := by
    convert! (hscale.smul hg).const_add c using 1
    simp [hx, hr.ne']
  have hγ0 : γ 0 = x := by simp [γ, hx, hr.ne']
  have hnorm : ∀ᶠ t in 𝓝 (0 : ℝ), x - c + t • v ≠ 0 :=
    hg.continuousAt.eventually_ne (by simpa using (norm_ne_zero_iff.mp (hx.trans_ne hr.ne')))
  have hγmem : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ closedBall c r := by
    filter_upwards [hnorm] with t ht
    rw [mem_closedBall, dist_eq_norm]
    dsimp [γ]
    rw [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr, abs_norm,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr ht)]
  have hγlim : Tendsto γ (𝓝 0) (𝓝[closedBall c r] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hγ0 ▸ hγ.continuousAt, hγmem⟩
  have hlocal : IsLocalMax (f ∘ γ) 0 := by
    simpa only [IsLocalMax, IsMaxFilter, Function.comp_apply, hγ0] using hγlim.eventually hmax
  exact hlocal.hasDerivAt_eq_zero ((hγ0.symm ▸ hf).comp_hasDerivAt 0 hγ)

theorem exists_nonneg_eq_smul_inner_of_isLocalMaxOn_closedBall
    (hf : HasFDerivAt f L x) (hr : 0 < r) (hx : ‖x - c‖ = r)
    (hmax : IsLocalMaxOn f (closedBall c r) x) :
    ∃ a : ℝ, 0 ≤ a ∧ L = a • innerSL ℝ (x - c) := by
  have hform (v : E) : L v = (⟪x - c, v⟫ / r ^ 2) * L (x - c) := by
    let w := v - (⟪x - c, v⟫ / r ^ 2) • (x - c)
    have hw : ⟪x - c, w⟫ = 0 := by
      dsimp [w]
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hx]
      field_simp
      ring
    have hzero := hf.apply_eq_zero_of_isLocalMaxOn_closedBall hr hx hmax hw
    simpa only [w, map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hzero
  have hcone : -(x - c) ∈ posTangentConeAt (closedBall c r) x := by
    simpa only [neg_sub] using sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall c r).segment_subset
        (by simpa only [mem_closedBall, dist_eq_norm] using hx.le) (mem_closedBall_self hr.le))
  have hnonpos := hmax.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hcone
  have hnonneg : 0 ≤ L (x - c) := by simpa using hnonpos
  refine ⟨L (x - c) / r ^ 2, div_nonneg hnonneg (sq_nonneg r), ?_⟩
  ext v
  change L v = (L (x - c) / r ^ 2) * ⟪x - c, v⟫
  rw [hform]
  ring

theorem exists_pos_eq_smul_inner_of_isLocalMaxOn_closedBall
    (hf : HasFDerivAt f L x) (hL : L ≠ 0) (hr : 0 < r) (hx : ‖x - c‖ = r)
    (hmax : IsLocalMaxOn f (closedBall c r) x) :
    ∃ a : ℝ, 0 < a ∧ L = a • innerSL ℝ (x - c) := by
  obtain ⟨a, ha, hLa⟩ := hf.exists_nonneg_eq_smul_inner_of_isLocalMaxOn_closedBall hr hx hmax
  refine ⟨a, lt_of_le_of_ne ha ?_, hLa⟩
  rintro rfl
  exact hL (by simpa only [zero_smul] using hLa)

section MapsToBall

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {g : E → F} {A : E →L[ℝ] F} {d : F} {s : ℝ}

theorem exists_pos_inner_eq_mul_inner_of_eventually_mem_closedBall
    (hg : HasFDerivAt g A x) (hA : Function.Surjective A)
    (hr : 0 < r) (hs : 0 < s) (hx : ‖x - c‖ = r) (hgx : ‖g x - d‖ = s)
    (hmap : ∀ᶠ y in 𝓝[closedBall c r] x, g y ∈ closedBall d s) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : E, ⟪g x - d, A v⟫ = a * ⟪x - c, v⟫ := by
  have hmax : IsLocalMaxOn (fun y => ‖g y - d‖ ^ 2) (closedBall c r) x := by
    filter_upwards [hmap] with y hy
    rw [hgx]
    exact (sq_le_sq₀ (norm_nonneg _) hs.le).mpr
      (by simpa only [mem_closedBall, dist_eq_norm] using hy)
  have hne : 2 • (innerSL ℝ (g x - d)).comp A ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := hA (g x - d)
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) hzero
    simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, zero_apply, hv,
      real_inner_self_eq_norm_sq, hgx] at hh
    nlinarith
  obtain ⟨a, ha, heq⟩ := (hg.sub_const d).norm_sq.exists_pos_eq_smul_inner_of_isLocalMaxOn_closedBall
    hne hr hx hmax
  refine ⟨a / 2, half_pos ha, ?_⟩
  intro v
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
  simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_apply, smul_eq_mul] at hh
  linarith

theorem exists_pos_inner_eq_mul_inner_of_mapsTo_closedBall
    (hg : HasFDerivAt g A x) (hA : Function.Surjective A)
    (hr : 0 < r) (hs : 0 < s) (hx : ‖x - c‖ = r) (hgx : ‖g x - d‖ = s)
    (hmap : MapsTo g (closedBall c r) (closedBall d s)) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : E, ⟪g x - d, A v⟫ = a * ⟪x - c, v⟫ := by
  apply hg.exists_pos_inner_eq_mul_inner_of_eventually_mem_closedBall hA hr hs hx hgx
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hmap hy

end MapsToBall

end HasFDerivAt
