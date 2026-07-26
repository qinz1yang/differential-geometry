import DifferentialGeometry.Analysis.ODE.GlobalLipschitzAffineExistence
import DifferentialGeometry.Analysis.ODE.SecondOrderGronwall
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

set_option linter.unusedSectionVars false

/-!
# Global forward solutions of second-order linear ODEs

`y'' = A(t) y` with an operator family `A` that is pointwise continuous in
time and uniformly bounded on the window has global forward solutions on
`[0, T]` for arbitrary initial position and velocity.  This is the linear-ODE
existence input of the Jacobi-field construction along intrinsic geodesics
(brick J-b of the option-1 route in
`Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`): the Jacobi equation in a
parallel orthonormal frame is exactly such a system.

The proof runs the first-order engine
`forward_solution_of_lipschitzWith_affineBound` on the phase space
`WithLp 2 (F × F)` — the plain product carries no inner-product structure, and
the engine's ball retraction is Hilbert-only — with the field
`f t z = (z₂, A t z₁)`, Lipschitz constant `max 1 M`, and affine constant `0`.

## Main result

* `forward_ode2_of_bound` — global forward solution pair `(y, v)` with
  `y' = v`, `v' = A t y` (`HasDerivWithinAt` on `Ici 0`, at every
  `t ∈ [0, T)`), continuous on `[0, T]`, with prescribed `y 0` and `v 0`.
  The sign convention is neutral: for the Jacobi system pass `-A`.
-/

open Set WithLp
open scoped NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Global forward existence for `y'' = A(t) y`.**  If each `A t` is a
continuous linear operator, `t ↦ A t x` is continuous on `[0, T]` for every
`x`, and `‖A t‖ ≤ M` on `[0, T]`, then for arbitrary initial position `y₀`
and velocity `v₀` there is a pair `(y, v)` on `[0, T]` with `y 0 = y₀`,
`v 0 = v₀`, both continuous on `[0, T]`, and `y' = v`, `v' = A t y` in the
forward (`Ici 0`) sense at every `t ∈ [0, T)`. -/
theorem forward_ode2_of_bound
    {A : ℝ → F →L[ℝ] F} {T : ℝ} (hT : 0 < T)
    (hAcont : ∀ x : F, ContinuousOn (fun t => A t x) (Icc (0 : ℝ) T))
    {M : ℝ} (hAbd : ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ M)
    (y₀ v₀ : F) :
    ∃ y v : ℝ → F, y 0 = y₀ ∧ v 0 = v₀ ∧
      ContinuousOn y (Icc (0 : ℝ) T) ∧ ContinuousOn v (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt y (v t) (Ici (0 : ℝ)) t) ∧
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt v (A t (y t)) (Ici (0 : ℝ)) t) := by
  classical
  -- the uniform Lipschitz constant
  have hM0 : 0 ≤ max 1 M := le_trans zero_le_one (le_max_left 1 M)
  set K : ℝ≥0 := ⟨max 1 M, hM0⟩ with hK_def
  have hAbd' : ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ (K : ℝ) :=
    fun t ht => le_trans (hAbd t ht) (le_max_right 1 M)
  -- the phase-space field `f t z = (z₂, A t z₁)`
  set f : ℝ → WithLp 2 (F × F) → WithLp 2 (F × F) :=
    fun t z => toLp 2 (z.snd, A t z.fst) with hf_def
  have hf_fst : ∀ t z, (f t z).fst = z.snd := fun _ _ => rfl
  have hf_snd : ∀ t z, (f t z).snd = A t z.fst := fun _ _ => rfl
  -- Lipschitz bound via the L² norm formula
  have hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (f t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub_fst : (f t z - f t w).fst = z.snd - w.snd := by
      simp [hf_def]
    have hsub_snd : (f t z - f t w).snd = A t (z.fst - w.fst) := by
      simp [hf_def]
    have hzw_fst : (z - w).fst = z.fst - w.fst := rfl
    have hzw_snd : (z - w).snd = z.snd - w.snd := rfl
    have hsq : ‖f t z - f t w‖ ^ 2 ≤ ((K : ℝ) * ‖z - w‖) ^ 2 := by
      rw [prod_norm_sq_eq_of_L2, hsub_fst, hsub_snd, mul_pow,
        prod_norm_sq_eq_of_L2, hzw_fst, hzw_snd, mul_add]
      have h1 : ‖z.snd - w.snd‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖z.snd - w.snd‖ ^ 2 := by
        have hK1 : (1 : ℝ) ≤ (K : ℝ) := le_max_left 1 M
        have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
        exact le_mul_of_one_le_left (sq_nonneg _) hK2
      have h2 : ‖A t (z.fst - w.fst)‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖z.fst - w.fst‖ ^ 2 := by
        have := (A t).le_opNorm (z.fst - w.fst)
        have hAt : ‖A t (z.fst - w.fst)‖ ≤ (K : ℝ) * ‖z.fst - w.fst‖ :=
          le_trans this (mul_le_mul_of_nonneg_right (hAbd' t ht) (norm_nonneg _))
        nlinarith [norm_nonneg (A t (z.fst - w.fst)),
          mul_nonneg (K.coe_nonneg) (norm_nonneg (z.fst - w.fst))]
      linarith
    have hnn : 0 ≤ (K : ℝ) * ‖z - w‖ := mul_nonneg K.coe_nonneg (norm_nonneg _)
    calc ‖f t z - f t w‖
        = Real.sqrt (‖f t z - f t w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (((K : ℝ) * ‖z - w‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (K : ℝ) * ‖z - w‖ := Real.sqrt_sq hnn
  -- continuity in time at every fixed point
  have hcont : ∀ z : WithLp 2 (F × F),
      ContinuousOn (fun t => f t z) (Icc (0 : ℝ) T) := by
    intro z
    have hpair : ContinuousOn (fun t => ((z.snd, A t z.fst) : F × F))
        (Icc (0 : ℝ) T) := continuousOn_const.prodMk (hAcont z.fst)
    exact ((prodContinuousLinearEquiv 2 ℝ F F).symm.continuous.comp_continuousOn
      hpair)
  -- affine bound with `C = 0`
  have haff : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : WithLp 2 (F × F),
      ‖f t z‖ ≤ 0 + (K : ℝ) * ‖z‖ := by
    intro t ht z
    have h0 : f t 0 = 0 := by
      simp [hf_def]
    have := (hlip t ht).dist_le_mul z 0
    rw [dist_eq_norm, dist_eq_norm, h0, sub_zero, sub_zero] at this
    linarith
  -- run the first-order engine on the phase space
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound (f := f) hT (le_refl 0)
      hlip hcont haff (toLp 2 (y₀, v₀))
  refine ⟨fun t => (γ t).fst, fun t => (γ t).snd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (γ 0).fst = y₀
    rw [hγ0]; rfl
  · show (γ 0).snd = v₀
    rw [hγ0]; rfl
  · exact ((ContinuousLinearMap.fst ℝ F F).comp
      (prodContinuousLinearEquiv 2 ℝ F F).toContinuousLinearMap)
      |>.continuous.comp_continuousOn hγcont
  · exact ((ContinuousLinearMap.snd ℝ F F).comp
      (prodContinuousLinearEquiv 2 ℝ F F).toContinuousLinearMap)
      |>.continuous.comp_continuousOn hγcont
  · intro t ht
    have h := ((ContinuousLinearMap.fst ℝ F F).comp
        (prodContinuousLinearEquiv 2 ℝ F F).toContinuousLinearMap)
      |>.hasFDerivAt.comp_hasDerivWithinAt t (hγderiv t ht)
    simpa using h
  · intro t ht
    have h := ((ContinuousLinearMap.snd ℝ F F).comp
        (prodContinuousLinearEquiv 2 ℝ F F).toContinuousLinearMap)
      |>.hasFDerivAt.comp_hasDerivWithinAt t (hγderiv t ht)
    simpa using h

/-- **Zero solution of a componentwise second-order system with zero initial
data.**  If each scalar coordinate `y · i` is continuous on `[0, b]` with
forward derivatives `y' = v`, `v' = w` on `[0, b)`, the second derivative is
dominated by the coordinates (`|w t i| ≤ C * ∑ j, |y t j|`), and
`y 0 = v 0 = 0`, then `y ≡ 0` on `[0, b]`.  This is the Grönwall closer of
the frame-coordinate Jacobi uniqueness argument (brick J-remaining (d)). -/
theorem ode2_pi_zero
    {ι : Type*} [Fintype ι]
    {y v w : ℝ → ι → ℝ} {b C : ℝ} (hC : 0 ≤ C)
    (hcy : ∀ i, ContinuousOn (fun t => y t i) (Icc (0 : ℝ) b))
    (hcv : ∀ i, ContinuousOn (fun t => v t i) (Icc (0 : ℝ) b))
    (hdy : ∀ t ∈ Ico (0 : ℝ) b, ∀ i,
      HasDerivWithinAt (fun s => y s i) (v t i) (Ici t) t)
    (hdv : ∀ t ∈ Ico (0 : ℝ) b, ∀ i,
      HasDerivWithinAt (fun s => v s i) (w t i) (Ici t) t)
    (hbound : ∀ t ∈ Ico (0 : ℝ) b, ∀ i, |w t i| ≤ C * ∑ j, |y t j|)
    (h0 : ∀ i, y 0 i = 0) (h0' : ∀ i, v 0 i = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, ∀ i, y t i = 0 := by
  classical
  set n : ℕ := Fintype.card ι with hn
  set K : ℝ := C * n with hKdef
  have hKnn : 0 ≤ K := mul_nonneg hC (Nat.cast_nonneg n)
  set L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm with hL
  set Y : ℝ → EuclideanSpace ℝ ι := fun t => L (y t) with hYdef
  set V : ℝ → EuclideanSpace ℝ ι := fun t => L (v t) with hVdef
  set W : ℝ → EuclideanSpace ℝ ι := fun t => L (w t) with hWdef
  have happly : ∀ (u : ι → ℝ) (i : ι), (L u : EuclideanSpace ℝ ι) i = u i :=
    fun _ _ => rfl
  have hcY : ContinuousOn Y (Icc (0 : ℝ) b) :=
    L.continuous.comp_continuousOn (continuousOn_pi.mpr hcy)
  have hcV : ContinuousOn V (Icc (0 : ℝ) b) :=
    L.continuous.comp_continuousOn (continuousOn_pi.mpr hcv)
  have hdY : ∀ t ∈ Ico (0 : ℝ) b, HasDerivWithinAt Y (V t) (Ici t) t := by
    intro t ht
    exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_pi.mpr (hdy t ht))
  have hdV : ∀ t ∈ Ico (0 : ℝ) b, HasDerivWithinAt V (W t) (Ici t) t := by
    intro t ht
    exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_pi.mpr (hdv t ht))
  have hWnorm : ∀ t, ‖W t‖ ^ 2 = ∑ i, (w t i) ^ 2 := by
    intro t
    rw [hWdef, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [happly, Real.norm_eq_abs, sq_abs]
  have hYnorm : ∀ t, ‖Y t‖ ^ 2 = ∑ i, (y t i) ^ 2 := by
    intro t
    rw [hYdef, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [happly, Real.norm_eq_abs, sq_abs]
  have hWle : ∀ t ∈ Ico (0 : ℝ) b, ‖W t‖ ≤ K * ‖Y t‖ + 0 := by
    intro t ht
    rw [add_zero]
    have habs : ∀ j, |y t j| ^ 2 = (y t j) ^ 2 := fun j => sq_abs _
    have hsum_sq : (∑ j, |y t j|) ^ 2 ≤ (n : ℝ) * ∑ j, (y t j) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset ι)) (f := fun j => |y t j|)
      simpa [hn, habs] using this
    have hterm : ∀ i, (w t i) ^ 2 ≤ C ^ 2 * (∑ j, |y t j|) ^ 2 := by
      intro i
      have h1 := hbound t ht i
      have h2 : (0 : ℝ) ≤ C * ∑ j, |y t j| :=
        mul_nonneg hC (Finset.sum_nonneg fun j _ => abs_nonneg _)
      calc (w t i) ^ 2 = |w t i| ^ 2 := (sq_abs _).symm
        _ ≤ (C * ∑ j, |y t j|) ^ 2 := by
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = C ^ 2 * (∑ j, |y t j|) ^ 2 := by ring
    have hsq : ‖W t‖ ^ 2 ≤ (K * ‖Y t‖) ^ 2 := by
      rw [hWnorm]
      have hsumw : ∑ i, (w t i) ^ 2 ≤ (n : ℝ) * (C ^ 2 * (∑ j, |y t j|) ^ 2) := by
        calc ∑ i, (w t i) ^ 2
            ≤ ∑ _i : ι, C ^ 2 * (∑ j, |y t j|) ^ 2 :=
              Finset.sum_le_sum fun i _ => hterm i
          _ = (n : ℝ) * (C ^ 2 * (∑ j, |y t j|) ^ 2) := by
              rw [Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul]
      calc ∑ i, (w t i) ^ 2
          ≤ (n : ℝ) * (C ^ 2 * (∑ j, |y t j|) ^ 2) := hsumw
        _ ≤ (n : ℝ) * (C ^ 2 * ((n : ℝ) * ∑ j, (y t j) ^ 2)) := by
            have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg _
            have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsum_sq hC2) hn0
        _ = (K * ‖Y t‖) ^ 2 := by
            rw [mul_pow, hYnorm t, hKdef]; ring
    have hnn : 0 ≤ K * ‖Y t‖ := mul_nonneg hKnn (norm_nonneg _)
    calc ‖W t‖ = Real.sqrt (‖W t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((K * ‖Y t‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = K * ‖Y t‖ := Real.sqrt_sq hnn
  have hY0 : ‖Y 0‖ ≤ 0 := by
    have hy0 : y 0 = 0 := funext h0
    have hz : Y 0 = 0 := by
      show L (y 0) = 0
      rw [hy0, map_zero]
    rw [hz, norm_zero]
  have hV0 : ‖V 0‖ ≤ 0 := by
    have hv0 : v 0 = 0 := funext h0'
    have hz : V 0 = 0 := by
      show L (v 0) = 0
      rw [hv0, map_zero]
    rw [hz, norm_zero]
  have hg := norm_le_gronwall_secondOrder (Y := Y) (Y' := V) (Y'' := W)
    hKnn le_rfl hcY hcV hdY hdV hWle hY0 hV0
  have hzero : ∀ x : ℝ, gronwallBound 0 (max K 1) 0 x = 0 := by
    intro x
    have h := gronwallBound_zero_mul_eps (K := max K 1) (eps := (1 : ℝ))
      (a := (0 : ℝ)) (x := x)
    simpa using h
  intro t ht i
  have hYt : Y t = 0 := by
    have h1 := hg t ht
    rw [hzero t] at h1
    exact norm_le_zero_iff.mp h1
  have : y t i = (Y t) i := (happly (y t) i).symm
  rw [this, hYt]
  rfl

end DifferentialGeometry.Analysis.ODE
