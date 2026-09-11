import DifferentialGeometry.Analysis.Parabolic.Energy.ParabolicLocalAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def travelingBallPhase (T : ℝ) (x₀ : E3) (r t : ℝ) (x : E3) : ℝ :=
  r ^ 2 - ‖x - (t / T) • x₀‖ ^ 2

private theorem phase_contDiff (T : ℝ) (x₀ : E3) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E3 => travelingBallPhase T x₀ r p.1 p.2) := by
  have hpath : ContDiff ℝ ∞ (fun p : ℝ × E3 => (p.1 / T) • x₀) :=
    (contDiff_fst.div_const T).smul contDiff_const
  exact contDiff_const.sub ((contDiff_snd.sub hpath).norm_sq ℝ)

private theorem phase_space (T : ℝ) (x₀ : E3) (r t : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (travelingBallPhase T x₀ r t) := by
  have h : ContDiff ℝ ∞ (fun x : E3 => r ^ 2 - ‖x - (t / T) • x₀‖ ^ 2) :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  exact h.contMDiff

private theorem phase_time (T : ℝ) (x₀ : E3) (r t : ℝ) (x : E3) :
    DifferentiableWithinAt ℝ (fun s => travelingBallPhase T x₀ r s x) (Icc 0 T) t := by
  have hp : ContDiff ℝ ∞ (fun s : ℝ => x - (s / T) • x₀) :=
    contDiff_const.sub ((contDiff_id.div_const T).smul contDiff_const)
  have h : ContDiff ℝ ∞ (fun s : ℝ => r ^ 2 - ‖x - (s / T) • x₀‖ ^ 2) :=
    contDiff_const.sub (hp.norm_sq ℝ)
  exact (h.differentiable (by simp) t).differentiableWithinAt

private def smoothTravelingBump (T : ℝ) (x₀ : E3) (r ε A t : ℝ) (x : E3) : ℝ :=
  ε * Real.exp (-A * t) * travelingBallPhase T x₀ r t x ^ 2

private theorem smooth_bump_contDiff (T : ℝ) (x₀ : E3) (r ε A : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E3 => smoothTravelingBump T x₀ r ε A p.1 p.2) := by
  exact (contDiff_const.mul (Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_fst))).mul ((phase_contDiff T x₀ r).pow 2)

private theorem smooth_bump_space (T : ℝ) (x₀ : E3) (r ε A t : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (smoothTravelingBump T x₀ r ε A t) := by
  have h : ContDiff ℝ ∞ (fun x : E3 => smoothTravelingBump T x₀ r ε A t x) :=
    (smooth_bump_contDiff T x₀ r ε A).comp (contDiff_const.prodMk contDiff_id)
  exact h.contMDiff

private theorem smooth_bump_time (T : ℝ) (x₀ : E3) (r ε A t : ℝ) (x : E3) :
    DifferentiableWithinAt ℝ (fun s => smoothTravelingBump T x₀ r ε A s x) (Icc 0 T) t := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => smoothTravelingBump T x₀ r ε A s x) :=
    (smooth_bump_contDiff T x₀ r ε A).comp (contDiff_id.prodMk contDiff_const)
  exact (h.differentiable (by simp) t).differentiableWithinAt

private theorem smooth_bump_operator
    (G : MetricConnectionFamily (I := 𝓡 3) (M := E3) ℝ)
    (T : ℝ) (hT : 0 < T) (x₀ : E3) (r ε A t : ℝ) (ht : t ∈ Icc 0 T) (x : E3) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
      (smoothTravelingBump T x₀ r ε A) t x =
        ε * Real.exp (-A * t) *
          (2 * travelingBallPhase T x₀ r t x *
              parabolicOperatorWithDrift G T (fun _ _ => 0) (travelingBallPhase T x₀ r) t x -
            2 * (G.metric t).inner x
              (gradientAt G t (travelingBallPhase T x₀ r t) x)
              (gradientAt G t (travelingBallPhase T x₀ r t) x) -
            A * travelingBallPhase T x₀ r t x ^ 2) := by
  let F := travelingBallPhase T x₀ r
  have hspace := phase_space T x₀ r t
  have htime := phase_time T x₀ r t x
  have hgrad := gradientFun_mdiffAt (G.metric t) hspace x
  have hnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (F t) y :=
    Eventually.of_forall fun y => hspace.mdifferentiableAt (by simp)
  have hmul := parabolic_mul_local G T (fun _ _ => 0) F F t x
    htime htime hnear hnear hgrad hgrad
  have hsquare : parabolicOperatorWithDrift G T (fun _ _ => 0)
      (fun s y => F s y ^ 2) t x =
        2 * F t x * parabolicOperatorWithDrift G T (fun _ _ => 0) F t x -
          2 * (G.metric t).inner x
            (gradientAt G t (F t) x) (gradientAt G t (F t) x) := by
    simpa only [pow_two, two_mul, add_mul] using hmul
  have hsqspace : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => F t y ^ 2) := hspace.pow 2
  have ha : HasDerivAt (fun s : ℝ => ε * Real.exp (-A * s))
      (-A * (ε * Real.exp (-A * t))) t := by
    have hh := ((Real.hasDerivAt_exp (-A * t)).comp t
      ((hasDerivAt_id t).const_mul (-A))).const_mul ε
    simpa only [Function.comp_def, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh
  have hprod := parabolic_time_mul_local G T (fun _ _ => 0)
    (fun s y => F s y ^ 2) t x (htime.pow 2)
    (Eventually.of_forall fun y => hsqspace.mdifferentiableAt (by simp))
    (gradientFun_mdiffAt (G.metric t) hsqspace x)
    (fun s => ε * Real.exp (-A * s)) (-A * (ε * Real.exp (-A * t)))
    ha.hasDerivWithinAt ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
  rw [hsquare] at hprod
  change parabolicOperatorWithDrift G T (fun _ _ => 0)
    (fun s y => ε * Real.exp (-A * s) * F s y ^ 2) t x = _
  rw [hprod]
  ring

private theorem quadratic_barrier_bound (D L A f : ℝ) (hL : 0 < L)
    (hAL : A * L = D ^ 2) :
    2 * D * f - 2 * L - A * f ^ 2 ≤ -L := by
  apply (mul_le_mul_iff_left₀ hL).mp
  calc
    (2 * D * f - 2 * L - A * f ^ 2) * L =
        -(D * f - L) ^ 2 - L ^ 2 - (A * L - D ^ 2) * f ^ 2 := by ring
    _ ≤ -L ^ 2 := by
      rw [hAL, sub_self, zero_mul, sub_zero]
      linarith only [sq_nonneg (D * f - L)]
    _ = (-L) * L := by ring

private theorem path_norm_le (T : ℝ) (hT : 0 < T) (x₀ : E3)
    (t : ℝ) (ht : t ∈ Icc 0 T) : ‖(t / T) • x₀‖ ≤ ‖x₀‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht.1 hT.le)]
  calc
    (t / T) * ‖x₀‖ ≤ 1 * ‖x₀‖ :=
      mul_le_mul_of_nonneg_right ((div_le_one hT).mpr ht.2) (norm_nonneg x₀)
    _ = ‖x₀‖ := one_mul _

theorem positive_of_traveling_ball_upper_supports
    (G : MetricConnectionFamily (I := 𝓡 3) (M := E3) ℝ)
    (T : ℝ) (hT : 0 < T) (x₀ : E3) (r η C c : ℝ)
    (hr : 0 < r) (hη : 0 < η) (hc : 0 < c)
    (u : ℝ → E3 → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × E3 => u p.1 p.2) (spacetimeSlab (M := E3) T))
    (hnonneg : ∀ t ∈ Icc 0 T, ∀ x : E3, 0 ≤ u t x)
    (hsupport : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : E3,
      Nonempty (ParabolicUpperSupportAt G T (fun _ _ => 0) u t x))
    (hinit : ∀ x ∈ Metric.closedBall (0 : E3) r, η ≤ u 0 x)
    (hphase : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : E3,
      0 < travelingBallPhase T x₀ r t x →
        parabolicOperatorWithDrift G T (fun _ _ => 0) (travelingBallPhase T x₀ r) t x ≤ C)
    (hgradient : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : E3,
      0 < travelingBallPhase T x₀ r t x →
        c * ‖x - (t / T) • x₀‖ ^ 2 ≤
          (G.metric t).inner x
            (gradientAt G t (travelingBallPhase T x₀ r t) x)
            (gradientAt G t (travelingBallPhase T x₀ r t) x)) :
    0 < u T x₀ := by
  classical
  let F := travelingBallPhase T x₀ r
  let L : ℝ := c * r ^ 2
  have hL : 0 < L := mul_pos hc (sq_pos_of_pos hr)
  let D : ℝ := C + c
  let A : ℝ := D ^ 2 / L
  have hAL : A * L = D ^ 2 := div_mul_cancel₀ _ hL.ne'
  let ε : ℝ := η / (r ^ 4 + 1)
  have hden : 0 < r ^ 4 + 1 := by positivity
  have hε : 0 < ε := div_pos hη hden
  have hεeq : ε * (r ^ 4 + 1) = η := div_mul_cancel₀ _ hden.ne'
  have hεbound : ε * r ^ 4 ≤ η := by nlinarith only [hεeq, hε.le]
  let b := smoothTravelingBump T x₀ r ε A
  let v : ℝ → E3 → ℝ := fun t x => ε * Real.exp (-A * t) * (max (F t x) 0) ^ 2
  let w : ℝ → E3 → ℝ := fun t x => u t x - v t x
  let K : Set E3 := Metric.closedBall 0 (r + ‖x₀‖)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hFcont : Continuous (fun p : ℝ × E3 => F p.1 p.2) :=
    (phase_contDiff T x₀ r).continuous
  have hvcont : Continuous (fun p : ℝ × E3 => v p.1 p.2) :=
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_fst))).mul ((hFcont.max continuous_const).pow 2)
  have hclip (t : ℝ) (x : E3) (hf : 0 < F t x) : v t x = b t x := by
    dsimp only [v, b, smoothTravelingBump]
    rw [max_eq_left hf.le]
  have hbnegative (t : ℝ) (ht : t ∈ Icc 0 T) (htpos : 0 < t)
      (x : E3) (hf : 0 < F t x) :
      parabolicOperatorWithDrift G T (fun _ _ => 0) b t x < 0 := by
    have hp := mul_le_mul_of_nonneg_left (hphase t ht htpos x hf)
      (show 0 ≤ 2 * F t x by positivity)
    have hg := hgradient t ht htpos x hf
    have hphase_eq : ‖x - (t / T) • x₀‖ ^ 2 = r ^ 2 - F t x := by
      dsimp only [F, travelingBallPhase]
      ring
    rw [hphase_eq] at hg
    have hbound :
        2 * F t x * parabolicOperatorWithDrift G T (fun _ _ => 0) F t x -
          2 * (G.metric t).inner x (gradientAt G t (F t) x) (gradientAt G t (F t) x) -
          A * F t x ^ 2 ≤ -L := by
      calc
        _ ≤ 2 * D * F t x - 2 * L - A * F t x ^ 2 := by
          dsimp only [D, L]
          nlinarith only [hp, hg]
        _ ≤ -L := quadratic_barrier_bound D L A (F t x) hL hAL
    rw [smooth_bump_operator G T hT x₀ r ε A t ht x]
    exact mul_neg_of_pos_of_neg (mul_pos hε (Real.exp_pos _))
      (hbound.trans_lt (neg_neg_of_pos hL))
  have hnonnegative := strict_barrier_compact_of_upperSupport G T (fun _ _ => 0) w K hK
    (fun t ht x hx => by
      have hxnorm : r + ‖x₀‖ < ‖x‖ := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      have hpath := path_norm_le T hT x₀ t ht
      have htriangle : ‖x‖ ≤ ‖x - (t / T) • x₀‖ + ‖(t / T) • x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x - (t / T) • x₀) ((t / T) • x₀)
      have hdist : r ≤ ‖x - (t / T) • x₀‖ := by linarith only [hxnorm, hpath, htriangle]
      have hf : F t x ≤ 0 := by
        dsimp only [F, travelingBallPhase]
        have hs := (sq_le_sq₀ hr.le (norm_nonneg _)).mpr hdist
        linarith only [hs]
      have hvzero : v t x = 0 := by simp only [v, max_eq_right hf, zero_pow (by decide : 2 ≠ 0), mul_zero]
      dsimp only [w]
      rw [hvzero, sub_zero]
      exact hnonneg t ht x)
    ((hcont.mono (prod_mono subset_rfl (subset_univ K))).sub hvcont.continuousOn)
    (fun x => by
      have hf0 : F 0 x = r ^ 2 - ‖x‖ ^ 2 := by
        simp only [F, travelingBallPhase, zero_div, zero_smul, sub_zero]
      by_cases hx : x ∈ Metric.closedBall (0 : E3) r
      · have hmax : max (F 0 x) 0 ≤ r ^ 2 :=
          max_le (by rw [hf0]; linarith only [sq_nonneg ‖x‖]) (sq_nonneg r)
        have hsquare : (max (F 0 x) 0) ^ 2 ≤ r ^ 4 := by
          have hh := (sq_le_sq₀ (le_max_right (F 0 x) 0) (sq_nonneg r)).mpr hmax
          calc
            (max (F 0 x) 0) ^ 2 ≤ (r ^ 2) ^ 2 := hh
            _ = r ^ 4 := by ring
        have hvbound : v 0 x ≤ η := by
          simp only [v, mul_zero, Real.exp_zero, mul_one]
          exact (mul_le_mul_of_nonneg_left hsquare hε.le).trans hεbound
        dsimp only [w]
        exact sub_nonneg.mpr (hvbound.trans (hinit x hx))
      · have hxnorm : r < ‖x‖ := by
          simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
        have hf : F 0 x ≤ 0 := by
          rw [hf0]
          have hs := (sq_le_sq₀ hr.le (norm_nonneg _)).mpr hxnorm.le
          linarith only [hs]
        have hvzero : v 0 x = 0 := by simp only [v, max_eq_right hf, zero_pow (by decide : 2 ≠ 0), mul_zero]
        dsimp only [w]
        rw [hvzero, sub_zero]
        exact hnonneg 0 ⟨le_rfl, hT.le⟩ x)
    (fun t ht htpos x hnegative => by
      have hvpos : 0 < v t x := by
        have hu := hnonneg t ht x
        dsimp only [w] at hnegative
        linarith only [hu, hnegative]
      have hf : 0 < F t x := by
        by_contra hnot
        have hvzero : v t x = 0 := by
          simp only [v, max_eq_right (le_of_not_gt hnot), zero_pow (by decide : 2 ≠ 0), mul_zero]
        exact (ne_of_gt hvpos) hvzero
      let q := Classical.choice (hsupport t ht htpos x)
      let U : ℝ → E3 → ℝ := fun s y => q.upperSupport s y + (-b s y)
      have hbtime := smooth_bump_time T x₀ r ε A t x
      have hbspace := smooth_bump_space T x₀ r ε A t
      have hbgrad := gradientFun_mdiffAt (G.metric t) hbspace x
      have hnegspace := hbspace.neg
      have hneggrad := gradientFun_mdiffAt (G.metric t) hnegspace x
      have hnearneg : ∀ᶠ y in 𝓝 x, MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun z => -b t z) y :=
        Eventually.of_forall fun y => hnegspace.mdifferentiableAt (by simp)
      have hUgrad : MDifferentiableAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E3))
          (T% (gradientFun (G.metric t) (U t))) x := by
        apply (mdifferentiableAt_add_section q.grad_diff hneggrad).congr_of_eventuallyEq
        filter_upwards [q.space_diff_nhds] with y hy
        apply congrArg (fun z => (⟨y, z⟩ : TotalSpace E3 (TangentSpace (𝓡 3))))
        exact gradientFun_add (G.metric t) hy (hnegspace.mdifferentiableAt (by simp))
      have hFnear : ∀ᶠ p in 𝓝[spacetimeSlab (M := E3) T] (t, x), 0 < F p.1 p.2 :=
        mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const hFcont).mem_nhds hf)
      refine
        { upperSupport := U
          eq_at := ?_
          upper_nhds := ?_
          time_diff := q.time_diff.add hbtime.neg
          space_diff_nhds := q.space_diff_nhds.mono
            (fun y hy => hy.add (hnegspace.mdifferentiableAt (by simp)))
          grad_diff := hUgrad
          operator_nonneg := ?_ }
      · dsimp only [U, w]
        rw [q.eq_at, hclip t x hf]
        ring
      · filter_upwards [q.upper_nhds, hFnear] with p hp hFp
        change u p.1 p.2 - v p.1 p.2 ≤ q.upperSupport p.1 p.2 + (-b p.1 p.2)
        rw [hclip p.1 p.2 hFp]
        linarith only [hp]
      · have hneg := parabolic_neg G T (fun _ _ => 0) b t x hbtime
          (fun y => hbspace.mdifferentiableAt (by simp)) hbgrad
        have hadd := parabolic_add_local G T (fun _ _ => 0) q.upperSupport (fun s y => -b s y) t x
          q.time_diff hbtime.neg q.space_diff_nhds hnearneg q.grad_diff hneggrad
        rw [hneg] at hadd
        have hb := hbnegative t ht htpos x hf
        change 0 ≤ parabolicOperatorWithDrift G T (fun _ _ => 0)
          (fun s y => q.upperSupport s y + (-b s y)) t x
        linarith only [hadd, q.operator_nonneg, hb])
  have hfinal := hnonnegative T ⟨hT.le, le_rfl⟩ x₀
  have hfend : F T x₀ = r ^ 2 := by
    simp only [F, travelingBallPhase, div_self hT.ne', one_smul, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0), sub_zero]
  have hvend : 0 < v T x₀ := by
    dsimp only [v]
    rw [hfend, max_eq_left (sq_nonneg r)]
    exact mul_pos (mul_pos hε (Real.exp_pos _)) (sq_pos_of_pos (sq_pos_of_pos hr))
  dsimp only [w] at hfinal
  linarith only [hfinal, hvend]
end DifferentialGeometry.Analysis
