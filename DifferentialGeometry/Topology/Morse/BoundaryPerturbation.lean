import DifferentialGeometry.Analysis.Calculus.CriticalPointPerturbation
import DifferentialGeometry.Topology.Morse.Separable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Support

open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Morse

variable {n : ℕ}

noncomputable def boundaryMorsePerturbation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (z : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 + b (Fin.tail z) *
    (a / 2 + Real.smoothAbs (a / 2) (z 0 - a / 2) - z 0)

private theorem contDiff_tail : ContDiff ℝ ∞ (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_apply ℝ ℝ i.succ

theorem contDiff_boundaryMorsePerturbation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) :
    ContDiff ℝ ∞ (boundaryMorsePerturbation c b a) := by
  have hq : ContDiff ℝ ∞ (fun z : Fin (n + 1) → ℝ => ∑ i : Fin n, c i * z i.succ ^ 2) := by
    fun_prop
  exact (hq.add (contDiff_apply ℝ ℝ 0)).add
    ((b.contDiff.comp contDiff_tail).mul
      ((contDiff_const.add ((Real.smoothAbs.contDiff (a / 2)).comp
        ((contDiff_apply ℝ ℝ 0).sub contDiff_const))).sub (contDiff_apply ℝ ℝ 0)))

theorem boundaryMorsePerturbation_eq_of_le (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a)
    (z : Fin (n + 1) → ℝ) (hz : a ≤ z 0) :
    boundaryMorsePerturbation c b a z = (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 := by
  unfold boundaryMorsePerturbation
  rw [Real.smoothAbs.eq_self_of_le (by linarith : 0 < a / 2) (by linarith : a / 2 ≤ z 0 - a / 2)]
  ring

theorem boundaryMorsePerturbation_eq_of_le_norm (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (z : Fin (n + 1) → ℝ)
    (hz : b.rOut ≤ ‖Fin.tail z‖) :
    boundaryMorsePerturbation c b a z = (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 := by
  have hb : b (Fin.tail z) = 0 := b.zero_of_le_dist (by simpa [dist_eq_norm] using hz)
  simp [boundaryMorsePerturbation, hb]

private theorem eventuallyEq_boundaryMorsePerturbation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (z : Fin (n + 1) → ℝ)
    (hz : ‖Fin.tail z‖ < b.rIn) :
    boundaryMorsePerturbation c b a =ᶠ[𝓝 z]
      (fun y => (∑ i : Fin n, c i * y i.succ ^ 2) +
        (a / 2 + Real.smoothAbs (a / 2) (y 0 - a / 2))) := by
  have hb := (b.eventuallyEq_one_of_mem_ball
    (by simpa [Metric.mem_ball, dist_eq_norm] using hz)).comp_tendsto
      (contDiff_tail.continuous.continuousAt (x := z))
  filter_upwards [hb] with y hy
  unfold boundaryMorsePerturbation
  change b (Fin.tail y) = 1 at hy
  rw [hy]
  ring

private theorem fderiv_boundaryMorsePerturbation_ne_zero_of_eq_zero (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (z : Fin (n + 1) → ℝ)
    (hb : b (Fin.tail z) = 0) : fderiv ℝ (boundaryMorsePerturbation c b a) z ≠ 0 := by
  intro hz
  let P := fun u : ℝ => Fin.cons u (Fin.tail z)
  have hP : HasDerivAt P (Fin.cons (1 : ℝ) (0 : Fin n → ℝ)) (z 0) := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hasDerivAt_id (z 0)
    · intro j
      exact hasDerivAt_const (z 0) ((Fin.tail z) j)
  have hF := ((contDiff_boundaryMorsePerturbation c b a).differentiable (by simp) z).hasFDerivAt
  have hzero : HasDerivAt (boundaryMorsePerturbation c b a ∘ P) 0 (z 0) := by
    have hPz : P (z 0) = z := Fin.cons_self_tail z
    have hF' : HasFDerivAt (boundaryMorsePerturbation c b a)
        (fderiv ℝ (boundaryMorsePerturbation c b a) z) (P (z 0)) := by
      rw [hPz]
      exact hF
    have hh := hF'.comp_hasDerivAt (z 0) hP
    simpa only [P, Fin.cons_self_tail, hz, zero_apply] using hh
  have hone : HasDerivAt (boundaryMorsePerturbation c b a ∘ P) 1 (z 0) := by
    convert! (hasDerivAt_id (z 0)).const_add (∑ i : Fin n, c i * z i.succ ^ 2) using 1
    funext u
    simp [boundaryMorsePerturbation, P, hb, Fin.tail]
  have hh := hzero.unique hone
  norm_num at hh

private theorem chartHessianAt_congr_eventuallyEq {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) :
    chartHessianAt f x = chartHessianAt g x := by
  ext v
  change fderiv ℝ (fderiv ℝ f) x v v = fderiv ℝ (fderiv ℝ g) x v v
  rw [h.fderiv.fderiv_eq]

private theorem isNondegenerateCriticalPointAt_congr_eventuallyEq {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E) f x ↔
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) g x := by
  simp only [IsNondegenerateCriticalPointAt, IsCriticalPointAt, mfderiv_eq_fderiv,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_symm, id_eq]
  rw [h.fderiv_eq, chartHessianAt_congr_eventuallyEq h]
  rfl

theorem chartHessianAt_boundaryMorsePerturbation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) :
    chartHessianAt (boundaryMorsePerturbation c b a) (Fin.cons (a / 2) 0) =
      QuadraticMap.weightedSumSquares ℝ (Fin.cons (4 / a) (fun i => 2 * c i)) := by
  rw [chartHessianAt_congr_eventuallyEq
    (eventuallyEq_boundaryMorsePerturbation c b a (Fin.cons (a / 2) 0)
      (by simpa using b.rIn_pos))]
  exact chartHessianAt_sum_sq_add_smoothAbs c a

theorem sigNeg_chartHessianAt_boundaryMorsePerturbation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    _root_.sigNeg (chartHessianAt (boundaryMorsePerturbation c b a) (Fin.cons (a / 2) 0)) =
      {i | c i < 0}.ncard := by
  rw [chartHessianAt_congr_eventuallyEq
    (eventuallyEq_boundaryMorsePerturbation c b a (Fin.cons (a / 2) 0)
      (by simpa using b.rIn_pos))]
  exact sigNeg_chartHessianAt_sum_sq_add_smoothAbs c ha

theorem exists_pos_boundaryMorsePerturbation_critical (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      (∀ z : Fin (n + 1) → ℝ, 0 ≤ z 0 →
        (IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) (boundaryMorsePerturbation c b a) z ↔
          z = Fin.cons (a / 2) 0)) ∧
      IsNondegenerateCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
        (boundaryMorsePerturbation c b a) (Fin.cons (a / 2) 0) ∧
      chartHessianAt (boundaryMorsePerturbation c b a) (Fin.cons (a / 2) 0) =
        QuadraticMap.weightedSumSquares ℝ (Fin.cons (4 / a) (fun i => 2 * c i)) := by
  classical
  let q := fun x : Fin n → ℝ => ∑ i : Fin n, c i * x i ^ 2
  let K : Set (Fin n → ℝ) := {x | b.rIn / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ b.rOut}
  have hK : IsCompact K := by
    have heq : K = Metric.closedBall 0 b.rOut ∩ {x : Fin n → ℝ | b.rIn / 2 ≤ ‖x‖} := by
      ext x
      simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, and_comm]
    rw [heq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hregular : ∀ x ∈ K, fderiv ℝ q x ≠ 0 := by
    intro x hx hz
    have hcrit : IsCriticalPointAt 𝓘(ℝ, Fin n → ℝ) q x := by
      rw [IsCriticalPointAt, mfderiv_eq_fderiv]
      change fderiv ℝ q x = 0
      exact hz
    have hcoord := (isCriticalPointAt_sum_pi_iff
      (f := fun i u => c i * u ^ 2) (x := x) (by intro i; fun_prop)).mp hcrit
    have hx0 : x = 0 := by
      funext i
      have hd : HasDerivAt (fun u : ℝ => c i * u ^ 2) (2 * c i * x i) (x i) := by
        convert! ((hasDerivAt_id (x i)).pow 2).const_mul (c i) using 1
        simp only [id_eq]
        ring
      have hi := hcoord i
      rw [hd.deriv] at hi
      exact (mul_eq_zero.mp hi).resolve_left (mul_ne_zero two_ne_zero (hc i))
    have hpos := b.rIn_pos
    change b.rIn / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ b.rOut at hx
    rw [hx0, norm_zero] at hx
    linarith [hx.1]
  obtain ⟨δ, hδ, hδreg⟩ := exists_pos_forall_fderiv_add_smoothAbs_ne_zero hK
    (fun x hx => (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffAt)
    (fun x hx => b.contDiffAt) hregular
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  have hcenter := eventuallyEq_boundaryMorsePerturbation c b a (Fin.cons (a / 2) 0)
    (by simpa using b.rIn_pos)
  have hF := contDiff_boundaryMorsePerturbation c b a
  refine ⟨?_, ?_, ?_⟩
  · intro z hzu
    by_cases hz : ‖Fin.tail z‖ < b.rIn / 2
    · have heq := eventuallyEq_boundaryMorsePerturbation c b a z
        (by linarith [b.rIn_pos])
      have hm := isCriticalPointAt_sum_sq_add_smoothAbs_iff c hc ha.1.ne' z
      rw [IsCriticalPointAt, mfderiv_eq_fderiv] at hm ⊢
      change (fderiv ℝ (boundaryMorsePerturbation c b a) z = 0) ↔ _
      rw [heq.fderiv_eq]
      exact hm
    · have hnot : ¬ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
          (boundaryMorsePerturbation c b a) z := by
        intro hcrit
        have hcrit' : fderiv ℝ (boundaryMorsePerturbation c b a) z = 0 := by
          rw [IsCriticalPointAt, mfderiv_eq_fderiv] at hcrit
          exact hcrit
        by_cases hb : b (Fin.tail z) = 0
        · exact fderiv_boundaryMorsePerturbation_ne_zero_of_eq_zero c b a z hb hcrit'
        · have htail : Fin.tail z ∈ K := by
            refine ⟨le_of_not_gt hz, ?_⟩
            have hh : Fin.tail z ∈ Function.support b := hb
            rw [b.support_eq] at hh
            exact (by simpa [Metric.mem_ball, dist_eq_norm] using hh : ‖Fin.tail z‖ < b.rOut).le
          have hn := hδreg a ha (Fin.tail z, z 0) ⟨htail, hzu⟩
          apply hn
          let P : (Fin n → ℝ) × ℝ → Fin (n + 1) → ℝ := fun p => Fin.cons p.2 p.1
          have hP : ContDiff ℝ ∞ P := by
            apply contDiff_pi.mpr
            intro i
            refine Fin.cases ?_ ?_ i
            · exact contDiff_snd
            · intro j
              exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
          have heq : (fun p : (Fin n → ℝ) × ℝ => q p.1 + p.2 + b p.1 *
              (a / 2 + Real.smoothAbs (a / 2) (p.2 - a / 2) - p.2)) =
              boundaryMorsePerturbation c b a ∘ P := by
            funext p
            simp [boundaryMorsePerturbation, P, q]
          rw [heq, fderiv_comp _ (hF.differentiable (by simp) _)
            (hP.differentiable (by simp) _)]
          have hp : P (Fin.tail z, z 0) = z := Fin.cons_self_tail z
          rw [hp, hcrit', ContinuousLinearMap.zero_comp]
      have hne : z ≠ Fin.cons (a / 2) 0 := by
        intro heq
        subst z
        simp only [Fin.tail_cons, norm_zero] at hz
        exact hz (by linarith [b.rIn_pos])
      exact iff_of_false hnot hne
  · exact (isNondegenerateCriticalPointAt_congr_eventuallyEq hcenter).mpr
      (isNondegenerateCriticalPointAt_sum_sq_add_smoothAbs c hc ha.1.ne')
  · exact chartHessianAt_boundaryMorsePerturbation c b a

theorem hasDerivAt_boundaryMorsePerturbation_normal (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => boundaryMorsePerturbation c b a (Fin.cons t x))
      (1 + b x * (deriv (Real.smoothAbs (a / 2)) (u - a / 2) - 1)) u := by
  have hs := (((Real.smoothAbs.contDiff (a / 2)).differentiable (by simp)
    (u - a / 2)).hasDerivAt.comp u ((hasDerivAt_id u).sub_const (a / 2)))
  have hp := (hs.const_add (a / 2)).sub (hasDerivAt_id u)
  convert! ((hasDerivAt_id u).const_add (∑ i : Fin n, c i * x i ^ 2)).add
    (hp.const_mul (b x)) using 1
  simp

theorem deriv_boundaryMorsePerturbation_normal_zero (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : a ≠ 0) :
    deriv (fun t : ℝ => boundaryMorsePerturbation c b a (Fin.cons t 0)) 0 = -1 := by
  rw [(hasDerivAt_boundaryMorsePerturbation_normal c b a 0 0).deriv]
  have hb : b (0 : Fin n → ℝ) = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  rw [hb, Real.smoothAbs.deriv]
  have hs : (a / 2 - (0 - a / 2)) / (2 * (a / 2)) = 1 := by field_simp; ring
  rw [hs]
  norm_num

theorem boundaryMorsePerturbation_sub_mem_Icc (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a)
    (z : Fin (n + 1) → ℝ) (hz : 0 ≤ z 0) :
    boundaryMorsePerturbation c b a z - ((∑ i : Fin n, c i * z i.succ ^ 2) + z 0) ∈
      Set.Icc 0 (2 * a) := by
  have hs := Real.smoothAbs.sub_abs_mem_Icc (by linarith : 0 < a / 2) (z 0 - a / 2)
  have hnorm : |z 0 - a / 2| ≤ z 0 + a / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdelta : a / 2 + Real.smoothAbs (a / 2) (z 0 - a / 2) - z 0 ∈ Set.Icc 0 (2 * a) := by
    constructor <;> linarith [hs.1, hs.2, le_abs_self (z 0 - a / 2)]
  have hb : 0 ≤ b (Fin.tail z) := b.nonneg
  have hb' : b (Fin.tail z) ≤ 1 := b.le_one
  simp only [boundaryMorsePerturbation, add_sub_cancel_left, Set.mem_Icc]
  refine ⟨mul_nonneg hb hdelta.1, ?_⟩
  exact (mul_le_of_le_one_left hdelta.1 hb').trans hdelta.2

theorem hasCompactSupport_boundaryMorsePerturbation_sub (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (fun p : (Fin n → ℝ) × Set.Ici (0 : ℝ) =>
      boundaryMorsePerturbation c b a (Fin.cons p.2.val p.1) -
        ((∑ i : Fin n, c i * p.1 i ^ 2) + p.2.val)) := by
  let j : (Fin n → ℝ) × Set.Ici (0 : ℝ) → (Fin n → ℝ) × ℝ := fun p => (p.1, p.2.val)
  have hj : Topology.IsClosedEmbedding j :=
    Topology.IsClosedEmbedding.id.prodMap isClosed_Ici.isClosedEmbedding_subtypeVal
  have hK := hj.isCompact_preimage
    ((isCompact_closedBall (0 : Fin n → ℝ) b.rOut).prod (isCompact_Icc (a := (0 : ℝ)) (b := a)))
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro p hp
  change (p.1, p.2.val) ∈ Metric.closedBall 0 b.rOut ×ˢ Set.Icc 0 a
  have hnorm : ‖p.1‖ < b.rOut := by
    by_contra h
    have heq := boundaryMorsePerturbation_eq_of_le_norm c b a (Fin.cons p.2.val p.1)
      (by simpa using le_of_not_gt h)
    exact hp (by simpa using sub_eq_zero.mpr heq)
  have hu : p.2.val < a := by
    by_contra h
    have heq := boundaryMorsePerturbation_eq_of_le c b ha (Fin.cons p.2.val p.1) (le_of_not_gt h)
    exact hp (by simpa using sub_eq_zero.mpr heq)
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm.le, p.2.property, hu.le⟩

noncomputable def boundaryMorseInterpolation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a s : ℝ) (z : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 +
    s * (boundaryMorsePerturbation c b a z - ((∑ i : Fin n, c i * z i.succ ^ 2) + z 0))

@[simp] theorem boundaryMorseInterpolation_zero (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (z : Fin (n + 1) → ℝ) :
    boundaryMorseInterpolation c b a 0 z = (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 := by
  simp [boundaryMorseInterpolation]

@[simp] theorem boundaryMorseInterpolation_one (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) (z : Fin (n + 1) → ℝ) :
    boundaryMorseInterpolation c b a 1 z = boundaryMorsePerturbation c b a z := by
  simp [boundaryMorseInterpolation]

theorem contDiff_boundaryMorseInterpolation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) =>
      boundaryMorseInterpolation c b a p.1 p.2) := by
  have hq : ContDiff ℝ ∞ (fun z : Fin (n + 1) → ℝ =>
      (∑ i : Fin n, c i * z i.succ ^ 2) + z 0) := by fun_prop
  exact (hq.comp contDiff_snd).add (contDiff_fst.mul
    (((contDiff_boundaryMorsePerturbation c b a).sub hq).comp contDiff_snd))

theorem boundaryMorseInterpolation_eq_of_le (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a) (s : ℝ)
    (z : Fin (n + 1) → ℝ) (hz : a ≤ z 0) :
    boundaryMorseInterpolation c b a s z = (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 := by
  simp only [boundaryMorseInterpolation, boundaryMorsePerturbation_eq_of_le c b ha z hz,
    sub_self, mul_zero, add_zero]

theorem boundaryMorseInterpolation_eq_of_le_norm (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a s : ℝ) (z : Fin (n + 1) → ℝ)
    (hz : b.rOut ≤ ‖Fin.tail z‖) :
    boundaryMorseInterpolation c b a s z = (∑ i : Fin n, c i * z i.succ ^ 2) + z 0 := by
  simp only [boundaryMorseInterpolation, boundaryMorsePerturbation_eq_of_le_norm c b a z hz,
    sub_self, mul_zero, add_zero]

theorem boundaryMorseInterpolation_sub_mem_Icc (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) (z : Fin (n + 1) → ℝ) (hz : 0 ≤ z 0) :
    boundaryMorseInterpolation c b a s z - ((∑ i : Fin n, c i * z i.succ ^ 2) + z 0) ∈
      Set.Icc 0 (2 * a) := by
  have h := boundaryMorsePerturbation_sub_mem_Icc c b ha z hz
  simp only [boundaryMorseInterpolation, add_sub_cancel_left, Set.mem_Icc]
  exact ⟨mul_nonneg hs.1 h.1, (mul_le_of_le_one_left h.1 hs.2).trans h.2⟩

theorem exists_isCompact_eqOn_boundaryMorseInterpolation (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a) :
    ∃ K : Set ((Fin n → ℝ) × Set.Ici (0 : ℝ)), IsCompact K ∧ ∀ s : ℝ,
      Set.EqOn (fun p => boundaryMorseInterpolation c b a s (Fin.cons p.2.val p.1))
        (fun p => (∑ i : Fin n, c i * p.1 i ^ 2) + p.2.val) Kᶜ := by
  let f := fun p : (Fin n → ℝ) × Set.Ici (0 : ℝ) =>
    boundaryMorsePerturbation c b a (Fin.cons p.2.val p.1) -
      ((∑ i : Fin n, c i * p.1 i ^ 2) + p.2.val)
  refine ⟨tsupport f, hasCompactSupport_boundaryMorsePerturbation_sub c b ha, ?_⟩
  intro s p hp
  have hz : f p = 0 := image_eq_zero_of_notMem_tsupport hp
  simp only [boundaryMorseInterpolation, Fin.cons_succ, Fin.cons_zero]
  change (∑ i : Fin n, c i * p.1 i ^ 2) + p.2.val + s * f p = _
  rw [hz, mul_zero, add_zero]

theorem hasDerivAt_boundaryMorseInterpolation_normal (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a s : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => boundaryMorseInterpolation c b a s (Fin.cons t x))
      (1 + s * b x * (deriv (Real.smoothAbs (a / 2)) (u - a / 2) - 1)) u := by
  have hbase := (hasDerivAt_id u).const_add (∑ i : Fin n, c i * x i ^ 2)
  convert! hbase.add (((hasDerivAt_boundaryMorsePerturbation_normal c b a x u).sub hbase).const_mul s)
    using 1
  ring

theorem boundaryMorseInterpolation_boundary (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a) (s : ℝ) (x : Fin n → ℝ) :
    boundaryMorseInterpolation c b a s (Fin.cons 0 x) =
      (∑ i : Fin n, c i * x i ^ 2) + s * a * b x := by
  have h := Real.smoothAbs.eq_neg_of_le (by linarith : 0 < a / 2)
    (show (0 : ℝ) - a / 2 ≤ -(a / 2) by linarith)
  simp only [boundaryMorseInterpolation, boundaryMorsePerturbation, Fin.cons_succ,
    Fin.cons_zero, Fin.tail_cons, h]
  ring

private theorem fderiv_sum_sq_eq_zero_iff (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => ∑ i, c i * y i ^ 2) x = 0 ↔ x = 0 := by
  have h := isCriticalPointAt_sum_pi_iff
    (f := fun i u => c i * u ^ 2) (x := x) (by intro i; fun_prop)
  rw [IsCriticalPointAt, mfderiv_eq_fderiv] at h
  have hd (i : Fin n) : deriv (fun u : ℝ => c i * u ^ 2) (x i) = 2 * c i * x i := by
    convert! (((hasDerivAt_id (x i)).pow 2).const_mul (c i)).deriv using 1
    simp only [id_eq]
    ring
  constructor
  · intro hx
    have hx' := h.mp hx
    simp only [hd] at hx'
    funext i
    exact (mul_eq_zero.mp (hx' i)).resolve_left (mul_ne_zero two_ne_zero (hc i))
  · rintro rfl
    apply h.mpr
    intro i
    simpa only [Pi.zero_apply, mul_zero] using hd i

private theorem fderiv_boundaryMorseInterpolation_tangential (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) (a s u : ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => boundaryMorseInterpolation c b a s (Fin.cons u y)) x =
      fderiv ℝ (fun y : Fin n → ℝ => ∑ i, c i * y i ^ 2) x +
        (s * (a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u)) • fderiv ℝ b x := by
  have hq : ContDiff ℝ ∞ (fun y : Fin n → ℝ => ∑ i, c i * y i ^ 2) := by fun_prop
  have hb := (((b.contDiff : ContDiff ℝ ∞ b).differentiable (by simp)) x).hasFDerivAt.const_mul
    (s * (a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u))
  convert! ((((hq.differentiable (by simp)) x).hasFDerivAt.add_const u).add hb).fderiv using 1
  apply congrArg (fun f : (Fin n → ℝ) → ℝ => fderiv ℝ f x)
  funext y
  simp only [Pi.add_apply, boundaryMorseInterpolation, boundaryMorsePerturbation, Fin.cons_succ,
    Fin.cons_zero, Fin.tail_cons]
  ring

private theorem fderiv_bump_eq_zero_of_norm_lt (b : ContDiffBump (0 : Fin n → ℝ))
    (x : Fin n → ℝ) (hx : ‖x‖ < b.rIn) : fderiv ℝ b x = 0 := by
  have h := b.eventuallyEq_one_of_mem_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
  simpa using h.fderiv_eq (𝕜 := ℝ)

private theorem exists_pos_boundaryMorseInterpolation_tangential (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ u ∈ Set.Ici (0 : ℝ), ∀ x : Fin n → ℝ,
        fderiv ℝ (fun y => boundaryMorseInterpolation c b a s (Fin.cons u y)) x = 0 ↔ x = 0 := by
  let q := fun x : Fin n → ℝ => ∑ i, c i * x i ^ 2
  let K : Set (Fin n → ℝ) := {x | b.rIn / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ b.rOut}
  have hK : IsCompact K := by
    have heq : K = Metric.closedBall 0 b.rOut ∩ {x : Fin n → ℝ | b.rIn / 2 ≤ ‖x‖} := by
      ext x
      simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, and_comm]
    rw [heq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hregular : ∀ x ∈ K, fderiv ℝ q x ≠ 0 := by
    intro x hx hz
    have hx0 := (fderiv_sum_sq_eq_zero_iff c hc x).mp hz
    change b.rIn / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ b.rOut at hx
    rw [hx0, norm_zero] at hx
    linarith [hx.1, b.rIn_pos]
  obtain ⟨ε, hε, hεreg⟩ := exists_pos_forall_fderiv_add_const_smul_ne_zero hK
    (fun x hx => (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).contDiffAt)
    (fun x hx => b.contDiffAt) hregular
  refine ⟨ε / 2, by positivity, ?_⟩
  intro a ha s hs u hu x
  have ha0 : 0 < a := ha.1
  have hu0 : 0 ≤ u := hu
  rw [fderiv_boundaryMorseInterpolation_tangential]
  by_cases hb : fderiv ℝ b x = 0
  · simpa only [hb, smul_zero, add_zero] using fderiv_sum_sq_eq_zero_iff c hc x
  · have hxK : x ∈ K := by
      constructor
      · by_contra hx
        exact hb (fderiv_bump_eq_zero_of_norm_lt b x (by linarith [b.rIn_pos, not_le.mp hx]))
      · by_contra hx
        apply hb
        apply fderiv_of_notMem_tsupport
        simpa only [b.tsupport_eq, Metric.mem_closedBall, dist_zero_right, not_le] using not_le.mp hx
    have hprof : |a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u| ≤ 2 * a := by
      have h := Real.smoothAbs.sub_abs_mem_Icc (by linarith : 0 < a / 2) (u - a / 2)
      have habs : |u - a / 2| ≤ u + a / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2, le_abs_self (u - a / 2)]
    have hsmall : |s * (a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u)| ≤ ε := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact ((mul_le_of_le_one_left (abs_nonneg _) hs.2).trans hprof).trans (by linarith [ha.2])
    have hne := hεreg x hxK (s * (a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u)) hsmall
    have hderiv := ((hq.differentiable (by simp)) x).hasFDerivAt.add
      ((((b.contDiff : ContDiff ℝ ∞ b).differentiable (by simp)) x).hasFDerivAt.const_smul
        (s * (a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u)))
    have hne' : fderiv ℝ q x +
        (s * (a / 2 + Real.smoothAbs (a / 2) (u - a / 2) - u)) • fderiv ℝ b x ≠ 0 := by
      intro hz
      exact hne (hderiv.fderiv.trans hz)
    have hxne : x ≠ 0 := by
      rintro rfl
      exact hb (fderiv_bump_eq_zero_of_norm_lt b 0 (by simpa using b.rIn_pos))
    exact iff_of_false hne' hxne


theorem convexOn_boundaryMorseInterpolation_normal (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : 0 ≤ s) (x : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun u : ℝ => boundaryMorseInterpolation c b a s (Fin.cons u x)) := by
  refine ⟨convex_univ, ?_⟩
  intro u hu v hv α β hα hβ hαβ
  have hc := (Real.smoothAbs.convexOn (by linarith : 0 < a / 2)).2
    (Set.mem_univ (u - a / 2)) (Set.mem_univ (v - a / 2)) hα hβ hαβ
  simp only [smul_eq_mul] at hc ⊢
  have heq : α * (u - a / 2) + β * (v - a / 2) = α * u + β * v - a / 2 := by
    nlinarith [hαβ]
  rw [heq] at hc
  have hmul := mul_le_mul_of_nonneg_left hc (mul_nonneg hs (b.nonneg' x))
  simp only [boundaryMorseInterpolation, boundaryMorsePerturbation, Fin.cons_succ,
    Fin.cons_zero, Fin.tail_cons]
  nlinarith [congrArg (fun r : ℝ => r * (∑ i, c i * x i ^ 2)) hαβ,
    congrArg (fun r : ℝ => r * (s * b x * (a / 2))) hαβ]


private theorem boundaryMorseInterpolation_critical_value (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a s : ℝ} (ha : 0 < a)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hreg : ∀ u ∈ Set.Ici (0 : ℝ), ∀ x : Fin n → ℝ,
      fderiv ℝ (fun y => boundaryMorseInterpolation c b a s (Fin.cons u y)) x = 0 ↔ x = 0)
    (z : Fin (n + 1) → ℝ) (hz : 0 ≤ z 0)
    (hcrit : IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
      (boundaryMorseInterpolation c b a s) z) :
    boundaryMorseInterpolation c b a s z ∈ Set.Icc 0 a := by
  let F := boundaryMorseInterpolation c b a s
  have hF : Differentiable ℝ F :=
    ((contDiff_boundaryMorseInterpolation c b a).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hzero : fderiv ℝ F z = 0 := by
    rw [IsCriticalPointAt, mfderiv_eq_fderiv] at hcrit
    exact hcrit
  have hG : Differentiable ℝ (fun y : Fin n → ℝ => (Fin.cons (z 0) y : Fin (n + 1) → ℝ)) := by
    apply differentiable_pi.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · exact differentiable_const _
    · intro j
      exact differentiable_apply j
  have ht : Fin.tail z = 0 := by
    apply (hreg (z 0) hz (Fin.tail z)).mp
    have h := ((hF (Fin.cons (z 0) (Fin.tail z))).hasFDerivAt.comp
      (Fin.tail z) (hG (Fin.tail z)).hasFDerivAt).fderiv
    simpa only [Function.comp_def, Fin.cons_self_tail, hzero,
      ContinuousLinearMap.zero_comp] using h
  have hrepr : Fin.cons (z 0) (0 : Fin n → ℝ) = z := by
    rw [← ht, Fin.cons_self_tail]
  have hP : HasDerivAt (fun u : ℝ => Fin.cons u (0 : Fin n → ℝ))
      (Fin.cons (1 : ℝ) (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) (z 0) := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hasDerivAt_id (z 0)
    · intro j
      exact hasDerivAt_const (z 0) 0
  have hderiv : HasDerivAt (fun u : ℝ => F (Fin.cons u 0)) 0 (z 0) := by
    have h := ((hF (Fin.cons (z 0) 0)).hasFDerivAt).comp_hasDerivAt (z 0) hP
    simpa only [hrepr, hzero, zero_apply, Function.comp_def] using h
  have hboundary : F (Fin.cons 0 0) = s * a := by
    simpa only [F, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero,
      Finset.sum_const_zero, zero_add, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), mul_one] using
      boundaryMorseInterpolation_boundary c b ha s (0 : Fin n → ℝ)
  have hlower := (boundaryMorseInterpolation_sub_mem_Icc c b ha hs z hz).1
  have hq : (∑ i : Fin n, c i * z i.succ ^ 2) = 0 := by
    have hi (i : Fin n) : z i.succ = 0 := congrFun ht i
    simp only [hi, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
  have hupp : F z ≤ F (Fin.cons 0 0) := by
    rcases hz.eq_or_lt with hu | hu
    · have hz0 : z = Fin.cons 0 0 := by rw [← hrepr, ← hu]
      rw [hz0]
    · have h := (convexOn_boundaryMorseInterpolation_normal c b ha hs.1 0).slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hu hderiv
      rw [slope_def_field, sub_zero, div_le_iff₀ hu, zero_mul] at h
      change F (Fin.cons (z 0) 0) - F (Fin.cons 0 0) ≤ 0 at h
      rw [hrepr] at h
      linarith
  change 0 ≤ F z ∧ F z ≤ a
  rw [hq, zero_add] at hlower
  rw [hboundary] at hupp
  exact ⟨by dsimp [F]; linarith, hupp.trans (mul_le_of_le_one_left ha.le hs.2)⟩

theorem exists_pos_boundaryMorseInterpolation_critical_values (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ z : Fin (n + 1) → ℝ, 0 ≤ z 0 →
        IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) (boundaryMorseInterpolation c b a s) z →
        boundaryMorseInterpolation c b a s z ∈ Set.Icc 0 a) ∧
      (∀ x : Fin n → ℝ,
        IsCriticalPointAt 𝓘(ℝ, Fin n → ℝ)
          (fun y => boundaryMorseInterpolation c b a s (Fin.cons 0 y)) x →
        boundaryMorseInterpolation c b a s (Fin.cons 0 x) ∈ Set.Icc 0 a) := by
  obtain ⟨δ, hδ, hreg⟩ := exists_pos_boundaryMorseInterpolation_tangential c hc b
  refine ⟨δ, hδ, ?_⟩
  intro a ha s hs
  refine ⟨boundaryMorseInterpolation_critical_value c b ha.1 hs (hreg a ha s hs), ?_⟩
  intro x hx
  have hx0 : x = 0 := (hreg a ha s hs 0 (by simp) x).mp (by
    rw [IsCriticalPointAt, mfderiv_eq_fderiv] at hx
    exact hx)
  rw [hx0, boundaryMorseInterpolation_boundary c b ha.1]
  simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Finset.sum_const_zero, zero_add, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), mul_one]
  exact ⟨mul_nonneg hs.1 ha.1.le, mul_le_of_le_one_left ha.1.le hs.2⟩


theorem exists_pos_boundaryMorseInterpolation_regular_levels (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ r ∉ Set.Icc 0 a,
        (∀ z : Fin (n + 1) → ℝ, 0 ≤ z 0 → boundaryMorseInterpolation c b a s z = r →
          ¬ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
            (boundaryMorseInterpolation c b a s) z) ∧
        (∀ x : Fin n → ℝ, boundaryMorseInterpolation c b a s (Fin.cons 0 x) = r →
          ¬ IsCriticalPointAt 𝓘(ℝ, Fin n → ℝ)
            (fun y => boundaryMorseInterpolation c b a s (Fin.cons 0 y)) x) := by
  obtain ⟨δ, hδ, hvalues⟩ := exists_pos_boundaryMorseInterpolation_critical_values c hc b
  refine ⟨δ, hδ, ?_⟩
  intro a ha s hs r hr
  constructor
  · intro z hz heq hcrit
    exact hr (heq ▸ (hvalues a ha s hs).1 z hz hcrit)
  · intro x heq hcrit
    exact hr (heq ▸ (hvalues a ha s hs).2 x hcrit)

end DifferentialGeometry.Topology.Morse
