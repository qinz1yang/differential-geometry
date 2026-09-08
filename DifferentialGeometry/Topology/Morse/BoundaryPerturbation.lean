import DifferentialGeometry.Analysis.Calculus.CriticalPointPerturbation
import DifferentialGeometry.Topology.Morse.Separable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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

end DifferentialGeometry.Topology.Morse
