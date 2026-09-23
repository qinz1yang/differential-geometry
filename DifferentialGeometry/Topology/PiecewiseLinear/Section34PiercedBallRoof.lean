import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallHeightMove
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem square_closedBall_eq (r : ℝ) :
    Metric.closedBall (0 : ℝ × ℝ) r = Icc (-r) r ×ˢ Icc (-r) r := by
  ext x
  simp only [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, max_le_iff,
    abs_le, mem_prod, mem_Icc]

private theorem square_closedBall_isHPolytope (r : ℝ) :
    IsHPolytope (Metric.closedBall (0 : ℝ × ℝ) r) := by
  rw [square_closedBall_eq]
  exact isHPolytope_Icc.prod isHPolytope_Icc

theorem isPLBall_square_closedBall {r : ℝ} (hr : 0 < r) :
    IsPLBall 2 (Metric.closedBall (0 : ℝ × ℝ) r) := by
  have hinter : (interior (Metric.closedBall (0 : ℝ × ℝ) r)).Nonempty := by
    rw [interior_closedBall _ hr.ne']
    exact ⟨0, Metric.mem_ball_self hr⟩
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd] using
    (square_closedBall_isHPolytope r).isPLBall hinter

theorem exists_piercing_square_roof {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKP : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1)) {a : ℝ} (ha : 0 < a) :
    ∃ g : (ℝ × ℝ) → ℝ, IsPiecewiseAffineOn g univ ∧
      (∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1, |g x| ≤ a / 2) ∧
      (∀ x ∈ frontier (Metric.closedBall (0 : ℝ × ℝ) 1), g x < 0) ∧
      (∀ x ∈ K, 0 < g x) ∧
      IsPLSphere 1 {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} := by
  have hKnorm (x) (hx : x ∈ K) : ‖x‖ < 1 := by
    have hm := hKP hx
    rwa [interior_closedBall _ one_ne_zero, mem_ball_zero_iff] at hm
  obtain ⟨r, hr, hr1, hKr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ K, ‖x‖ < r := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      simp only [hKe, mem_empty_iff_false, false_implies, implies_true]
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
      refine ⟨(‖x‖ + 1) / 2, by positivity, by linarith [hKnorm x hx], ?_⟩
      intro y hy
      exact (hmax hy).trans_lt (by linarith [hKnorm x hx])
  let c := a / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let g : (ℝ × ℝ) → ℝ := fun x => c * (r - ‖x‖)
  have hnorm : IsPiecewiseAffineOn (norm : (ℝ × ℝ) → ℝ) univ := by
    have hfst : IsPiecewiseAffineOn (Prod.fst : ℝ × ℝ → ℝ) univ :=
      isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ ℝ).toAffineMap isOpen_univ
    have hsnd : IsPiecewiseAffineOn (Prod.snd : ℝ × ℝ → ℝ) univ :=
      isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
    convert hfst.abs.max hsnd.abs using 1
    ext x
    exact (Prod.norm_def x).trans (by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hg : IsPiecewiseAffineOn g univ := by
    let A : ℝ →ᵃ[ℝ] ℝ := (-c) • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (c * r)
    have hcomp := (isPiecewiseAffineOn_of_affine A isOpen_univ).comp hnorm
    simp only [preimage_univ, inter_univ] at hcomp
    convert hcomp using 1
    ext x
    change c * (r - ‖x‖) = -c * ‖x‖ + c * r
    ring
  have hzero : {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} =
      Metric.sphere (0 : ℝ × ℝ) r := by
    ext x
    simp only [mem_ofPred_eq, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨-, hx⟩
      have hx' : r - ‖x‖ = 0 := (mul_eq_zero.mp hx).resolve_left hc.ne'
      linarith
    · intro hx
      exact ⟨hx ▸ hr1.le, by dsimp [g]; rw [hx, sub_self, mul_zero]⟩
  refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hn := mem_closedBall_zero_iff.mp hx
    have hnonneg := norm_nonneg x
    dsimp [g, c]
    apply abs_le.mpr
    constructor <;> nlinarith
  · intro x hx
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm] at hx
    dsimp [g]
    rw [hx]
    exact mul_neg_of_pos_of_neg hc (sub_neg.mpr hr1)
  · intro x hx
    exact mul_pos hc (sub_pos.mpr (hKr x hx))
  · rw [hzero, ← frontier_closedBall _ hr.ne']
    exact (square_closedBall_isHPolytope r).isPLSphere_frontier
      (by simp only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd])
      (by rw [interior_closedBall _ hr.ne']; exact ⟨0, Metric.mem_ball_self hr⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
