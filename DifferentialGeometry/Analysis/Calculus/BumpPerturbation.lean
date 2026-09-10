import DifferentialGeometry.Analysis.Calculus.RegularValue
import DifferentialGeometry.Topology.Compactness.Nonvanishing
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped Topology ContDiff
namespace Poincare.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def bumpPerturbation (f : E → E) (ρ : E → ℝ) (v : E) (x : E) : E := f x - ρ x • v

theorem norm_bumpPerturbation_sub_le (f : E → E) {ρ : E → ℝ}
    (hρ : ∀ x, ρ x ∈ Icc (0 : ℝ) 1) (v x : E) :
    ‖bumpPerturbation f ρ v x - f x‖ ≤ ‖v‖ := by
  have heq : bumpPerturbation f ρ v x - f x = -(ρ x • v) := by
    unfold bumpPerturbation
    abel
  rw [heq,norm_neg,norm_smul,Real.norm_of_nonneg (hρ x).1]
  exact mul_le_of_le_one_left (norm_nonneg v) (hρ x).2

theorem contDiffOn_bumpPerturbation {f : E → E} {ρ : E → ℝ} {U : Set E}
    {n : ℕ∞} (hf : ContDiffOn ℝ n f U) (hρ : ContDiff ℝ n ρ) (v : E) :
    ContDiffOn ℝ n (bumpPerturbation f ρ v) U :=
  hf.sub (hρ.contDiffOn.smul contDiffOn_const)

theorem fderiv_bumpPerturbation_of_eventuallyEq_one {f : E → E} {ρ : E → ℝ}
    {x : E} (hρ : ρ =ᶠ[𝓝 x] 1) (v : E) :
    fderiv ℝ (bumpPerturbation f ρ v) x = fderiv ℝ f x := by
  have heq : bumpPerturbation f ρ v =ᶠ[𝓝 x] (fun y => f y - v) := by
    filter_upwards [hρ] with y hy
    simp only [bumpPerturbation,hy,Pi.one_apply,one_smul]
  rw [heq.fderiv_eq,fderiv_sub_const]

variable [FiniteDimensional ℝ E]

theorem exists_small_regular_bumpPerturbation {f : E → E} {ρ : E → ℝ}
    {a : E} {r R : ℝ} (hrR : r ≤ R) {U : Set E} (hU : IsOpen U)
    (hRU : closedBall a R ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hρ : ContDiff ℝ ∞ ρ) (hρrange : ∀ x, ρ x ∈ Icc (0 : ℝ) 1)
    (hρone : EqOn ρ 1 (closedBall a r))
    (hρzero : ∀ x, R ≤ dist x a → ρ x = 0)
    (hn : ∀ x ∈ closedBall a R, r ≤ dist x a → f x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, ‖v‖ < ε ∧
      (∀ x ∈ ball a r, f x = v → (fderiv ℝ f x).det ≠ 0) ∧
      ContDiffOn ℝ ∞ (bumpPerturbation f ρ v) U ∧
      (∀ x, R ≤ dist x a → bumpPerturbation f ρ v x = f x) ∧
      (∀ x, ‖bumpPerturbation f ρ v x - f x‖ < ε) ∧
      (∀ x ∈ closedBall a R, bumpPerturbation f ρ v x = 0 →
        x ∈ ball a r ∧ (fderiv ℝ (bumpPerturbation f ρ v) x).det ≠ 0) ∧
      {x | x ∈ closedBall a R ∧ bumpPerturbation f ρ v x = 0}.Finite := by
  let K := closedBall a R ∩ {x : E | r ≤ dist x a}
  have hK : IsCompact K := (isCompact_closedBall a R).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  obtain ⟨δ,hδ,hbound⟩ := Poincare.Topology.exists_pos_lt_norm_of_isCompact hK
    (hf.continuousOn.mono (fun _ hx => hRU hx.1)) (fun x hx => hn x hx.1 hx.2)
  have hfd : ∀ x ∈ ball a r, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hf.contDiffAt (hU.mem_nhds
      (hRU (closedBall_subset_closedBall hrR (ball_subset_closedBall hx))))).differentiableAt (by simp)
  obtain ⟨v,hv,hreg⟩ := exists_near_regular_value hfd (0 : E) (lt_min hε hδ)
  have hvε : ‖v‖ < ε := (show ‖v‖ < min ε δ by simpa only [dist_zero_right] using hv).trans_le (min_le_left _ _)
  have hvδ : ‖v‖ < δ := (show ‖v‖ < min ε δ by simpa only [dist_zero_right] using hv).trans_le (min_le_right _ _)
  let g := bumpPerturbation f ρ v
  have hg : ContDiffOn ℝ ∞ g U := contDiffOn_bumpPerturbation hf hρ v
  have hzeros : ∀ x ∈ closedBall a R, g x = 0 →
      x ∈ ball a r ∧ (fderiv ℝ g x).det ≠ 0 := by
    intro x hx hzero
    have hxin : x ∈ ball a r := by
      by_contra hxin
      have hxK : x ∈ K := ⟨hx,show r ≤ dist x a from le_of_not_gt hxin⟩
      have heq : f x = ρ x • v := sub_eq_zero.mp hzero
      have hle : ‖f x‖ ≤ ‖v‖ := by
        rw [heq,norm_smul,Real.norm_of_nonneg (hρrange x).1]
        exact mul_le_of_le_one_left (norm_nonneg v) (hρrange x).2
      exact (not_lt_of_ge hle) (hvδ.trans (hbound x hxK))
    have hplateau : ρ =ᶠ[𝓝 x] 1 := by
      filter_upwards [isOpen_ball.mem_nhds hxin] with y hy
      exact hρone (ball_subset_closedBall hy)
    have hfx : f x = v := by
      have hh : f x - v = 0 := by
        simpa only [g,bumpPerturbation,hρone (ball_subset_closedBall hxin),Pi.one_apply,one_smul] using hzero
      exact sub_eq_zero.mp hh
    refine ⟨hxin,?_⟩
    rw [show fderiv ℝ g x = fderiv ℝ f x from fderiv_bumpPerturbation_of_eventuallyEq_one hplateau v]
    exact hreg x hxin hfx
  refine ⟨v,hvε,hreg,hg,?_,fun x => (norm_bumpPerturbation_sub_le f hρrange v x).trans_lt hvε,hzeros,?_⟩
  · intro x hx
    simp only [bumpPerturbation,hρzero x hx,zero_smul,sub_zero]
  · exact finite_regular_fiber (isCompact_closedBall a R)
      (fun x hx => (hg.contDiffAt (hU.mem_nhds (hRU hx))).of_le (by norm_num)) 0
      (fun x hx hz => (hzeros x hx hz).2)

theorem exists_small_regular_ball_perturbation {f : E → E} (a : E)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {U : Set E} (hU : IsOpen U)
    (hRU : closedBall a R ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hn : ∀ x ∈ closedBall a R, r ≤ dist x a → f x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : E → ℝ) (v : E), ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      support ρ = ball a R ∧ EqOn ρ 1 (closedBall a r) ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ ‖v‖ < ε ∧
      (∀ x ∈ ball a r, f x = v → (fderiv ℝ f x).det ≠ 0) ∧
      ContDiffOn ℝ ∞ (bumpPerturbation f ρ v) U ∧
      (∀ x, R ≤ dist x a → bumpPerturbation f ρ v x = f x) ∧
      (∀ x, ‖bumpPerturbation f ρ v x - f x‖ < ε) ∧
      (∀ x ∈ closedBall a R, bumpPerturbation f ρ v x = 0 →
        x ∈ ball a r ∧ (fderiv ℝ (bumpPerturbation f ρ v) x).det ≠ 0) ∧
      {x | x ∈ closedBall a R ∧ bumpPerturbation f ρ v x = 0}.Finite := by
  let ρ : ContDiffBump a := ⟨r,R,hr,hrR⟩
  obtain ⟨v,hv⟩ := exists_small_regular_bumpPerturbation hrR.le hU hRU hf ρ.contDiff
    (fun _ => ⟨ρ.nonneg,ρ.le_one⟩) (fun _ hx => ρ.one_of_mem_closedBall hx)
    (fun _ hx => ρ.zero_of_le_dist hx) hn hε
  exact ⟨ρ,v,ρ.contDiff,ρ.hasCompactSupport,ρ.support_eq,
    fun _ hx => ρ.one_of_mem_closedBall hx,fun _ => ⟨ρ.nonneg,ρ.le_one⟩,hv⟩

end Poincare.Calculus
