import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismLift
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.CompactConvergence

noncomputable section

open Set Filter Function ContinuousMap
open scoped Topology
open DifferentialGeometry.Topology

private theorem signed_monotone_periodic_of_tendsto
    {A : Type*} {l : Filter A} [l.NeBot] {f : A → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ᶠ a in l,
      (Monotone (f a) ∧ ∀ t, f a (t + 1) = f a t + 1) ∨
      (Antitone (f a) ∧ ∀ t, f a (t + 1) = f a t - 1))
    (hlim : ∀ t, Tendsto (fun a => f a t) l (𝓝 (g t))) :
    (Monotone g ∧ ∀ t, g (t + 1) = g t + 1) ∨
      (Antitone g ∧ ∀ t, g (t + 1) = g t - 1) := by
  have hi : IsClosed {f : ℝ → ℝ | Monotone f ∧ ∀ t, f (t + 1) = f t + 1} := by
    have hp : IsClosed {f : ℝ → ℝ | ∀ t, f (t + 1) = f t + 1} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t =>
        isClosed_eq (continuous_apply (t + 1)) ((continuous_apply t).add continuous_const)
    exact isClosed_monotone.inter hp
  have hd : IsClosed {f : ℝ → ℝ | Antitone f ∧ ∀ t, f (t + 1) = f t - 1} := by
    have hp : IsClosed {f : ℝ → ℝ | ∀ t, f (t + 1) = f t - 1} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t =>
        isClosed_eq (continuous_apply (t + 1)) ((continuous_apply t).sub continuous_const)
    exact isClosed_antitone.inter hp
  exact (hi.union hd).mem_of_tendsto (tendsto_pi_nhds.mpr hlim) hf

namespace AddCircle

private theorem abs_lt_of_norm_coe_lt
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {p ε : ℝ} (hp : p ≠ 0) (hε : ε ≤ |p| / 2)
    {f : X → ℝ} (hf : Continuous f) (x₀ : X)
    (h₀ : |f x₀| < ε) (h : ∀ x, ‖(f x : AddCircle p)‖ < ε) :
    ∀ x, |f x| < ε := by
  intro x
  by_contra hx
  obtain ⟨y, hy⟩ := intermediate_value_univ x₀ x hf.abs
    ⟨h₀.le, le_of_not_gt hx⟩
  have heq : ‖(f y : AddCircle p)‖ = |f y| :=
    (norm_coe_eq_abs_iff p hp).2 (hy.trans_le hε)
  exact (h y).ne (heq.trans hy)

private theorem dist_lt_of_dist_coe_lt
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {p ε : ℝ} (hp : p ≠ 0) (hε : ε ≤ |p| / 2)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (x₀ : X)
    (h₀ : dist (f x₀) (g x₀) < ε)
    (h : ∀ x, dist (f x : AddCircle p) (g x : AddCircle p) < ε) :
    ∀ x, dist (f x) (g x) < ε := by
  simpa only [Real.dist_eq, Pi.sub_apply] using abs_lt_of_norm_coe_lt hp hε (hf.sub hg) x₀
    (by simpa only [Real.dist_eq, Pi.sub_apply] using h₀)
    (fun x => by simpa only [dist_eq_norm, ← coe_sub, Pi.sub_apply] using h x)

end AddCircle

namespace DifferentialGeometry.Geometry

private theorem exists_continuous_circle_lift (σ : C(loopCircle, loopCircle)) :
    ∃ ψ : C(ℝ, ℝ), ∀ t, (ψ t : loopCircle) = σ (t : loopCircle) := by
  let p : ℝ → loopCircle := fun t => (t : loopCircle)
  have hcov : IsCoveringMap p := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (σ 0)
  let f : C(ℝ, loopCircle) := ⟨σ ∘ p, σ.continuous.comp hcov.continuous⟩
  obtain ⟨ψ, ⟨_, hψ⟩, _⟩ := hcov.existsUnique_continuousMap_lifts f 0 a (by
    change (a : loopCircle) = σ (0 : loopCircle)
    exact ha)
  exact ⟨ψ, fun t => congrFun hψ t⟩

private theorem IsWeaklyMonotoneOnce.of_forall_of_tendsto
    {A : Type*} {l : Filter A} [l.NeBot]
    {σ : A → C(loopCircle, loopCircle)} {τ : C(loopCircle, loopCircle)}
    (hσ : ∀ a, IsWeaklyMonotoneOnce (σ a)) (hlim : Tendsto σ l (𝓝 τ)) :
    IsWeaklyMonotoneOnce τ := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_continuous_circle_lift τ
  choose f hfc hfl hfs using hσ
  let k := fun a => round (f a 0 - ψ 0)
  let F := fun a t => f a t - (k a : ℝ)
  have hFcont (a : A) : Continuous (F a) := (hfc a).sub continuous_const
  have hFlift (a : A) (t : ℝ) : (F a t : loopCircle) = σ a (t : loopCircle) := by
    have hk : ((k a : ℝ) : loopCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k a, by simp⟩
    dsimp only [F]
    rw [AddCircle.coe_sub, hk, sub_zero, hfl]
  have hFnorm (a : A) : dist (F a 0) (ψ 0) = dist (σ a 0) (τ 0) := by
    have hf0 : (f a 0 : loopCircle) = σ a 0 := by simpa using hfl a 0
    have hψ0 : (ψ 0 : loopCircle) = τ 0 := by simpa using hψ 0
    rw [Real.dist_eq, dist_eq_norm, ← hf0, ← hψ0, ← AddCircle.coe_sub]
    simp only [AddCircle.norm_eq, inv_one, one_mul, mul_one]
    congr 1
    dsimp only [F, k]
    ring
  have hFsign (a : A) :
      (Monotone (F a) ∧ ∀ t, F a (t + 1) = F a t + 1) ∨
      (Antitone (F a) ∧ ∀ t, F a (t + 1) = F a t - 1) := by
    rcases hfs a with ⟨hm, hp⟩ | ⟨hm, hp⟩
    · left
      exact ⟨fun x y hxy => sub_le_sub_right (hm hxy) _, fun t => by dsimp only [F]; rw [hp]; ring⟩
    · right
      exact ⟨fun x y hxy => sub_le_sub_right (hm hxy) _, fun t => by dsimp only [F]; rw [hp]; ring⟩
  have hfun := ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim
  have hFconverges : ∀ t, Tendsto (fun a => F a t) l (𝓝 (ψ t)) := by
    intro t
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := min ε (1 / 2 : ℝ)
    have hδ : 0 < δ := lt_min hε (by norm_num)
    have hevent := (Metric.tendstoUniformly_iff.mp hfun) δ hδ
    filter_upwards [hevent] with a ha
    have ha' : ∀ x : ℝ, dist (F a x : loopCircle) (ψ x : loopCircle) < δ := by
      intro x
      rw [hFlift, hψ, dist_comm]
      exact ha (x : loopCircle)
    have ha₀ : dist (F a 0) (ψ 0) < δ := by
      rw [hFnorm, dist_comm]
      exact ha 0
    exact (AddCircle.dist_lt_of_dist_coe_lt (by norm_num : (1 : ℝ) ≠ 0)
      (by simpa only [abs_one] using (min_le_right ε (1 / 2 : ℝ)))
      (hFcont a) ψ.continuous 0 ha₀ ha' t).trans_le (min_le_left ε (1 / 2 : ℝ))
  exact ⟨ψ, ψ.continuous, hψ,
    signed_monotone_periodic_of_tendsto (Eventually.of_forall hFsign) hFconverges⟩


theorem isClosed_isWeaklyMonotoneOnce :
    IsClosed {σ : C(loopCircle, loopCircle) | IsWeaklyMonotoneOnce σ} := by
  apply IsSeqClosed.isClosed
  intro σ τ hσ hlim
  exact IsWeaklyMonotoneOnce.of_forall_of_tendsto hσ hlim

theorem IsWeaklyMonotoneOnce.of_tendsto
    {A : Type*} {l : Filter A} [l.NeBot]
    {σ : A → C(loopCircle, loopCircle)} {τ : C(loopCircle, loopCircle)}
    (hσ : ∀ᶠ a in l, IsWeaklyMonotoneOnce (σ a)) (hlim : Tendsto σ l (𝓝 τ)) :
    IsWeaklyMonotoneOnce τ :=
  isClosed_isWeaklyMonotoneOnce.mem_of_tendsto hlim hσ

end DifferentialGeometry.Geometry

end
