import DifferentialGeometry.Topology.LocalDegree.SphereMap

set_option autoImplicit false
open Filter Metric Set
open scoped Topology
noncomputable section
namespace Poincare.LocalDegree
variable {E F : Type*} [PseudoMetricSpace E] [TopologicalSpace F] [Zero F]

structure IsolatingRadius (f : E → F) (x : E) (R : ℝ) : Prop where
  pos : 0 < R
  continuousOn : ContinuousOn f (closedBall x R)
  zero_iff : ∀ y ∈ closedBall x R, f y = 0 ↔ y = x


def isolatedZero (f : E → F) (x : E) : Prop :=
  ∃ R, IsolatingRadius f x R

namespace IsolatingRadius

variable {f g : E → F} {x : E} {R : ℝ} (h : IsolatingRadius f x R)

include h


theorem zero : f x = 0 := (h.zero_iff x (mem_closedBall_self h.pos.le)).mpr rfl


theorem nonzero (y : E) (hy : y ∈ closedBall x R) (hne : y ≠ x) : f y ≠ 0 :=
  mt (h.zero_iff y hy).mp hne


theorem mono {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) : IsolatingRadius f x r where
  pos := hr
  continuousOn := h.continuousOn.mono (closedBall_subset_closedBall hrR)
  zero_iff y hy := h.zero_iff y (closedBall_subset_closedBall hrR hy)


theorem congr (hfg : EqOn f g (closedBall x R)) : IsolatingRadius g x R where
  pos := h.pos
  continuousOn := h.continuousOn.congr hfg.symm
  zero_iff y hy := by rw [← hfg hy]; exact h.zero_iff y hy

end IsolatingRadius

theorem isolatedZero_of_nhds {f : E → F} {x : E} {s : Set E}
    (hs : s ∈ 𝓝 x) (hc : ContinuousOn f s) (hz : f x = 0)
    (hzero : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) : isolatedZero f x := by
  have hs' : ∀ᶠ y in 𝓝 x, y ∈ s := hs
  have hn := hs'.and (eventually_nhdsWithin_iff.mp hzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε / 2, ?_⟩
  have hsub : closedBall x (ε / 2) ⊆ s ∩ {y | y ≠ x → f y ≠ 0} := by
    intro y hy
    apply hball
    exact (closedBall_subset_ball (by linarith)) hy
  exact {
    pos := by positivity
    continuousOn := hc.mono (fun y hy ↦ (hsub hy).1)
    zero_iff := fun y hy ↦ ⟨fun hfy ↦ by
      by_contra hne
      exact (hsub hy).2 hne hfy, fun hyx ↦ hyx ▸ hz⟩ }


theorem isolatedZero_congr {f g : E → F} {x : E} (hfg : f =ᶠ[𝓝 x] g) :
    isolatedZero f x ↔ isolatedZero g x := by
  suffices transfer : ∀ {f g : E → F}, f =ᶠ[𝓝 x] g →
      isolatedZero f x → isolatedZero g x from
    ⟨transfer hfg, transfer hfg.symm⟩
  intro f g hfg ⟨R, hR⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfg
  let r := min R (ε / 2)
  have hr : 0 < r := lt_min hR.pos (by positivity)
  have hrr : r ≤ R := min_le_left _ _
  refine ⟨r, (hR.mono hr hrr).congr ?_⟩
  intro y hy
  exact hball (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _)
    (by linarith)) hy)

end Poincare.LocalDegree
