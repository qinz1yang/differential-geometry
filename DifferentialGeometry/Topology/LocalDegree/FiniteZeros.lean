import DifferentialGeometry.Topology.LocalDegree.IsolatedZero
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [PseudoMetricSpace E] [T1Space E]
  [TopologicalSpace F] [Zero F] {f : E → F} {p : E}

theorem isolatedZero_of_finite_zeroSet {s : Set E} (hs : s ∈ 𝓝 p)
    (hf : ContinuousOn f s) (hZ : {x ∈ s | f x = 0}.Finite) (hp : f p = 0) :
    isolatedZero f p := by
  have hN : ({x ∈ s | f x = 0} \ {p})ᶜ ∈ 𝓝 p :=
    hZ.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  apply isolatedZero_of_nhds hs hf hp
  filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds hs,
    Eventually.filter_mono nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with x hxs hxn hxp
  intro hx
  exact hxn ⟨⟨hxs,hx⟩,hxp⟩

theorem isolatedZero_of_continuous_finite_zeroSet (hf : Continuous f)
    (hZ : {x | f x = 0}.Finite) (hp : f p = 0) : isolatedZero f p :=
  isolatedZero_of_finite_zeroSet (s := univ) univ_mem hf.continuousOn (by simpa using hZ) hp

omit [T1Space E] [TopologicalSpace F] in
theorem closedBall_zeroSet_subset_ball {a : E} {r : ℝ}
    (hb : ∀ x ∈ sphere a r, f x ≠ 0) :
    {x ∈ closedBall a r | f x = 0} ⊆ ball a r := by
  intro x hx
  exact lt_of_le_of_ne hx.1 (fun he => hb x (mem_sphere.mpr he) hx.2)


theorem isolatedZero_of_finite_closedBall_zeroSet {a : E} {r : ℝ}
    (hf : ContinuousOn f (closedBall a r)) (hZ : {x ∈ closedBall a r | f x = 0}.Finite)
    (hb : ∀ x ∈ sphere a r, f x ≠ 0) (hp : p ∈ closedBall a r) (hz : f p = 0) :
    isolatedZero f p :=
  isolatedZero_of_finite_zeroSet
    (closedBall_mem_nhds_of_mem (closedBall_zeroSet_subset_ball hb ⟨hp,hz⟩)) hf hZ hz

end DifferentialGeometry.LocalDegree
