import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set

namespace DifferentialGeometry.Topology.Flow

theorem exists_transverse_hit_after
    {X : Type*} [TopologicalSpace X] (φ : _root_.Flow ℝ X)
    {σ : ℝ → X} {ε : ℝ} (e : OpenPartialHomeomorph (ℝ × ℝ) X)
    (hsource : e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε)
    (he : ∀ p, e p = φ p.2 (σ p.1)) {z : X}
    (hvisits : ∀ T : ℝ, ∃ t ≥ T, φ t z ∈ e.target) :
    ∀ T : ℝ, ∃ t ≥ T, ∃ u ∈ Ioo (-ε) ε, φ t z = σ u := by
  intro T
  obtain ⟨t, ht, htarget⟩ := hvisits (T + ε)
  let p := e.symm (φ t z)
  have hp : p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε := by
    rw [← hsource]
    exact e.map_target htarget
  have horbit : φ p.2 (σ p.1) = φ t z := (he p).symm.trans (e.right_inv htarget)
  refine ⟨t - p.2, by linarith [hp.2.2], p.1, hp.1, ?_⟩
  calc
    φ (t - p.2) z = φ (-p.2) (φ t z) := by rw [← φ.map_add]; congr 1; ring
    _ = φ (-p.2) (φ p.2 (σ p.1)) := congrArg (φ (-p.2)) horbit.symm
    _ = σ p.1 := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]

end DifferentialGeometry.Topology.Flow
