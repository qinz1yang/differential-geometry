import Mathlib.Topology.Homotopy.Affine
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import DifferentialGeometry.Topology.Compactness.Nonvanishing

set_option autoImplicit false
noncomputable section
open Set Metric
namespace Poincare.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineInterpolation_ne_zero_of_norm_sub_lt {u v : E}
    (h : ‖v - u‖ < ‖u‖) (t : unitInterval) :
    (1 - (t : ℝ)) • u + (t : ℝ) • v ≠ 0 := by
  have hs : ‖(t : ℝ) • (v - u)‖ < ‖u‖ := by
    rw [norm_smul,Real.norm_of_nonneg t.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans_lt h
  intro hz
  have he : (t : ℝ) • (v - u) = -u := by
    calc
      _ = ((1 - (t : ℝ)) • u + (t : ℝ) • v) - u := by module
      _ = -u := by rw [hz,zero_sub]
  rw [he,norm_neg] at hs
  exact (lt_irrefl _) hs

variable {X : Type*} [TopologicalSpace X]

theorem affineHomotopy_ne_zero_of_norm_sub_lt (f g : C(X, E))
    (hclose : ∀ x, ‖g x - f x‖ < ‖f x‖) (q : unitInterval × X) :
    ContinuousMap.Homotopy.affine f g q ≠ 0 := by
  rw [ContinuousMap.Homotopy.affine_apply,AffineMap.lineMap_apply]
  change (q.1 : ℝ) • (g q.2 - f q.2) + f q.2 ≠ 0
  have he : (q.1 : ℝ) • (g q.2 - f q.2) + f q.2 =
      (1 - (q.1 : ℝ)) • f q.2 + (q.1 : ℝ) • g q.2 := by module
  rw [he]
  exact affineInterpolation_ne_zero_of_norm_sub_lt (hclose q.2) q.1

theorem exists_pos_nonzero_affineHomotopy [CompactSpace X] (f : C(X, E))
    (hf : ∀ x, f x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : C(X, E), (∀ x, ‖g x - f x‖ < δ) →
      ∀ q, ContinuousMap.Homotopy.affine f g q ≠ 0 := by
  obtain ⟨δ,hδ,hbound⟩ := exists_pos_lt_norm_of_isCompact isCompact_univ
    f.continuous.continuousOn (fun x _ => hf x)
  exact ⟨δ,hδ,fun g hg q => affineHomotopy_ne_zero_of_norm_sub_lt f g
    (fun x => (hg x).trans (hbound x (mem_univ x))) q⟩

end Poincare.Topology
