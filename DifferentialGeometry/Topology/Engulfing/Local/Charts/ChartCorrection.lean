import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology

variable {E M : Type*} [NormedAddCommGroup E]
  [TopologicalSpace M]

def correctedAffineChart (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E) :
    OpenPartialHomeomorph M E := e.transHomeomorph H.symm

@[simp] theorem correctedAffineChart_source (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E) :
    (correctedAffineChart e H).source = e.source := rfl

@[simp] theorem correctedAffineChart_target (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E) :
    (correctedAffineChart e H).target = H ⁻¹' e.target := rfl

@[simp] theorem correctedAffineChart_apply (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E) (x : M) :
    correctedAffineChart e H x = H.symm (e x) := rfl

@[simp] theorem correctedAffineChart_symm_apply (e : OpenPartialHomeomorph M E)
    (H : E ≃ₜ E) (y : E) : (correctedAffineChart e H).symm y = e.symm (H y) := rfl

theorem norm_homeomorph_symm_sub_self_lt (H : E ≃ₜ E) {η : ℝ}
    (hH : ∀ y, ‖H y - y‖ < η) (x : E) : ‖H.symm x - x‖ < η := by
  have h := hH (H.symm x)
  rw [H.apply_symm_apply, norm_sub_rev] at h
  exact h

theorem correctedAffineChart_closedBall_subset_target
    (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E) (c : E) {r R η : ℝ}
    (hH : ∀ y, ‖H y - y‖ < η) (hrR : r + η ≤ R)
    (hR : closedBall c R ⊆ e.target) : closedBall c r ⊆ (correctedAffineChart e H).target := by
  intro y hy
  change H y ∈ e.target
  apply hR
  apply mem_closedBall.mpr
  have hnear : dist (H y) y < η := by simpa only [dist_eq_norm] using hH y
  have hy' := mem_closedBall.mp hy
  have ht := dist_triangle (H y) y c
  linarith

theorem correctedAffineChart_eq_of_eq (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E)
    {x : M} {y : E} (h : e x = H y) : correctedAffineChart e H x = y := by
  rw [correctedAffineChart_apply, h, H.symm_apply_apply]

theorem correctedAffineChart_core_subset
    (e : OpenPartialHomeomorph M E) (H : E ≃ₜ E) (c : E) {r R η : ℝ}
    (hH : ∀ y, ‖H y - y‖ < η) (hrR : r + η ≤ R) :
    (correctedAffineChart e H).source ∩ correctedAffineChart e H ⁻¹' ball c r ⊆
      e.source ∩ e ⁻¹' ball c R := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hnear := hH (H.symm (e x))
  rw [H.apply_symm_apply, ← dist_eq_norm] at hnear
  have hsmall : dist (H.symm (e x)) c < r := hx.2
  have ht := dist_triangle (e x) (H.symm (e x)) c
  change dist (e x) c < R
  linarith

end DifferentialGeometry.Topology.Engulfing
