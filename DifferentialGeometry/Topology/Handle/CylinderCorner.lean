import DifferentialGeometry.Topology.Handle.HalfBallRounding
import DifferentialGeometry.Topology.Diffeomorph.Graph

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

private noncomputable def cylinderCornerShear : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toDiffeomorph.trans
    ((Diffeomorph.graphShear (f := fun _ : ℝ => (0 : ℝ))
      contDiff_const (contDiff_id.pow 2)).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toDiffeomorph)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

noncomputable def cylinderCorner (r : ℝ) (v : sphere (0 : E) 1) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
      (E × ℝ) (sphere (0 : E) 1 × (ℝ × ℝ)) ∞ :=
  (halfBallCorner (n := n) r v).trans
    ((Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞).prodCongr
      cylinderCornerShear).toPartialDiffeomorph

@[simp] theorem cylinderCorner_apply (r : ℝ) (v : sphere (0 : E) 1) (p : E × ℝ) :
    cylinderCorner (n := n) r v p =
      (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
        (r ^ 2 - ‖p.1‖ ^ 2, p.2)) := by
  change (_, (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 + (p.2 ^ 2 - 0), p.2)) = _
  congr 2
  ring

@[simp] theorem cylinderCorner_symm_apply (r : ℝ) (v : sphere (0 : E) 1)
    (p : sphere (0 : E) 1 × (ℝ × ℝ)) :
    (cylinderCorner (n := n) r v).toPartialEquiv.symm p =
      (Real.sqrt (r ^ 2 - p.2.1) • p.1.val, p.2.2) := by
  change (Real.sqrt (r ^ 2 - (p.2.1 + -(p.2.2 ^ 2 - 0)) - p.2.2 ^ 2) • p.1.val, p.2.2) = _
  rw [show r ^ 2 - (p.2.1 + -(p.2.2 ^ 2 - 0)) - p.2.2 ^ 2 = r ^ 2 - p.2.1 by ring]

@[simp] theorem cylinderCorner_source (r : ℝ) (v : sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).source = {p : E × ℝ | p.1 ≠ 0} := by
  ext p
  change (p.1 ≠ 0 ∧ True) ↔ p.1 ≠ 0
  simp

@[simp] theorem cylinderCorner_target (r : ℝ) (v : sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).target = {p | p.2.1 < r ^ 2} := by
  ext p
  change (True ∧ 0 < r ^ 2 - (p.2.1 + -(p.2.2 ^ 2 - 0)) - p.2.2 ^ 2) ↔ _
  simp only [true_and, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

theorem cylinderCorner_isImage (r : ℝ) (v : sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | ‖p.1‖ ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}
      {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by
  intro p _
  change (0 ≤ (cylinderCorner (n := n) r v p).2.1 ∧
    0 ≤ (cylinderCorner (n := n) r v p).2.2) ↔ _
  rw [cylinderCorner_apply]
  exact and_congr (sub_nonneg) Iff.rfl

theorem cylinderCorner_isImage_boundary (r : ℝ) (v : sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | (‖p.1‖ ^ 2 ≤ r ^ 2 ∧ p.2 = 0) ∨
        (‖p.1‖ ^ 2 = r ^ 2 ∧ 0 ≤ p.2)}
      {p | (0 ≤ p.2.1 ∧ p.2.2 = 0) ∨ (p.2.1 = 0 ∧ 0 ≤ p.2.2)} := by
  intro p _
  change ((0 ≤ (cylinderCorner (n := n) r v p).2.1 ∧
    (cylinderCorner (n := n) r v p).2.2 = 0) ∨
    ((cylinderCorner (n := n) r v p).2.1 = 0 ∧
      0 ≤ (cylinderCorner (n := n) r v p).2.2)) ↔ _
  rw [cylinderCorner_apply]
  exact or_congr (and_congr sub_nonneg Iff.rfl)
    (and_congr (sub_eq_zero.trans eq_comm) Iff.rfl)

theorem cylinderCorner_strip_subset_target (r : ℝ) (v : sphere (0 : E) 1)
    {ε : ℝ} (hε : ε < r ^ 2) :
    {p : sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      (cylinderCorner (n := n) r v).target := by
  rw [cylinderCorner_target]
  intro p hp
  exact lt_of_le_of_lt (by linarith [hp.2.1, hp.2.2]) hε

end PartialDiffeomorph
