import DifferentialGeometry.Topology.Manifold.BoundaryOrientationFrameChange

set_option autoImplicit false
noncomputable section
open Function Module

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem boundaryFrameSign_iff_transverseCoefficient_neg (c : ℝ) :
    (∀ s : ℝ, 0 < c * s ↔ s < 0) ↔ c < 0 := by
  constructor
  · intro h
    have hneg : 0 < c * (-1) := (h (-1)).mpr (by norm_num)
    linarith
  · intro hc s
    constructor <;> intro hs <;> nlinarith

theorem det_normalFirst_transverse (t a b c d : ℝ) :
    Matrix.det (Matrix.of ![![t, 0, 0], ![0, a, c], ![0, b, d]]) =
      t * (a * d - b * c) := by
  simp [Matrix.det_fin_three]
  ring

theorem det_normalFirst_reference (a b c d : ℝ) :
    Matrix.det (Matrix.of ![![1, 0, 0], ![0, a, c], ![0, b, d]]) =
      a * d - b * c := by
  simp [Matrix.det_fin_three]
  ring

theorem boundaryFrameSign_matrix (t : ℝ) :
    (∀ a b c d : ℝ,
      0 < Matrix.det (Matrix.of ![![t, 0, 0], ![0, a, c], ![0, b, d]]) ↔
        Matrix.det (Matrix.of ![![1, 0, 0], ![0, a, c], ![0, b, d]]) < 0) ↔ t < 0 := by
  constructor
  · intro h
    refine (boundaryFrameSign_iff_transverseCoefficient_neg t).mp ?_
    intro s
    have hs := h s 0 0 1
    simpa only [det_normalFirst_transverse, det_normalFirst_reference, mul_one, mul_zero,
      sub_zero, one_mul] using hs
  · intro ht a b c d
    rw [det_normalFirst_transverse, det_normalFirst_reference]
    exact (boundaryFrameSign_iff_transverseCoefficient_neg t).mpr ht (a * d - b * c)

theorem boundaryFrameSign_matrix_negative :
    ∀ a b c d : ℝ,
      0 < Matrix.det (Matrix.of ![![(-1 : ℝ), 0, 0], ![0, a, c], ![0, b, d]]) ↔
        Matrix.det (Matrix.of ![![1, 0, 0], ![0, a, c], ![0, b, d]]) < 0 := by
  intro a b c d
  rw [det_normalFirst_transverse, det_normalFirst_reference]
  constructor <;> intro h <;> nlinarith

theorem not_boundaryFrameSign_matrix_positive :
    ¬ (∀ a b c d : ℝ,
      0 < Matrix.det (Matrix.of ![![(1 : ℝ), 0, 0], ![0, a, c], ![0, b, d]]) ↔
        Matrix.det (Matrix.of ![![1, 0, 0], ![0, a, c], ![0, b, d]]) < 0) := by
  intro h
  have h1 : 0 < Matrix.det (Matrix.of ![![(1 : ℝ), 0, 0], ![0, 1, 0], ![0, 0, 1]]) := by
    rw [det_normalFirst_transverse]
    norm_num
  have h2 := (h 1 0 0 1).mp h1
  rw [det_normalFirst_reference] at h2
  norm_num at h2

theorem normalFirstOrientation_change_negative_normal
    (e e' : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F) (c : ℝ) (hc : c < 0) (w : F)
    (hn : e' (1, 0) = c • e (1, 0) + e (0, w))
    (ht : ∀ v : F, e' (0, v) = e (0, v)) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation e' b o = -normalFirstOrientation e b o := by
  let r : (ℝ × F) ≃ₗ[ℝ] E := normalFirstReflection.trans e
  have hr1 : r (1, 0) = -e (1, 0) := by
    change e (normalFirstReflection (1, 0)) = -e (1, 0)
    rw [show normalFirstReflection (1, 0) = -((1 : ℝ), (0 : F)) by
      simp [normalFirstReflection], map_neg]
  have hr0 : ∀ v : F, r (0, v) = e (0, v) := by
    intro v
    change e (normalFirstReflection (0, v)) = e (0, v)
    rw [show normalFirstReflection (0, v) = ((0 : ℝ), v) by simp [normalFirstReflection]]
  have hr : e' (1, 0) = (-c) • r (1, 0) + r (0, w) := by
    rw [hn, hr1, hr0, smul_neg, neg_smul, neg_neg]
  have ht' : ∀ v : F, e' (0, v) = r (0, v) := by
    intro v
    rw [ht v, hr0 v]
  calc
    normalFirstOrientation e' b o = normalFirstOrientation r b o :=
      normalFirstOrientation_change_positive_normal r e' b (-c) (by linarith) w hr ht' o
    _ = -normalFirstOrientation e b o := normalFirstOrientation_reflect_normal e b o

end DifferentialGeometry.Topology.Manifold
