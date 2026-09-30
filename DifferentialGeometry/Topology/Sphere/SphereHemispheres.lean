import DifferentialGeometry.Topology.Sphere.SphereSuspension

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

def lowerClosedHemisphere (m : ℕ) :
    Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :=
  {z | (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ≤ 0}

def upperClosedHemisphere (m : ℕ) :
    Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :=
  {z | 0 ≤ (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))}

@[simp]
theorem mem_lowerClosedHemisphere {m : ℕ}
    (z : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    z ∈ lowerClosedHemisphere m ↔
      (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ≤ 0 := Iff.rfl

@[simp]
theorem mem_upperClosedHemisphere {m : ℕ}
    (z : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    z ∈ upperClosedHemisphere m ↔
      0 ≤ (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) := Iff.rfl

@[simp]
theorem lowerHemisphere_last (m : ℕ) (x : Disk (m + 1)) :
    (lowerHemisphere m x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) =
      -diskHeight x := euclidSnoc_apply_last _ _

@[simp]
theorem upperHemisphere_last (m : ℕ) (x : Disk (m + 1)) :
    (upperHemisphere m x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) =
      diskHeight x := euclidSnoc_apply_last _ _

theorem range_lowerHemisphere_eq (m : ℕ) :
    range (lowerHemisphere m) = lowerClosedHemisphere m := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [mem_lowerClosedHemisphere, lowerHemisphere_last, neg_nonpos] using
      diskHeight_nonneg x
  · intro hz
    have hcover : z ∈ range (lowerHemisphere m) ∪ range (upperHemisphere m) := by
      rw [range_lowerHemisphere_union_range_upperHemisphere]
      trivial
    rcases hcover with h | ⟨x, rfl⟩
    · exact h
    · have hx : diskHeight x = 0 := le_antisymm
        (by simpa only [mem_lowerClosedHemisphere, upperHemisphere_last] using hz)
        (diskHeight_nonneg x)
      exact ⟨x, (lowerHemisphere_eq_upperHemisphere_iff m x x).2
        ⟨rfl, (diskHeight_eq_zero_iff x).1 hx⟩⟩

theorem range_upperHemisphere_eq (m : ℕ) :
    range (upperHemisphere m) = upperClosedHemisphere m := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [mem_upperClosedHemisphere, upperHemisphere_last] using diskHeight_nonneg x
  · intro hz
    have hcover : z ∈ range (lowerHemisphere m) ∪ range (upperHemisphere m) := by
      rw [range_lowerHemisphere_union_range_upperHemisphere]
      trivial
    rcases hcover with ⟨x, rfl⟩ | h
    · have hx : diskHeight x = 0 := le_antisymm
        (by simpa only [mem_upperClosedHemisphere, lowerHemisphere_last, neg_nonneg] using hz)
        (diskHeight_nonneg x)
      exact ⟨x, ((lowerHemisphere_eq_upperHemisphere_iff m x x).2
        ⟨rfl, (diskHeight_eq_zero_iff x).1 hx⟩).symm⟩
    · exact h

noncomputable def lowerClosedHemisphereHomeomorph (m : ℕ) :
    lowerClosedHemisphere m ≃ₜ Disk (m + 1) :=
  (((continuous_lowerHemisphere m).isClosedEmbedding
    (lowerHemisphere_injective m)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_lowerHemisphere_eq m))).symm

noncomputable def upperClosedHemisphereHomeomorph (m : ℕ) :
    upperClosedHemisphere m ≃ₜ Disk (m + 1) :=
  (((continuous_upperHemisphere m).isClosedEmbedding
    (upperHemisphere_injective m)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_upperHemisphere_eq m))).symm

@[simp]
theorem lowerHemisphere_closedHemisphereHomeomorph (m : ℕ)
    (z : lowerClosedHemisphere m) :
    lowerHemisphere m (lowerClosedHemisphereHomeomorph m z) = z.val :=
  congrArg Subtype.val ((lowerClosedHemisphereHomeomorph m).symm_apply_apply z)

@[simp]
theorem upperHemisphere_closedHemisphereHomeomorph (m : ℕ)
    (z : upperClosedHemisphere m) :
    upperHemisphere m (upperClosedHemisphereHomeomorph m z) = z.val :=
  congrArg Subtype.val ((upperClosedHemisphereHomeomorph m).symm_apply_apply z)

@[simp]
theorem lowerClosedHemisphereHomeomorph_mem_diskSphere_iff (m : ℕ)
    (z : lowerClosedHemisphere m) :
    lowerClosedHemisphereHomeomorph m z ∈ diskSphere (m + 1) ↔
      (z.val : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) = 0 := by
  have hz := congrArg
    (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 =>
      (w : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)))
    (lowerHemisphere_closedHemisphereHomeomorph m z)
  simp only [lowerHemisphere_last] at hz
  rw [← hz, neg_eq_zero]
  exact (diskHeight_eq_zero_iff _).symm

@[simp]
theorem upperClosedHemisphereHomeomorph_mem_diskSphere_iff (m : ℕ)
    (z : upperClosedHemisphere m) :
    upperClosedHemisphereHomeomorph m z ∈ diskSphere (m + 1) ↔
      (z.val : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) = 0 := by
  have hz := congrArg
    (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 =>
      (w : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)))
    (upperHemisphere_closedHemisphereHomeomorph m z)
  simp only [upperHemisphere_last] at hz
  rw [← hz]
  exact (diskHeight_eq_zero_iff _).symm

@[simp]
theorem sphereSouthPole_last (m : ℕ) :
    (sphereSouthPole m : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) = -1 :=
  euclidSnoc_apply_last _ _

@[simp]
theorem sphereNorthPole_last (m : ℕ) :
    (sphereNorthPole m : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) = 1 :=
  euclidSnoc_apply_last _ _

theorem sphereSouthPole_last_neg (m : ℕ) :
    (sphereSouthPole m : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) < 0 := by
  simp

theorem sphereNorthPole_last_pos (m : ℕ) :
    0 < (sphereNorthPole m : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) := by
  simp

end DifferentialGeometry.Topology
