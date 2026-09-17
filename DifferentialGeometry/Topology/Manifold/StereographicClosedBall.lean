import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Embedding.Frontier

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem stereographic_symm_zero (p : Metric.sphere (0 : E) 1) :
    (stereographic' n p).symm 0 = -p := by
  apply Subtype.ext
  change ((stereographic' n p).symm 0 : E) = -(p : E)
  norm_num [stereographic'_symm_apply, smul_smul]

theorem mem_antipodal_stereographic_symm_closedBall
    (p : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(stereographic' n p).symm x ∈ (stereographic' n p).symm '' closedBall 0 (4 / r) ↔
      r ≤ ‖x‖ := by
  let c := stereographic' n p
  have hinj : Function.Injective c.symm := (c.symm.isOpenEmbedding (by simp [c])).injective
  by_cases hx : x = 0
  · subst x
    rw [stereographic_symm_zero, neg_neg, norm_zero]
    have hp : p ∉ c.symm '' closedBall 0 (4 / r) := by
      rintro ⟨y, _, hy⟩
      have hs := c.map_target (show y ∈ c.target by simp [c])
      rw [hy] at hs
      simp [c] at hs
    exact iff_of_false hp (not_le.mpr hr)
  · rw [← stereographicInverse_antipodal p x hx]
    change c.symm ((-4 / ‖x‖ ^ 2) • x) ∈ c.symm '' closedBall 0 (4 / r) ↔ _
    rw [hinj.mem_set_image, mem_closedBall_zero_iff]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hnorm : ‖(-4 / ‖x‖ ^ 2) • x‖ = 4 / ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_neg (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hxpos))]
      field_simp
    rw [hnorm, div_le_div_iff₀ hxpos hr]
    constructor <;> intro h <;> nlinarith

theorem antipodal_image_stereographic_symm_closedBall
    (p : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) :
    Neg.neg '' ((stereographic' n p).symm '' closedBall 0 (4 / r)) =
      ((stereographic' n p).symm '' ball 0 r)ᶜ := by
  let c := stereographic' n p
  have hinj : Function.Injective c.symm := (c.symm.isOpenEmbedding (by simp [c])).injective
  ext y
  have hleft : y ∈ Neg.neg '' (c.symm '' closedBall 0 (4 / r)) ↔
      -y ∈ c.symm '' closedBall 0 (4 / r) := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [neg_neg] using hz
    · intro hy
      exact ⟨-y, hy, neg_neg y⟩
  rw [hleft]
  by_cases hy : y = p
  · subst y
    have hmem : -p ∈ c.symm '' closedBall 0 (4 / r) :=
      ⟨0, mem_closedBall_self (by positivity), stereographic_symm_zero p⟩
    have hnot : p ∉ c.symm '' ball 0 r := by
      rintro ⟨x, _, hx⟩
      have hs := c.map_target (show x ∈ c.target by simp [c])
      rw [hx] at hs
      simp [c] at hs
    exact iff_of_true hmem hnot
  · have hys : y ∈ c.source := by
      simpa only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff] using hy
    have he : c.symm (c y) = y := c.left_inv hys
    rw [← he, mem_antipodal_stereographic_symm_closedBall p hr, mem_compl_iff,
      hinj.mem_set_image, mem_ball_zero_iff, not_lt]

theorem interior_image_stereographic_symm_closedBall
    (p : Metric.sphere (0 : E) 1) {r : ℝ} (hr : r ≠ 0) :
    interior ((stereographic' n p).symm '' closedBall 0 r) =
      (stereographic' n p).symm '' ball 0 r := by
  rw [DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding
    ((stereographic' n p).symm.isOpenEmbedding (by simp)), interior_closedBall _ hr]

end DifferentialGeometry.Topology.Manifold
