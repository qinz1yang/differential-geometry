import DifferentialGeometry.Topology.Manifold.StereographicAntipodal

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def stereographicBallImage (north : Metric.sphere (0 : E) 1) (r : ℝ) :
    TopologicalSpace.Opens (Metric.sphere (0 : E) 1) :=
  ⟨(stereographic' n north).symm '' Metric.ball 0 r,
    ((stereographic' n north).symm.isOpenEmbedding (by simp)).isOpenMap _ Metric.isOpen_ball⟩

theorem mem_stereographicBallImage_inverse (north : Metric.sphere (0 : E) 1) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (stereographic' n north).symm x ∈ stereographicBallImage (n := n) north r ↔ ‖x‖ < r := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy := ((stereographic' n north).symm.isOpenEmbedding (by simp)).injective he
    simpa only [hxy, Metric.mem_ball, dist_zero_right] using hy
  · intro hx
    exact ⟨x, by simpa only [Metric.mem_ball, dist_zero_right] using hx, rfl⟩

theorem stereographicBallImage_subset_punctured (north : Metric.sphere (0 : E) 1) (r : ℝ) :
    (stereographicBallImage (n := n) north r : Set (Metric.sphere (0 : E) 1)) ⊆ {north}ᶜ := by
  rintro p ⟨x, _, rfl⟩
  simpa only [stereographic'_source] using
    (stereographic' n north).map_target (show x ∈ (stereographic' n north).target by simp)

private theorem inverse_zero (north : Metric.sphere (0 : E) 1) :
    (stereographic' n north).symm 0 = -north := by
  apply Subtype.ext
  change ((stereographic' n north).symm 0 : E) = -(north : E)
  norm_num [stereographic'_symm_apply, smul_smul]

theorem stereographicBallImage_antipodal_cover (north : Metric.sphere (0 : E) 1)
    (r : ℝ) (hr : 2 < r) (p : Metric.sphere (0 : E) 1) :
    p ∈ stereographicBallImage (n := n) north r ∨
      sphereAntipodalDiffeomorph (n := n) p ∈ stereographicBallImage (n := n) north r := by
  have hr0 : 0 < r := by linarith
  by_cases hp : p = north
  · subst p
    right
    exact ⟨0, by simpa only [Metric.mem_ball, dist_self] using hr0, inverse_zero north⟩
  · let x := stereographic' n north p
    have he : (stereographic' n north).symm x = p :=
      (stereographic' n north).left_inv (by simpa only [stereographic'_source, mem_compl_iff, mem_singleton_iff] using hp)
    by_cases hx : ‖x‖ < r
    · left
      exact ⟨x, by simpa only [Metric.mem_ball, dist_zero_right] using hx, he⟩
    · have hxr : r ≤ ‖x‖ := le_of_not_gt hx
      have hx0 : 0 < ‖x‖ := hr0.trans_le hxr
      have hnorm : ‖(-4 / ‖x‖ ^ 2) • x‖ = 4 / ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_neg (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hx0))]
        field_simp
      have hsmall : ‖(-4 / ‖x‖ ^ 2) • x‖ < r := by
        rw [hnorm, div_lt_iff₀ hx0]
        nlinarith
      right
      refine ⟨(-4 / ‖x‖ ^ 2) • x,
        by simpa only [Metric.mem_ball, dist_zero_right] using hsmall, ?_⟩
      change (stereographic' n north).symm ((-4 / ‖x‖ ^ 2) • x) = -p
      rw [stereographicInverse_antipodal north x (norm_pos_iff.mp hx0), he]
end DifferentialGeometry.Topology.Manifold
