import DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import DifferentialGeometry.Topology.Manifold.EmbeddedBallContraction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_diffeomorph_straightening_embedded_closedBall
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ φ.source)
    {V : Set E} (hV : IsOpen V) (himage : φ '' closedBall 0 r ⊆ V) :
    ∃ (A : E ≃L[ℝ] E) (ε : ℝ) (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞),
      (A : E →L[ℝ] E) = fderiv ℝ φ 0 ∧ 0 < ε ∧ ε ≤ 1 ∧
      (∀ x ∈ closedBall 0 r, F (φ x) = ε • A x + φ 0) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
        ∀ y, y ∉ K → F y = y ∧ F.symm y = y := by
  have h0B : (0 : E) ∈ closedBall 0 r := mem_closedBall_self hr.le
  obtain ⟨A, hA, L, hgerm, K₀, hK₀, hK₀V, hLfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_straightening_partialDiffeomorph
      φ (hrs h0B) hV (himage ⟨0, h0B, rfl⟩)
  obtain ⟨δ, hδ, hδeq⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgerm
  let ε := min 1 (δ / r)
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hδ hr)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε * r ≤ δ := (le_div_iff₀ hr).mp (min_le_right _ _)
  let t := -Real.log ε
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos hε.le hε1)
  have hexp : Real.exp (-t) = ε := by simp only [t, neg_neg, Real.exp_log hε]
  obtain ⟨D, _, _, _, hrad, K₁, hK₁, hK₁V, _, hDfix⟩ :=
    exists_diffeomorphs_contracting_embedded_closedBall φ hr hrs hV himage
  let F := (D t).trans L.symm
  have hFfix (y : E) (hy : y ∉ K₀ ∪ K₁) : F y = y := by
    have h₀ : y ∉ K₀ := fun h ↦ hy (Or.inl h)
    have h₁ : y ∉ K₁ := fun h ↦ hy (Or.inr h)
    change L.symm (D t y) = y
    rw [(hDfix t y h₁).1, (hLfix y h₀).2]
  refine ⟨A, ε, F, hA, hε, hε1, ?_, K₀ ∪ K₁, hK₀.union hK₁,
    union_subset hK₀V hK₁V, ?_⟩
  · intro x hx
    have hεx : ε • x ∈ closedBall 0 δ := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hε.le).trans hεr
    have heq : L (A (ε • x) + φ 0) = φ (ε • x) := hδeq hεx
    change L.symm (D t (φ x)) = _
    rw [hrad t x ht hx, hexp, ← heq, L.symm_apply_apply, map_smul]
  · intro y hy
    refine ⟨hFfix y hy, ?_⟩
    apply F.injective
    exact (F.apply_symm_apply y).trans (hFfix y hy).symm

end DifferentialGeometry.Topology.Manifold
