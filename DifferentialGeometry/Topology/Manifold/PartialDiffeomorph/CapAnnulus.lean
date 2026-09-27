import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (C T : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R)
    (hC : closedBall (0 : E3) L ⊆ C.source)
    (hT : closedBall (0 : E3) R \ ball (0 : E3) L ⊆ T.source)
    {O : Set E3} (hO : IsOpen O) (hSO : sphere (0 : E3) L ⊆ O)
    (heq : EqOn C T O)
    (hinter : C '' closedBall (0 : E3) L ∩ T '' (closedBall (0 : E3) R \ ball (0 : E3) L) ⊆
      C '' sphere (0 : E3) L) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧
      (∀ z ∈ closedBall (0 : E3) L, B (R⁻¹ • z) = C z) ∧
      (∀ z ∈ closedBall (0 : E3) R \ ball (0 : E3) L, B (R⁻¹ • z) = T z) ∧
      B '' ball (0 : E3) 1 = C '' closedBall (0 : E3) L ∪
        T '' (ball (0 : E3) R \ ball (0 : E3) L) ∧
      ∃ V₀ V₁ : Set E3, IsOpen V₀ ∧ IsOpen V₁ ∧
        closedBall (0 : E3) L ⊆ V₀ ∧
        closedBall (0 : E3) R \ ball (0 : E3) L ⊆ V₁ ∧
        EqOn (fun z => B (R⁻¹ • z)) C V₀ ∧ EqOn (fun z => B (R⁻¹ • z)) T V₁ := by
  have hR : 0 < R := hL.trans hLR
  let K₀ := closedBall (0 : E3) L
  let K₁ := closedBall (0 : E3) R \ ball (0 : E3) L
  have hK₁ : IsCompact K₁ := (isCompact_closedBall (0 : E3) R).inter_right isOpen_ball.isClosed_compl
  have hseam : K₀ ∩ K₁ = sphere (0 : E3) L := by
    ext z
    simp only [K₀, K₁, mem_inter_iff, mem_sdiff, mem_closedBall_zero_iff,
      mem_ball_zero_iff, mem_sphere_zero_iff_norm, not_lt]
    constructor
    · rintro ⟨hl, _, hg⟩
      exact le_antisymm hl hg
    · intro hz
      exact ⟨hz.le, hz.le.trans hLR.le, hz.ge⟩
  have hcover : K₀ ∪ K₁ = closedBall (0 : E3) R := by
    apply subset_antisymm
    · exact union_subset (closedBall_subset_closedBall hLR.le) sdiff_subset
    · intro z hz
      by_cases h : z ∈ ball (0 : E3) L
      · exact Or.inl (ball_subset_closedBall h)
      · exact Or.inr ⟨hz, h⟩
  obtain ⟨F, U₀, U₁, hU₀o, hU₁o, hK₀U, hK₁U, hU, hFC, hFT⟩ :=
    PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact C T
      (isCompact_closedBall (0 : E3) L) hK₁ hC hT hO
      (hseam ▸ hSO) heq (hseam ▸ hinter)
  have hRF : closedBall (0 : E3) R ⊆ F.source := by
    rw [← hcover]
    exact (union_subset_union hK₀U hK₁U).trans hU
  let D : E3 ≃ₘ[ℝ] E3 :=
    (LinearEquiv.smulOfNeZero ℝ E3 R hR.ne').toContinuousLinearEquiv.toDiffeomorph
  let B := D.toPartialDiffeomorph.trans F
  have hB (z : E3) : B z = F (R • z) := rfl
  have hBinv (z : E3) : B (R⁻¹ • z) = F z := by
    rw [hB, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hBsrc : closedBall (0 : E3) 1 ⊆ B.source := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    apply hRF
    rw [mem_closedBall_zero_iff]
    change ‖R • z‖ ≤ R
    rw [norm_smul, Real.norm_of_nonneg hR.le]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hR.le).trans_eq (mul_one R)
  refine ⟨B, hBsrc, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hBinv]
    exact hFC (hK₀U hz)
  · intro z hz
    rw [hBinv]
    exact hFT (hK₁U hz)
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hRz : R • z ∈ ball (0 : E3) R := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hR.le]
        exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) hR).trans_eq (mul_one R)
      by_cases hzL : R • z ∈ closedBall (0 : E3) L
      · exact Or.inl ⟨R • z, hzL, (hFC (hK₀U hzL)).symm⟩
      · have hznot : R • z ∉ ball (0 : E3) L := fun h => hzL (ball_subset_closedBall h)
        exact Or.inr ⟨R • z, ⟨hRz, hznot⟩,
          (hFT (hK₁U ⟨ball_subset_closedBall hRz, hznot⟩)).symm⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine ⟨R⁻¹ • z, ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
          exact (inv_mul_lt_iff₀ hR).mpr (by simpa only [mul_one] using
            (mem_closedBall_zero_iff.mp hz).trans_lt hLR)
        · rw [hBinv]
          exact hFC (hK₀U hz)
      · refine ⟨R⁻¹ • z, ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
          exact (inv_mul_lt_iff₀ hR).mpr (by simpa only [mul_one] using mem_ball_zero_iff.mp hz.1)
        · rw [hBinv]
          exact hFT (hK₁U ⟨ball_subset_closedBall hz.1, hz.2⟩)
  · exact ⟨U₀, U₁, hU₀o, hU₁o, hK₀U, hK₁U,
      fun z hz => (hBinv z).trans (hFC hz), fun z hz => (hBinv z).trans (hFT hz)⟩

theorem exists_ball_chart_of_cap_and_annulus
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (C T : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R)
    (hC : closedBall (0 : E3) L ⊆ C.source)
    (hT : closedBall (0 : E3) R \ ball (0 : E3) L ⊆ T.source)
    {O : Set E3} (hO : IsOpen O) (hSO : sphere (0 : E3) L ⊆ O)
    (heq : EqOn C T O)
    (hinter : C '' closedBall (0 : E3) L ∩ T '' (closedBall (0 : E3) R \ ball (0 : E3) L) ⊆
      C '' sphere (0 : E3) L) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧
      (∀ z ∈ closedBall (0 : E3) L, B (R⁻¹ • z) = C z) ∧
      (∀ z ∈ closedBall (0 : E3) R \ ball (0 : E3) L, B (R⁻¹ • z) = T z) ∧
      B '' ball (0 : E3) 1 = C '' closedBall (0 : E3) L ∪
        T '' (ball (0 : E3) R \ ball (0 : E3) L) := by
  obtain ⟨B, hBs, hBC, hBT, hBi, _⟩ :=
    exists_ball_chart_of_cap_and_annulus_eqOn_neighborhoods C T hL hLR hC hT hO hSO heq hinter
  exact ⟨B, hBs, hBC, hBT, hBi⟩

end DifferentialGeometry.Topology.Manifold
