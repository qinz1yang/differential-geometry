import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFillingClosedBall
import DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening
import DifferentialGeometry.Topology.Handle.Embedding

open scoped ContDiff Manifold
open Set Metric Manifold

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

noncomputable def smoothSchoenfliesCore : Prop :=
  ∀ (e : S² → ℝ³), IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
    ∃ (b : ClosedCell 3 → ℝ³)
      (φ : PartialDiffeomorph (𝓡 3) (𝓡 3) ℝ³ ℝ³ ∞),
      IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b ∧
      Set.range (b ∘ cellBoundaryInclusion 3) = Set.range e ∧
      closedBall (0 : ℝ³) 1 ⊆ φ.source ∧
      ∀ x : ClosedCell 3, (φ : ℝ³ → ℝ³) (x : ℝ³) = b x

private noncomputable def affineChartDiffeomorph (A : ℝ³ ≃L[ℝ] ℝ³) (c : ℝ³)
    (ε : ℝ) (hε : ε ≠ 0) : ℝ³ ≃ₘ[ℝ] ℝ³ where
  toFun y := ε⁻¹ • A.symm (y - c)
  invFun x := A (ε • x) + c
  left_inv y := by
    dsimp only
    rw [smul_smul, mul_inv_cancel₀ hε, one_smul, A.apply_symm_apply, sub_add_cancel]
  right_inv x := by
    dsimp only
    rw [add_sub_cancel_right, A.symm_apply_apply, smul_smul, inv_mul_cancel₀ hε, one_smul]
  contMDiff_toFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : ℝ³ => ε⁻¹ • A.symm (y - c))
    apply ContDiff.contMDiff
    fun_prop
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : ℝ³ => A (ε • x) + c)
    apply ContDiff.contMDiff
    fun_prop

private theorem image_sphere_eq_range_comp_cellBoundary (φ : ℝ³ → ℝ³)
    (b : ClosedCell 3 → ℝ³)
    (hext : ∀ x : ClosedCell 3, φ (x : ℝ³) = b x) :
    φ '' (S² : Set ℝ³) = Set.range (b ∘ cellBoundaryInclusion 3) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, by simpa [Metric.mem_sphere, dist_eq_norm] using hx⟩, ?_⟩
    rw [Function.comp_apply,
      hext ⟨x, by simpa [mem_closedBall_zero_iff] using sphere_subset_closedBall hx⟩]
    exact congrArg b (Subtype.ext rfl)
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℝ³), by simpa [Metric.mem_sphere, dist_eq_norm] using c.2, ?_⟩
    change φ (cellBoundaryInclusion 3 c : ℝ³) = y
    rw [hext (cellBoundaryInclusion 3 c)]
    exact hc

private theorem image_cellBoundaryInclusion_eq_sphere :
    (Subtype.val : ClosedCell 3 → ℝ³) '' Set.range (cellBoundaryInclusion 3) =
      (S² : Set ℝ³) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := hy
    simpa [Metric.mem_sphere, dist_eq_norm, cellBoundaryInclusion, Subtype.coe_mk] using c.2
  · intro hx
    let c : CellBoundary 3 :=
      ⟨x, by simpa [Metric.mem_sphere, dist_eq_norm] using hx⟩
    exact ⟨cellBoundaryInclusion 3 c, ⟨c, rfl⟩, rfl⟩

theorem exists_ambient_diffeomorph_image_sphere_of_smoothSchoenfliesCore
    (h : smoothSchoenfliesCore) (e : S² → ℝ³)
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e := by
  obtain ⟨b, φ, _hb, hbdy, hsrc, hext⟩ := h e he
  obtain ⟨A, ε, F, _hA, hε, _hε1, hformula, _K, _hK, _hKV, _hfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_straightening_embedded_closedBall
      φ (r := 1) zero_lt_one hsrc isOpen_univ (subset_univ _)
  let G : ℝ³ ≃ₘ[ℝ] ℝ³ := F.trans (affineChartDiffeomorph A (φ 0) ε (ne_of_gt hε))
  have hG : ∀ x ∈ closedBall (0 : ℝ³) 1, G (φ x) = x := by
    intro x hx
    change affineChartDiffeomorph A (φ 0) ε (ne_of_gt hε) (F (φ x)) = x
    rw [hformula x hx]
    change ε⁻¹ • A.symm ((ε • A x + φ 0) - φ 0) = x
    rw [add_sub_cancel_right, map_smul A.symm ε (A x), A.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hε), one_smul]
  have hφS : φ '' (S² : Set ℝ³) = Set.range e :=
    (image_sphere_eq_range_comp_cellBoundary (φ : ℝ³ → ℝ³) b hext).trans hbdy
  have hGimage : G '' Set.range e = (S² : Set ℝ³) := by
    rw [← hφS]
    ext y
    constructor
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      rw [hG u (sphere_subset_closedBall hu)]
      exact hu
    · intro hy
      exact ⟨φ y, ⟨y, hy, rfl⟩, hG y (sphere_subset_closedBall hy)⟩
  refine ⟨G.symm, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ G '' Set.range e := by
      rw [hGimage]
      exact hz
    obtain ⟨w, hw, hwz⟩ := hz'
    simpa [← hwz] using hw
  · rintro ⟨x, rfl⟩
    have hxmem : e x ∈ φ '' (S² : Set ℝ³) := by
      rw [hφS]
      exact ⟨x, rfl⟩
    obtain ⟨u, hu, hue⟩ := hxmem
    refine ⟨G (e x), ?_, ?_⟩
    · rw [← hue, hG u (sphere_subset_closedBall hu)]
      exact hu
    · exact G.symm_apply_apply (e x)

theorem smooth_schoenflies_three_of_smoothSchoenfliesCore
    (h : smoothSchoenfliesCore) (e : S² → ℝ³)
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e :=
  exists_ambient_diffeomorph_image_sphere_of_smoothSchoenfliesCore h e he

theorem smoothSchoenfliesThree_of_smoothSchoenfliesCore
    (h : smoothSchoenfliesCore) : SphereSeparation.smoothSchoenfliesThree :=
  SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
    (fun e he => exists_ambient_diffeomorph_image_sphere_of_smoothSchoenfliesCore h e he)

theorem smoothSchoenfliesCore_of_smoothSchoenfliesBallFilling
    (h : SphereSeparation.smoothSchoenfliesBallFilling) : smoothSchoenfliesCore := by
  intro e he
  obtain ⟨D, hD⟩ := SphereSeparation.exists_global_diffeomorph_of_smoothSchoenflies
    (SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mpr h) e he
  refine ⟨D ∘ Subtype.val, D.toPartialDiffeomorph,
    (Handle.closedCellInclusion_isSmoothEmbedding 2).diffeomorph_comp D, ?_, ?_, ?_⟩
  · rw [Set.range_comp, Set.image_comp, image_cellBoundaryInclusion_eq_sphere, hD]
  · exact subset_univ _
  · intro x
    rfl

theorem smoothSchoenfliesCore_iff_smoothSchoenfliesBallFilling :
    smoothSchoenfliesCore ↔ SphereSeparation.smoothSchoenfliesBallFilling :=
  ⟨fun h =>
      SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp
        (smoothSchoenfliesThree_of_smoothSchoenfliesCore h),
    smoothSchoenfliesCore_of_smoothSchoenfliesBallFilling⟩

theorem smoothSchoenfliesCore_witness_roundSphere :
    ∃ (b : ClosedCell 3 → ℝ³)
      (φ : PartialDiffeomorph (𝓡 3) (𝓡 3) ℝ³ ℝ³ ∞),
      IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b ∧
      Set.range (b ∘ cellBoundaryInclusion 3) =
        Set.range (Subtype.val : S² → ℝ³) ∧
      closedBall (0 : ℝ³) 1 ⊆ φ.source ∧
      ∀ x : ClosedCell 3, (φ : ℝ³ → ℝ³) (x : ℝ³) = b x := by
  refine ⟨Subtype.val, (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞).toPartialDiffeomorph,
    Handle.closedCellInclusion_isSmoothEmbedding 2, ?_, ?_, ?_⟩
  · rw [Set.range_comp, image_cellBoundaryInclusion_eq_sphere, Subtype.range_coe]
  · exact subset_univ _
  · intro x
    rfl

theorem exists_contMDiff_no_ambient_diffeomorph_image_sphere :
    ∃ e : S² → ℝ³,
      ContMDiff (𝓡 2) (𝓡 3) ∞ e ∧
        ¬ ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e := by
  refine ⟨fun _ => 0, contMDiff_const, ?_⟩
  rintro ⟨Φ, hΦ⟩
  rw [Set.range_const] at hΦ
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : ℝ³)) (r := (1 : ℝ))).mpr
    zero_le_one
  have hnu : (-u : ℝ³) ∈ S² := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu
  have hzu : Φ u = 0 := by
    have : Φ u ∈ ({0} : Set ℝ³) := by rw [← hΦ]; exact ⟨u, hu, rfl⟩
    simpa using this
  have hnzu : Φ (-u) = 0 := by
    have : Φ (-u) ∈ ({0} : Set ℝ³) := by rw [← hΦ]; exact ⟨-u, hnu, rfl⟩
    simpa using this
  have huu : u = -u := Φ.injective (hzu.trans hnzu.symm)
  have hnorm : ‖u‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu
  have hsum : u + u = 0 :=
    (congrArg (fun v : ℝ³ => u + v) huu).trans (add_neg_cancel u)
  have htwo : (2 : ℝ) • u = 0 := by rw [two_smul]; exact hsum
  have hzero : ‖(2 : ℝ) • u‖ = 0 := by rw [htwo, norm_zero]
  rw [norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_one] at hzero
  norm_num at hzero

end DifferentialGeometry.Topology.ThreeManifold
