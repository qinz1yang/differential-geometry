import DifferentialGeometry.Topology.Manifold.BallDiffeomorphExtension
import DifferentialGeometry.Topology.Handle.DiffeomorphExtension
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesCore
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesRoundSphere
import DifferentialGeometry.Topology.ThreeManifold.schoenflies

open scoped ContDiff Manifold
open Set Metric Manifold

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

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

private theorem range_comp_cellBoundaryInclusion_eq_range_sphereTwo :
    Set.range ((Subtype.val : ClosedCell 3 → ℝ³) ∘ cellBoundaryInclusion 3) =
      Set.range (Subtype.val : S² → ℝ³) := by
  rw [Set.range_comp, image_cellBoundaryInclusion_eq_sphere, Subtype.range_coe]

noncomputable def smoothEmbeddedSphereBoundsSmoothBall : Prop :=
  ∀ (e : S² → ℝ³), IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
    ∃ b : ClosedCell 3 → ℝ³,
      IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b ∧
      Set.range (b ∘ cellBoundaryInclusion 3) = Set.range e

noncomputable def smoothBallFillingExtendsLocally : Prop :=
  ∀ (e : S² → ℝ³) (b : ClosedCell 3 → ℝ³),
    IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b →
    Set.range (b ∘ cellBoundaryInclusion 3) = Set.range e →
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) ℝ³ ℝ³ ∞,
      closedBall (0 : ℝ³) 1 ⊆ φ.source ∧
      ∀ x : ClosedCell 3, (φ : ℝ³ → ℝ³) (x : ℝ³) = b x

noncomputable def smoothBallFillingIsAmbientDiffeomorphic : Prop :=
  ∀ (e : S² → ℝ³) (b : ClosedCell 3 → ℝ³),
    IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b →
    Set.range (b ∘ cellBoundaryInclusion 3) = Set.range e →
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, ∀ x : ClosedCell 3, Φ (x : ℝ³) = b x

theorem smoothBallFillingExtendsLocally_of_isAmbientDiffeomorphic
    (h : smoothBallFillingIsAmbientDiffeomorphic) : smoothBallFillingExtendsLocally := by
  intro e b hb hbdy
  obtain ⟨Φ, hΦ⟩ := h e b hb hbdy
  exact ⟨Φ.toPartialDiffeomorph, subset_univ _, fun x => hΦ x⟩

theorem smoothSchoenfliesCore_of_boundsSmoothBall_and_extendsLocally
    (h₁ : smoothEmbeddedSphereBoundsSmoothBall) (h₂ : smoothBallFillingExtendsLocally) :
    smoothSchoenfliesCore := by
  intro e he
  obtain ⟨b, hb, hbdy⟩ := h₁ e he
  obtain ⟨φ, hsrc, hφ⟩ := h₂ e b hb hbdy
  exact ⟨b, φ, hb, hbdy, hsrc, hφ⟩

theorem smooth_schoenflies_three_of_boundsSmoothBall_and_extendsLocally
    (h₁ : smoothEmbeddedSphereBoundsSmoothBall) (h₂ : smoothBallFillingExtendsLocally)
    (e : S² → ℝ³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e :=
  smooth_schoenflies_three_of_smoothSchoenfliesCore
    (smoothSchoenfliesCore_of_boundsSmoothBall_and_extendsLocally h₁ h₂) e he

theorem image_sphere_eq_range_of_eqOn_closedCell
    (e : S² → ℝ³) (b : ClosedCell 3 → ℝ³)
    (hbdy : Set.range (b ∘ cellBoundaryInclusion 3) = Set.range e) (Φ : ℝ³ ≃ₘ[ℝ] ℝ³)
    (hΦ : ∀ x : ClosedCell 3, Φ (x : ℝ³) = b x) :
    Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e := by
  calc Φ '' Metric.sphere (0 : ℝ³) 1
      = Φ '' Set.range (Subtype.val : S² → ℝ³) := by rw [Subtype.range_coe]
    _ = Φ '' Set.range ((Subtype.val : ClosedCell 3 → ℝ³) ∘ cellBoundaryInclusion 3) := by
        rw [range_comp_cellBoundaryInclusion_eq_range_sphereTwo]
    _ = Set.range (Φ ∘ ((Subtype.val : ClosedCell 3 → ℝ³) ∘ cellBoundaryInclusion 3)) :=
        (Set.range_comp _ _).symm
    _ = Set.range
        ((Φ ∘ (Subtype.val : ClosedCell 3 → ℝ³)) ∘ cellBoundaryInclusion 3) := by
        rw [Function.comp_assoc]
    _ = Set.range (b ∘ cellBoundaryInclusion 3) := by
        rw [show (Φ ∘ (Subtype.val : ClosedCell 3 → ℝ³)) = b from funext hΦ]
    _ = Set.range e := hbdy

theorem smooth_schoenflies_three_of_boundsSmoothBall_and_isAmbientDiffeomorphic
    (h₁ : smoothEmbeddedSphereBoundsSmoothBall) (h₂ : smoothBallFillingIsAmbientDiffeomorphic)
    (e : S² → ℝ³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e := by
  obtain ⟨b, hb, hbdy⟩ := h₁ e he
  obtain ⟨Φ, hΦ⟩ := h₂ e b hb hbdy
  exact ⟨Φ, image_sphere_eq_range_of_eqOn_closedCell e b hbdy Φ hΦ⟩

theorem smooth_schoenflies_three_of_boundsSmoothBall
    (h : smoothEmbeddedSphereBoundsSmoothBall)
    (e : S² → ℝ³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e := by
  obtain ⟨b, hb, hbdy⟩ := h e he
  obtain ⟨Φ, hΦ⟩ := Handle.exists_diffeomorph_extension_closedCell 2 hb
  exact ⟨Φ, image_sphere_eq_range_of_eqOn_closedCell e b hbdy Φ hΦ⟩

theorem smoothEmbeddedSphereBoundsSmoothBall_of_exists_ambient_diffeomorph
    (h : ∀ (e : S² → ℝ³), IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
      ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e) :
    smoothEmbeddedSphereBoundsSmoothBall := by
  intro e he
  obtain ⟨Φ, hΦ⟩ := h e he
  refine ⟨Φ ∘ (Subtype.val : ClosedCell 3 → ℝ³), ?_, ?_⟩
  · exact (Handle.closedCellInclusion_isSmoothEmbedding 2).postcomp_diffeomorph Φ
  · calc Set.range ((Φ ∘ (Subtype.val : ClosedCell 3 → ℝ³)) ∘ cellBoundaryInclusion 3)
        = Φ '' Set.range ((Subtype.val : ClosedCell 3 → ℝ³) ∘ cellBoundaryInclusion 3) := by
          rw [Function.comp_assoc, Set.range_comp]
      _ = Φ '' Set.range (Subtype.val : S² → ℝ³) := by
          rw [range_comp_cellBoundaryInclusion_eq_range_sphereTwo]
      _ = Φ '' Metric.sphere (0 : ℝ³) 1 := by rw [Subtype.range_coe]
      _ = Set.range e := hΦ

theorem exists_smooth_ball_filling_and_local_straightening_of_round_sphere
    (c : ℝ³) {r : ℝ} (hr : 0 < r) :
    ∃ b : ClosedCell 3 → ℝ³,
      IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b ∧
      Set.range (b ∘ cellBoundaryInclusion 3) = Metric.sphere c r ∧
      ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) ℝ³ ℝ³ ∞,
        closedBall (0 : ℝ³) 1 ⊆ φ.source ∧
        ∀ x : ClosedCell 3, (φ : ℝ³ → ℝ³) (x : ℝ³) = b x := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_image_sphere c hr
  refine ⟨Φ ∘ (Subtype.val : ClosedCell 3 → ℝ³),
    (Handle.closedCellInclusion_isSmoothEmbedding 2).postcomp_diffeomorph Φ, ?_,
    Φ.toPartialDiffeomorph, subset_univ _, fun x => rfl⟩
  calc Set.range ((Φ ∘ (Subtype.val : ClosedCell 3 → ℝ³)) ∘ cellBoundaryInclusion 3)
      = Φ '' Set.range ((Subtype.val : ClosedCell 3 → ℝ³) ∘ cellBoundaryInclusion 3) := by
        rw [Function.comp_assoc, Set.range_comp]
    _ = Φ '' Set.range (Subtype.val : S² → ℝ³) := by
        rw [range_comp_cellBoundaryInclusion_eq_range_sphereTwo]
    _ = Φ '' Metric.sphere (0 : ℝ³) 1 := by rw [Subtype.range_coe]
    _ = Metric.sphere c r := hΦ

theorem not_exists_partialDiffeomorph_eqOn_zero_closedCell :
    ¬ ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) ℝ³ ℝ³ ∞,
      closedBall (0 : ℝ³) 1 ⊆ φ.source ∧
      ∀ x : ClosedCell 3, (φ : ℝ³ → ℝ³) (x : ℝ³) = (0 : ℝ³) := by
  rintro ⟨φ, hsub, hzero⟩
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : ℝ³)) (r := (1 : ℝ))).mpr
    zero_le_one
  have hnorm : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hu
  let x₀ : ClosedCell 3 := ⟨0, by simp⟩
  let x₁ : ClosedCell 3 := ⟨u, le_of_eq hnorm⟩
  have hx₀ : (0 : ℝ³) ∈ φ.source := by
    refine hsub (mem_closedBall_zero_iff.mpr ?_)
    simp
  have hx₁ : (x₁ : ℝ³) ∈ φ.source :=
    hsub (mem_closedBall_zero_iff.mpr (by change ‖u‖ ≤ 1; rw [hnorm]))
  have hzero₁ : (x₁ : ℝ³) = (0 : ℝ³) := by
    have h₁ := (φ.toPartialEquiv).left_inv hx₁
    have h₀ := (φ.toPartialEquiv).left_inv hx₀
    have h : (φ.toPartialEquiv).symm ((φ : ℝ³ → ℝ³) (x₁ : ℝ³)) =
        (φ.toPartialEquiv).symm ((φ : ℝ³ → ℝ³) (x₀ : ℝ³)) := by
      rw [hzero x₁, hzero x₀]
    exact h₁.symm.trans (h.trans h₀)
  have hnorm₁ : ‖(x₁ : ℝ³)‖ = 1 := by
    change ‖u‖ = 1
    exact hnorm
  rw [hzero₁, norm_zero] at hnorm₁
  norm_num at hnorm₁

end DifferentialGeometry.Topology.ThreeManifold
