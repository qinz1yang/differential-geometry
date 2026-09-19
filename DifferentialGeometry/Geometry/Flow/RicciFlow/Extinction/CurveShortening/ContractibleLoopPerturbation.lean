import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import DifferentialGeometry.Topology.LoopSpace.ContractibleNearby

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ x y : M, ‖e x - e y‖ < δ → riemannianEDistOf g x y < ρ := by
  exact DifferentialGeometry.SmoothRiemannianMetric.exists_pos_forall_riemannianEDistOf_lt_of_norm_sub_lt
    g e he hρ

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_forall_isContractibleLoop_of_riemannianEDistOf_lt
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧
      ∀ {γ₀ γ₁ : ContinuousFreeLoop M}, IsContractibleLoop γ₀ →
      (∀ z, riemannianEDistOf g (γ₁ z) (γ₀ z) < ρ) → IsContractibleLoop γ₁ := by
  exact DifferentialGeometry.Topology.FreeLoop.exists_pos_forall_nullhomotopic_of_riemannianEDistOf_lt g

theorem exists_pos_forall_isContractibleLoop_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ {γ₀ γ₁ : ContinuousFreeLoop M}, IsContractibleLoop γ₀ →
      (∀ z, ‖e (γ₁ z) - e (γ₀ z)‖ < δ) → IsContractibleLoop γ₁ := by
  exact DifferentialGeometry.Topology.FreeLoop.exists_pos_forall_nullhomotopic_of_norm_sub_lt g e he

theorem exists_pos_forall_loopFamily_isContractibleLoop_of_norm_sub_lt
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ (γ Γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ),
      (∀ t ∈ J, IsContractibleLoop (γ t)) →
      (∀ t ∈ J, ∀ z, ‖e (Γ t z) - e (γ t z)‖ < δ) →
      ∀ t ∈ J, IsContractibleLoop (Γ t) := by
  obtain ⟨δ, hδ, h⟩ :=
    DifferentialGeometry.Topology.FreeLoop.exists_pos_forall_loopFamily_nullhomotopic_of_norm_sub_lt g e he
  exact ⟨δ, hδ, h⟩

omit [CompactSpace M] [T2Space M] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem exists_ne_isContractibleLoop_of_norm_sub_lt (e : M → F) {δ : ℝ} {x y : M}
    (hne : x ≠ y) (h : ‖e y - e x‖ < δ) :
    ∃ γ₁ : ContinuousFreeLoop M, γ₁ ≠ constantLoops x ∧
      (∀ z, ‖e (γ₁ z) - e (constantLoops x z)‖ < δ) ∧ IsContractibleLoop γ₁ := by
  refine ⟨constantLoops y, ?_, ?_, isContractibleLoop_constant y⟩
  · intro hxy
    exact hne (congrArg
      (fun γ : ContinuousFreeLoop M => γ (0 : Surgery.Topology.Circle)) hxy).symm
  · intro z
    change ‖e y - e x‖ < δ
    exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem loopFamily_norm_sub_lt_of_iteratedFDerivWithin_zero
    {M : Type*} [TopologicalSpace M] (e : M → F)
    (γ Γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ) (δ : ℝ)
    (h : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ 0
          (fun q : ℝ × ℝ => e (Γ q.2 (q.1 : Surgery.Topology.Circle))) (univ ×ˢ J) p -
        iteratedFDerivWithin ℝ 0
          (fun q : ℝ × ℝ => e (γ q.2 (q.1 : Surgery.Topology.Circle))) (univ ×ˢ J) p‖ < δ) :
    ∀ t ∈ J, ∀ z, ‖e (Γ t z) - e (γ t z)‖ < δ := by
  exact DifferentialGeometry.Topology.FreeLoop.loopFamily_norm_sub_lt_of_iteratedFDerivWithin_zero
    e γ Γ J δ h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

theorem exists_pos_forall_loopFamily_isContractibleLoop_of_iteratedFDerivWithin_zero
    (g : SmoothRiemannianMetric I M) (e : M → F) (he : Topology.IsEmbedding e) :
    ∃ δ > 0, ∀ (γ Γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ),
      (∀ t ∈ J, IsContractibleLoop (γ t)) →
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
        ‖iteratedFDerivWithin ℝ 0
            (fun q : ℝ × ℝ => e (Γ q.2 (q.1 : Surgery.Topology.Circle))) (univ ×ˢ J) p -
          iteratedFDerivWithin ℝ 0
            (fun q : ℝ × ℝ => e (γ q.2 (q.1 : Surgery.Topology.Circle))) (univ ×ˢ J) p‖ < δ) →
      ∀ t ∈ J, IsContractibleLoop (Γ t) := by
  exact DifferentialGeometry.Topology.FreeLoop.exists_pos_forall_loopFamily_nullhomotopic_of_iteratedFDerivWithin_zero
    g e he


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
