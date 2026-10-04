import DifferentialGeometry.Topology.Ehresmann.FaceTransportProducer
import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  [I.Boundaryless] [T2Space Y] [SigmaCompactSpace Y]

/-- The SAME original closed disk and its boundary become the WHOLE final face fibre. -/
theorem exists_sameDisk_faceTransport
    (h : Y × ℝ → F) (T : Y × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a : F) (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c + ε →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → |T (y, τ) - c| < ε →
      Surjective (mfderiv I 𝓘(ℝ, F × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c + ε → y ∈ Q) :
    let := closedCellChartedSpaceSucc 1
    let := closedCellIsManifold 1
    ∀ κ : ClosedCell 2 → Y, IsSmoothEmbedding (𝓡∂ 2) I ∞ κ →
      range κ = {y | h (y, 0) = a ∧ T (y, 0) ≤ c} →
      κ '' (𝓡∂ 2).boundary (ClosedCell 2) = {y | h (y, 0) = a ∧ T (y, 0) = c} →
      ∃ Ψ : Y ≃ₘ⟮I, I⟯ Y, ∃ κ' : ClosedCell 2 → Y,
        (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧ κ' = Ψ ∘ κ ∧
        IsSmoothEmbedding (𝓡∂ 2) I ∞ κ' ∧
        range κ' = {y | h (y, 1) = a ∧ T (y, 1) ≤ c} ∧
        κ' '' (𝓡∂ 2).boundary (ClosedCell 2) = {y | h (y, 1) = a ∧ T (y, 1) = c} := by
  let := closedCellChartedSpaceSucc 1
  let := closedCellIsManifold 1
  dsimp only
  intro κ hκ hwhole hboundary
  obtain ⟨Ψ, hsupport, htrace, hfaceImage⟩ :=
    exists_diffeomorph_face_of_compact_transport h T hh hT a c hε hreg hface hQ hloc
  let κ' : ClosedCell 2 → Y := Ψ ∘ κ
  have hκ' : IsSmoothEmbedding (𝓡∂ 2) I ∞ κ' :=
    ⟨hκ.isImmersion.comp_diffeomorph Ψ, Ψ.toHomeomorph.isEmbedding.comp hκ.isEmbedding⟩
  refine ⟨Ψ, κ', hsupport, rfl, hκ', ?_, ?_⟩
  · rw [show range κ' = Ψ '' range κ from range_comp Ψ κ, hwhole]
    exact htrace
  · rw [show κ' '' (𝓡∂ 2).boundary (ClosedCell 2) =
      Ψ '' (κ '' (𝓡∂ 2).boundary (ClosedCell 2)) from image_comp Ψ κ _, hboundary]
    exact hfaceImage

end DifferentialGeometry.Geometry.Collapse
