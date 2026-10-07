/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveDepthFrame
import DifferentialGeometry.Geometry.Hyperbolic.UniversalCover
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₂" => Fin 2 → ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

variable {H : FiniteVolumeHyperbolicModel}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalized_cover_frame (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    let x₀ := positiveMap Tr i q (basePoint r₀ hr₀)
    letI -zeta : Inhabited H.Carrier := ⟨x₀⟩
    letI -zeta : LocallyPathConnectedSpace E₃ :=
      (𝓡 3).toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI -zeta : LocallyPathConnectedSpace H.Carrier :=
      ChartedSpace.locallyPathConnectedSpace E₃ H.Carrier
    letI -zeta : SemilocallySimplyConnectedSpace H.Carrier :=
      manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
    letI -zeta : SecondCountableTopology E₃ := ModelWithCorners.secondCountableTopology (𝓡 3)
    letI -zeta : SecondCountableTopology H.Carrier :=
      ChartedSpace.secondCountable_of_sigmaCompact E₃ H.Carrier
    let gN := scaleMetric (- (-(1 / 4 : ℝ)))
      (neg_pos.mpr (by norm_num : -(1 / 4 : ℝ) < 0)) H.metric
    let ĝ := UniversalCover.liftedMetric (I := 𝓡 3) gN
    letI -zeta : IsManifold (𝓡 3) 1 (UniversalCover H.Carrier) :=
      IsManifold.of_le (I := 𝓡 3) (M := UniversalCover H.Carrier) (n := ∞) (by decide)
    letI -zeta : TopologicalSpace.MetrizableSpace (UniversalCover H.Carrier) :=
      Manifold.metrizableSpace (𝓡 3) (UniversalCover H.Carrier)
    letI -zeta : T3Space (UniversalCover H.Carrier) := inferInstance
    letI -zeta : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : UniversalCover H.Carrier → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI -zeta : IsContinuousRiemannianBundle E₃
        (TangentSpace (𝓡 3) : UniversalCover H.Carrier → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    ∃ frame : E₃ ≃ₗᵢ[ℝ]
        TangentSpace (𝓡 3) (UniversalCover.basePoint (X := H.Carrier)),
      ∀ v, (show E₃ from frame v) =
        comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀) v := by
  let x₀ := positiveMap Tr i q (basePoint r₀ hr₀)
  let L₀ : E₃ ≃ₗ[ℝ] E₃ :=
    (comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀)).toLinearEquiv
  have hL₀ (v w : E₃) :
      (1 / 4) * H.metric.inner x₀ (L₀ v) (L₀ w) = inner ℝ v w :=
    comparisonFrame_base_metric Tr i hq hqmetric r₀ hr₀ v w
  let _ : Inhabited H.Carrier := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace E₃ :=
    (𝓡 3).toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace H.Carrier :=
    ChartedSpace.locallyPathConnectedSpace E₃ H.Carrier
  let _ : SemilocallySimplyConnectedSpace H.Carrier :=
    manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SecondCountableTopology E₃ := ModelWithCorners.secondCountableTopology (𝓡 3)
  let _ : SecondCountableTopology H.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact E₃ H.Carrier
  let gN := scaleMetric (- (-(1 / 4 : ℝ)))
    (neg_pos.mpr (by norm_num : -(1 / 4 : ℝ) < 0)) H.metric
  let ĝ := UniversalCover.liftedMetric (I := 𝓡 3) gN
  let _ : IsManifold (𝓡 3) 1 (UniversalCover H.Carrier) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover H.Carrier) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover H.Carrier) :=
    Manifold.metrizableSpace (𝓡 3) (UniversalCover H.Carrier)
  let _ : T3Space (UniversalCover H.Carrier) := inferInstance
  let _ : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : UniversalCover H.Carrier → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃
      (TangentSpace (𝓡 3) : UniversalCover H.Carrier → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  dsimp only
  let L : E₃ ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (UniversalCover.basePoint (X := H.Carrier)) := L₀
  have hL (v w : E₃) : inner ℝ (L v) (L w) = inner ℝ v w := by
    change ĝ.inner (UniversalCover.basePoint (X := H.Carrier)) (L v) (L w) = _
    change (- (-(1 / 4 : ℝ))) * H.metric.inner x₀ (L₀ v) (L₀ w) = _
    simpa only [neg_neg] using hL₀ v w
  refine ⟨L.isometryOfInner hL, ?_⟩
  intro v
  rfl

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
