import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseEFE

/-!
# Consumer of the abstract edge base (G2a): the final closed family

Lane S-EDP-FDC2, group G2. On the final closed family `LocalChartPacketsC14Z`, for a chain `Ĉ` on
the `C14D` projection and the adapter `A := bases_BAS.toSmoothStageBases74` of its own BASES object,
the edge projection `p ↦ π₂E p` from the open source `U₂ ∩ (π₂E)⁻¹(edgeRatio)` to `B₂ ⊆ W₂` is
smooth for the abstract structure (`edgeProj_contMDiff_EFE`), `∂M₁` lies in the zero faces
(`frontier_cutM1_subset_faces_EFE`), and `edgeProj_disk_EFE` gives `fibre_disk` over every point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainE

/-- **The abstract edge base on the final closed family**: smoothness of the projection, the
zero-face containment of `∂M₁` and the whole disks over `B₂`. -/
theorem edgeBase_C14Z_EFE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    let A : SmoothStageBasesOn74 C.toChain := C.bases_BAS.toSmoothStageBases74
    type_of% (C.edgeProj_contMDiff_EFE A) ∧ type_of% (C.frontier_cutM1_subset_faces_EFE hεr) ∧
      type_of% (C.edgeProj_disk_EFE) := by
  intro A
  exact ⟨C.edgeProj_contMDiff_EFE A, C.frontier_cutM1_subset_faces_EFE hεr, C.edgeProj_disk_EFE⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
