import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleBaseEFE

/-!
# Consumer of FDC03's circle bundle (G6): the final closed family

Lane S-EDP-FDC2, group G6. `gaf07_circle_bundle_C14Z_EFE`: on the final closed family
`LocalChartPacketsC14Z`, for every enhanced chain with (JA), the clauses of the rows' `CircleBundle`
over the abstract base `W₁ ∩ R₁` (the manifold structure of the adapter
`Gaf02Bases.toSmoothStageBases74` applied to the chain's own BASES object `bases_BAS`): smooth,
submersion, proper, onto, and the local trivializations with the circle as fibre.
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

namespace Gaf02ChainEJA

/-- **FDC03's circle bundle on the final closed family** (the clauses of `CircleBundle` over
`W₁ ∩ R₁`, the abstract smooth base of the chain's own bases object). -/
theorem gaf07_circle_bundle_C14Z_EFE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    let A : SmoothStageBasesOn74 C.toChain := C.toGaf02ChainE.bases_BAS.toSmoothStageBases74
    type_of% (C.circleProj_contMDiff_EFE A) ∧
      type_of% (C.circleProj_mfderiv_surjective_EFE A hβ hd) ∧
      IsProperMap C.circleProj_EFE ∧ Surjective C.circleProj_EFE ∧
      type_of% (C.circleProj_trivial_EFE A hβ hd) := by
  intro A
  exact ⟨C.circleProj_contMDiff_EFE A, C.circleProj_mfderiv_surjective_EFE A hβ hd,
    C.circleProj_isProper_EFE, C.circleProj_surjective_EFE, C.circleProj_trivial_EFE A hβ hd⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
