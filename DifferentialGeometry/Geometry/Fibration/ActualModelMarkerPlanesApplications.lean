import DifferentialGeometry.Geometry.Fibration.ActualModelMarkerPlanes
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: GAF04's plane half for the model planes of `LocalChartPacketsC14`

* `gaf04_model_planes_C14`: for the family of `LocalChartPacketsC14`, the model planes
  `im DΦ(a)` of SGP04 (`sgpFullGraph`), EGP06 (`egpModelGraph`) and TCP05 (`tcpModelGraph`) lie in
  the kernel of the stage's marker `v_t` under the open-plateau condition, and TCP05's model planes
  lie in the kernel of the scale block (`P y ≤ Kᗮ` in GAF03's hypothesis, with `K` the marker line).
  Consumes the four model lemmas of `ActualModelMarkerPlanes`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14MMP_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14MMP_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14MMP_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF04's plane half for the model planes of `LocalChartPacketsC14`**: under the open-plateau
condition of the listed block, `im DΦ(a) ≤ ker v_t` for the slim tags of SGP04's model, the edge
tags of EGP06's model and the circle tags of TCP05's model; and TCP05's model planes have zero
scale block. -/
theorem gaf04_model_planes_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) :
    (∀ (i j : P.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) (a : ℝ),
      (j ≠ i → j.1 ∈ sgpSlimList P.slim i.1 →
        |(ρ j.1 / ρ i.1)⁻¹ * (sgn j.1 * a + c j.1)| < 8 * (10 ^ 5 * Δ)) →
      ∀ v ∈ LinearMap.range
          (fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc) a :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        blockMarkerCLM (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) v = 0) ∧
    (∀ (i : X) (sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ)
        (j : P.edge.finite_centres.toFinset) (a : ℝ),
      (j.1 ≠ i → j.1 ∈ egpEdgeList P.toLocalChartFamily i →
        |(ρ j.1 / ρ i)⁻¹ * (sgn (.inr (.inr (.inl j))) * a + c (.inr (.inr (.inl j))))| <
          8 * Δ) →
      ∀ v ∈ LinearMap.range
          (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        blockMarkerCLM (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) v = 0) ∧
    ∀ (i : X) (S : Finset (CGPTag P.toLocalChartFamily P.zero))
      (Se : Finset P.edge.finite_centres.toFinset)
      (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
      (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
      (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
      (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (a : ℝ²),
      (∀ v ∈ LinearMap.range
          (fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ) a :
            ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        v (cgpScaleTag P.toLocalChartFamily P.zero) = 0) ∧
      ∀ j : P.circle.finite_centres.toFinset,
        ((.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S → j.1 ≠ i →
          ‖(ρ j.1 / ρ i)⁻¹ • (Ac (.inl j) a + cc (.inl j))‖ < 8) →
        ∀ v ∈ LinearMap.range
            (fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ) a :
              ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          blockMarkerCLM (.inl j : CGPTag P.toLocalChartFamily P.zero) v = 0 := by
  refine ⟨fun i j sgn c zsgn zc a hplat => ?_, fun i sgn c j a hplat => ?_,
    fun i S Se Ac cc A1 c1 Bτ cτ a => ⟨?_, fun j hplat => ?_⟩⟩
  · rintro _ ⟨h, rfl⟩
    exact sgpFullGraph_marker_fderiv_GAFS P.toLocalChartFamily P.zero hΔ i sgn c zsgn zc j a hplat h
  · rintro _ ⟨h, rfl⟩
    exact egpModelGraph_marker_fderiv_GAFS P.toLocalChartFamily P.zero hΔ i sgn c j a hplat h
  · rintro _ ⟨h, rfl⟩
    exact tcpModelGraph_scale_fderiv_GAFS P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ a h
  · rintro _ ⟨h, rfl⟩
    exact tcpModelGraph_marker_fderiv_GAFS P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ j a
      hplat h

end DifferentialGeometry.Geometry.Collapse
