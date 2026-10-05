import DifferentialGeometry.Geometry.Fibration.ActualStageTwoThreeStep

/-!
# GAF02's stage outputs in the input form of the next stage

Consumers of `gaf02_stageOne_step_GAF5`, `gaf02_stageTwo_step_GAF6`, `gaf02_stageThree_step_GAF6`:
each stage output `g_{k+1} = Ψ_k ∘ g_k` is differentiable at every point (as a manifold map) and
carries the prior value and derivative errors in exactly the form the next stage step takes
(`hf`, `hprior`, `hpriorD`) — the inductive step of GAF02's step 6.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF6a
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF6a
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF6a
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Stage one's output** `g₁ = Ψ₁ ∘ 𝓔⁰`: differentiable everywhere, with prior errors
`E₁ = (5/3)ΞΣ` and `H₁ = (5/3)ΞΣ·b·L + ΞL + e` for stage two. -/
theorem gaf02_stageOne_output_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {Ξ sg eg : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (heg : 0 ≤ eg)
    (hPst : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) :
    (∀ p, MDifferentiableAt 𝓘(ℝ, E3)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p) ∧
      (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 5 / 3 * Ξ * sg * ρ p) ∧
      ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        (5 / 3 * Ξ * sg * gafCutoffConstant * gafDerivativeBound + Ξ * gafDerivativeBound + eg) *
          Real.sqrt (g.inner p w w) := by
  have hstep := gaf02_stageOne_step_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr sel
    hsel plane Pst hΞ hsg heg hPst hPd hrank
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT ⟨hσs, by linarith⟩ hσc hγc
    hεr
  refine ⟨fun p => ?_, fun p => (hstep p).1, fun p w => (hstep p).2.2 w⟩
  exact (hstep p).2.1.mdifferentiableAt.comp p ((hder.1 p).mdifferentiableAt (by simp))

/-- **Stage two's output** `g₂ = Ψ₂ ∘ f`: differentiable everywhere, with prior errors
`E₂ = E + a` and `H₂ = a·b·(L + H₀) + Ξ(L + H₀) + e + 2H₀` for stage three. -/
theorem gaf02_stageTwo_output_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {Ξ sg eg E H₀ : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (heg : 0 ≤ eg) (hE0 : 0 ≤ E)
    (hE : E ≤ 3 * sg / 10) (hEκ : E ≤ 4 * gafKappa / 5) (hH₀ : 0 ≤ H₀)
    (hPst : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hf : ∀ p, MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) f p)
    (hprior : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hpriorD : ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) f p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        H₀ * Real.sqrt (g.inner p w w))
    (hZM : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    (∀ p, MDifferentiableAt 𝓘(ℝ, E3)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
          (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘ f) p) ∧
      (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
          (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘ f) p -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
        (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p) ∧
      ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
          (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘ f) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ * sg + (1 + Ξ) * E) * gafCutoffConstant * (gafDerivativeBound + H₀) +
          Ξ * (gafDerivativeBound + H₀) + eg + 2 * H₀) * Real.sqrt (g.inner p w w) := by
  have hstep := gaf02_stageTwo_step_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr sel
    hsel plane Pst hΞ hsg heg hE0 hE hEκ hH₀ hPst hPd hrank f hf hprior hpriorD hZM
  refine ⟨fun p => ?_, fun p => (hstep p).1, fun p w => (hstep p).2.2 w⟩
  exact (hstep p).2.1.mdifferentiableAt.comp p (hf p)

/-- **Stage three's output** `g₃ = Ψ₃ ∘ f`: differentiable everywhere, with the final errors
`E + a` and `a·b·(L + H₀) + Ξ(L + H₀) + e + 2H₀`. -/
theorem gaf02_stageThree_output_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {Ξ sg eg E H₀ : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (heg : 0 ≤ eg) (hE0 : 0 ≤ E)
    (hE : E ≤ 3 * sg / 10) (hEκ : E ≤ 4 * gafKappa / 5) (hH₀ : 0 ≤ H₀)
    (hPst : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x →
        ∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero))
                q) v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hf : ∀ p, MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) f p)
    (hprior : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hpriorD : ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) f p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        H₀ * Real.sqrt (g.inner p w w))
    (hZM : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    (∀ p, MDifferentiableAt 𝓘(ℝ, E3)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘ f) p) ∧
      (∀ p, ‖(adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘ f) p -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
        (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p) ∧
      ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘ f) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ * sg + (1 + Ξ) * E) * gafCutoffConstant * (gafDerivativeBound + H₀) +
          Ξ * (gafDerivativeBound + H₀) + eg + 2 * H₀) * Real.sqrt (g.inner p w w) := by
  have hstep := gaf02_stageThree_step_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel hsel plane Pst hΞ hsg heg hE0 hE hEκ hH₀ hPst hPd hrank f hf hprior hpriorD hZM
  refine ⟨fun p => ?_, fun p => (hstep p).1, fun p w => (hstep p).2.2 w⟩
  exact (hstep p).2.1.mdifferentiableAt.comp p (hf p)

end DifferentialGeometry.Geometry.Collapse
