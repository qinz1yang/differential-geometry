import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf05
import DifferentialGeometry.Geometry.Fibration.ActualStageChainE

/-!
# GAF04 and GAF05's plateau clause on the enhanced chain `Gaf02ChainE`

Blueprint `master207B.tex`, GAF04 (B:5896–5970), GAF05 (B:5971–6006); review 66, D66-8 (GAF04 as a
consumer of `C` + the same-plane FM certificate, FM\* source = ChainE). `Gaf02ChainE` (lane
C14-GAF8b) carries exactly the certificate data of `ActualStageChainGaf04.lean` /
`ActualStageChainGaf05.lean`: the enhanced planes `planes_j`, the base point `x₀`, the binding
equations `sel_eq`, `plane_eq`, and in `rough` GAF01's `Σ_j < ε_j/10000` (`sigma_le`). The theorems
below therefore take ONLY `C : Gaf02ChainE …` (no further hypothesis) and are the chain theorems of
`C.toChain` instantiated with these fields.

* `Gaf02ChainE.gaf04_first_G47`, `gaf04_edge_G47`, `gaf04_slim_G47`: (FM) and GAF03's consequence.
* `Gaf02ChainE.gaf05_first_plateau_G47`, `gaf05_edge_plateau_G47`, `gaf05_slim_plateau_G47`: the
  final image has marker `R_i` on the original threshold-`6` plateaux.
* Consumer `Gaf02ChainE.gaf05_plateau_markers_G47`: the three plateau clauses at one point.
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

/-- **GAF04 on `Gaf02ChainE`, circle (first) stage** (B:5896): (FM) for every window contributor of
the
chain's own radius — `v_i(y) = R_i`, `C.toChain.plane 0 y ≤ ker v_i` — and GAF03's consequence
`v_i(a z) = R_i` on `B(x, r_x)`; the FM certificate is `C.planes₀` (FM\* = its `full_marker`),
bound by `C.sel_eq`, `C.plane_eq`, and `Σ ≤ Ξ/10000` is `C.rough.sigma_le`. -/
theorem gaf04_first_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1))
    (hηp : ‖cgpCircleCoord P.toLocalChartFamily i.1 ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7) :
    (∀ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      (closedBall y (80 * (Ξ 0)⁻¹ * (S 0 * ρ (C.toChain.sel 0 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p)
          (8 * (Ξ 0)⁻¹ * (S 0 * ρ (C.toChain.sel 0 (cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 0) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) y = ρ i.1 ∧
        C.toChain.plane 0 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag
            P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        p)
        (S 0 * ρ (C.toChain.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
            P.toLocalChartFamily P.zero 0) p))),
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) ((C.toChain.slot 0).map z) = ρ i.1 :=
  C.toChain.gaf04_first_G47 C.planes₀ C.x₀ C.sel_eq.1 C.plane_eq.1 (C.rough.sigma_le 0).le i
    hpi hηp

/-- **GAF04 on `Gaf02ChainE`, edge stage** (B:5896): (FM) for every window contributor of the
chain's own radius — `v_i(y) = R_i`, `C.toChain.plane 1 y ≤ ker v_i` — and GAF03's consequence
`v_i(a z) = R_i` on `B(x, r_x)`; the FM certificate is `C.planes₁` (FM\* = its `full_marker`),
bound by `C.sel_eq`, `C.plane_eq`, and `Σ ≤ Ξ/10000` is `C.rough.sigma_le`. -/
theorem gaf04_edge_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hηp : |P.edge.coord i.1 p| ≤ 7 * Δ)
    (htp : cgpHeight P.toLocalChartFamily p ≤ 7 * Δ) :
    (∀ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      (closedBall y (80 * (Ξ 1)⁻¹ * (S 1 * ρ (C.toChain.sel 1 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p)
          (8 * (Ξ 1)⁻¹ * (S 1 * ρ (C.toChain.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 1) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) y = ρ i.1 ∧
        C.toChain.plane 1 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag
            P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        p)
        (S 1 * ρ (C.toChain.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
            P.toLocalChartFamily P.zero 1) p))),
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) ((C.toChain.slot 1).map z) = ρ
              i.1 :=
  C.toChain.gaf04_edge_G47 C.planes₁ C.x₀ C.sel_eq.2.1 C.plane_eq.2.1 (C.rough.sigma_le 1).le i
    hpi hηp htp

/-- **GAF04 on `Gaf02ChainE`, slim stage** (B:5896): (FM) for every window contributor of the
chain's own radius — `v_i(y) = R_i`, `C.toChain.plane 2 y ≤ ker v_i` — and GAF03's consequence
`v_i(a z) = R_i` on `B(x, r_x)`; the FM certificate is `C.planes₂` (FM\* = its `full_marker`),
bound by `C.sel_eq`, `C.plane_eq`, and `Σ ≤ Ξ/10000` is `C.rough.sigma_le`. -/
theorem gaf04_slim_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hηp : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ)) :
    (∀ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      (closedBall y (80 * (Ξ 2)⁻¹ * (S 2 * ρ (C.toChain.sel 2 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p)
          (8 * (Ξ 2)⁻¹ * (S 2 * ρ (C.toChain.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 2) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) y = ρ i.1 ∧
        C.toChain.plane 2 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag
            P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        p)
        (S 2 * ρ (C.toChain.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
            P.toLocalChartFamily P.zero 2) p))),
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) ((C.toChain.slot 2).map z) = ρ
              i.1 :=
  C.toChain.gaf04_slim_G47 C.planes₂ C.x₀ C.sel_eq.2.2 C.plane_eq.2.2 (C.rough.sigma_le 2).le i
    hpi hηp

/-- **GAF05's source-plateau clause on `Gaf02ChainE`, circle plateau** (B:5998–6005): the final
image `C.E p` has marker EXACTLY `R_i` (certificate `C.planes₀`, `C.sel_eq`, `C.plane_eq`,
`C.rough.sigma_le`). -/
theorem gaf05_first_plateau_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) (C.E p) = ρ i.1 :=
  (C.toChain.gaf05_first_plateau_G47 C.planes₀ C.x₀ C.sel_eq.1 C.plane_eq.1
    (C.rough.sigma_le 0).le i hpi hη).2.2.2

/-- **GAF05's source-plateau clause on `Gaf02ChainE`, edge plateau** (B:5998–6005): the final
image `C.E p` has marker EXACTLY `R_i` (certificate `C.planes₁`, `C.sel_eq`, `C.plane_eq`,
`C.rough.sigma_le`). -/
theorem gaf05_edge_plateau_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hη : |P.edge.coord i.1 p| < 6 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) (C.E p) = ρ i.1 :=
  (C.toChain.gaf05_edge_plateau_G47 C.planes₁ C.x₀ C.sel_eq.2.1 C.plane_eq.2.1
    (C.rough.sigma_le 1).le i hpi hη ht).2.2.2

/-- **GAF05's source-plateau clause on `Gaf02ChainE`, slim plateau** (B:5998–6005): the final
image `C.E p` has marker EXACTLY `R_i` (certificate `C.planes₂`, `C.sel_eq`, `C.plane_eq`,
`C.rough.sigma_le`). -/
theorem gaf05_slim_plateau_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 6 * (10 ^ 5 * Δ)) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) (C.E p) = ρ i.1 :=
  (C.toChain.gaf05_slim_plateau_G47 C.planes₂ C.x₀ C.sel_eq.2.2 C.plane_eq.2.2
    (C.rough.sigma_le 2).le i hpi hη).2.2

/-- **Consumer: GAF05's plateau clauses at one point** for a chain on the enhanced planes: on
every original threshold-`6` plateau through `p` (circle, edge with `t < 6Δ`, slim) the final image
`C.E p` has marker exactly `R_i`. -/
theorem gaf05_plateau_markers_G47 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (p : X) :
    (∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) →
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6 →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) (C.E p) = ρ
          i.1) ∧
    (∀ i : P.toLocalChartFamily.edge.finite_centres.toFinset, p ∈ ball i.1 (100 * Δ * ρ i.1) →
      |P.edge.coord i.1 p| < 6 * Δ → cgpHeight P.toLocalChartFamily p < 6 * Δ →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl i)))
          (C.E p) = ρ i.1) ∧
    ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 6 * (10 ^ 5 * Δ) →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) (C.E
          p) = ρ i.1 :=
  ⟨fun i hpi hη => C.gaf05_first_plateau_G47 i hpi hη,
    fun i hpi hη ht => C.gaf05_edge_plateau_G47 i hpi hη ht,
    fun i hpi hη => C.gaf05_slim_plateau_G47 i hpi hη⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
