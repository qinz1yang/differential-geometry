import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneFullMarker

/-!
# GAF03's contributor input from (FM\*) on the enhanced stage planes

Blueprint `master207B.tex`, GAF03 (`large_cloud_affine_marker_locality`, B:5871) fed by GAF04's
(FM) (B:5896–5970); draft 59 §1.4. For a marked chart `i` of the stage with a threshold-`7` core
    point
`p`, `x = π_st𝓔⁰(p)` and the marker line `K = (ker v_i)ᗮ`, `c = K.starProjection x`: every
contributor `y ∈ S_st` of the window `B̄(y, 80ε⁻¹r(y)) ∩ B(x, 8ε⁻¹r(x)) ≠ ∅` satisfies
`K.starProjection y = c` and `A.plane y ≤ Kᗮ` — the hypothesis of GAF03 (and of
`Cfs15StageOutput.locality_of_cloud_C15`) for the radius `r = Σρ ∘ A.rsel x₀`.

* `FirstStagePlanes_PLN.gaf03_input`, `EdgeStagePlanes_PLN.gaf03_input`,
  `SlimStagePlanes_PLN.gaf03_input`.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_PLNg {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNg {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNg {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **GAF03's input at the first stage** (marker line of a circle chart `i`,
`c = K.starProjection x`). -/
theorem FirstStagePlanes_PLN.gaf03_input
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hηp : ‖cgpCircleCoord P.toLocalChartFamily i.1
        ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p =
      x) :
    ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
        ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty →
      (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace
                    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection y =
        (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace
                    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection x ∧
      A.plane y ≤ (LinearMap.ker ((blockMarkerCLM (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨hvy, hpl⟩ := A.full_marker hΔ hΛ hLΛ heg0 heg hε hσ hσε x₀ i hpi hηp hpx hy hmeet
  have hcutp : P.circle.cutoff i.1 p = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyE.toLocalChartFamilyQ P.zero i hpi
      (le_trans hηp (by norm_num))
  have hvx : cgpMarker P.toLocalChartFamily P.zero (.inl i) x = ρ i.1 := by
    rw [← hpx, cgpMarker_projMap P.toLocalChartFamily P.zero
      (t := gafStageTags P.toLocalChartFamily P.zero 0) (Finset.mem_univ _)]
    change ρ i.1 * P.circle.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  exact markerLine_input_PLN _ _ (hvy.trans hvx.symm) hpl

/-- **GAF03's input at the edge stage** (marker line of an edge chart `i`). -/
theorem EdgeStagePlanes_PLN.gaf03_input
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hηp : |P.edge.coord i.1 p| ≤ 7 * Δ)
    (htp : cgpHeight P.toLocalChartFamily p ≤ 7 * Δ) {x :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p =
      x) :
    ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
        ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty →
      (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace
                    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection y =
        (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace
                    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection x ∧
      A.plane y ≤ (LinearMap.ker ((blockMarkerCLM (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨hvy, hpl⟩ := A.full_marker hΔ hΛ hLΛ heg0 heg hε hσ hσε x₀ i hpi hηp htp hpx hy hmeet
  have hΔ0 : 0 < Δ := by linarith
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcutp : P.edge.cutoff i.1 p = 1 :=
    P.edge.cutoff_eq_one_of_le hΔ0 hi hpi (by linarith) (by unfold cgpHeight at htp; linarith)
  have hvx : cgpMarker P.toLocalChartFamily P.zero (.inr (.inr i)) x = ρ i.1 := by
    rw [← hpx, cgpMarker_projMap P.toLocalChartFamily P.zero
      (t := gafStageTags P.toLocalChartFamily P.zero 1)
      (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i)]
    change ρ i.1 * P.edge.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  exact markerLine_input_PLN _ _ (hvy.trans hvx.symm) hpl

/-- **GAF03's input at the slim stage** (marker line of a slim chart `i`). -/
theorem SlimStagePlanes_PLN.gaf03_input
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hηp : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ))
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p =
      x) :
    ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
        ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty →
      (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace
                    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection y =
        (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace
                    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection x ∧
      A.plane y ≤ (LinearMap.ker ((blockMarkerCLM (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨hvy, hpl⟩ := A.full_marker hΔ hΛ hLΛ heg0 heg hε hσ hσε x₀ i hpi hηp hpx hy hmeet
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcutp : P.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hi]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hpi (by linarith)
  have hvx : cgpMarker P.toLocalChartFamily P.zero (.inr (.inl i)) x = ρ i.1 := by
    rw [← hpx, cgpMarker_projMap P.toLocalChartFamily P.zero
      (t := gafStageTags P.toLocalChartFamily P.zero 2)
      (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i)]
    change ρ i.1 * P.slim.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  exact markerLine_input_PLN _ _ (hvy.trans hvx.symm) hpl

end C14

end DifferentialGeometry.Geometry.Collapse
