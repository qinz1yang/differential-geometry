import DifferentialGeometry.Geometry.Fibration.ActualStageFirstPlanes
import DifferentialGeometry.Geometry.Fibration.ActualStageEdgePlanes
import DifferentialGeometry.Geometry.Fibration.ActualStageSlimPlanes

/-!
# Consumers of the enhanced stage planes: TCP05's package, CFS15 inputs, the present tests

Draft 59 §1 (D59-2), review 60 (consumption packages). On the witnesses of
`exists_firstStagePlanes_PLN` / `exists_edgeStagePlanes_PLN` / `exists_slimStagePlanes_PLN`:

* `FirstStagePlanes_PLN.tcp05_package`: review 60's TCP05 joint output on the SAME model table:
  at every circle reference `a`, `K_a ∘ Φ_a` is smooth, has the own block `(u, 1)`, the global `C²`
  bounds, (TG), the frozen scale (`v_scale ∘ D(K_aΦ_a) = 0`) and CFS27's pruning (the marker of
  every block with `ρ(c_b) ≤ ρ(a)/2` annihilates `D(K_aΦ_a)`).
* `FirstStagePlanes_PLN.cfs15_inputs`, `EdgeStagePlanes_PLN.cfs15_inputs`,
  `SlimStagePlanes_PLN.cfs15_inputs`: the three inputs of `gafStage_package_of_output_C15`
  (`hsel` for `sel = A.rsel x₀`, planes in `Q_st`, (PP)) for the plane slot `A.plane` and the
  radius slot `A.radius x₀ Σ ρ`.
* `fc27_edge_test_pp_of_planes_PLN`, `fc27_slim_test_pp_of_planes_PLN`: the present edge and slim
  tests recovered verbatim from the producers through the forgetful exits (witness `A.plane`). (The
  first-cloud analogue is `FirstStagePlanes_PLN.to_first_test_pps` applied to the witness of
  `exists_firstStagePlanes_PLN`; restating `fc27_first_test_pps_GAF5` verbatim here only costs a
  WithLp instance-path conversion, so it is not repeated.)
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
local instance instMetricNC14_PLNa {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNa {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNa {X : Type} [MetricSpace X] [ChartedSpace E3 X]
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

open Classical in
/-- **TCP05's joint package on the same model table** (review 60): at every circle reference `a`
of a stage-`0` witness, the pruned model `K_a ∘ Φ_a` is smooth, has the own block `(u, 1)`, the
global `C²` bounds and (TG), frozen scale and CFS27's pruning. -/
theorem FirstStagePlanes_PLN.tcp05_package
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg)
    (a : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ContDiff ℝ ∞ (A.prune a ∘ A.model a) ∧
    (∀ u, (A.prune a ∘ A.model a) u (.inl a) = WithLp.toLp 2 (u, 1)) ∧
    (∀ u, ‖fderiv ℝ (A.prune a ∘ A.model a) u‖ ≤ tcpGraphConst ∧
      ‖fderiv ℝ (fderiv ℝ (A.prune a ∘ A.model a)) u‖ ≤ tcpGraphConst) ∧
    tcpTG_PLN P eg (A.prune a ∘ A.model a) (A.coord a) a.1 ∧
    (∀ u v, blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero)
      (fderiv ℝ (A.prune a ∘ A.model a) u v) = 0) ∧
    ∀ c : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily c) ≤ ρ a.1 / 2 → ∀ u v,
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero c)
        (fderiv ℝ (A.prune a ∘ A.model a) u v) = 0 := by
  have hsm := contDiff_tcpModelGraph P.toLocalChartFamily P.zero a.1
    (tcpListedTags P.toLocalChartFamily P.zero a.1) (tcpListedEdges P.toLocalChartFamily a.1)
    (A.Ac a) (A.cc a) (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a)
  have hd := hsm.differentiable (by simp)
  have hD : ∀ u, fderiv ℝ (A.prune a ∘ A.model a) u = (A.prune a).comp (fderiv ℝ (A.model a) u) :=
    fun u => by
      rw [fderiv_comp u (A.prune a).differentiableAt (by rw [A.model_eq a]; exact hd u),
        (A.prune a).fderiv]
  refine ⟨(A.prune a).contDiff.comp (by rw [A.model_eq a]; exact hsm), fun u => ?_,
    A.model_bounds a, A.model_tg a, fun u v => ?_, fun c hc u v => ?_⟩
  · change A.prune a (A.model a u) (.inl a) = _
    rw [A.prune_eq a, A.model_eq a, blockRestrict_apply,
      ite_eq_left (firstKeep_own_GAF5 P.toLocalChartFamily P.zero a)]
    exact tcpModelGraph_own _ _ _ _ _ _ _ _ _ _ _ a rfl u
  · rw [hD, ContinuousLinearMap.comp_apply, A.prune_eq a, blockMarkerCLM_apply,
      blockRestrict_apply]
    split_ifs
    · rw [A.model_eq a, tcpModelGraph_scale_fderiv_GAFS]
      rfl
    · rfl
  · rw [hD, ContinuousLinearMap.comp_apply, A.prune_eq a]
    exact firstPrune_marker_GAF5 P.toLocalChartFamily P.zero c hc _

/-- **CFS15 inputs, stage `0`**: for any `x₀ : X`, the radius selection `A.rsel x₀` is a selection
of preimages over `S̃₁`, the planes lie in `Q₁`, and (PP) — the hypotheses `hsel`, `hplaneQ`, `hpp` of
`gafStage_package_of_output_C15` for the slots `A.plane`, `A.radius x₀ Σ ρ`. -/
theorem FirstStagePlanes_PLN.cfs15_inputs
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (x₀ : X) :
    (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (A.rsel x₀ x) = x) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      A.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        A.plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) :=
  ⟨A.toStagePlaneData_PLN.rsel_spec x₀ _ fun x => (A.rpre_spec x).2,
    fun x hx => (A.dimension x hx).2, A.small_pp⟩

/-- **CFS15 inputs, stage `1`** (as `FirstStagePlanes_PLN.cfs15_inputs`). -/
theorem EdgeStagePlanes_PLN.cfs15_inputs
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (x₀ : X) :
    (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (A.rsel x₀ x) = x) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      A.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        A.plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) :=
  ⟨A.toStagePlaneData_PLN.rsel_spec x₀ _ fun x => (A.rpre_spec x).2,
    fun x hx => (A.dimension x hx).2, A.small_pp⟩

/-- **CFS15 inputs, stage `2`** (as `FirstStagePlanes_PLN.cfs15_inputs`). -/
theorem SlimStagePlanes_PLN.cfs15_inputs
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (x₀ : X) :
    (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (A.rsel x₀ x) = x) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      A.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        A.plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) :=
  ⟨A.toStagePlaneData_PLN.rsel_spec x₀ _ fun x => (A.rpre_spec x).2,
    fun x hx => (A.dimension x hx).2, A.small_pp⟩

end C14

/-- **The present edge test from the producer** (`fc27_edge_test_pp_GAF4`'s statement verbatim;
witness `A.plane` of `exists_edgeStagePlanes_PLN` through `to_edge_test_pp`). -/
theorem fc27_edge_test_pp_of_planes_PLN {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (hS : 0 < Sg)
    (hSmin : Sg < min (Γ / 200) (Γ ^ 3 / (100 * egpGraphConst)))
    (heg : 0 < eg) (hemin : eg < min (1 / 100) (min (Γ * Sg / 100) (Sg / 1000))) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
            Module.finrank ℝ (plane x) = gafStageDim 1 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 1) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
                  ball x (Sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (Sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (Sg * ρ (sel x)))) ∧
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
            ∀ q : X,
            cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
                  (plane x).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(plane x).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
              (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
                1 / 2 ≤ ‖(plane x).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                      (cgpProjMap P.toLocalChartFamily P.zero
                        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
              (∀ k ∈ plane x, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
                  (plane x).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
            cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
              x →
            ∀ a : CGPMarkerIndex P.toLocalChartFamily,
              ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
              plane x ≤ LinearMap.ker ((blockMarkerCLM
                (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := exists_edgeStagePlanes_PLN hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  obtain ⟨A⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  exact A.to_edge_test_pp

/-- **The present slim test from the producer** (`fc27_slim_test_pp_C14_GAF4`'s statement verbatim;
witness `A.plane` of `exists_slimStagePlanes_PLN` through `to_slim_test_pp`). -/
theorem fc27_slim_test_pp_of_planes_PLN {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            Module.finrank ℝ (plane x) = gafStageDim 2 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
                  ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              x →
            let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
            cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
              x →
            ∀ a : CGPMarkerIndex P.toLocalChartFamily,
              ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
              plane x ≤ LinearMap.ker ((blockMarkerCLM
                (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, h⟩ :=
    exists_slimStagePlanes_PLN hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  obtain ⟨A⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  exact A.to_slim_test_pp

end DifferentialGeometry.Geometry.Collapse
