import DifferentialGeometry.Geometry.Fibration.ActualStagePlanesApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTest

/-!
# FC07 as a row: the two-stratum image packet (KL 12.7) on ONE plane field

Blueprint `master207B.tex`, FC07 (`found:fibration-two-cloud`, B:351–370). For the closed-carrier
LC87 data and FC04's `S₁ ⊆ S̃₁` (`S₁ = 𝓔⁰(A₁)`, `S̃₁ = 𝓔⁰(Ã₁)`, thresholds `7 ⊆ 8`):

* a `(2, Γ₁)` cloudy two-manifold in `H`: planes `A_x` of dimension `2` with FC27's (CS) test at
  quality `Γ₁` for every selection of preimages (radius `Σ₁ρ` of the selected preimage);
* at EVERY preimage `p` of `x ∈ S₁`, the projected derivative onto `A_x⁰` is onto, with lower
  singular-value bound `1/2` on `(ker)ᗮ`, upper bound `3Ω₁` and normal error `e₁ < Γ₁` (all in the
  units `ρ(i)⁻²g` of the reference `i`);
* for each circle centre `i ∈ I₂` a smooth `Ψ_i : ℝ² → H` (= `(η, R_i⁻¹ h_i(η))`: its own block is
  `(u, 1)`, so `R_i⁻¹h_i = Ψ_i − (own block)` takes values in the complement of the own vector
  coordinate `H_i'`) with `‖DΨ_i‖ ≤ Ω₁ = tcpGraphConst` and the C¹ comparison
  `‖R_i⁻¹𝓔⁰ − Ψ_i ∘ η_i‖ < e₁ < Γ₁`, `‖R_i⁻¹d𝓔⁰ − DΨ_i dη_i‖ ≤ e₁|·|_{R_i⁻²g}` on
  `B(i, 200R_i) ∩ {‖η_i‖ ≤ 8}`;
* at `x ∈ S₁` a choice of `i` and of a preimage `p` with `‖η_i(p)‖ ≤ 7` gives
  `A_x⁰ = im DΨ_i(η_i(p))` (= `im(I, R_i⁻¹(Dh_i)_{η_i(p)})`).

All four clauses are read off ONE enhanced stage-`0` plane witness
`A : FirstStagePlanes_PLN P Γ Σ e` (lane C14-PLANES, producer `exists_firstStagePlanes_PLN`,
TCP05's model table with CFS27's pruning `Ψ_i = K_i ∘ Φ_i`): `fc07_row_RFC` has the producer's
ordered thresholds verbatim.
Consumer: `FirstStagePlanes_PLN.fc07_plane_graph_RFC` (the plane at `x` is the graph plane of the
reference coordinate: for every `v ∈ ℝ²` it contains `DΨ_i(η_i p) v`, whose own block is
`(v, 0)`, i.e. `A_x⁰ = im(I, R_i⁻¹Dh_i)`), via `own_block_fderiv_RFC`.
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
local instance instMetricNC14_RFC7 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_RFC7 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_RFC7 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- `ContinuousSMul` on the plane block, as a named local instance (the 2026-10-05 pitfall fix:
instance search for it times out inside `fderiv` on `WithLp 2 (ℝ² × ℝ)`). -/
local instance instContinuousSMulPlaneBlock_RFC :
    ContinuousSMul ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  IsBoundedSMul.continuousSMul

/-- The derivative of a map with own block `u ↦ (u, 1)` at the tag `t` has own block
`v ↦ (v, 0)`. -/
theorem own_block_fderiv_RFC {κ : Type*} [Finite κ] (f : ℝ² → BlockSpace (fun _ : κ => ℝ²))
    (t : κ) (hown : ∀ u, f u t = WithLp.toLp 2 (u, (1 : ℝ))) (u₀ : ℝ²)
    (hd : DifferentiableAt ℝ f u₀) (v : ℝ²) :
    fderiv ℝ f u₀ v t = WithLp.toLp 2 (v, (0 : ℝ)) := by
  have := Fintype.ofFinite κ
  have hp : HasFDerivAt (fun y : ℝ² => ((y, (1 : ℝ)) : ℝ² × ℝ))
      ((ContinuousLinearMap.id ℝ ℝ²).prod 0) u₀ :=
    (hasFDerivAt_id u₀).prodMk (hasFDerivAt_const (1 : ℝ) u₀)
  have h2 := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm :
    (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)).hasFDerivAt.comp u₀ hp
  have h1 : HasFDerivAt (fun u => blockProjCLM_PLN (V := fun _ : κ => ℝ²) t (f u))
      ((blockProjCLM_PLN (V := fun _ : κ => ℝ²) t).comp (fderiv ℝ f u₀)) u₀ :=
    (blockProjCLM_PLN (V := fun _ : κ => ℝ²) t).hasFDerivAt.comp _ hd.hasFDerivAt
  have heq : (fun u => blockProjCLM_PLN (V := fun _ : κ => ℝ²) t (f u)) =
      (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm : (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)) ∘
        fun y : ℝ² => ((y, (1 : ℝ)) : ℝ² × ℝ)) := by
    funext u
    rw [blockProjCLM_apply_PLN, hown u]
    rfl
  rw [heq] at h1
  have h3 := congrArg (fun L : ℝ² →L[ℝ] WithLp 2 (ℝ² × ℝ) => L v) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, blockProjCLM_apply_PLN] at h3
  rw [h3]
  rfl

section Row

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

open Classical in
/-- **FC07 read off one stage-`0` plane witness**: FC04's clouds, the `h_i` graph clause for every
circle centre, the planes with (CS), the rank / normal clauses at every preimage, and the plane
choice `A_x⁰ = im DΨ_i(η_i(p))` at a core preimage `‖η_i(p)‖ ≤ 7`. -/
theorem FirstStagePlanes_PLN.fc07_RFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) :
    gafCloud P.toLocalChartFamily P.zero 0 =
        cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ∧
      gafCloudEnlarged P.toLocalChartFamily P.zero 0 =
        cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 8 ∧
      (∀ a : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ContDiff ℝ ∞ (A.prune a ∘ A.model a) ∧
        (∀ u, (A.prune a ∘ A.model a) u (.inl a) = WithLp.toLp 2 (u, 1)) ∧
        (∀ u, ‖fderiv ℝ (A.prune a ∘ A.model a) u‖ ≤ tcpGraphConst) ∧
        tcpTG_PLN P eg (A.prune a ∘ A.model a)
          (cgpCircleCoord P.toLocalChartFamily a.1 ((Set.Finite.mem_toFinset _).mp a.2)) a.1) ∧
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, Module.finrank ℝ (A.plane x) = 2) ∧
      (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
            (sel x) = x) →
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          hausdorffEDist
            (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩ ball x (sg * ρ (sel x) / Γ))
            ((AffineSubspace.mk' x (A.plane x) :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
      (∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0) q,
        cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        tcpNormalSpec_PLN P eg (A.plane x) (A.ref ⟨x, hx⟩).1 q) ∧
      ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0),
        A.pre ⟨x, hx⟩ ∈ ball (A.ref ⟨x, hx⟩).1 (200 * ρ (A.ref ⟨x, hx⟩).1) ∧
        ‖cgpCircleCoord P.toLocalChartFamily (A.ref ⟨x, hx⟩).1
            ((Set.Finite.mem_toFinset _).mp (A.ref ⟨x, hx⟩).2) (A.pre ⟨x, hx⟩)‖ ≤ 7 ∧
        cgpGlobalMap P.toLocalChartFamily P.zero (A.pre ⟨x, hx⟩) = x ∧
        A.plane x = LinearMap.range (fderiv ℝ (A.prune (A.ref ⟨x, hx⟩) ∘ A.model (A.ref ⟨x, hx⟩))
          (cgpCircleCoord P.toLocalChartFamily (A.ref ⟨x, hx⟩).1
            ((Set.Finite.mem_toFinset _).mp (A.ref ⟨x, hx⟩).2) (A.pre ⟨x, hx⟩)) :
              ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
  refine ⟨gafCloud_zero_GAF4 _ _, gafCloudEnlarged_zero_GAF4 _ _, fun a => ?_,
    fun x hx => (A.dimension x hx).1, A.cloudy, fun x hx q hq => A.normal x hx q hq,
    fun x hx => ?_⟩
  · obtain ⟨hsm, hown, hb, htg, -, -⟩ := A.tcp05_package a
    rw [A.coord_eq a] at htg
    exact ⟨hsm, hown, fun u => (hb u).1, htg⟩
  · obtain ⟨hpre, hη, hpx⟩ := A.pre_spec ⟨x, hx⟩
    rw [A.coord_eq] at hη
    have hpx' : cgpGlobalMap P.toLocalChartFamily P.zero (A.pre ⟨x, hx⟩) = x := by
      rw [← cgpProjMap_univ_GAF P.toLocalChartFamily P.zero]
      exact hpx
    refine ⟨hpre, hη, hpx', ?_⟩
    rw [A.toStagePlaneData_PLN.plane_of_mem hx, A.coord_eq]

/-- **Consumer: the FC07 plane is the graph plane of the reference coordinate**: at `x ∈ S₁` with
reference `i` and core preimage `p`, for every `v ∈ ℝ²` the plane `A_x⁰ = im DΨ_i(η_i p)` contains
a vector whose own block at `i` is `(v, 0)`; so `A_x⁰ = im(I, R_i⁻¹Dh_i)` is a graph over the own
coordinate `H_i'`. -/
theorem FirstStagePlanes_PLN.fc07_plane_graph_RFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) {x : BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0) (v : ℝ²) :
    ∃ w ∈ A.plane x, w (.inl (A.ref ⟨x, hx⟩)) = WithLp.toLp 2 (v, (0 : ℝ)) := by
  obtain ⟨-, -, hpk, -, -, -, hpl⟩ := A.fc07_RFC
  obtain ⟨-, -, -, hplane⟩ := hpl x hx
  obtain ⟨hsm, hown, -, -⟩ := hpk (A.ref ⟨x, hx⟩)
  rw [hplane]
  exact ⟨_, ⟨v, rfl⟩, own_block_fderiv_RFC _ _ hown _ (hsm.differentiable (by simp) _) v⟩

end Row

/-- **FC07** (`found:fibration-two-cloud`, B:351–370) on the final family. For the first-stage
quality `Γ₁ ∈ (0, 1)`, the scale `0 < Σ₁ < min(Γ₁/200, Γ₁³/(100Ω₁))`, the accuracy
`0 < e₁ < min(1/100, Γ₁Σ₁/100)` and the exclusion quality `ν ∈ (0, 1)`: the thresholds of the
first-stage producer (verbatim, `Δ ≥ 1200`) such that every packet of `LocalChartPacketsC14`
satisfying them carries ONE plane field `A_x` and ONE table `Ψ_i` with: `e₁ < Γ₁`; FC04's clouds;
the `h_i` clause (`Ψ_i` smooth, own block `(u, 1)`, `‖DΨ_i‖ ≤ Ω₁`, C¹ comparison `< e₁` on
`B(i, 200R_i) ∩ {‖η_i‖ ≤ 8}`); `dim A_x = 2` and (CS) at `Γ₁`; the rank / normal clauses at every
preimage; and `A_x⁰ = im DΨ_i(η_i(p))` at a core preimage `‖η_i(p)‖ ≤ 7`. -/
theorem fc07_row_RFC {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      eg < Γ ∧ ∃ A : FirstStagePlanes_PLN P Γ sg eg,
        gafCloud P.toLocalChartFamily P.zero 0 =
            cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7 ∧
          gafCloudEnlarged P.toLocalChartFamily P.zero 0 =
            cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 8 ∧
          (∀ a : P.toLocalChartFamily.circle.finite_centres.toFinset,
            ContDiff ℝ ∞ (A.prune a ∘ A.model a) ∧
            (∀ u, (A.prune a ∘ A.model a) u (.inl a) = WithLp.toLp 2 (u, 1)) ∧
            (∀ u, ‖fderiv ℝ (A.prune a ∘ A.model a) u‖ ≤ tcpGraphConst) ∧
            tcpTG_PLN P eg (A.prune a ∘ A.model a)
              (cgpCircleCoord P.toLocalChartFamily a.1 ((Set.Finite.mem_toFinset _).mp a.2))
              a.1) ∧
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, Module.finrank ℝ (A.plane x) = 2) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
              cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
                (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
              hausdorffEDist
                (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩ ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (A.plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
          (∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0) q,
            cgpGlobalMap P.toLocalChartFamily P.zero q = x →
            tcpNormalSpec_PLN P eg (A.plane x) (A.ref ⟨x, hx⟩).1 q) ∧
          ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0),
            A.pre ⟨x, hx⟩ ∈ ball (A.ref ⟨x, hx⟩).1 (200 * ρ (A.ref ⟨x, hx⟩).1) ∧
            ‖cgpCircleCoord P.toLocalChartFamily (A.ref ⟨x, hx⟩).1
                ((Set.Finite.mem_toFinset _).mp (A.ref ⟨x, hx⟩).2) (A.pre ⟨x, hx⟩)‖ ≤ 7 ∧
            cgpGlobalMap P.toLocalChartFamily P.zero (A.pre ⟨x, hx⟩) = x ∧
            A.plane x = LinearMap.range
              (fderiv ℝ (A.prune (A.ref ⟨x, hx⟩) ∘ A.model (A.ref ⟨x, hx⟩))
                (cgpCircleCoord P.toLocalChartFamily (A.ref ⟨x, hx⟩).1
                  ((Set.Finite.mem_toFinset _).mp (A.ref ⟨x, hx⟩).2) (A.pre ⟨x, hx⟩)) :
                ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
  have hegΓ' : eg < Γ := by
    have h1 : Γ * sg / 100 < Γ := by
      have hsg1 : sg < 1 := by linarith only [hsgΓ, hΓ1]
      nlinarith only [hΓ, hsg1, hsg]
    linarith only [hegΓ, h1]
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, hrow⟩ :=
    exists_firstStagePlanes_PLN hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hν hν1
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, h⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31
  obtain ⟨A⟩ := h P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26 h27 h28 h29 h30 h31
  exact ⟨hegΓ', A, A.fc07_RFC⟩

end DifferentialGeometry.Geometry.Collapse
