import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRoughData
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes

/-!
# GAF02 CORE on the enhanced planes: the chain object `Gaf02ChainE`

Blueprint `master207B.tex`, GAF02 (B:5797); draft 59 §1, §3 and D59-1 (order: enhanced stage planes
→
CFS15 stage outputs → chain), lead decisions 2026-10-05: `Gaf02ChainE` carries the enhanced plane
witnesses of lane C14-PLANES (`FirstStagePlanes_PLN`, `EdgeStagePlanes_PLN`, `SlimStagePlanes_PLN`,
PDEF planes `A.plane`, total radius selections `A.rsel x₀`) and the rough-graph data of lane
C14-BASES
(`Gaf02RoughData`), on top of the chain object `Gaf02Chain`, which is its FORGETFUL PROJECTION
`Gaf02ChainE.toChain` (a field): every definition (`Ψ_j`, `g_j`, `E`, `scale`) and every theorem of
`Gaf02Chain` applies to `C.toChain` unchanged; the chain's selections and planes ARE the enhanced
ones
(`sel_eq`, `plane_eq`).

* `gaf02_test0_of_planes_GAF8`, `gaf02_test1_of_planes_GAF8`, `gaf02_test2_of_planes_GAF8`: the
present
  FC27 stage-test conclusions for the PDEF plane `A.plane` itself (the forgetful exits of PLANES
  with
  the witness fixed to `A.plane`), the form of `Gaf02Chain`'s test fields.
* `Gaf02ChainE` (structure), `Gaf02ChainE.E`, `Gaf02ChainE.scale` (`= C.toChain.E`,
`C.toChain.scale`, rfl),
  `Gaf02ChainE.core` (consumer: `C.toChain.core` together with the rough data's (OS) budgets).
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF8E {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF8E {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF8E {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The first-cloud test conclusion (FC27 with (PP) and the scale clause) for the PDEF plane
`A.plane`
of a stage-one enhanced plane witness. -/
theorem gaf02_test0_of_planes_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ}
    (A : FirstStagePlanes_PLN P Γ sg eg) :
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      Module.finrank ℝ (A.plane x) = gafStageDim 0 ∧
        A.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
    (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 0) (sel' x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
            ball x (sg * ρ (sel' x) / Γ))
          ((AffineSubspace.mk' x (A.plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (sel' x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel' x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := (A.plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      A.plane x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpScaleTag P.toLocalChartFamily P.zero) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        A.plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) :=
  ⟨A.dimension, A.cloudy, fun x hx => ⟨A.ref ⟨x, hx⟩, fun q hq => A.normal x hx q hq⟩,
    A.scale_zero, A.small_pp⟩

/-- The edge test conclusion (FC27 with (PP)) for the PDEF plane `A.plane` of a stage-two enhanced
plane witness. -/
theorem gaf02_test1_of_planes_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ}
    (A : EdgeStagePlanes_PLN P Γ sg eg) :
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      Module.finrank ℝ (A.plane x) = gafStageDim 1 ∧
        A.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
    (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 1) (sel' x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
            ball x (sg * ρ (sel' x) / Γ))
          ((AffineSubspace.mk' x (A.plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (sel' x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel' x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (A.plane x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
        (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(A.plane x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
        (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
          1 / 2 ≤ ‖(A.plane x).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
        (∀ k ∈ A.plane x, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
            (A.plane x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        A.plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) :=
  ⟨A.dimension, A.cloudy,
    fun x hx => ⟨(A.ref ⟨x, hx⟩).1, (Set.Finite.mem_toFinset _).mp (A.ref ⟨x, hx⟩).2,
      fun q hq => A.normal x hx q hq⟩, A.small_pp⟩

/-- The slim test conclusion (FC27 with (PP)) for the PDEF plane `A.plane` of a stage-three enhanced
plane witness. -/
theorem gaf02_test2_of_planes_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ}
    (A : SlimStagePlanes_PLN P Γ sg eg) :
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      Module.finrank ℝ (A.plane x) = gafStageDim 2 ∧
        A.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
    (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 2) (sel' x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
            ball x (sg * ρ (sel' x) / Γ))
          ((AffineSubspace.mk' x (A.plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (sel' x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel' x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
        x →
      let Pq := (A.plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
        eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        A.plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) :=
  ⟨A.dimension, A.cloudy, fun x hx => ⟨A.ref ⟨x, hx⟩, fun q hq => A.normal x hx q hq⟩,
    A.small_pp⟩

section Object

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **GAF02 CORE on the enhanced planes** (draft 59 §3.1, D59-1 order, lead decisions 2026-10-05):
the
chain object `toChain` (its forgetful projection) whose selections are the radius selections
`A_j.rsel x₀`
and whose planes are the PDEF planes `A_j.plane` of the enhanced plane witnesses `planes₀`,
`planes₁`,
`planes₂` (TCP05 / EGP / SGP reference-model tables of lane C14-PLANES), together with the
rough-graph
data `rough` (TCP05, EGP06, SGP04 at `e_j` and GAF01's (OS)) on the same family. -/
structure Gaf02ChainE
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) : Type where
  /-- The underlying chain: selections, planes, CFS15 smoothing slots, numbers; `Ψ_j`, `g_j`, `E`.
  -/
  toChain : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw
  /-- The base point of the total radius selections. -/
  x₀ : X
  /-- The stage-one enhanced plane witness (TCP05 table, CFS27 pruning). -/
  planes₀ : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0)
  /-- The stage-two enhanced plane witness (EGP model graphs). -/
  planes₁ : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)
  /-- The stage-three enhanced plane witness (SGP full graphs). -/
  planes₂ : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2)
  /-- The chain's selections are the planes' radius selections. -/
  sel_eq : toChain.sel 0 = planes₀.rsel x₀ ∧ toChain.sel 1 = planes₁.rsel x₀ ∧
    toChain.sel 2 = planes₂.rsel x₀
  /-- The chain's planes are the PDEF planes. -/
  plane_eq : toChain.plane 0 = planes₀.plane ∧ toChain.plane 1 = planes₁.plane ∧
    toChain.plane 2 = planes₂.plane
  /-- The rough-graph data on the same family and accuracies (lane C14-BASES). -/
  rough : Gaf02RoughData toChain

end Object

namespace Gaf02ChainE

/-- The final map `E` of the chain on the enhanced planes (`= C.toChain.E`). -/
def E {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) :=
  C.toChain.E

/-- The scale `s = ℓ_ρ ∘ E` of the chain on the enhanced planes (`= C.toChain.scale`). -/
def scale {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : X → ℝ :=
  C.toChain.scale

/-- `E` and `scale` are those of the forgetful projection. -/
theorem toChain_E_scale {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) : C.E = C.toChain.E ∧ C.scale = C.toChain.scale :=
  ⟨rfl, rfl⟩

/-- **Consumer: GAF02 CORE on the enhanced planes** — `C.toChain.core` (the analytic core of `E`,
the
scale exit, kept blocks) together with the rough data's budgets: `ε_j < 1/(2Ω)` (CGP06's margin) and
`ν + e_j ≤ 1/(48Ω)` for every normal error `ν ≤ e_j`. -/
theorem core {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    (∀ p, 0 < C.scale p ∧ |C.scale p - ρ p| < c 0 * ρ p) ∧
      (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 2 * ρ p) ∧
      (∀ j, Ξ j < 1 / (2 * gafGraphOmega_BAS)) ∧
      ∀ j, ∀ ν ≤ eg j, ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS) :=
  ⟨fun p => ⟨(C.toChain.scale_pos p).2, (C.toChain.scale_pos p).1⟩, C.toChain.stage_error_lt.2.2,
    fun j => (C.rough.eps_lt_margin_BAS j).1, fun j _ hν => C.rough.normal_add_rough_le_BAS j hν⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
