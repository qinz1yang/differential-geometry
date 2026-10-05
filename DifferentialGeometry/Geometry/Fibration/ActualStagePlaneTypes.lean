import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneData
import DifferentialGeometry.Geometry.Fibration.ActualStageFirstScale
import DifferentialGeometry.Geometry.Fibration.ActualStageEdgeTestPP
import DifferentialGeometry.Geometry.Fibration.ActualStageSlimTestPP

/-!
# The enhanced stage planes: one plane witness per stage (draft 59 §1.2–1.3, D59-2)

Blueprint `master207B.tex`, FC27 (B:1658) with TCP05–TCP06 / EGP06–EGP07 / SGP04–SGP06, CFS27
(B:3626–3686); external review 55 §2.5, review 60 (TCP05 / SGP04 / EGP06 / FC27 consumption
packages) and the binding draft 59 §1. For each stage `st` (`0` circle / TCP, `1` edge / EGP,
`2` slim / SGP) the structure below extends the generic data `StagePlaneData_PLN` (radius preimage
`q̂`, model preimage `q`, reference label `a`, reference-model table `Φ`, pruning `K`, coordinates
`η`; plane = (PDEF) `im D(K_a ∘ Φ_a)(η_a q)`) with

* the ACTUAL reference-model table: the comparison data of the producer (TCP05: `A_c, c_c, A₁,
  c₁, B_τ, c_τ`; EGP06: signs and translations; SGP04: slim and zero signs and translations), the
  equation `Φ_a = tcpModelGraph … / egpModelGraph … / sgpFullGraph …` with the actual support lists
  (`tcpListedTags`, `egpEdgeList`, …, inside the model definitions), the pruning (`K_a =
  blockRestrict (firstKeepTags_GAF5 (ρ a))` at stage `0`, the identity at stages `1, 2`), the
  coordinates, the global model bounds and the graph comparison (TG) of `K_a ∘ Φ_a` on the whole
  reference core (stage `0`: the predicate `tcpTG_PLN`) — for EVERY reference `a`;
* the selections, as data on the clouds (so the structures are inhabited also for `X = ∅`): the
  radius preimage over the enlarged cloud `S̃_st`, the model preimage over `S_st` with its core
  membership in the reference chart of the SAME choice;
* the specifications of the SAME plane as `Prop` fields: `dimension` (with `L ≤ Q_st`), `cloudy`
  (FC27's (CS) for every selection), `normal` (the rank / normal-error clauses at EVERY preimage, in
  the units of the actual reference), `small_pp` ((PP), exact kernel inclusion), and `scale_zero`
  (stage `0` only).

The present tests are forgetful projections: `FirstStagePlanes_PLN.to_first_test_pps`
(`fc27_first_test_pps_GAF5`'s conclusion), `EdgeStagePlanes_PLN.to_edge_test_pp`
(`fc27_edge_test_pp_GAF4`'s), `SlimStagePlanes_PLN.to_slim_test_pp` (`fc27_slim_test_pp_GAF4`'s),
witness `A.plane`.
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
local instance instMetricNC14_PLNt {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNt {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNt {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- TCP05's graph comparison (TG) of a model `Ψ` in a chart `η` of the circle centre `c`, on the
reference core `B(c, 200ρ(c)) ∩ {‖η‖ ≤ 8}`: value error `< e`, derivative error `≤ e|w|` (`|w|` of
`ρ(c)⁻²g`). -/
def tcpTG_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (eg : ℝ)
    (Ψ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (η : X → ℝ²)
    (c : X) : Prop :=
  ∀ x ∈ ball c (200 * ρ c), ‖η x‖ ≤ 8 →
    ‖(ρ c)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x - Ψ (η x)‖ < eg ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ c)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
          fderiv ℝ Ψ (η x) (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤
        eg * Real.sqrt ((ρ c)⁻¹ ^ 2 * g.inner x w w)

/-- TCP06's rank / normal clauses for a plane `W` at a preimage `q`, in the units of `ρ(i)`
(`P_q = π_W ∘ ρ(i)⁻¹d𝓔⁰_q`: onto, normal error `≤ e`, lower bound `1/2` on `ker P_q`ᗮ, upper bound
`3C`). -/
def tcpNormalSpec_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (eg : ℝ)
    (W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (i q : X) :
    Prop :=
  let Pq := W.orthogonalProjectionOnto.comp
    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q)
  Function.Surjective Pq ∧
  (∀ v, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
      (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)) ∧
  (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
    1 / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
  ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)

/-- EGP07's rank clauses for a plane `W` at a preimage `q`, in the units of `ρ(i)` (on
`ρ(i)⁻²g`-unit vectors: normal error `< e`, projection `≤ 3C†`, a vector with projection `≥ 1/2`,
the projection onto `W` is onto). -/
def egpNormalSpec_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (eg : ℝ)
    (W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (i q : X) :
    Prop :=
  (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
    ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
      W.starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
  (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
    ‖W.starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
  (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
    1 / 2 ≤ ‖W.starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
      (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
  (∀ k ∈ W, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
    W.starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)

/-- SGP05's rank / normal clauses for a plane `W` at a preimage `q`, in the units of `ρ(i)`
(`P_q = π_W ∘ ρ(i)⁻¹d(π₃𝓔⁰)_q`). -/
def sgpNormalSpec_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (eg : ℝ)
    (W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) (i q : X) :
    Prop :=
  let Pq := W.orthogonalProjectionOnto.comp ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
    (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
  Function.Surjective Pq ∧
  (∀ v, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
    eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)) ∧
  (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
    1 / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
  ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)

open Classical in
/-- **Stage `0` (circle / TCP05–TCP06, `Q₁ = H`, planes of dimension `2`)**: the enhanced plane
witness. Its reference-model table is TCP05's joint output on the SAME `Φ_a` (review 60):
global `C²` bounds, own block, (TG), and — from the model equation and the pruning equation —
frozen scale and CFS27's pruning. -/
structure FirstStagePlanes_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (Γ sg eg : ℝ) extends
    StagePlaneData_PLN X (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ℝ²
      P.toLocalChartFamily.circle.finite_centres.toFinset (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) where
  /-- TCP05's circle rows `A_j` at every reference. -/
  Ac : P.toLocalChartFamily.circle.finite_centres.toFinset →
    CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²
  /-- TCP05's circle offsets `c_j` at every reference. -/
  cc : P.toLocalChartFamily.circle.finite_centres.toFinset → CGPTag P.toLocalChartFamily P.zero → ℝ²
  /-- TCP05's scalar rows (slim, edge, zero) at every reference. -/
  A1 : P.toLocalChartFamily.circle.finite_centres.toFinset →
    CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ
  /-- TCP05's scalar offsets at every reference. -/
  c1 : P.toLocalChartFamily.circle.finite_centres.toFinset → CGPTag P.toLocalChartFamily P.zero → ℝ
  /-- TCP05's height row at every reference. -/
  Bτ : P.toLocalChartFamily.circle.finite_centres.toFinset → ℝ² →L[ℝ] ℝ
  /-- TCP05's height offset at every reference. -/
  cτ : P.toLocalChartFamily.circle.finite_centres.toFinset → ℝ
  /-- The actual model: TCP05's model graph with the ACTUAL support lists of
  `D_a = B(a, 10ρ(a))`. -/
  model_eq : ∀ a, model a = tcpModelGraph P.toLocalChartFamily P.zero a.1
    (tcpListedTags P.toLocalChartFamily P.zero a.1) (tcpListedEdges P.toLocalChartFamily a.1)
    (Ac a) (cc a) (A1 a) (c1 a) (Bτ a) (cτ a)
  /-- CFS27's pruning at the reference radius. -/
  prune_eq : ∀ a, prune a = blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1))
  /-- The reference coordinates are the circle coordinates. -/
  coord_eq : ∀ a, coord a =
    cgpCircleCoord P.toLocalChartFamily a.1 ((Set.Finite.mem_toFinset _).mp a.2)
  /-- Global `C²` bounds of the pruned model. -/
  model_bounds : ∀ a u, ‖fderiv ℝ (prune a ∘ model a) u‖ ≤ tcpGraphConst ∧
    ‖fderiv ℝ (fderiv ℝ (prune a ∘ model a)) u‖ ≤ tcpGraphConst
  /-- (TG) of the pruned model on the whole reference core `B(a, 200ρ(a)) ∩ {‖η_a‖ ≤ 8}`. -/
  model_tg : ∀ a, tcpTG_PLN P eg (prune a ∘ model a) (coord a) a.1
  /-- The radius preimage lies in the enlargement `Ã₁` and maps to its point. -/
  rpre_spec : ∀ x : gafCloudEnlarged P.toLocalChartFamily P.zero 0,
    rpre x ∈ gafStageEnlargement P.toLocalChartFamily P.zero 0 ∧
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) (rpre x) =
        x.1
  /-- The model preimage lies in the threshold-`7` core of its reference and maps to its point. -/
  pre_spec : ∀ x : gafCloud P.toLocalChartFamily P.zero 0,
    pre x ∈ ball (ref x).1 (200 * ρ (ref x).1) ∧ ‖coord (ref x) (pre x)‖ ≤ 7 ∧
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) (pre x) =
        x.1
  /-- `dim L_x = 2` and `L_x ≤ Q₁`. -/
  dimension : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
    Module.finrank ℝ (toStagePlaneData_PLN.plane x) = gafStageDim 0 ∧
      toStagePlaneData_PLN.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0
  /-- FC27's (CS) for every selection of preimages, radius `Σρ(sel x)`, quality `Γ`. -/
  cloudy : ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
    (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) (sel x) =
        x) →
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩ ball x (sg * ρ (sel x) / Γ))
        ((AffineSubspace.mk' x (toStagePlaneData_PLN.plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))
  /-- TCP06's rank / normal clauses at EVERY preimage, in the units of the actual reference. -/
  normal : ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0),
    ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      tcpNormalSpec_PLN P eg (toStagePlaneData_PLN.plane x) (ref ⟨x, hx⟩).1 q
  /-- EDP01's scale clause: `L_x ≤ ker v_scale`. -/
  scale_zero : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
    toStagePlaneData_PLN.plane x ≤ LinearMap.ker ((blockMarkerCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)
  /-- (PP): every preimage `q`, every retained marker with `ρ(c_a) < ρ(q)/5`: `L_x ≤ ker v_a`. -/
  small_pp : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
    cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q = x →
    ∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
      toStagePlaneData_PLN.plane x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)

open Classical in
/-- **Stage `1` (edge / EGP06–EGP07, `Q₂`, planes of dimension `1`)**: the enhanced plane witness;
no pruning (`K_a = id`); the model is EGP06's full model `egpModelGraph` with its actual lists. -/
structure EdgeStagePlanes_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (Γ sg eg : ℝ) extends
    StagePlaneData_PLN X (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ℝ
      P.toLocalChartFamily.edge.finite_centres.toFinset (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) where
  /-- EGP06's signs at every reference. -/
  sgn : P.toLocalChartFamily.edge.finite_centres.toFinset → CGPTag P.toLocalChartFamily P.zero → ℝ
  /-- EGP06's translations at every reference. -/
  trans : P.toLocalChartFamily.edge.finite_centres.toFinset →
    CGPTag P.toLocalChartFamily P.zero → ℝ
  /-- The actual model: EGP06's model graph (actual edge / slim / zero lists of `i`). -/
  model_eq : ∀ a, model a = egpModelGraph P.toLocalChartFamily P.zero a.1 (sgn a) (trans a)
  /-- No pruning at the edge stage. -/
  prune_eq : ∀ a, prune a = ContinuousLinearMap.id ℝ _
  /-- The reference coordinates are the edge coordinates. -/
  coord_eq : ∀ a, coord a = P.edge.coord a.1
  /-- The signs are bounded. -/
  sgn_le : ∀ a t, |sgn a t| ≤ 1
  /-- Global `C²` bounds of the model. -/
  model_bounds : ∀ a u, ‖fderiv ℝ (prune a ∘ model a) u‖ ≤ egpGraphConst ∧
    ‖fderiv ℝ (fderiv ℝ (prune a ∘ model a)) u‖ ≤ egpGraphConst
  /-- The derivative of the model is injective with constant `1` (own block). -/
  model_lower : ∀ a u (v : ℝ), ‖v‖ ≤ ‖fderiv ℝ (prune a ∘ model a) u v‖
  /-- The model takes values in `Q₂`. -/
  model_mem_Q : ∀ a u, blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
    ((prune a ∘ model a) u) = (prune a ∘ model a) u
  /-- (EG) of the model on the whole reference core. -/
  model_tg : ∀ a, ∀ x ∈ ball a.1 (100 * Δ * ρ a.1), |coord a x| ≤ 8 * Δ →
    cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
    ‖(ρ a.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) x -
        (prune a ∘ model a) (coord a x)‖ < eg ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ a.1)⁻¹ ^ 2 * g.inner x w w = 1 →
      ‖(ρ a.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
        fderiv ℝ (prune a ∘ model a) (coord a x) (mvfderiv 𝓘(ℝ, E3) (coord a) x w)‖ < eg
  /-- The radius preimage lies in the enlargement `Ã₂` and maps to its point. -/
  rpre_spec : ∀ x : gafCloudEnlarged P.toLocalChartFamily P.zero 1,
    rpre x ∈ gafStageEnlargement P.toLocalChartFamily P.zero 1 ∧
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) (rpre x) =
        x.1
  /-- The model preimage lies in the threshold-`7` edge core of its reference (same height). -/
  pre_spec : ∀ x : gafCloud P.toLocalChartFamily P.zero 1,
    pre x ∈ ball (ref x).1 (100 * Δ * ρ (ref x).1) ∧ |coord (ref x) (pre x)| ≤ 7 * Δ ∧
      cgpHeight P.toLocalChartFamily (pre x) ≤ 7 * Δ ∧
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) (pre x) =
        x.1
  /-- `dim L_x = 1` and `L_x ≤ Q₂`. -/
  dimension : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
    Module.finrank ℝ (toStagePlaneData_PLN.plane x) = gafStageDim 1 ∧
      toStagePlaneData_PLN.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 1
  /-- FC27's (CS) for every selection of preimages. -/
  cloudy : ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
    (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) (sel x) =
        x) →
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩ ball x (sg * ρ (sel x) / Γ))
        ((AffineSubspace.mk' x (toStagePlaneData_PLN.plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))
  /-- EGP07's rank clauses at EVERY preimage, in the units of the actual reference. -/
  normal : ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1), ∀ q : X,
    cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
      egpNormalSpec_PLN P eg (toStagePlaneData_PLN.plane x) (ref ⟨x, hx⟩).1 q
  /-- (PP): every preimage `q`, every retained marker with `ρ(c_a) < ρ(q)/5`: `L_x ≤ ker v_a`. -/
  small_pp : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
    cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q = x →
    ∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
      toStagePlaneData_PLN.plane x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)

open Classical in
/-- **Stage `2` (slim / SGP04–SGP06, `Q₃`, planes of dimension `1`)**: the enhanced plane witness;
no pruning (`K_a = id`); the model is SGP04's FULL model `sgpFullGraph` (slim blocks and the meeting
zero block). -/
structure SlimStagePlanes_PLN
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (Γ sg eg : ℝ) extends
    StagePlaneData_PLN X (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ℝ
      P.toLocalChartFamily.slim.finite_centres.toFinset (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) where
  /-- SGP04's slim signs at every reference. -/
  sgn : P.toLocalChartFamily.slim.finite_centres.toFinset → X → ℝ
  /-- SGP04's slim translations at every reference. -/
  trans : P.toLocalChartFamily.slim.finite_centres.toFinset → X → ℝ
  /-- SGP04's zero sign at every reference. -/
  zsgn : P.toLocalChartFamily.slim.finite_centres.toFinset → X → ℝ
  /-- SGP04's zero translation at every reference. -/
  ztrans : P.toLocalChartFamily.slim.finite_centres.toFinset → X → ℝ
  /-- The actual model: SGP04's full model graph (actual slim list, meeting zero block). -/
  model_eq : ∀ a, model a = sgpFullGraph P.toLocalChartFamily P.zero a (sgn a) (trans a) (zsgn a)
    (ztrans a)
  /-- No pruning at the slim stage. -/
  prune_eq : ∀ a, prune a = ContinuousLinearMap.id ℝ _
  /-- The reference coordinates are the slim coordinates. -/
  coord_eq : ∀ a, coord a = (P.slim.centre a.1 ((Set.Finite.mem_toFinset _).mp a.2)).coord
  /-- The signs are bounded. -/
  sgn_le : ∀ a j, |sgn a j| ≤ 1
  /-- The zero signs are bounded. -/
  zsgn_le : ∀ a k, |zsgn a k| ≤ 1
  /-- Global `C²` bounds of the model. -/
  model_bounds : ∀ a u, ‖fderiv ℝ (prune a ∘ model a) u‖ ≤ sgpGraphBound ∧
    ‖fderiv ℝ (fderiv ℝ (prune a ∘ model a)) u‖ ≤ sgpGraphBound
  /-- The model takes values in `Q₃`. -/
  model_mem_Q : ∀ a u, blockRestrict (cgpQ3Tags P.toLocalChartFamily P.zero)
    ((prune a ∘ model a) u) = (prune a ∘ model a) u
  /-- (SG) of the model on the whole reference core. -/
  model_tg : ∀ a, ∀ x ∈ ball a.1 (10 ^ 6 * Δ * ρ a.1), |coord a x| ≤ 8 * 10 ^ 5 * Δ →
    ‖(ρ a.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        (prune a ∘ model a) (coord a x)‖ < eg ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ a.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
        fderiv ℝ (prune a ∘ model a) (coord a x) (mvfderiv 𝓘(ℝ, E3) (coord a) x w)‖ ≤
      eg * Real.sqrt ((ρ a.1)⁻¹ ^ 2 * g.inner x w w)
  /-- The radius preimage lies in the enlargement `Ã₃` and maps to its point. -/
  rpre_spec : ∀ x : gafCloudEnlarged P.toLocalChartFamily P.zero 2,
    rpre x ∈ gafStageEnlargement P.toLocalChartFamily P.zero 2 ∧
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) (rpre x) =
        x.1
  /-- The model preimage lies in the threshold-`7` slim core of its reference. -/
  pre_spec : ∀ x : gafCloud P.toLocalChartFamily P.zero 2,
    pre x ∈ ball (ref x).1 (10 ^ 6 * Δ * ρ (ref x).1) ∧
      |coord (ref x) (pre x)| ≤ 7 * (10 ^ 5 * Δ) ∧
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) (pre x) =
        x.1
  /-- `dim L_x = 1` and `L_x ≤ Q₃`. -/
  dimension : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
    Module.finrank ℝ (toStagePlaneData_PLN.plane x) = gafStageDim 2 ∧
      toStagePlaneData_PLN.plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2
  /-- FC27's (CS) for every selection of preimages. -/
  cloudy : ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
    (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) =
        x) →
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩ ball x (sg * ρ (sel x) / Γ))
        ((AffineSubspace.mk' x (toStagePlaneData_PLN.plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))
  /-- SGP05's rank / normal clauses at EVERY preimage, in the units of the actual reference. -/
  normal : ∀ x (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2),
    ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x →
      sgpNormalSpec_PLN P eg (toStagePlaneData_PLN.plane x) (ref ⟨x, hx⟩).1 q
  /-- (PP): every preimage `q`, every retained marker with `ρ(c_a) < ρ(q)/5`: `L_x ≤ ker v_a`. -/
  small_pp : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
    cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q = x →
    ∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
      toStagePlaneData_PLN.plane x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)


section Exits

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
  e T V vs ζ Λz} {Γ sg eg : ℝ}

/-- **Forgetful exit to the present first-cloud test** (`fc27_first_test_pps_GAF5`'s conclusion,
witness `A.plane`, rank reference `A.ref x`). -/
theorem FirstStagePlanes_PLN.to_first_test_pps (A : FirstStagePlanes_PLN P Γ sg eg) :
    ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      Module.finrank ℝ (plane x) = gafStageDim 0 ∧
        plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
    (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 0) (sel x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
            ball x (sg * ρ (sel x) / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpScaleTag P.toLocalChartFamily P.zero) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)  :=
  ⟨A.plane, A.dimension, A.cloudy, fun x hx => ⟨A.ref ⟨x, hx⟩, fun q hq => A.normal x hx q hq⟩,
    A.scale_zero, A.small_pp⟩

/-- **Forgetful exit to the present edge test** (`fc27_edge_test_pp_GAF4`'s conclusion, witness
`A.plane`, rank reference `A.ref x`). -/
theorem EdgeStagePlanes_PLN.to_edge_test_pp (A : EdgeStagePlanes_PLN P Γ sg eg) :
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
            ball x (sg * ρ (sel x) / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
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
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)  :=
  ⟨A.plane, A.dimension, A.cloudy,
    fun x hx => ⟨(A.ref ⟨x, hx⟩).1, (Set.Finite.mem_toFinset _).mp (A.ref ⟨x, hx⟩).2,
      fun q hq => A.normal x hx q hq⟩, A.small_pp⟩

/-- **Forgetful exit to the present slim test** (`fc27_slim_test_pp_GAF4`'s conclusion, witness
`A.plane`, rank reference `A.ref x`). -/
theorem SlimStagePlanes_PLN.to_slim_test_pp (A : SlimStagePlanes_PLN P Γ sg eg) :
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
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)  :=
  ⟨A.plane, A.dimension, A.cloudy, fun x hx => ⟨A.ref ⟨x, hx⟩, fun q hq => A.normal x hx q hq⟩,
    A.small_pp⟩

end Exits

end DifferentialGeometry.Geometry.Collapse
