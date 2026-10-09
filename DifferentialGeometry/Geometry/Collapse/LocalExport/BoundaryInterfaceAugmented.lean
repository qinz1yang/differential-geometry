import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInterior
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspSaturationBC7C
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedSupportSlot
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalSlimValue
import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockModel
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneData
import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff

/-!
# Boundary route interfaces, part 1: the augmented data `BoundaryAugmentedData` (lane BIFACE)

External draft 61 §1.4, §2, §7.6 and dispositions D61-1, D61-2, D61-4, D61-5, D61-6, D64-6. The
boundary chain is

`BoundarySupply S → BoundaryAugmentedData S Φ → BoundaryGaf02Chain D … → BoundaryGaf02Bases C → …`

and nothing downstream re-chooses `P`, `ρ`, `ĝ`, the family, the planes or the map.

* T3B's two geometric branches as named propositions of the SAME supply (verbatim disjuncts of
  `BoundarySupply.geometric_cases`): `BoundarySupply.LabelledWholeProduct_BIF`,
  `BoundarySupply.SeparatedCollarZero_BIF`, `BoundarySupply.geometric_cases_BIF`.
* The active reference coordinates (definitions on the stored family, never re-chosen):
  `circleEta_BIF` (rescaled circle chart coordinate), `edgeEta_BIF` (`edgeB.coord_BCG1`),
  `slimEta_BIF` (`coord_BCG2`), the stage centres `stageCentres_BIF` and the reference-domain
  constants `stageDomain_BIF = (10, 20Δ, 950000Δ)` (BCG-8's `C_a`).
* `BoundaryInteriorSlots_BIF S`: the PARAMETER SLOT for the definitions that are not in the tree
  yet — the interior stage tags, the original stage cores `A_j ⊆ Ã_j` (threshold-7/8 sets of the
  active family) and the three CFS31 cutoffs `ψ_j` (BAUG-C/D). The interior tag type, `F_int^W`,
  the scale and `E'` tags are BAUG-A G3's DEFINITIONS (`S.IntTag_BAUGA`, `S.interiorMapW_BAUGA`,
  `S.scaleTag_BAUGA`, `S.edgeTag_BAUGA`). In the final instance every slot field is a DEFINITION
  of `S`; it is never a free choice of a producer.
* Derived definitions: `H^∂ = BoundaryAmbient_BIF`, `F_∂ = S.boundaryOriginalMap` (BAUG-A G3), the
  stage tags with ALL boundary tags, the stage projections `π_j = blockRestrict`,
  `Q_j^∂ = range π_j`, the stage clouds `S_j = π_j F_∂(A_j)`, `S̃_j = π_j F_∂(Ã_j)`.
* `BoundaryStageReferences_BIF Φ st E eta row`: one stage of the augmented reference table — the
  PLANES data `StagePlaneData_PLN` (plane = (PDEF) `im D(K_a Φ_a)(η_a q)`, radius = the
  `Cfs15StageOutput` slot), labels in the stage centres, `coord = eta` on centres, model / radius
  preimages, and the BOUNDARY half of the plane contract: the ONE affine row `A_{a,b}` per listed
  `b ∈ J_∂(a)` with `‖A‖ = 1` and BOTH (BA) errors on `D_a` (BCG-8 / BCG2-BIND clause shape), the
  boundary model slots (BM) `Φ^∂_{a,b} = R_a⁻¹ 𝓑(h_{a,b})` on listed `b` and `0` on unlisted `b`,
  and `K_a = id` on `H_∂`.
* `BoundaryAugmentedData S Φ`: the separated branch and the three stage
  tables (circle on `ℝ²`, revised edge `edgeB` on `ℝ`, slim on `ℝ`). TODO(BAUG-C): the enhanced
  interior plane spec (CS, dimension, rank margin, PP, scale, full marker, whole zero block) is
  BAUG-C's `BoundaryEnhancedPlaneSpec D st`; it enters through the extension frozen in
  `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`, not as a placeholder
  proposition here.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The augmented target `H^∂ = H_int ⊕ ⊕_b ℝ²_b` in the `BlockSpace` encoding (interior tags `ι`,
boundary tags `κ`). -/
abbrev BoundaryAmbient_BIF (ι κ : Type) : Type :=
  BlockSpace (fun _ : ι ⊕ κ => ℝ²)

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- The reference-domain constants `C_a` of the three stages (BCG-8's `10`, `20Δ`, `950000Δ`;
`D_a = B(a, C_a ρ(a))`). -/
def stageDomain_BIF (Δ : ℝ) : Fin 3 → ℝ :=
  ![10, 20 * Δ, 950000 * Δ]

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **T3B's labelled whole-product branch** of the stored supply (the left disjunct of
`geometric_cases`, verbatim). -/
def LabelledWholeProduct_BIF : Prop :=
  ∃ (i j : Fin S.packet.cusp.count), i ≠ j ∧
    ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
      (∀ p, D p ∈ S.packet.cusp.component i ↔ p.2.1 = 0) ∧
        ∀ p, D p ∈ S.packet.cusp.component j ↔ p.2.1 = 1

/-- **T3B's separated branch** of the stored supply (the right disjunct of `geometric_cases`,
verbatim): collars and level sets apart, zero balls off the collars and off every collar block. -/
def SeparatedCollarZero_BIF : Prop :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  (∀ i j : Fin S.packet.cusp.count, i ≠ j →
    Disjoint ((S.packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
      ((S.packet.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
    Disjoint {x | S.packet.level i x ≤ 90} {y | S.packet.level j y ≤ 90} ∧
    ∀ x y, S.packet.level i x ≤ 90 → S.packet.level j y ≤ 90 →
      ENNReal.ofReal 1 ≤ riemannianEDistOf g x y) ∧
  (∀ z (hz : z ∈ S.family.zero.centres) (i : Fin S.packet.cusp.count),
    Disjoint (riemannianBallOf g z.val (S.family.zero.zero z hz).radius)
      ((S.packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
  Disjoint (⋃ z, ⋃ hz : z ∈ S.family.zero.centres,
      riemannianBallOf g z.val (S.family.zero.zero z hz).radius)
    (⋃ i, tsupport (S.packet.toBoundaryCollarPacket.block i))

/-- T3B's alternative on the stored supply, in the named form. -/
theorem geometric_cases_BIF : S.LabelledWholeProduct_BIF ∨ S.SeparatedCollarZero_BIF :=
  S.geometric_cases

open Classical in
/-- The circle reference coordinate `η_j` (the rescaled circle chart coordinate of the stored
family; `0` off the centres). -/
def circleEta_BIF (j : W.pieceInterior ⊤) : W.pieceInterior ⊤ → ℝ² :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if hj : j ∈ S.family.circle.centres then
    (let c := S.family.circle.chart j hj
     letI := (inducedMetricSpace S.completion.metric).rescale (S.rho j)⁻¹
       (inv_pos.mpr (S.rho_pos j))
     c.coord)
  else fun _ => 0

open Classical in
/-- The revised-edge reference coordinate `η_j = edgeB.coord_BCG1 j` (`0` off the centres). -/
def edgeEta_BIF (j : W.pieceInterior ⊤) : W.pieceInterior ⊤ → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if hj : j ∈ S.family.edgeB.centres then S.family.edgeB.coord_BCG1 j hj else fun _ => 0

open Classical in
/-- The slim reference coordinate `η_j = (slim.centre j).coord_BCG2` (`0` off the centres). -/
def slimEta_BIF (j : W.pieceInterior ⊤) : W.pieceInterior ⊤ → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if hj : j ∈ S.family.slim.centres then (S.family.slim.centre j hj).coord_BCG2 else fun _ => 0

/-- The centres of the three stage families: circle, the REVISED edge family `edgeB`, slim. -/
def stageCentres_BIF : Fin 3 → Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  ![S.family.circle.centres, S.family.edgeB.centres, S.family.slim.centres]

end BoundarySupplyCore

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

open Classical in
/-- **The ONE circle boundary row** `A_{j,b} = pr₀ ∘ A_b` of the stored (BA) certificate
`ba_spec` (D61-3: never chosen twice; `0` when `b` is not listed at `j`). -/
def circleRow_BIF (j : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count) : ℝ² →L[ℝ] ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : j ∈ S.family.forgetBFR_BFZD.circle.centres ∧
      ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
        riemannianEDistOf g j.val x < ENNReal.ofReal (10 * S.rho j) then
    (EuclideanSpace.proj (0 : Fin 1)).comp (Classical.choose (S.ba_spec.1 j h.1 i h.2))
  else 0

open Classical in
/-- **The ONE revised-edge boundary row** `A_{j,b} = a • id` (`a = ±1`, the stored sign). -/
def edgeRow_BIF (j : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count) : ℝ →L[ℝ] ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : j ∈ S.family.forgetBFR_BFZD.edgeB.centres ∧
      ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
        riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * S.rho j) then
    Classical.choose (S.ba_spec.2.1 j h.1 i h.2) • ContinuousLinearMap.id ℝ ℝ
  else 0

open Classical in
/-- **The ONE slim boundary row** `A_{j,b} = a • id` (`a = ±1`, the stored sign). -/
def slimRow_BIF (j : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count) : ℝ →L[ℝ] ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : j ∈ S.family.forgetBFR_BFZD.slim.centres ∧
      ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
        riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * S.rho j) then
    Classical.choose (S.ba_spec.2.2 j h.1 i h.2) • ContinuousLinearMap.id ℝ ℝ
  else 0

/-- The whole boundary support list `J_∂(a)` of the stage-`st` reference `a`:
`{b : tsupport (P.block b) ∩ B_g(a, C_a ρ(a)) ≠ ∅}` (BCG-8b's two-sided list). -/
def boundaryList_BIF (st : Fin 3) (a : W.pieceInterior ⊤) : Set (Fin S.packet.cusp.count) :=
  S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b a.val (stageDomain_BIF Δ st * S.rho a)

end BoundarySupply

/-- The interior tag type of BAUG-A G3 has decidable equality (classical; one instance for every
use of `blockRestrict` on `H^∂`). -/
noncomputable instance decEqIntTag_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s'
    ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM) : DecidableEq S.IntTag_BAUGA :=
  Classical.decEq _

/-- **The parameter slot of the boundary route** (draft 61 §2, D61-4, D61-6; lane BIFACE): the
definitions the boundary construction reads that are not in the tree yet. The interior tags, the
interior map `F_int^W`, the scale and `E'` tags are BAUG-A G3's DEFINITIONS (`S.IntTag_BAUGA`,
`S.interiorMapW_BAUGA`, `S.scaleTag_BAUGA`, `S.edgeTag_BAUGA`) and are not slots; the slot holds

* `stageTags`: the interior tags of the three stage subspaces (closed pattern: all, `Q₂`, `Q₃`);
* `stageCore`, `stageEnlargement`: the original stage cores `A_j ⊆ Ã_j` on `W°` (threshold-7 /
  threshold-8 sets of the active family);
* `cutoff`: the three CFS31 cutoffs `ψ_j` on `H^∂` (source / CFS23 / CFS22 formulas of the active
  family; BAUG-C/D).

In the final instance every field is a DEFINITION of the supply `S`. -/
structure BoundaryInteriorSlots_BIF (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) : Type where
  /-- The interior tags of the stage subspaces. -/
  stageTags : Fin 3 → Finset S.IntTag_BAUGA
  /-- The original stage cores `A_j`. -/
  stageCore : Fin 3 → Set (W.pieceInterior ⊤)
  /-- The original stage enlargements `Ã_j`. -/
  stageEnlargement : Fin 3 → Set (W.pieceInterior ⊤)
  /-- The CFS31 stage cutoffs `ψ_j`. -/
  cutoff : Fin 3 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ

namespace BoundaryInteriorSlots_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S)

/-- The augmented stage tags: the interior stage tags and EVERY boundary tag (`Q_j^∂ ⊇ H_∂`). -/
def stageTagsAug (st : Fin 3) : Finset (S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) :=
  (Φ.stageTags st).disjSum Finset.univ

/-- The stage projection `π_j` onto the blocks of the augmented stage tags. -/
def stageProj (st : Fin 3) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  blockRestrict (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Φ.stageTagsAug st)

/-- The stage subspace `Q_j^∂ = range π_j`. -/
def stageQ (st : Fin 3) :
    Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  LinearMap.range (Φ.stageProj st :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))

/-- The actual stage cloud `S_j = π_j F_∂(A_j)`. -/
def stageCloud (st : Fin 3) : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  (fun p : W.pieceInterior ⊤ => Φ.stageProj st (S.boundaryOriginalMap p.val)) '' Φ.stageCore st

/-- The actual enlarged stage cloud `S̃_j = π_j F_∂(Ã_j)`. -/
def stageCloudEnlarged (st : Fin 3) :
    Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  (fun p : W.pieceInterior ⊤ => Φ.stageProj st (S.boundaryOriginalMap p.val)) ''
    Φ.stageEnlargement st

end BoundaryInteriorSlots_BIF

/-- `J_b ∘ F_∂ = F_{∂,b}` on BAUG-A's augmented map (BCG7-COLLAR's `J_b`). -/
theorem BoundarySupplyCore.augmentedBoundaryCoord_boundaryOriginalMap_BIF
    (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      W g δn n B oM) (p : W.Carrier) (i : Fin S.packet.cusp.count) :
    augmentedBoundaryCoord_BC7C i (S.boundaryOriginalMap p) =
      S.packet.toBoundaryCollarPacket.block i p :=
  augmentedBoundaryCoord_boundaryAugmentedMap_BC7C S.interiorMapW_BAUGA
    S.packet.toBoundaryCollarPacket.block p i

section References

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

/-- **One stage of the augmented reference table** (draft 61 §1.4, D61-5, D61-6) at stage `st`,
model coordinate space `E`, reference coordinates `eta` and boundary rows `row` (definitions of the
supply): PLANES' data (the plane is the DEFINITION (PDEF) `im D(K_a Φ_a)(η_a q)`, the radius
`Σρ(q̂ x)` the slot of `Cfs15StageOutput`), labels in the stage centres, `coord = eta` on centres,
radius / model preimages (the model preimage in `D_{a(x)}`), the boundary model slots (BM) on the
listed `b ∈ J_∂(a)` and `0` on unlisted `b`, and `K_a = id` on `H_∂`. -/
structure BoundaryStageReferences_BIF (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ) : Type where
  /-- PLANES' stage data on the stage clouds. -/
  planes : StagePlaneData_PLN (W.pieceInterior ⊤) (BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)) E (W.pieceInterior ⊤) (Φ.stageCloud st) (Φ.stageCloudEnlarged st)
  /-- Every reference label is a centre of the stage family. -/
  ref_mem : ∀ x, planes.ref x ∈ S.stageCentres_BIF st
  /-- The reference coordinates are the stored family's. -/
  coord_eq : ∀ a ∈ S.stageCentres_BIF st, planes.coord a = eta a
  /-- The radius preimages are preimages under `π_j F_∂`. -/
  rpre_spec : ∀ x : Φ.stageCloudEnlarged st,
    Φ.stageProj st (S.boundaryOriginalMap (planes.rpre x).val) = x.1
  /-- The model preimages are preimages under `π_j F_∂` inside `D_{a(x)}`. -/
  pre_spec : ∀ x : Φ.stageCloud st,
    Φ.stageProj st (S.boundaryOriginalMap (planes.pre x).val) = x.1 ∧
      (letI := inducedMetricSpace S.completion.metric
       dist (planes.pre x) (planes.ref x) < stageDomain_BIF Δ st * S.rho (planes.ref x))
  /-- (BM) on the listed boundary components: `Φ^∂_{a,b} = R_a⁻¹ 𝓑(h_{a,b})`,
  `h_{a,b}(z) = η_b(a) + R_a A_{a,b}(z − η_a(a))`. -/
  model_listed : ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a, ∀ z : E,
    planes.model a z (Sum.inr i) = planeBlockEmbed_BAUGA
      (boundaryModel_BCG8b (S.packet.height i a) (S.rho a) (row a i) (eta a a) z)
  /-- Unlisted boundary components: the model slot vanishes. -/
  model_unlisted : ∀ a ∈ S.stageCentres_BIF st, ∀ i ∉ S.boundaryList_BIF st a, ∀ z : E,
    planes.model a z (Sum.inr i) = 0
  /-- The pruning keeps the whole boundary part: `K_a = id` on `H_∂`. -/
  prune_boundary : ∀ a, ∀ v ∈ (augmentedBoundarySubmodule_BC7C :
    Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))),
    planes.prune a v = v

end References

/-- **`BoundaryAugmentedData`** (draft 61 §1.4, D61-2 … D61-6): on the stored supply `S` and the
parameter slot `Φ`, the separated geometric branch and the three stage tables of the augmented
model — circle (`ℝ²`, rows `circleRow_BIF`), the REVISED edge family
`edgeB` (`ℝ`, rows `edgeRow_BIF`), slim (`ℝ`, rows `slimRow_BIF`). The rows, the coordinates, the
support lists and `F_∂` are DEFINITIONS of `S` and `Φ`; only the PLANES data are stored. The
smoothness of `F_int^W` is BAUG-A's theorem `contMDiff_interiorMapW_BAUGA` (register parameter
inequalities), not a field. -/
structure BoundaryAugmentedData (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (Φ : BoundaryInteriorSlots_BIF S) : Type where
  /-- The separated branch of T3B. -/
  separated : S.SeparatedCollarZero_BIF
  /-- The circle stage table. -/
  circle : BoundaryStageReferences_BIF Φ 0 ℝ² S.circleEta_BIF S.circleRow_BIF
  /-- The revised-edge stage table. -/
  edge : BoundaryStageReferences_BIF Φ 1 ℝ S.edgeEta_BIF S.edgeRow_BIF
  /-- The slim stage table. -/
  slim : BoundaryStageReferences_BIF Φ 2 ℝ S.slimEta_BIF S.slimRow_BIF

namespace BoundaryAugmentedData

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} (D : BoundaryAugmentedData S Φ)

/-- The stage planes `L_x^j` ((PDEF) of the stored tables; `⊥` off the cloud). -/
def stagePlane : Fin 3 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
    Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ![D.circle.planes.plane, D.edge.planes.plane, D.slim.planes.plane]

/-- The stage radius selections `q̂` (total: an arbitrary point of `W°` off the enlarged cloud). -/
def stageSel :
    Fin 3 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤ :=
  ![D.circle.planes.rsel (Classical.arbitrary _), D.edge.planes.rsel (Classical.arbitrary _),
    D.slim.planes.rsel (Classical.arbitrary _)]

/-- The CFS15 stage radius `r_j(x) = Σ_j ρ(q̂_j x)`. -/
def stageRadius (st : Fin 3) (sg : ℝ)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ℝ :=
  sg * S.rho (D.stageSel st x)

end BoundaryAugmentedData

end DifferentialGeometry.Geometry.Collapse
