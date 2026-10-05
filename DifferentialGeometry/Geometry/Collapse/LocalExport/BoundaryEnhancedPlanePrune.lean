import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec

/-!
# The pruning of the augmented tables is block-diagonal (lane BAUG-C, review 69 D69-6 (1))

Review 69 §6.2: BIFACE's field `prune_boundary` ("`K_a = id` on `H_∂`") alone does not exclude a
mixing `K(x, y) = (x, y + Lx)` from interior into boundary coordinates. The enhanced spec carries
`prune_slot` (`K_a` never writes into `H_∂`); together they make `K_a` BLOCK-DIAGONAL and equal to
G1's actual block operator `augmentedPrune_BAUGC (pr_int K_a ι_int)`
(`BoundaryEnhancedPlaneSpec.prune_eq_augmented_BAUGC`, G2'). Here, for every table with the spec:

* `prune_blockDiagonal_BAUGC`: `pr_int ∘ K_a = K_int ∘ pr_int` and `(K_a v)_b = v_b` for every
  boundary component `b` (projection commutation in both blocks);
* `pruned_model_unlisted_BAUGC`: an UNLISTED boundary model block stays zero after pruning,
  `(K_a Φ_a(z))_b = 0` for `b ∉ J_∂(a)` (the reviewer's required consequence);
* `pruned_model_listed_BAUGC`: a listed block is the (BM) block after pruning;
* consumer `pruned_model_boundary_BAUGC`: both, at every centre, on the three stored tables of a
  `BoundaryAugmentedData` with plane specs.
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **Block-diagonality, generically**: `K^∂(K_int)` commutes with `pr_int` and keeps every boundary
slot. -/
theorem augmentedPrune_blockDiagonal_BAUGC {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    augIntProjCLM_BAUGC (augmentedPrune_BAUGC Kint v) = Kint (augIntProjCLM_BAUGC v) ∧
      ∀ i : κ, augmentedPrune_BAUGC Kint v (Sum.inr i) = v (Sum.inr i) :=
  ⟨augIntProj_augmentedPrune_BAUGC Kint v, augmentedPrune_apply_inr_BAUGC Kint v⟩

namespace BoundaryEnhancedPlaneSpec

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}
  {R : BoundaryStageReferences_BIF Φ st E eta row} {Γ sg eg : ℝ}

/-- **The stored pruning is block-diagonal** (D69-6 (1)): `pr_int ∘ K_a = K_int ∘ pr_int` with
`K_int = pr_int K_a ι_int`, and `(K_a v)_b = v_b` for every boundary component. -/
theorem prune_blockDiagonal_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    (a : W.pieceInterior ⊤) (v : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    augIntProjCLM_BAUGC (R.planes.prune a v) =
        (augIntProjCLM_BAUGC.comp ((R.planes.prune a).comp augIntInclCLM_BAUGC))
          (augIntProjCLM_BAUGC v) ∧
      ∀ i : Fin S.packet.cusp.count, R.planes.prune a v (Sum.inr i) = v (Sum.inr i) := by
  have hK := hR.prune_eq_augmented_BAUGC a
  refine ⟨?_, hR.prune_slot a v⟩
  have h := (augmentedPrune_blockDiagonal_BAUGC
    (augIntProjCLM_BAUGC.comp ((R.planes.prune a).comp augIntInclCLM_BAUGC)) v).1
  calc augIntProjCLM_BAUGC (R.planes.prune a v) =
        augIntProjCLM_BAUGC (augmentedPrune_BAUGC
          (augIntProjCLM_BAUGC.comp ((R.planes.prune a).comp augIntInclCLM_BAUGC)) v) :=
      congrArg (fun L : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
          augIntProjCLM_BAUGC (L v)) hK
    _ = _ := h

/-- **An unlisted boundary model block stays zero after pruning** (review 69 §6.2): at a centre `a`
and `b ∉ J_∂(a)`, `(K_a Φ_a(z))_b = 0`. -/
theorem pruned_model_unlisted_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    {a : W.pieceInterior ⊤} (ha : a ∈ S.stageCentres_BIF st) {i : Fin S.packet.cusp.count}
    (hi : i ∉ S.boundaryList_BIF st a) (z : E) :
    (R.planes.prune a ∘ R.planes.model a) z (Sum.inr i) = 0 :=
  (hR.prune_slot a (R.planes.model a z) i).trans (R.model_unlisted a ha i hi z)

/-- A listed boundary block is the (BM) block after pruning. -/
theorem pruned_model_listed_BAUGC (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    {a : W.pieceInterior ⊤} (ha : a ∈ S.stageCentres_BIF st) {i : Fin S.packet.cusp.count}
    (hi : i ∈ S.boundaryList_BIF st a) (z : E) :
    (R.planes.prune a ∘ R.planes.model a) z (Sum.inr i) = planeBlockEmbed_BAUGA
      (boundaryModel_BCG8b (S.packet.height i a) (S.rho a) (row a i) (eta a a) z) :=
  (hR.prune_slot a (R.planes.model a z) i).trans (R.model_listed a ha i hi z)

end BoundaryEnhancedPlaneSpec

/-- **Consumer** (D69-6 (1) on the stored tables): for `D : BoundaryAugmentedData S Φ` whose three
tables carry plane specs, at every centre of every stage the unlisted boundary blocks of the pruned
models vanish. -/
theorem pruned_model_boundary_BAUGC {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}
    (D : BoundaryAugmentedData S Φ) {Γ sg eg : Fin 3 → ℝ}
    (hc : BoundaryEnhancedPlaneSpec D.circle (Γ 0) (sg 0) (eg 0))
    (he : BoundaryEnhancedPlaneSpec D.edge (Γ 1) (sg 1) (eg 1))
    (hs : BoundaryEnhancedPlaneSpec D.slim (Γ 2) (sg 2) (eg 2)) (i : Fin S.packet.cusp.count) :
    (∀ a ∈ S.stageCentres_BIF 0, i ∉ S.boundaryList_BIF 0 a → ∀ z : ℝ²,
      (D.circle.planes.prune a ∘ D.circle.planes.model a) z (Sum.inr i) = 0) ∧
    (∀ a ∈ S.stageCentres_BIF 1, i ∉ S.boundaryList_BIF 1 a → ∀ z : ℝ,
      (D.edge.planes.prune a ∘ D.edge.planes.model a) z (Sum.inr i) = 0) ∧
    ∀ a ∈ S.stageCentres_BIF 2, i ∉ S.boundaryList_BIF 2 a → ∀ z : ℝ,
      (D.slim.planes.prune a ∘ D.slim.planes.model a) z (Sum.inr i) = 0 :=
  ⟨fun _ ha hi z => hc.pruned_model_unlisted_BAUGC ha hi z,
    fun _ ha hi z => he.pruned_model_unlisted_BAUGC ha hi z,
    fun _ ha hi z => hs.pruned_model_unlisted_BAUGC ha hi z⟩

end DifferentialGeometry.Geometry.Collapse
