import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransfer
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpecV3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageNativeOutput

/-!
# The transfer layer, table part: the augmented stage table of a port output (lane BAUG-C)

Step 1 of the transfer from the INTERIOR port tables (`PortTargets v3.1`,
`port_{circle,edge,slim}_interior_table_BAUGP`) to `BoundaryEnhancedPlaneSpecV3` (dry-run table in
`build-logs/resume/state-BAUG-C.md`), uniform in the stage `st`, the model space `E`, the reference
coordinates `eta` and the boundary rows `row`, on any parameter slot `Φ`:

* `portTable_BAUGC`: the stage table `BoundaryStageReferences_BIF Φ st E eta row` of the port data
  `(Ψ, K_int, q̂, q, a)`: model `a ↦ Φ^∂[Ψ_a]` (G1's augmented model with the (BM) blocks of the
  listed boundary components), pruning `a ↦ K^∂(K_int a)`, coordinates `eta`; the selections and
  the reference labels from the port clause (SEL);
* `portTable_plane_BAUGC`: (PDEF) of that table is G1's augmented derivative image
  `im (ι_int D(K_int Ψ) + Σ_{b listed} slot_b DΦ^∂_b)` (port (M) differentiability);
* the spec fields that need no boundary geometry: `prune_slot`, `cloud_subset` (slot v2),
  `dimension` (port (M), (OWN), (Q)), `small_pp` (PP-int), `scale_zero` (SCL), `small_block`
  (SB-int), `full_marker` (FM*-int), `zero_block` (ZB*-int), and at stage `0` (scale block kept)
  `radius_mcb` and `preimage_comparable`; at stages `1, 2` `radius_mcb` from the port (MCb) called at
  `5Σ/4` (`portTable_radius_mcb_of_port_BAUGC`).
* consumer `portTable_kernel_fields_BAUGC`: the eight kernel / dimension fields together.

The remaining fields `cloudy` and `normal` need the boundary geometry of the collar blocks on the
reference domains (next modules of the transfer).
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

/-! ### Generic block lemmas (abstract tags; instantiated on `H^∂` below) -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-- `K^∂ = id` on `H_∂` (the vectors with zero interior slots). -/
theorem augmentedPrune_eq_self_of_mem_boundary_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    {v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (hv : v ∈ (augmentedBoundarySubmodule_BC7C : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))) :
    augmentedPrune_BAUGC Kint v = v :=
  augmentedPrune_eq_self_of_proj_eq_zero_BAUGC Kint (PiLp.ext fun i => hv i)

/-- **A vanishing block of a map has vanishing derivative block**: if `(Φ u)_t = 0` for every `u`
then `(DΦ(z) v)_t = 0`. -/
theorem fderiv_apply_block_eq_zero_BAUGC {τ : Type*} [Finite τ]
    {Φ : E → BlockSpace (fun _ : τ => ℝ²)} (t : τ) (h : ∀ u, Φ u t = 0) {z : E}
    (hΦ : DifferentiableAt ℝ Φ z) (v : E) : fderiv ℝ Φ z v t = 0 := by
  classical
  have := Fintype.ofFinite τ
  have hfix : ∀ u, blockRestrict (Finset.univ.erase t) (Φ u) = Φ u := fun u =>
    PiLp.ext fun i => by
      rw [blockRestrict_apply]
      by_cases hi : i = t
      · subst hi
        rw [ite_eq_right (Finset.notMem_erase i Finset.univ), h u]
      · rw [ite_eq_left (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)]
  have h1 := clm_fderiv_of_fixed_BAUGC (blockRestrict (Finset.univ.erase t)) hfix hΦ v
  rw [← h1, blockRestrict_apply, ite_eq_right (Finset.notMem_erase t Finset.univ)]

/-- **(PP-int) / (FM*-int) / (SCL) ⟹ marker kernel**: if the pruned interior model has vanishing
`t`-marker derivative at `z`, the augmented pruned plane at `z` lies in the kernel of the marker of
`inl t`. -/
theorem range_fderiv_augmented_le_ker_marker_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    {Φint : E → BlockSpace (fun _ : ι => ℝ²)} {J : Set κ} {Φb : κ → E → ℝ × ℝ} {z : E}
    (hint : DifferentiableAt ℝ (Kint ∘ Φint) z) (hb : ∀ b ∈ J, DifferentiableAt ℝ (Φb b) z)
    (t : ι) (h : ∀ v, ((fderiv ℝ (Kint ∘ Φint) z v) t).snd = 0) :
    LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J Φb) z :
        E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ≤
      LinearMap.ker ((blockMarkerCLM (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] ℝ) : BlockSpace (fun _ : ι ⊕ κ => ℝ²) →ₗ[ℝ] ℝ) := by
  classical
  rw [fderiv_augmented_pruned_BAUGC Kint hint hb]
  exact range_augDeriv_le_ker_marker_BAUGC _ _ t h

/-- **(SB-int) / (ZB*-int) ⟹ block kernel**: a vanishing `t`-block derivative of the pruned
interior model puts the augmented pruned plane in the kernel of the whole block of `inl t`. -/
theorem range_fderiv_augmented_le_ker_block_BAUGC
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    {Φint : E → BlockSpace (fun _ : ι => ℝ²)} {J : Set κ} {Φb : κ → E → ℝ × ℝ} {z : E}
    (hint : DifferentiableAt ℝ (Kint ∘ Φint) z) (hb : ∀ b ∈ J, DifferentiableAt ℝ (Φb b) z)
    (t : ι) (h : ∀ v, fderiv ℝ (Kint ∘ Φint) z v t = 0) :
    LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC Kint ∘ augmentedModel_BAUGC Φint J Φb) z :
        E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ≤
      LinearMap.ker ((blockProjCLM_PLN (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inl t) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BlockSpace (fun _ : ι ⊕ κ => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  classical
  rw [fderiv_augmented_pruned_BAUGC Kint hint hb]
  exact range_augDeriv_le_ker_block_BAUGC _ _ t h

/-- **(M) + (OWN) + (Q) ⟹ dimension and `L ≤ Q`** (generic): the augmented pruned plane has
dimension `dim E` and lies in the range of the restriction to `s ⊕ (all boundary tags)`. -/
theorem augmented_plane_dimension_range_BAUGC [DecidableEq ι] [DecidableEq κ]
    (Kint : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] BlockSpace (fun _ : ι => ℝ²))
    (Φint : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ) (Φb : κ → E → ℝ × ℝ) {z : E}
    (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E) (hPc : ∀ u, Pc ((Kint ∘ Φint) u) = u)
    (s : Finset ι) (hQ : ∀ u, blockRestrict s ((Kint ∘ Φint) u) = (Kint ∘ Φint) u)
    (hint : DifferentiableAt ℝ (Kint ∘ Φint) z) (hb : ∀ b ∈ J, DifferentiableAt ℝ (Φb b) z) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC Kint ∘
        augmentedModel_BAUGC Φint J Φb) z : E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²))) =
      Module.finrank ℝ E ∧
    LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC Kint ∘
        augmentedModel_BAUGC Φint J Φb) z : E →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ≤
      LinearMap.range (blockRestrict (V := fun _ : ι ⊕ κ => ℝ²) (s.disjSum Finset.univ) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) := by
  have h := augmented_plane_dimension_BAUGC Kint Φint J Φb Pc hPc s hQ hint hb
  refine ⟨h.1, fun w hw => ⟨w, h.2 w hw⟩⟩

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-! ### The stage table of a port output -/

section Table

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
  (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
  (Ψ : W.pieceInterior ⊤ → E → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
  (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
    BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
  (rpre : Φ.stageCloudEnlarged st → W.pieceInterior ⊤)
  (pre ref : Φ.stageCloud st → W.pieceInterior ⊤)

/-- The augmented reference model of a port output at the centre `a`: `Φ^∂[Ψ_a]` with the (BM)
blocks `R_a⁻¹𝓑(h_{a,b})` of the listed boundary components (`J_∂(a) = S.boundaryList_BIF st a`). -/
def portModel_BAUGC (a : W.pieceInterior ⊤) :
    E → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  augmentedModel_BAUGC (Ψ a) (S.boundaryList_BIF st a)
    (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a))

/-- **The stage table of a port output** (transfer Step 1): PLANES' data `(q̂, q, a, Φ^∂[Ψ],
K^∂(K_int), eta)` with the port's selections; the (BM) slots and `K_a = id` on `H_∂` hold by
construction. -/
def portTable_BAUGC (href : ∀ x, ref x ∈ S.stageCentres_BIF st)
    (hrpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (rpre x).val) = x.1)
    (hpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (pre x).val) = x.1 ∧
      (letI := inducedMetricSpace S.completion.metric
       dist (pre x) (ref x) < stageDomain_BIF Δ st * S.rho (ref x))) :
    BoundaryStageReferences_BIF Φ st E eta row where
  planes :=
    { rpre := rpre
      pre := pre
      ref := ref
      model := portModel_BAUGC st eta row Ψ
      prune := fun a => augmentedPrune_BAUGC (Kint a)
      coord := eta }
  ref_mem := href
  coord_eq := fun _ _ => rfl
  rpre_spec := hrpre
  pre_spec := hpre
  model_listed := fun a _ i hi z => by
    simp only [portModel_BAUGC, augmentedModel_apply_inr_BAUGC, augmentedBlocks_of_mem_BAUGC _ hi]
    rfl
  model_unlisted := fun a _ i hi z => by
    simp only [portModel_BAUGC, augmentedModel_apply_inr_BAUGC,
      augmentedBlocks_of_notMem_BAUGC _ hi, Pi.zero_apply, map_zero]
  prune_boundary := fun a _ hv => augmentedPrune_eq_self_of_mem_boundary_BAUGC (Kint a) hv

variable (href : ∀ x, ref x ∈ S.stageCentres_BIF st)
  (hrpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (rpre x).val) = x.1)
  (hpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (pre x).val) = x.1 ∧
    (letI := inducedMetricSpace S.completion.metric
     dist (pre x) (ref x) < stageDomain_BIF Δ st * S.rho (ref x)))

/-- The (BM) blocks of the port model are differentiable everywhere. -/
theorem portModel_blocks_differentiableAt_BAUGC (a : W.pieceInterior ⊤) (z : E) :
    ∀ i ∈ S.boundaryList_BIF st a, DifferentiableAt ℝ
      (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a) i) z :=
  fun i _ => differentiableAt_bmBlocks_BAUGC _ (S.rho_pos a).ne' _ _ z i

/-- **(PDEF) of the port table**: at a cloud point `x` with reference `a = ref x` and model
preimage `q = pre x`, the plane is `im D(K^∂(K_int a) ∘ Φ^∂[Ψ_a])(η_a q)`. -/
theorem portTable_plane_BAUGC {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ Φ.stageCloud st) :
    (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x =
      LinearMap.range (fderiv ℝ (augmentedPrune_BAUGC (Kint (ref ⟨x, hx⟩)) ∘
        portModel_BAUGC st eta row Ψ (ref ⟨x, hx⟩)) (eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) :
          E →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  StagePlaneData_PLN.plane_of_mem _ hx

/-- Field `prune_slot` of the port table. -/
theorem portTable_prune_slot_BAUGC (a : W.pieceInterior ⊤)
    (v : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (i : Fin S.packet.cusp.count) :
    (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.prune a v (Sum.inr i) =
      v (Sum.inr i) :=
  augmentedPrune_apply_inr_BAUGC (Kint a) v i

/-- Field `dimension` of the port table (port (M) differentiability, (OWN) left inverse, (Q) values
in `Q_st`; `dim E = k_st`). -/
theorem portTable_dimension_BAUGC (hdim : Module.finrank ℝ E = gafStageDim st)
    (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] E)
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hOWN : ∀ a ∈ S.stageCentres_BIF st, ∀ u, Pc a ((Kint a ∘ Ψ a) u) = u)
    (hQ : ∀ a ∈ S.stageCentres_BIF st, ∀ u,
      blockRestrict (Φ.stageTags st) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) :
    ∀ x ∈ Φ.stageCloud st,
      Module.finrank ℝ
          ((portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x) =
        gafStageDim st ∧
      (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x ≤
        Φ.stageQ st := by
  intro x hx
  have ha := href ⟨x, hx⟩
  have h := augmented_plane_dimension_range_BAUGC (Kint (ref ⟨x, hx⟩)) (Ψ (ref ⟨x, hx⟩))
    (S.boundaryList_BIF st (ref ⟨x, hx⟩))
    (bmBlocks_BAUGC (fun i => S.packet.height i (ref ⟨x, hx⟩)) (S.rho (ref ⟨x, hx⟩))
      (row (ref ⟨x, hx⟩)) (eta (ref ⟨x, hx⟩) (ref ⟨x, hx⟩)))
    (z := eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) (Pc (ref ⟨x, hx⟩)) (hOWN _ ha) (Φ.stageTags st)
    (hQ _ ha) ((hM _ ha).differentiable (by norm_num) _)
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _)
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx]
  exact ⟨h.1.trans hdim, h.2⟩

/-- Field `small_pp` of the port table (port (PP-int)). -/
theorem portTable_small_pp_BAUGC (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hPP : ∀ x (hx : x ∈ Φ.stageCloud st), ∀ q : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
        ∀ v : E, ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
          (eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) :
    ∀ x ∈ Φ.stageCloud st, ∀ q : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
        (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x ≤
          LinearMap.ker ((S.markerCLM_BAUGC m :
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) := by
  intro x hx q hq m hm
  have ha := href ⟨x, hx⟩
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx]
  exact range_fderiv_augmented_le_ker_marker_BAUGC (Kint (ref ⟨x, hx⟩))
    ((hM _ ha).differentiable (by norm_num) _)
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _) _ (hPP x hx q hq m hm)

/-- Field `scale_zero` of the port table (port (SCL) at stage `0`). -/
theorem portTable_scale_zero_BAUGC
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hSCL : st = 0 → ∀ a ∈ S.stageCentres_BIF st, ∀ u v : E,
      ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0) :
    st = 0 → ∀ x ∈ Φ.stageCloud st,
      (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x ≤
        LinearMap.ker ((S.scaleCLM_BAUGC :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) := by
  intro hst x hx
  have ha := href ⟨x, hx⟩
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx]
  exact range_fderiv_augmented_le_ker_marker_BAUGC (Kint (ref ⟨x, hx⟩))
    ((hM _ ha).differentiable (by norm_num) _)
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _) _
    (hSCL hst _ ha _)

/-- Field `small_block` of the port table (port (SB-int): the whole small block of `K_int a ∘ Ψ_a`
vanishes). -/
theorem portTable_small_block_BAUGC
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hSB : ∀ a ∈ S.stageCentres_BIF st, ∀ m : S.MarkerIdx_BAUGC,
      S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC st * S.rho a →
      ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) :
    ∀ x (hx : x ∈ Φ.stageCloud st) (m : S.MarkerIdx_BAUGC),
      S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC st *
          S.rho ((portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.ref
            ⟨x, hx⟩) →
        (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x ≤
          LinearMap.ker ((S.markerBlockCLM_BAUGC m :
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
              WithLp 2 (ℝ² × ℝ))) := by
  intro x hx m hm
  have ha := href ⟨x, hx⟩
  have hd := (hM _ ha).differentiable (by norm_num) (eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩))
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx]
  exact range_fderiv_augmented_le_ker_block_BAUGC (Kint (ref ⟨x, hx⟩)) hd
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _) _
    (fderiv_apply_block_eq_zero_BAUGC _ (hSB _ ha m hm) hd)

open Classical in
/-- The window radius of the port table: `σρ(q̂ y)` with the port's selection (coercion to `W` in
the branches, as the port clauses elaborate). -/
theorem portTable_radius_BAUGC (x₀ : W.pieceInterior ⊤) (σ : ℝ)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.radius x₀ σ
        (fun q : W.pieceInterior ⊤ => S.rho q) y =
      σ * S.rho (if hyT : y ∈ Φ.stageCloudEnlarged st then rpre ⟨y, hyT⟩ else x₀) := by
  by_cases hyT : y ∈ Φ.stageCloudEnlarged st
  · rw [StagePlaneData_PLN.radius_of_mem _ _ _ _ hyT, dite_eq_left hyT]
    rfl
  · rw [StagePlaneData_PLN.radius, StagePlaneData_PLN.rsel, dite_eq_right hyT, dite_eq_right hyT]

open Classical in
/-- Field `full_marker` of the port table (port (FM*-int) at `σ' = σ`; the window radius
`σρ(q̂ ·)` of the table is literally the port's). -/
theorem portTable_full_marker_BAUGC
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hFM : ∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = st → ∀ p ∈ S.markerCore7_BAUGC m,
      ∀ y (hy : y ∈ Φ.stageCloud st),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ Φ.stageCloudEnlarged st
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball (Φ.stageProj st (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : Φ.stageProj st
                (S.boundaryOriginalMap p.val) ∈ Φ.stageCloudEnlarged st
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
        ∀ v : E, ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
          (eta (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) :
    ∀ εc σ : ℝ, 0 < εc → 0 ≤ σ → σ ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = st → ∀ p ∈ S.markerCore7_BAUGC m,
      ∀ y ∈ Φ.stageCloud st,
        (closedBall y (80 * εc⁻¹ *
            (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.radius x₀ σ
              (fun q : W.pieceInterior ⊤ => S.rho q) y) ∩
          ball (Φ.stageProj st (S.boundaryOriginalMap p.val)) (8 * εc⁻¹ *
            (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.radius x₀ σ
              (fun q : W.pieceInterior ⊤ => S.rho q)
              (Φ.stageProj st (S.boundaryOriginalMap p.val)))).Nonempty →
        S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane y ≤
            LinearMap.ker ((S.markerCLM_BAUGC m :
              BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) := by
  intro εc σ hε hσ hσε x₀ m hm p hp y hy hmeet
  rw [portTable_radius_BAUGC, portTable_radius_BAUGC] at hmeet
  have hF := hFM εc σ hε hσ hσε x₀ m hm p hp y hy hmeet
  have ha := href ⟨y, hy⟩
  refine ⟨hF.1, ?_⟩
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hy]
  exact range_fderiv_augmented_le_ker_marker_BAUGC (Kint (ref ⟨y, hy⟩))
    ((hM _ ha).differentiable (by norm_num) _)
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _) _ hF.2

open Classical in
/-- Field `zero_block` of the port table (port (ZB*-int) at `σ' = σ`). -/
theorem portTable_zero_block_BAUGC
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hZB : ∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
      Φ.stageProj st (S.boundaryOriginalMap p.val) ∈ Φ.stageCloud st →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ y (hy : y ∈ Φ.stageCloud st),
        (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ Φ.stageCloudEnlarged st
            then rpre ⟨y, hyT⟩ else x₀))) ∩
          ball (Φ.stageProj st (S.boundaryOriginalMap p.val))
            (8 * εc⁻¹ * (σ' * S.rho (if hpT : Φ.stageProj st
                (S.boundaryOriginalMap p.val) ∈ Φ.stageCloudEnlarged st
              then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
        S.zeroBlockCLM_BAUGC k y = 0 ∧
        ∀ v : E, (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
          (eta (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) :
    ∀ εc σ : ℝ, 0 < εc → σ ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
      (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
      Φ.stageProj st (S.boundaryOriginalMap p.val) ∈ Φ.stageCloud st →
      200 * S.zeroRadius_BAUGC k / T < S.rho p →
      ∀ y ∈ Φ.stageCloud st,
        (closedBall y (80 * εc⁻¹ *
            (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.radius x₀ σ
              (fun q : W.pieceInterior ⊤ => S.rho q) y) ∩
          ball (Φ.stageProj st (S.boundaryOriginalMap p.val)) (8 * εc⁻¹ *
            (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.radius x₀ σ
              (fun q : W.pieceInterior ⊤ => S.rho q)
              (Φ.stageProj st (S.boundaryOriginalMap p.val)))).Nonempty →
        S.zeroBlockCLM_BAUGC k y = 0 ∧
          (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane y ≤
            LinearMap.ker ((S.zeroBlockCLM_BAUGC k :
              BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
                WithLp 2 (ℝ² × ℝ))) := by
  intro εc σ hε hσε x₀ k p hpx hρp y hy hmeet
  rw [portTable_radius_BAUGC, portTable_radius_BAUGC] at hmeet
  have hZ := hZB εc σ hε hσε x₀ k p hpx hρp y hy hmeet
  have ha := href ⟨y, hy⟩
  refine ⟨hZ.1, ?_⟩
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hy]
  exact range_fderiv_augmented_le_ker_block_BAUGC (Kint (ref ⟨y, hy⟩))
    ((hM _ ha).differentiable (by norm_num) _)
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _) _ hZ.2

end Table

/-! ### Scale comparisons -/

section Scale

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

/-- **`radius_mcb` from a kept scale block** (stage `0`): the scale of a preimage is the scale
marker of its image, a `1`-Lipschitz functional, so `|ρ(q̂ x) − ρ(q̂ y)| ≤ ‖x − y‖` on the enlarged
cloud and BAUG-C's (MCb) arithmetic applies. -/
theorem radius_mcb_of_scale_kept_BAUGC {st : Fin 3} (hsc : S.scaleTag_BAUGA ∈ Φ.stageTags st)
    {sg : ℝ} (hsg : 0 < sg) :
    ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
      (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
      ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
        dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
        sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
          sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x)) := by
  intro sel hsel L' _ hL x hx y hy hd
  have hrx : S.rho (sel x) = S.scaleMarker_BIF x := by
    rw [← scaleMarker_stageProj_BAUGC hsc (sel x).val, hsel x hx]
  have hry : S.rho (sel y) = S.scaleMarker_BIF y := by
    rw [← scaleMarker_stageProj_BAUGC hsc (sel y).val, hsel y hy]
  refine radius_ratio_of_scale_BAUGC (S.rho_pos _) (S.rho_pos _) hsg hL ?_
  have hlip : |S.scaleMarker_BIF x - S.scaleMarker_BIF y| ≤ dist y x := by
    rw [← map_sub, dist_comm, dist_eq_norm, ← S.scaleCLM_BAUGC_eq_scaleMarker_BIF]
    exact abs_blockMarkerCLM_le_BAUGC _ _
  rw [hrx, hry]
  rw [hrx, hry] at hd
  exact hlip.trans hd

/-- **`preimage_comparable` from a kept scale block** (stage `0`): two preimages of the same point
have the same scale. -/
theorem preimage_comparable_of_scale_kept_BAUGC {st : Fin 3}
    (hsc : S.scaleTag_BAUGA ∈ Φ.stageTags st) :
    ∀ x ∈ Φ.stageCloudEnlarged st, ∀ q₁ q₂ : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q₁.val) = x →
      Φ.stageProj st (S.boundaryOriginalMap q₂.val) = x → S.rho q₁ ≤ 5 / 3 * S.rho q₂ := by
  intro x _ q₁ q₂ h₁ h₂
  have he : S.rho q₁ = S.rho q₂ := by
    rw [← scaleMarker_stageProj_BAUGC hsc q₁.val, ← scaleMarker_stageProj_BAUGC hsc q₂.val, h₁, h₂]
  have hp := S.rho_pos q₂
  rw [he]
  linarith

/-- **`radius_mcb` from the port (MCb) called at `5Σ/4`** (stages `1, 2`): the port's buffer
`L'' = 4L'/5` gives the spec's buffer `L'`. -/
theorem radius_mcb_of_port_BAUGC {st : Fin 3} {sg : ℝ}
    (hMCb : ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
        W.pieceInterior ⊤,
      (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ L' : ℝ, 0 ≤ L' → L' * (5 / 4 * sg) ≤ 1 / 5 →
      ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
        dist y x ≤ L' * max (5 / 4 * sg * S.rho (sel y)) (5 / 4 * sg * S.rho (sel x)) →
        5 / 4 * sg * S.rho (sel x) / (5 / 3) ≤ 5 / 4 * sg * S.rho (sel y) ∧
          5 / 4 * sg * S.rho (sel y) ≤ 5 / 3 * (5 / 4 * sg * S.rho (sel x))) :
    ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
      (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
      ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
        dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
        sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
          sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x)) := by
  intro sel hsel L' hL0 hL x hx y hy hd
  have hL'' : 4 / 5 * L' * (5 / 4 * sg) ≤ 1 / 5 := by nlinarith
  have hmax : max (5 / 4 * sg * S.rho (sel y)) (5 / 4 * sg * S.rho (sel x)) =
      5 / 4 * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) := by
    rw [mul_assoc (5 / 4 : ℝ) sg, mul_assoc (5 / 4 : ℝ) sg,
      mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  have hd' : dist y x ≤ 4 / 5 * L' *
      max (5 / 4 * sg * S.rho (sel y)) (5 / 4 * sg * S.rho (sel x)) := by
    rw [hmax]
    calc dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) := hd
      _ = 4 / 5 * L' * (5 / 4 * max (sg * S.rho (sel y)) (sg * S.rho (sel x))) := by ring
  have h := hMCb sel hsel (4 / 5 * L') (by positivity) hL'' x hx y hy hd'
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

end Scale

/-! ### Consumer -/

section Consumer

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

/-- **Consumer: the circle stage of the actual slot v2** — for port data on the circle stage
(`ℝ²`, `S.circleEta_BIF`, `S.circleRow_BIF`) with (SEL), (M), (OWN), (Q), the port table has the
spec fields `prune_slot`, `cloud_subset`, `dimension`, `radius_mcb` and `preimage_comparable` (scale
block of `Q₁^∂`). -/
theorem portTable_circle_fields_BAUGC (hΔ : 0 ≤ Δ) {sg : ℝ} (hsg : 0 < sg)
    (Ψ : W.pieceInterior ⊤ → ℝ² → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
    (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
      BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
    (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ²)
    (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 → W.pieceInterior ⊤)
    (pre ref : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤)
    (href : ∀ x, ref x ∈ S.stageCentres_BIF 0)
    (hrpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (rpre x).val) = x.1)
    (hpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1 ∧
      (letI := inducedMetricSpace S.completion.metric
       dist (pre x) (ref x) < stageDomain_BIF Δ 0 * S.rho (ref x)))
    (hM : ∀ a ∈ S.stageCentres_BIF 0, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hOWN : ∀ a ∈ S.stageCentres_BIF 0, ∀ u, Pc a ((Kint a ∘ Ψ a) u) = u)
    (hQ : ∀ a ∈ S.stageCentres_BIF 0, ∀ u,
      blockRestrict (S.stageTagsV2_BAUGD 0) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) :
    (∀ a v i, (portTable_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint
        rpre pre ref href hrpre hpre).planes.prune a v (Sum.inr i) = v (Sum.inr i)) ∧
    (actualSlotsV2_BAUGD S).stageCore 0 ⊆ (actualSlotsV2_BAUGD S).stageEnlargement 0 ∧
    (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloud 0,
      Module.finrank ℝ ((portTable_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF
          S.circleRow_BIF Ψ Kint rpre pre ref href hrpre hpre).planes.plane x) = gafStageDim 0 ∧
        (portTable_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint
          rpre pre ref href hrpre hpre).planes.plane x ≤ (actualSlotsV2_BAUGD S).stageQ 0) ∧
    (∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
      (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
      ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
      ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
        dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
        sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
          sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x))) ∧
    (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0, ∀ q₁ q₂ : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q₁.val) = x →
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q₂.val) = x →
        S.rho q₁ ≤ 5 / 3 * S.rho q₂) :=
  ⟨portTable_prune_slot_BAUGC _ 0 _ _ Ψ Kint rpre pre ref href hrpre hpre,
    actualSlotsV2_cloud_subset_BAUGD S hΔ 0,
    portTable_dimension_BAUGC _ 0 _ _ Ψ Kint rpre pre ref href hrpre hpre
      (finrank_euclideanSpace_fin) Pc hM hOWN hQ,
    radius_mcb_of_scale_kept_BAUGC (actualSlotsV2_scale_kept_BAUGD S) hsg,
    preimage_comparable_of_scale_kept_BAUGC (actualSlotsV2_scale_kept_BAUGD S)⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
