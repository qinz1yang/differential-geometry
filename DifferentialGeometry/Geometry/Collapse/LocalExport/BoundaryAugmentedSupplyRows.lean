import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedModelTable
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedModelCircle

/-!
# BCG03: the augmented model table bound to the stored supply (lane BAUG-C, G1b)

Draft 61 §1.4, §2.5; dispositions D61-3, D61-5, D61-6. G1 (`BoundaryAugmentedModelTable.lean`)
built the augmented reference model generically in the interior model table. Here it is bound to
the ACTUAL supply `S : BoundarySupply` and to BIFACE's stage tables
`BoundaryStageReferences_BIF Φ st E eta row` (rows `S.circleRow_BIF`, `S.edgeRow_BIF`,
`S.slimRow_BIF` = the ONE row / sign of `S.ba_spec`, never re-chosen; lists
`S.boundaryList_BIF st a` = BCG-8b's two-sided whole lists at `C_a ρ(a)`):

* the rows have norm `≤ 1` (`norm_circleRow_BIF_le_BAUGC`, `norm_edgeRow_BIF_le_BAUGC`,
  `norm_slimRow_BIF_le_BAUGC`; `0` off the list);
* on the list, the stored row carries BOTH (BA) errors of `S.ba_spec` on the whole comparison domain
  `D_a` (value `circleRow_BIF_value_BAUGC` / `edgeRow_BIF_value_BAUGC` / `slimRow_BIF_value_BAUGC`,
  differential `circleRow_BIF_deriv_BAUGC` / `edgeRow_BIF_deriv_BAUGC` /
  `slimRow_BIF_deriv_BAUGC`);
* **the model binding** (`BoundaryStageReferences_BIF.model_eq_augmented_BAUGC`): at every centre
  `a` the stored model is G1's augmented (BM) model
  `Φ^∂_a = augmentedModel_BAUGC (pr_int ∘ Φ_a) J_∂(a) (bmBlocks_BAUGC (η_b(a)) ρ(a) A_a η_a(a))`;
* consumer (D61-5 on the stored model slots): `‖D(Φ^∂_a)_b‖ ≤ 2P_*` for every stage table whose rows
  have norm `≤ 1` (`norm_fderiv_model_slot_le_BAUGC`), instantiated on the three tables of a
  `BoundaryAugmentedData` (`BoundaryAugmentedData.norm_fderiv_model_slot_le_BAUGC`).
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

/-- `ContinuousSMul` on one block `WithLp 2 (ℝ² × ℝ)`, as a named local instance (the default
search times out; protocol pitfall, lane C14-KA6). -/
local instance instContinuousSMulPlaneBlock_BAUGC :
    ContinuousSMul ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  IsBoundedSMul.continuousSMul

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-! ### The stored rows have norm at most one -/

/-- The circle row `proj₀ ∘ A_b` of `S.ba_spec` has norm `≤ 1` (`0` off the list). -/
theorem norm_circleRow_BIF_le_BAUGC (j : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count) :
    ‖S.circleRow_BIF j i‖ ≤ 1 := by
  unfold circleRow_BIF
  split_ifs with h
  · exact norm_circleRow_le_one_BCG8b _ (Classical.choose_spec (S.ba_spec.1 j h.1 i h.2)).1
  · rw [norm_zero]
    exact zero_le_one

/-- The sign row `a • id` (`a = ±1`) has norm `≤ 1`. -/
theorem norm_signRow_le_BAUGC {a : ℝ} (ha : a = 1 ∨ a = -1) :
    ‖a • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
  refine (norm_smul_le a _).trans ?_
  have h1 : ‖a‖ = 1 := by rcases ha with rfl | rfl <;> simp
  rw [h1, one_mul]
  exact ContinuousLinearMap.norm_id_le

/-- The revised-edge row of `S.ba_spec` has norm `≤ 1` (`0` off the list). -/
theorem norm_edgeRow_BIF_le_BAUGC (j : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count) :
    ‖S.edgeRow_BIF j i‖ ≤ 1 := by
  unfold edgeRow_BIF
  split_ifs with h
  · exact norm_signRow_le_BAUGC (Classical.choose_spec (S.ba_spec.2.1 j h.1 i h.2)).1
  · rw [norm_zero]
    exact zero_le_one

/-- The slim row of `S.ba_spec` has norm `≤ 1` (`0` off the list). -/
theorem norm_slimRow_BIF_le_BAUGC (j : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count) :
    ‖S.slimRow_BIF j i‖ ≤ 1 := by
  unfold slimRow_BIF
  split_ifs with h
  · exact norm_signRow_le_BAUGC (Classical.choose_spec (S.ba_spec.2.2 j h.1 i h.2)).1
  · rw [norm_zero]
    exact zero_le_one

/-! ### (BA) with the stored rows on the two-sided whole lists -/

/-- The first coordinate of `single 0 U − v` in `ℝ¹` is controlled by its norm. -/
theorem abs_sub_proj_le_norm_BAUGC (U : ℝ) (v : EuclideanSpace ℝ (Fin 1)) :
    |U - (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) v| ≤
      ‖EuclideanSpace.single 0 U - v‖ := by
  have h := PiLp.norm_apply_le (EuclideanSpace.single 0 U - v) 0
  rw [Real.norm_eq_abs] at h
  convert h using 2
  simp

/-- **Circle (BA), value**: on the list `J_∂(j)` (two-sided, at `10ρ(j)`) the stored row
`S.circleRow_BIF j i` has value error `< θ` on the whole domain `D_j = B(j, 10ρ(j))`. -/
theorem circleRow_BIF_value_BAUGC {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 0)
    {i : Fin S.packet.cusp.count} (hi : i ∈ S.boundaryList_BIF 0 j) :
    letI := inducedMetricSpace S.completion.metric
    ∀ y : W.pieceInterior ⊤, dist y j < 10 * S.rho j →
      |(S.packet.height i y - S.packet.height i j) / S.rho j -
        S.circleRow_BIF j i (S.circleEta_BIF j y - S.circleEta_BIF j j)| < θ := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.forgetBFR_BFZD.circle.centres := hj
  have hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g j.val x < ENNReal.ofReal (10 * S.rho j) :=
    BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mp hi
  have hrow : S.circleRow_BIF j i = (EuclideanSpace.proj (0 : Fin 1)).comp
      (Classical.choose (S.ba_spec.1 j hj' i hmeet)) := by
    unfold circleRow_BIF
    rw [dite_eq_left ⟨hj', hmeet⟩]
  have heta : S.circleEta_BIF j =
      (let c := S.family.forgetBFR_BFZD.circle.chart j hj'
       letI := (inducedMetricSpace S.completion.metric).rescale (S.rho j)⁻¹
         (inv_pos.mpr (S.rho_pos j))
       c.coord) := by
    unfold BoundarySupplyCore.circleEta_BIF
    rw [dite_eq_left (show j ∈ S.family.circle.centres from hj)]
    rfl
  intro y hy
  rw [hrow, heta]
  exact lt_of_le_of_lt (abs_sub_proj_le_norm_BAUGC _ _)
    ((Classical.choose_spec (S.ba_spec.1 j hj' i hmeet)).2.1 y hy)

/-- **Circle (BA), differential**: on the list, the stored row has differential error `< θ` (in the
units of `ρ(j)⁻²ĝ`) on the whole domain `D_j`. -/
theorem circleRow_BIF_deriv_BAUGC {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 0)
    {i : Fin S.packet.cusp.count} (hi : i ∈ S.boundaryList_BIF 0 j) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x : W.pieceInterior ⊤, dist x j < 10 * S.rho j → ∃ θ' < θ,
      ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3)
            (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i j) / S.rho j)
            x u - S.circleRow_BIF j i (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF j) x u)| ≤
          θ' * Real.sqrt ((scaleMetric ((S.rho j)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (S.rho_pos j)) 2) S.completion.metric).inner x u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.forgetBFR_BFZD.circle.centres := hj
  have hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g j.val x < ENNReal.ofReal (10 * S.rho j) :=
    BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mp hi
  have hrow : S.circleRow_BIF j i = (EuclideanSpace.proj (0 : Fin 1)).comp
      (Classical.choose (S.ba_spec.1 j hj' i hmeet)) := by
    unfold circleRow_BIF
    rw [dite_eq_left ⟨hj', hmeet⟩]
  have heta : S.circleEta_BIF j =
      (let c := S.family.forgetBFR_BFZD.circle.chart j hj'
       letI := (inducedMetricSpace S.completion.metric).rescale (S.rho j)⁻¹
         (inv_pos.mpr (S.rho_pos j))
       c.coord) := by
    unfold BoundarySupplyCore.circleEta_BIF
    rw [dite_eq_left (show j ∈ S.family.circle.centres from hj)]
    rfl
  intro x hx
  rw [hrow, heta]
  exact (Classical.choose_spec (S.ba_spec.1 j hj' i hmeet)).2.2 x hx

/-- **Revised-edge (BA), value and differential**: on the list `J_∂(j)` (at `20Δρ(j)`) the stored
sign row `S.edgeRow_BIF j i` has both errors `< θ` on `D_j = B(j, 20Δρ(j))`. -/
theorem edgeRow_BIF_value_deriv_BAUGC {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    {i : Fin S.packet.cusp.count} (hi : i ∈ S.boundaryList_BIF 1 j) :
    letI := inducedMetricSpace S.completion.metric
    (∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * S.rho j →
      |(S.packet.height i y - S.packet.height i j) / S.rho j -
        S.edgeRow_BIF j i (S.edgeEta_BIF j y - S.edgeEta_BIF j j)| < θ) ∧
    ∀ x : W.pieceInterior ⊤, dist x j < 20 * Δ * S.rho j → ∃ θ' < θ,
      ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3)
            (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i j) / S.rho j)
            x u - S.edgeRow_BIF j i (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF j) x u)| ≤
          θ' * Real.sqrt ((scaleMetric ((S.rho j)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (S.rho_pos j)) 2) S.completion.metric).inner x u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.forgetBFR_BFZD.edgeB.centres := hj
  have hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * S.rho j) :=
    BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mp hi
  have hrow : S.edgeRow_BIF j i =
      Classical.choose (S.ba_spec.2.1 j hj' i hmeet) • ContinuousLinearMap.id ℝ ℝ := by
    unfold edgeRow_BIF
    rw [dite_eq_left ⟨hj', hmeet⟩]
  have heta : S.edgeEta_BIF j = S.family.forgetBFR_BFZD.edgeB.coord_BCG1 j hj' := by
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left (show j ∈ S.family.edgeB.centres from hj)]
    rfl
  have hspec := Classical.choose_spec (S.ba_spec.2.1 j hj' i hmeet)
  rw [hrow, heta]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · exact hspec.2.1 y hy
  · obtain ⟨θ', hθ', hu⟩ := hspec.2.2 x hx
    exact ⟨θ', hθ', hu⟩

/-- **Slim (BA), value and differential**: on the list `J_∂(j)` (at `950000Δρ(j)`) the stored sign
row `S.slimRow_BIF j i` has both errors `< θ` on `D_j = B(j, 950000Δρ(j))`. -/
theorem slimRow_BIF_value_deriv_BAUGC {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 2)
    {i : Fin S.packet.cusp.count} (hi : i ∈ S.boundaryList_BIF 2 j) :
    letI := inducedMetricSpace S.completion.metric
    (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * S.rho j →
      |(S.packet.height i y - S.packet.height i j) / S.rho j -
        S.slimRow_BIF j i (S.slimEta_BIF j y - S.slimEta_BIF j j)| < θ) ∧
    ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * S.rho j → ∃ θ' < θ,
      ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3)
            (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i j) / S.rho j)
            x u - S.slimRow_BIF j i (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF j) x u)| ≤
          θ' * Real.sqrt ((scaleMetric ((S.rho j)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (S.rho_pos j)) 2) S.completion.metric).inner x u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.forgetBFR_BFZD.slim.centres := hj
  have hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * S.rho j) :=
    BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mp hi
  have hrow : S.slimRow_BIF j i =
      Classical.choose (S.ba_spec.2.2 j hj' i hmeet) • ContinuousLinearMap.id ℝ ℝ := by
    unfold slimRow_BIF
    rw [dite_eq_left ⟨hj', hmeet⟩]
  have heta : S.slimEta_BIF j = (S.family.forgetBFR_BFZD.slim.centre j hj').coord_BCG2 := by
    unfold BoundarySupplyCore.slimEta_BIF
    rw [dite_eq_left (show j ∈ S.family.slim.centres from hj)]
    rfl
  have hspec := Classical.choose_spec (S.ba_spec.2.2 j hj' i hmeet)
  rw [hrow, heta]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · exact hspec.2.1 y hy
  · obtain ⟨θ', hθ', hu⟩ := hspec.2.2 x hx
    exact ⟨θ', hθ', hu⟩

end BoundarySupply

/-! ### The stored model is the augmented (BM) model of G1 -/

section Binding

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}

/-- **The model binding** (D61-5, D61-6): at every centre `a` of the stage, the stored model of the
stage table is G1's augmented model with the interior part `pr_int ∘ Φ_a`, the two-sided whole list
`J_∂(a)` and the (BM) blocks `R_a⁻¹𝓑(η_b(a) + R_a A_{a,b}(z − η_a(a)))` of the stored rows. -/
theorem BoundaryStageReferences_BIF.model_eq_augmented_BAUGC
    (R : BoundaryStageReferences_BIF Φ st E eta row) {a : W.pieceInterior ⊤}
    (ha : a ∈ S.stageCentres_BIF st) :
    R.planes.model a = augmentedModel_BAUGC (augIntProjCLM_BAUGC ∘ R.planes.model a)
      (S.boundaryList_BIF st a)
      (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a)) := by
  funext z
  refine PiLp.ext fun t => ?_
  rcases t with t | i
  · rfl
  · rw [augmentedModel_apply_inr_BAUGC]
    by_cases hi : i ∈ S.boundaryList_BIF st a
    · rw [R.model_listed a ha i hi z, augmentedBlocks_of_mem_BAUGC _ hi]
      rfl
    · rw [R.model_unlisted a ha i hi z, augmentedBlocks_of_notMem_BAUGC _ hi, Pi.zero_apply,
        map_zero]

/-- The slot of a stored model: `(Φ^∂_a)_b = planeEmbed((BM) block)` on the list, `0` off it. -/
theorem BoundaryStageReferences_BIF.model_slot_eq_BAUGC
    (R : BoundaryStageReferences_BIF Φ st E eta row) {a : W.pieceInterior ⊤}
    (ha : a ∈ S.stageCentres_BIF st) (i : Fin S.packet.cusp.count) :
    (fun z => R.planes.model a z (Sum.inr i)) = fun z => planeBlockEmbed_BAUGA
      (augmentedBlocks_BAUGC (S.boundaryList_BIF st a)
        (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a)) i z) := by
  funext z
  rw [R.model_eq_augmented_BAUGC ha]
  rfl

/-- The plane encoding as an operator: `‖planeEmbed ∘ T‖ ≤ 2‖T‖`. -/
theorem norm_planeBlockEmbed_comp_le_BAUGC (Tb : E →L[ℝ] ℝ × ℝ) :
    ‖planeBlockEmbed_BAUGA.comp Tb‖ ≤ 2 * ‖Tb‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [ContinuousLinearMap.comp_apply]
  refine (norm_planeBlockEmbed_le_BAUGC (Tb w)).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (Tb.le_opNorm w) zero_le_two

/-- **Consumer: D61-5 on the stored model slots.** For a stage table whose rows have norm `≤ 1` and
BCG.0's `P_*`, every boundary slot of the stored model at a centre has `‖D(Φ^∂_a)_b‖ ≤ 2P_*`
(the marker `1/R_a` never enters; unlisted slots have derivative `0`). -/
theorem BoundaryStageReferences_BIF.norm_fderiv_model_slot_le_BAUGC
    (R : BoundaryStageReferences_BIF Φ st E eta row) {P : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) (hrow : ∀ a i, ‖row a i‖ ≤ 1)
    {a : W.pieceInterior ⊤} (ha : a ∈ S.stageCentres_BIF st) (i : Fin S.packet.cusp.count)
    (z : E) : ‖fderiv ℝ (fun z => R.planes.model a z (Sum.inr i)) z‖ ≤ 2 * P := by
  rw [R.model_slot_eq_BAUGC ha i]
  have hP0 := nonneg_of_boundaryBlock_bound_BCG8b hP
  by_cases hi : i ∈ S.boundaryList_BIF st a
  · simp only [augmentedBlocks_of_mem_BAUGC _ hi]
    have hd := (hasFDerivAt_boundaryModel_BCG8b (S.packet.height i a) (S.rho_pos a).ne' (row a i)
      (eta a a) z).differentiableAt
    rw [show (fun z => planeBlockEmbed_BAUGA (bmBlocks_BAUGC (fun i => S.packet.height i a)
        (S.rho a) (row a) (eta a a) i z)) = planeBlockEmbed_BAUGA ∘
        boundaryModel_BCG8b (S.packet.height i a) (S.rho a) (row a i) (eta a a) from rfl,
      (planeBlockEmbed_BAUGA.hasFDerivAt.comp z hd.hasFDerivAt).fderiv]
    refine (norm_planeBlockEmbed_comp_le_BAUGC _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_fderiv_boundaryModel_le_BCG8b hP _
      (S.rho_pos a).ne' (hrow a i) _ _) zero_le_two
  · simp only [augmentedBlocks_of_notMem_BAUGC _ hi, Pi.zero_apply, map_zero, fderiv_const_apply,
      norm_zero]
    positivity

end Binding

namespace BoundaryAugmentedData

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

/-- **Consumer on the three stored tables**: for every `D : BoundaryAugmentedData S Φ`, every stage
centre and every boundary component, the boundary slot of the stored circle / edge / slim model has
derivative norm `≤ 2P_*` (the rows are those of `S.ba_spec`). -/
theorem norm_fderiv_model_slot_le_BAUGC (D : BoundaryAugmentedData S Φ) {P : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) (i : Fin S.packet.cusp.count) :
    (∀ a ∈ S.stageCentres_BIF 0, ∀ z : ℝ²,
      ‖fderiv ℝ (fun z => D.circle.planes.model a z (Sum.inr i)) z‖ ≤ 2 * P) ∧
    (∀ a ∈ S.stageCentres_BIF 1, ∀ z : ℝ,
      ‖fderiv ℝ (fun z => D.edge.planes.model a z (Sum.inr i)) z‖ ≤ 2 * P) ∧
    ∀ a ∈ S.stageCentres_BIF 2, ∀ z : ℝ,
      ‖fderiv ℝ (fun z => D.slim.planes.model a z (Sum.inr i)) z‖ ≤ 2 * P :=
  ⟨fun _ ha z => D.circle.norm_fderiv_model_slot_le_BAUGC hP S.norm_circleRow_BIF_le_BAUGC ha i z,
    fun _ ha z => D.edge.norm_fderiv_model_slot_le_BAUGC hP S.norm_edgeRow_BIF_le_BAUGC ha i z,
    fun _ ha z => D.slim.norm_fderiv_model_slot_le_BAUGC hP S.norm_slimRow_BIF_le_BAUGC ha i z⟩

end BoundaryAugmentedData

end DifferentialGeometry.Geometry.Collapse
