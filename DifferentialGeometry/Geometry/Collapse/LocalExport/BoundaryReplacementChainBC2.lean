import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesRestBC2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEExits
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictECBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementClosedBCF2KApplications
import DifferentialGeometry.Geometry.Fibration.ActualSegmentLocalization
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesLocalizationCircle

/-!
# BCF02 (Repl_∂) on the production chain `BoundaryGaf02ChainE` (lane S-BCF02b, G2)

The chain-level strict replacement (frozen G5 `bcf02_strict_replacement_BCF2K`,
`TargetsBoundary-v3.2`): the EC-level kernel `LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K` is
bound to the actual final map `E = Ψ₂ ∘ Ψ₁ ∘ Ψ₀ ∘ F_∂` of an enhanced boundary chain, with
`π₂ = stageProj 1`, `u = edgeBlockU_BCF2K`, `v = edgeBlockV_BCF2K`.

* **FM, the boundary twin of GAF04 / GAF05's edge plateau**
  `BoundaryGaf02ChainE.edge_full_marker_BC2`: at a threshold-6 plateau point of a revised edge chart
  `j` (`|η_j| < 6Δ`, `t < 6Δ`), `v_j(π₂ E x) = ρ_j`. Route: the cutoff binding gives `ψ₁(g₁ x) = 1`;
  `current_input_tests_BAUGD` puts the stage input in the tube; (FM*) of `DP.edge_spec` gives the
  contributor input (`gaf03_input_BAUGC`); the generic locality `stage_output_marker_const_BC2`
  (CFS15's `locality_of_cloud_C15`) gives `v_j(a₁ z) = ρ_j` on `B(x, r_x)`; the generic
  `adjust_marker_eq_BC2` (A0, `adjustmentMap_apply_eq_GAF2`) carries the value to `g₂ x`, and the
  last stage keeps the `edgeB` block (`E_edge_marker_BC2`, `adjust_keeps_block_V2_BAUGD`);
* (ERR) `edge_err_BC2`: `|u_j(π₂ E x) − ρ_j η_j ζ_j| < c₂ρ(x)`;
* the kernel applied to the stored family, `strict_kernel_apply_BC2`, and the strict constants
  `bcf02SigmaStrict_BC2`, `bcf02EtaStrict_BC2` (chosen from the strict kernel; see the docstring);
* the vector bound `edge_vector_norm_lt_BC2` and **`bcf02_strict_replacement_BC2`**: the frozen G5
  statement with the strict kernel's constants.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- A scalar functional is unchanged by the projection onto the orthogonal complement of its
kernel. -/
theorem marker_proj_orth_ker_BC2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (v : H →L[ℝ] ℝ) (w : H) :
    v ((LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w) = v w := by
  have h : w - (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w ∈
      (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮᗮ :=
    Submodule.sub_starProjection_mem_orthogonal w
  rw [Submodule.orthogonal_orthogonal, LinearMap.mem_ker, map_sub] at h
  have h' : v w - v ((LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w) = 0 := h
  linarith

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- The stage adjustment keeps a scalar functional at the value `c` where the cutoff is one and
the projected smoothing value of the projected input has the value `c` (generic form). -/
theorem adjustmentMap_marker_BC2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (Q : Submodule ℝ H) (P : H → H) (hP : ∀ y, Q.starProjection y = P y)
    (a : H → H) (ψ : H → ℝ) (ℓ : H →L[ℝ] ℝ) (hJQ : ∀ y, ℓ (P y) = ℓ y) {y : H} {c : ℝ}
    (hy : ℓ (P (a (P y))) = c) (hψ : ψ y = 1) :
    ℓ (adjustmentMap Q (fun z => Q.starProjection (a z)) ψ y) = c := by
  refine adjustmentMap_apply_eq_GAF2 Q (fun z => Q.starProjection (a z)) ψ ℓ
    (fun z => (congrArg ℓ (hP z)).trans (hJQ z)) ?_ (Or.inl hψ)
  change ℓ (Q.starProjection (a (Q.starProjection y))) = c
  rw [hP, hP]
  exact hy

section Adjust

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

/-- The stage adjustment of `Φ` keeps a scalar functional at the value `c` where the cutoff is one
and the smoothing map of the projected input has the value `c`. -/
theorem adjust_marker_eq_BC2 (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
    (hJQ : ∀ y, ℓ (Φ.stageProj st y) = ℓ y)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} {c : ℝ}
    (hy : ℓ (Φ.stageProj st (a (Φ.stageProj st y))) = c) (hψ : Φ.cutoff st y = 1) :
    ℓ (Φ.adjust st a y) = c :=
  adjustmentMap_marker_BC2 (Φ.stageQ st) (Φ.stageProj st)
    (fun z => by rw [stageQ_starProjection_BAUGD]) a (Φ.cutoff st) ℓ hJQ hy hψ

end Adjust

/-- **GAF03 / GAF04 locality, generic form**: for a CFS15 stage output `O` and a scalar functional
`ℓ` with value `c` at the cloud point `x`, if every contributor `i` of the window of `x` has the
same marker-line projection as `x` and its plane in the line, then `ℓ ∘ a = c` on `B(x, r_x)`. -/
theorem stage_output_marker_const_BC2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {k Kj : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ}
    {P : H → Submodule ℝ H} (O : Cfs15StageOutput k Kj ε cw S T r P) (ℓ : H →L[ℝ] ℝ) {x : H}
    (hx : x ∈ S) {c : ℝ} (hvx : ℓ x = c)
    (hcontrib : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      (LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))ᗮ.starProjection i =
        (LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))ᗮ.starProjection x ∧
      P i ≤ (LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))ᗮᗮ) :
    ∀ z ∈ ball x (r x), ℓ (O.ambient z) = c := by
  intro z hz
  have h := congrArg ℓ ((O.locality_of_cloud_C15 hx (LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))ᗮ
    ((LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))ᗮ.starProjection x) hcontrib).2.2 z hz)
  rw [marker_proj_orth_ker_BC2, marker_proj_orth_ker_BC2] at h
  rw [h, hvx]

open Classical in
/-- **The EGP04 constant `σ` of the strict replacement kernel** (chosen once, for `Δ ≥ 2`, from
`LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K`; `1` otherwise). Not `bcf02Sigma_BCF2K`,
which is chosen from the E-free kernel and is not related to the strict kernel's `σ`. -/
def bcf02SigmaStrict_BC2 (Δ : ℝ) : ℝ :=
  if h : 2 ≤ Δ then Classical.choose (LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K h) else 1

open Classical in
/-- **The EGP04 constant `η` of the strict replacement kernel** (chosen with `σ`). -/
def bcf02EtaStrict_BC2 (Δ : ℝ) : ℝ :=
  if h : 2 ≤ Δ then
    Classical.choose (Classical.choose_spec
      (LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K h)).2.2
  else 1

theorem bcf02SigmaStrict_eq_BC2 {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    bcf02SigmaStrict_BC2 Δ =
      Classical.choose (LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K hΔ) := by
  unfold bcf02SigmaStrict_BC2
  rw [dite_eq_left hΔ]

theorem bcf02EtaStrict_eq_BC2 {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    bcf02EtaStrict_BC2 Δ = Classical.choose (Classical.choose_spec
      (LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K hΔ)).2.2 := by
  unfold bcf02EtaStrict_BC2
  rw [dite_eq_left hΔ]

section KernelApply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **The strict replacement kernel applied to the stored final family** (with the strict
constants):
for maps `E, π₂, u, v` with (ERR) and (FM), a point `q` of the edge chart `i` with `D(q) ≥ 35`
outside the zero balls and slim regions has a revised centre `j` with `|η_j(q)| < 2Δ`,
`ζ_j(q) = 1`, `v_j(π₂ E q) = ρ_j`. -/
theorem strict_kernel_apply_BC2 (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8)
    (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hn : 1140 * Δ ≤ 35 * (n : ℝ))
    (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hb : b < 1 / 1000000)
    (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000) {c₃ : ℝ} (hc₃ : c₃ ≤ Δ / 2)
    (hσL : (bcf02SigmaStrict_BC2 Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02EtaStrict_BC2 Δ)
    (h3b : 3 * b ≤ bcf02SigmaStrict_BC2 Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) {Y : Type}
    (E : W.pieceInterior ⊤ → Y) (π₂ : Y → Y) (u v : W.pieceInterior ⊤ → Y → ℝ)
    (hERR : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      ∀ j ∈ S.family.edgeB.centres, ∀ x, |u j (π₂ (E x)) -
        S.rho j * (S.family.edgeB.coord_BAUGA j x * S.family.edgeB.cutoff_BAUGA j x)| <
          c₃ * S.rho x)
    (hFM : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      ∀ j ∈ S.family.edgeB.centres, ∀ x, dist x j < 100 * Δ * S.rho j →
        |S.family.edgeB.coord_BAUGA j x| < 6 * Δ → S.family.edgeB.smoothing x / S.rho x < 6 * Δ →
          v j (π₂ (E x)) = S.rho j)
    {i : W.pieceInterior ⊤} {q : W.pieceInterior ⊤}
    (hi : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      i ∈ S.family.edgeB.centres)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q i < 100 * Δ * S.rho i)
    (hηq : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      |S.family.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ)
    (htq : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.smoothing q / S.rho q ≤ 401 / 100 * Δ)
    (hq35 : ENNReal.ofReal 35 ≤ distanceToBoundary W g q)
    (hZ : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ z (hz : z ∈ S.family.zero.centres),
        38 / 100 * (S.family.zero.zero z hz).radius ≤ dist q z)
    (hS : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      ∀ k (hk : k ∈ S.family.slim.centres), dist q k < 9 * Δ * S.rho k →
        10 * Δ ≤ |(S.family.slim.centre k hk).coord_BCG2 q|) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∃ j ∈ S.family.edgeB.centres, |S.family.edgeB.coord_BAUGA j q| < 2 * Δ ∧
      S.family.edgeB.cutoff_BAUGA j q = 1 ∧ v j (π₂ (E q)) = S.rho j := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hspec := Classical.choose_spec (LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K hΔ)
  have hη := Classical.choose_spec hspec.2.2
  rw [bcf02SigmaStrict_eq_BC2 hΔ] at hσL h3b
  rw [bcf02EtaStrict_eq_BC2 hΔ] at hbη
  obtain ⟨j, hj, hηj, hζj, hv, -⟩ := hη.2 W g S.completion.metric S.completion.inner_le S.rho
    S.rho_pos S.scale_spec.2.2.2.2 (c₃ := c₃) hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hc₃ hσL hbη
    h3b hbH hLΛ hμΔ oM S.family E π₂ u v hERR hFM i hi q hq hηq htq hq35 hZ hS
  exact ⟨j, hj, hηj, hζj, hv⟩

end KernelApply

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The marker entry `v_j` of the `edgeB` block is the marker functional of the edge marker
chart. -/
theorem edgeBlockV_eq_markerCLM_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeBlockV_BCF2K j y = S.markerCLM_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩)) y := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  unfold BoundarySupplyCore.edgeBlockV_BCF2K
  rw [dite_eq_left hj']
  rfl

include C in
/-- **The stage-one adjustment gives the marker value** (chain level): if the cutoff `ψ₁` is one at
`g₁ p` and `ℓ(a₁(π₁ g₁ p)) = c` for the smoothing map `a₁` of the slot, then `ℓ(g₂ p) = c` for a
functional `ℓ` kept by `π₁`. -/
theorem g₂_marker_BC2
    (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
    (hJQ : ∀ y, ℓ ((actualSlotsV2_BAUGD S).stageProj 1 y) = ℓ y) {p : W.Carrier} {c : ℝ}
    (hψ : (actualSlotsV2_BAUGD S).cutoff 1 (C.toChain.g₁ p) = 1)
    (hy : ℓ ((C.toChain.slot 1).map ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.g₁ p))) = c) :
    ℓ (C.toChain.g₂ p) = c :=
  adjust_marker_eq_BC2 (actualSlotsV2_BAUGD S) 1 (C.toChain.slot 1).map ℓ hJQ
    (by rw [hJQ]; exact hy) hψ

include C in
/-- **The final map keeps the `edgeB` marker of the second stage output**: the last adjustment
(stage three) never moves an `edgeB` block (A0). -/
theorem E_edge_marker_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    (p : W.Carrier) :
    S.edgeBlockV_BCF2K j (C.toChain.E p) = S.edgeBlockV_BCF2K j (C.toChain.g₂ p) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  have hkeep := adjust_keeps_block_V2_BAUGD S 2 (C.toChain.slot 2).map (C.toChain.g₂ p)
    (.inr (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩)))
    (S.edgeBTag_notMem_stageTagsV2_two_BAUGD _)
  unfold BoundarySupplyCore.edgeBlockV_BCF2K
  rw [dite_eq_left hj', dite_eq_left hj']
  exact congrArg Prod.snd (congrArg _ hkeep)

include C in
/-- **FM at the edge stage (boundary twin of GAF04 / GAF05's edge plateau)**: at a point `x` of the
threshold-6 plateau of a revised edge chart `j` (`|η_j(x)| < 6Δ`, `t(x) < 6Δ`) the final map has the
full marker `v_j(π₂ E x) = ρ_j`. -/
theorem edge_full_marker_BC2
    {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1) {x : W.pieceInterior ⊤}
    (hx : letI := inducedMetricSpace S.completion.metric; dist x j < 100 * Δ * S.rho j)
    (hη : |S.edgeEta_BIF j x| < 6 * Δ) (hh : S.edgeHeightRaw x < 6 * Δ) :
    S.edgeBlockV_BCF2K j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val)) = S.rho j := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  have hΔ0 : 0 < Δ := C.std.2.1
  have hmst : S.markerStage_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩) : S.MarkerIdx_BAUGC) = 1 := rfl
  rw [edgeBlockV_eq_markerCLM_BC2 hj]
  generalize hm : (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩) :
    S.MarkerIdx_BAUGC) = m at hmst ⊢
  have hmj : S.markerCentre_BAUGC m = j := by rw [← hm]; rfl
  have htag : S.markerTag_BAUGC m ∈ S.stageTagsV2_BAUGD 1 := by
    have h := S.markerTag_mem_stageTagsV2_BAUGD m
    rwa [hmst] at h
  have hJQ : ∀ y, S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).stageProj 1 y) =
      S.markerCLM_BAUGC m y := by
    intro y
    rw [markerCLM_stageProj_BAUGD, ite_eq_left htag]
  have hψ : (actualSlotsV2_BAUGD S).cutoff 1 (C.toChain.g₁ x.val) = 1 :=
    (C.toChain.cutoff_bindings).2.1.2.2.1 x ⟨j, hj, hx, hη, hh⟩
  have hψ' : (actualSlotsV2_BAUGD S).cutoff 1 (C.toChain.stage (Fin.castSucc 1) x.val) = 1 := hψ
  have hsupp : C.toChain.stage (Fin.castSucc 1) x.val ∈
      tsupport ((actualSlotsV2_BAUGD S).cutoff 1) :=
    subset_tsupport _ (by rw [Function.mem_support, hψ']; exact one_ne_zero)
  obtain ⟨-, hq⟩ := C.current_input_tests_BAUGD 1 x.val
  obtain ⟨q, hqx, hcore, hcloud, hr1, hr2, htube, -, -⟩ := hq hsupp
  have hqx' : q = x := Subtype.ext hqx
  subst hqx'
  have hp7 : q ∈ S.markerCore7_BAUGC m := by
    rw [← hm]
    exact ⟨hx, by linarith [abs_nonneg (S.edgeEta_BIF j q)], by linarith⟩
  have hvx : S.markerCLM_BAUGC m
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)) =
        S.rho (S.markerCentre_BAUGC m) := by
    rw [markerCLM_stageProj_BAUGD, ite_eq_left htag, S.markerCLM_boundaryOriginalMap_BAUGD,
      S.markerCutoffW_eq_one_of_core7_BAUGD hΔ0 m hp7, mul_one]
  obtain ⟨hΞ, hSg, -, -, hSgΞ, -⟩ := C.toChain.numbers.1 1
  have hcontrib := DP.edge_spec.gaf03_input_BAUGC hΞ hSg.le hSgΞ (Classical.arbitrary _) m hmst
    hp7 hvx
  obtain ⟨O, hO⟩ : ∃ O, C.toChain.slot 1 = .active O := by
    cases hs : C.toChain.slot 1 with
    | active O => exact ⟨O, rfl⟩
    | inactive hc he => exact absurd hcore (by rw [hc]; exact notMem_empty _)
  have hmap : (C.toChain.slot 1).map = O.ambient := by rw [hO]; rfl
  have hrpos : 0 < DP.stageRadius 1 (Sg 1)
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)) := by
    have : 0 < Sg 1 * S.rho q := mul_pos hSg (S.rho_pos q.val)
    linarith [hr1]
  have hz : (actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.stage (Fin.castSucc 1) q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))
        (DP.stageRadius 1 (Sg 1)
          ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))) := by
    rw [mem_ball, dist_eq_norm]
    linarith [htube]
  have hz2 : S.markerCLM_BAUGC m (O.ambient
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.stage (Fin.castSucc 1) q.val))) =
        S.rho (S.markerCentre_BAUGC m) :=
    stage_output_marker_const_BC2 O (S.markerCLM_BAUGC m) hcloud hvx hcontrib _ hz
  rw [hmj] at hz2
  have hy : S.markerCLM_BAUGC m ((C.toChain.slot 1).map
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.g₁ q.val))) = S.rho j := by
    rw [hmap]
    exact hz2
  have hg2 := C.g₂_marker_BC2 (S.markerCLM_BAUGC m) hJQ hψ hy
  have hE := C.E_edge_marker_BC2 hj q.val
  rw [edgeBlockV_eq_markerCLM_BC2 hj, edgeBlockV_eq_markerCLM_BC2 hj, hm] at hE
  rw [hJQ, hE, hg2]

/-- A stage projection keeps the block of a stage tag. -/
theorem stageProj_block_BC2 (st : Fin 3) {t : S.IntTag_BAUGA} (ht : t ∈ S.stageTagsV2_BAUGD st)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).stageProj st y (Sum.inl t) = y (Sum.inl t) := by
  have hiff : (Sum.inl t : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug st ↔ t ∈ S.stageTagsV2_BAUGD st :=
    Finset.inl_mem_disjSum
  simp only [BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hiff.mpr ht, ite_true]

/-- The tangential entry `u_j` of the `edgeB` block is the first coordinate of the block vector. -/
theorem edgeBlockU_eq_vector_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeBlockU_BCF2K j y = (blockVectorCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
      y) 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  unfold BoundarySupplyCore.edgeBlockU_BCF2K
  rw [dite_eq_left hj']
  rfl

/-- The block vector has norm at most that of the whole point. -/
theorem norm_blockVector_le_BC2 (t : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y‖ ≤ ‖y‖ := by
  have h := ContinuousLinearMap.le_of_opNorm_le
    (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t)
    (norm_blockVectorCLM_le (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t) y
  rwa [one_mul] at h

/-- The block vector of `y` is at most that of `y'` plus the distance `‖y - y'‖`. -/
theorem norm_vector_le_add_BC2 (t : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count)
    (y y' : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y‖ ≤
      ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y'‖ +
        ‖y - y'‖ := by
  have h := norm_blockVector_le_BC2 t (y - y')
  rw [map_sub] at h
  calc _ = ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y' +
        (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y -
          blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y')‖ := by
        rw [add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem abs_vector_sub_le_BC2 (t : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count)
    (y y' : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    |(blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y).ofLp 0 -
      (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y').ofLp 0| ≤
        ‖y - y'‖ := by
  have h := norm_blockVector_le_BC2 t (y - y')
  rw [map_sub] at h
  refine le_trans ?_ h
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (blockVectorCLM
    (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y -
    blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) t y') 0

/-- The tangential entry changes by at most the distance. -/
theorem abs_edgeBlockU_sub_le_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    (y y' : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    |S.edgeBlockU_BCF2K j y - S.edgeBlockU_BCF2K j y'| ≤ ‖y - y'‖ := by
  rw [edgeBlockU_eq_vector_BC2 hj, edgeBlockU_eq_vector_BC2 hj]
  exact abs_vector_sub_le_BC2 _ y y'

include C in
/-- **(ERR) for the final map**: `|u_j(π₂ E x) − ρ_j η_j ζ_j| < c₂ ρ(x)` (stage three moves a point
by less than `c₂ρ`, `u_j(F_∂) = ρ_j η_j ζ_j`, the block is kept by `π₂`). -/
theorem edge_err_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    |S.edgeBlockU_BCF2K j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val)) -
        S.rho j * (S.family.edgeB.coord_BAUGA j x * S.family.edgeB.cutoff_BAUGA j x)| <
      c 2 * S.rho x := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  have hmst : S.markerStage_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩) : S.MarkerIdx_BAUGC) = 1 := rfl
  have htag : S.markerTag_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩) : S.MarkerIdx_BAUGC) ∈
        S.stageTagsV2_BAUGD 1 := by
    have h := S.markerTag_mem_stageTagsV2_BAUGD
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩) : S.MarkerIdx_BAUGC)
    rwa [hmst] at h
  have hproj : S.edgeBlockU_BCF2K j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val)) =
      S.edgeBlockU_BCF2K j (C.toChain.E x.val) := by
    rw [edgeBlockU_eq_vector_BC2 hj, edgeBlockU_eq_vector_BC2 hj, blockVectorCLM_apply,
      blockVectorCLM_apply, stageProj_block_BC2 1 htag]
  have horig := ((S.edgeBlock_boundaryOriginalMap_BCF2K x j) hj').1
  have herr := C.stage_error_lt_BAUGD 2 x.val
  have hsub := abs_edgeBlockU_sub_le_BC2 hj (C.toChain.E x.val) (S.boundaryOriginalMap x.val)
  rw [hproj, ← horig]
  exact lt_of_le_of_lt hsub herr

/-- **The `edgeB` block vector of `F_∂`**: `ρ_j ζ_j • (η_j, 0)`. -/
theorem edgeVector_original_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
      (S.boundaryOriginalMap x.val) =
        (S.rho j * S.family.edgeB.cutoff_BAUGA j x) •
          planeAxis (S.family.edgeB.coord_BAUGA j x) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hslot : ∀ t : S.IntTag_BAUGA,
      S.boundaryOriginalMap x.val (Sum.inl t) = S.interiorMapOn_BAUGA x t := by
    intro t
    change S.interiorMapW_BAUGA x.val t = _
    rw [S.interiorMapW_val_BAUGA x]
  rw [blockVectorCLM_apply, hslot]
  rfl

include C in
/-- **The final block vector is short on a plateau**: `ζ_j(x) = 1`, `|η_j(x)| < 2Δ` give
`‖vec_j(π₂ E x)‖ < 3Δρ_j` (`‖E − F_∂‖ ≤ ρ_j/400`, `Δ ≥ 2`). -/
theorem edge_vector_norm_lt_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1)
    {x : W.pieceInterior ⊤}
    (hζ : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.cutoff_BAUGA j x = 1)
    (hη : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      |S.family.edgeB.coord_BAUGA j x| < 2 * Δ) (hΔ : 2 ≤ Δ) :
    ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val))‖ < 3 * Δ * S.rho j := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hr := S.rho_pos j
  have hmst : S.markerStage_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) : S.MarkerIdx_BAUGC) = 1 := rfl
  have htag : S.markerTag_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) : S.MarkerIdx_BAUGC) ∈
        S.stageTagsV2_BAUGD 1 := by
    have h := S.markerTag_mem_stageTagsV2_BAUGD
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) : S.MarkerIdx_BAUGC)
    rwa [hmst] at h
  have hpos : 0 < S.markerCutoffW_BAUGD
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) : S.MarkerIdx_BAUGC) x.val := by
    rw [S.markerCutoffW_val_BAUGD]
    change 0 < S.family.edgeB.cutoff_BAUGA j x
    rw [hζ]
    exact one_pos
  have herr := C.final_err_le_BBP
    (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) : S.MarkerIdx_BAUGC) hpos
  have hF := edgeVector_original_BC2 hj x
  have hproj : blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val)) =
      blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
      (C.toChain.E x.val) := by
    rw [blockVectorCLM_apply, blockVectorCLM_apply, stageProj_block_BC2 1 htag]
  have hsum := norm_vector_le_add_BC2
    (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
    (C.toChain.E x.val) (S.boundaryOriginalMap x.val)
  rw [hproj]
  have hnorm : ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.markerTag_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))
      (S.boundaryOriginalMap x.val)‖ = S.rho j * |S.family.edgeB.coord_BAUGA j x| := by
    rw [hF, hζ, mul_one, norm_smul, norm_planeAxis, Real.norm_eq_abs, abs_of_pos hr]
  have hρm : S.rho (S.markerCentre_BAUGC
      (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) : S.MarkerIdx_BAUGC)) =
      S.rho j := rfl
  rw [hρm] at herr
  rw [hnorm] at hsum
  nlinarith [mul_lt_mul_of_pos_left hη hr, hsum, herr]

variable {Bs : BoundaryGaf02BasesV2 C.toChain}

include C in
/-- **BCF02 (Repl_∂) on the production chain, EC instantiated** (frozen G5,
`bcf02_strict_replacement_BCF2K` of `TargetsBoundary-v3.2`, with the strict kernel's own EGP04
constants): for `q ∈ M₂` in the edge chart `i` with `|η_i(q)|, t(q) ≤ 4.01Δ`, a marker chart `m` of
stage two (an `edgeB` centre `j`) has `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`, the full marker
`v_j(π₂ E q) = ρ_j` and `‖vec_j(π₂ E q)‖/ρ_j < 3Δ`. -/
theorem bcf02_strict_replacement_BC2 (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02SigmaStrict_BC2 Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02EtaStrict_BC2 Δ)
    (h3b : 3 * b ≤ bcf02SigmaStrict_BC2 Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) :
    letI := inducedMetricSpace S.completion.metric
    ∀ q : W.pieceInterior ⊤, q.val ∈ Kc.M₂ → ∀ i ∈ S.stageCentres_BIF 1,
      dist q i < 100 * Δ * S.rho i → |S.edgeEta_BIF i q| ≤ 401 / 100 * Δ →
      S.edgeHeightRaw q ≤ 401 / 100 * Δ →
      ∃ m : S.MarkerIdx_BAUGC, S.markerStage_BAUGC m = 1 ∧
        |S.edgeEta_BIF (S.markerCentre_BAUGC m) q| < 2 * Δ ∧
        S.intCutoff_BAUGA (S.markerTag_BAUGC m) q = 1 ∧
        blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
            (Sum.inl (S.markerTag_BAUGC m)) (C.toChain.stageMap 1 q.val) =
          S.rho (S.markerCentre_BAUGC m) ∧
        ‖blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
            (Sum.inl (S.markerTag_BAUGC m)) (C.toChain.stageMap 1 q.val)‖ /
              S.rho (S.markerCentre_BAUGC m) < 3 * Δ := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro q hqM i hi hqi hηi hhi
  have hΔ0 : 0 < Δ := by linarith
  have hc₃ : c 2 ≤ Δ / 2 := by linarith [C.c_two_le_BBP]
  have heta : ∀ j, j ∈ S.stageCentres_BIF 1 → ∀ x : W.pieceInterior ⊤,
      S.edgeEta_BIF j x = S.family.edgeB.coord_BAUGA j x := by
    intro j hj x
    have hj' : j ∈ S.family.edgeB.centres := hj
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left hj', S.family.edgeB.coord_BAUGA_of_mem hj']
  have hERR : ∀ j ∈ S.family.edgeB.centres, ∀ x : W.pieceInterior ⊤,
      |S.edgeBlockU_BCF2K j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val)) -
        S.rho j * (S.family.edgeB.coord_BAUGA j x * S.family.edgeB.cutoff_BAUGA j x)| <
          c 2 * S.rho x := fun j hj x => C.edge_err_BC2 hj x
  have hFM : ∀ j ∈ S.family.edgeB.centres, ∀ x : W.pieceInterior ⊤,
      dist x j < 100 * Δ * S.rho j → |S.family.edgeB.coord_BAUGA j x| < 6 * Δ →
        S.family.edgeB.smoothing x / S.rho x < 6 * Δ →
        S.edgeBlockV_BCF2K j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E x.val)) =
          S.rho j := by
    intro j hj x hx hη hh
    exact C.edge_full_marker_BC2 hj hx (by rw [heta j hj]; exact hη) hh
  have h35 : ENNReal.ofReal 35 ≤ distanceToBoundary W g q := Kc.M₂_subset_D35_BCF hqM
  have hZ := Kc.zero_exclusion_of_mem_M₂_BCF Z q hqM
  have hS := Kc.slim_exclusion_of_mem_M₂_BCF hΔ0.le hσs q hqM
  obtain ⟨j, hj, hηj, hζj, hv⟩ := strict_kernel_apply_BC2 S hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs
    hβ2 hc₃ hσL hbη h3b hbH hLΛ hμΔ (fun x : W.pieceInterior ⊤ => C.toChain.E x.val)
    ((actualSlotsV2_BAUGD S).stageProj 1) S.edgeBlockU_BCF2K S.edgeBlockV_BCF2K hERR hFM hi hqi
    (by rw [← heta i hi]; exact hηi) hhi h35 hZ hS
  refine ⟨Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩), rfl, ?_, ?_, ?_, ?_⟩
  · change |S.edgeEta_BIF j q| < 2 * Δ
    rw [heta j hj]
    exact hηj
  · exact hζj
  · have hjs : j ∈ S.stageCentres_BIF 1 := hj
    change S.markerCLM_BAUGC (Sum.inr (Sum.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E q.val)) = S.rho j
    rw [← edgeBlockV_eq_markerCLM_BC2 hjs]
    exact hv
  · have hjs : j ∈ S.stageCentres_BIF 1 := hj
    exact (div_lt_iff₀ (S.rho_pos j)).mpr (C.edge_vector_norm_lt_BC2 hjs hζj hηj hΔ)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
