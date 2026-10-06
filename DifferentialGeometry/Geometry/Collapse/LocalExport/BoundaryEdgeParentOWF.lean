import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreLevelOWF

/-!
# O-WF G6c (part 2): the open edge parent `U = f₁⁻¹(O₁) ∩ {T < 4.1Δ}` maps into the edge base

The open parent data `(U, hU, hcut, hsub, hrk)` of the A4 assembly
(`exists_boundaryGaf02BasesV2b_of_parts_BAUGD`), with the parent
`U = C.edgeParentSet_OWF = {p | f₁ p ∈ O₁, T p < 4.1Δ}` (a sub-parent of S-BASES-PORT2's
`edgeParentSet_BBP`, threshold `5Δ`):

* `isOpen_edgeParentSet_OWF`, `baseSource_one_eq_edgeParent_OWF` (`X₁ = U ∩ {T ≤ 4Δ}`),
  `edgeParent_rank_OWF` (`rank df₁ = 1` on `U`, from `edgeParent_rank_BBP`);
* `edge_loc41_OWF`: a point of `U` in the piece of chart `j` lies in the original source `Y_j`
  (S-BASES-PORT2's threshold-`5Δ` localization and EDP03's (EH) band);
* **`edgeParent_sub_OWF`** (`hsub`): `U ⊆ f₁⁻¹(B₁)`. For `p ∈ U` with `T(p) = 4Δ + δ`,
  `0 < δ < Δ/10`, the adjusted disk `D(a, δ)` at `a = κ_j(f₁ p)` is preconnected, contains `p` and
  the nonempty disk `D(a, 0)`; the native map is constant on it (`edge_native_const_OWF`), so
  `f₁ p = f₁ q₀` for a point `q₀ ∈ D(a, 0) ⊆ X₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The open edge parent** `U = f₁⁻¹(O₁) ∩ {T < 4.1Δ}`. -/
def edgeParentSet_OWF : Set W.Carrier :=
  {p | C.toChain.stageMap 1 p ∈ S.ratioSet_BBP 1 ∧ C.toChain.heightRatio p < 41 / 10 * Δ}

include C in
/-- `U` is open. -/
theorem isOpen_edgeParentSet_OWF : IsOpen C.edgeParentSet_OWF :=
  ((S.isOpen_ratioSet_BBP 1).preimage (C.continuous_stageMap_V2_BAUGD 1)).inter
    (isOpen_lt C.continuous_heightRatio_BAUGD continuous_const)

include C in
/-- **`X₁ = U ∩ {T ≤ 4Δ}`** (the `hcut` argument). -/
theorem baseSource_one_eq_edgeParent_OWF : C.baseSource_BBP 1 =
    C.edgeParentSet_OWF ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} := by
  obtain ⟨-, hΔ, -⟩ := C.std
  ext p
  constructor
  · rintro ⟨hp, hT⟩
    exact ⟨⟨hp, by linarith [hT rfl]⟩, hT rfl⟩
  · rintro ⟨⟨hp, -⟩, hT⟩
    exact ⟨hp, fun _ => hT⟩

include C in
/-- **`rank df₁ = 1` on `U`** (the `hrk` argument; `U ⊆ edgeParentSet_BBP`). -/
theorem edgeParent_rank_OWF (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) {p : W.Carrier}
    (hp : p ∈ C.edgeParentSet_OWF) : C.toChain.stageRank_BIFc 1 p = 1 := by
  obtain ⟨-, hΔ, -⟩ := C.std
  exact C.edgeParent_rank_BBP hσ hb ⟨hp.1, by linarith [hp.2]⟩

include C in
/-- A point whose final value lies in the edge stage piece of an active-type chart forces an
ACTIVE edge slot. -/
theorem exists_active_of_edgeSource_OWF (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : q ∈ S.edgeSource_OWF j) :
    ∃ O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1)
      ((actualSlotsV2_BAUGD S).stageCloud 1) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 1)
      (DP.stageRadius 1 (Sg 1)) (DP.stagePlane 1), C.toChain.slot 1 = .active O := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨hd, hη, ht⟩ := hq
  rcases hsl : C.toChain.slot 1 with O | ⟨hc, he⟩
  · exact ⟨O, rfl⟩
  · exfalso
    have hmem : q ∈ (actualSlotsV2_BAUGD S).stageCore 1 :=
      Set.mem_iUnion₂.mpr ⟨Sum.inr (Sum.inr j), rfl, hd, by linarith, by linarith⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hc) q hmem

include C in
/-- **Localization at threshold `4.1Δ`**: `f₁(p)` in the piece of chart `j` and `T(p) < 4.1Δ` put
`p` in the original source `Y_j`, with `|η_j| < 4.01Δ`. -/
theorem edge_loc41_OWF (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 1 p ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ)
    (hT : C.toChain.heightRatio p < 41 / 10 * Δ) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ S.edgeSource_OWF j ∧
      |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ := by
  obtain ⟨-, hΔ0, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  obtain ⟨q, rfl, hd, hη, ht6⟩ := C.edge_final_loc5_BBP j hp (by linarith)
  obtain ⟨-, hhigh⟩ := C.edge_height_band_OWF hc hC j hd (by linarith) ht6
  have ht5 : S.edgeHeightRaw q < 5 * Δ := by
    rcases le_or_gt (S.edgeHeightRaw q) (2 * Δ) with h2 | h2
    · linarith
    · have := (abs_lt.mp (hhigh h2.le)).1
      linarith
  exact ⟨q, rfl, ⟨hd, by linarith, ht5⟩, hη⟩

include C in
/-- **The parent maps into the edge base** (the `hsub` argument; see the module docstring). -/
theorem edgeParent_sub_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    C.edgeParentSet_OWF ⊆ C.toChain.stageMap 1 ⁻¹' C.baseSet_BBP 1 := by
  obtain ⟨-, hΔ0, -⟩ := C.std
  intro p hp
  by_cases hT4 : C.toChain.heightRatio p ≤ 4 * Δ
  · exact ⟨p, ⟨hp.1, fun _ => hT4⟩, rfl⟩
  push Not at hT4
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, rfl, hqY, hη⟩ := C.edge_loc41_OWF hc hC j hj hp.2
  set a := S.edgeKappa_BBP j (C.toChain.stageMap 1 q.val) with ha_def
  have hga : S.edgeRatio_BAUGD j (C.toChain.E q.val) = a := (C.edgeKappa_stageMap_OWF j _).symm
  have ha : |a| < 81 / 20 * Δ := by
    have hcl := C.edge_value_close_OWF j hqY.1 (by linarith [hqY.2.1]) (by linarith [hqY.2.2])
    rw [← hga]
    have h1 := abs_sub_abs_le_abs_sub (S.edgeRatio_BAUGD j (C.toChain.E q.val))
      (S.edgeEta_BIF j.1 q)
    obtain ⟨-, -, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
    linarith
  set δ' := C.toChain.heightRatio q.val - 4 * Δ with hδ'
  have hδ0 : 0 ≤ δ' := by linarith
  have hδ1 : δ' ≤ Δ / 10 := by linarith [hp.2]
  obtain ⟨hpc, -⟩ := C.edgeDisk_preconnected_nonempty_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1
    hβc1 j ha hδ0 hδ1
  obtain ⟨-, ⟨q₀, hq₀⟩⟩ := C.edgeDisk_preconnected_nonempty_OWF hμ hτ hσc hb hc hC hε0 hε hγc
    hγc1 hβc1 j ha le_rfl (by positivity)
  obtain ⟨O, hO⟩ := C.exists_active_of_edgeSource_OWF j hqY
  have hconst := C.edge_native_const_OWF (by linarith) hb O hO j hpc (fun x hx => hx.1)
    (a := a) (fun x hx => by rw [C.edgeKappa_stageMap_OWF]; exact hx.2.1)
  have hqD : q ∈ {x | x ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E x.val) = a ∧
      C.toChain.heightRatio x.val - δ' ≤ 4 * Δ} := ⟨hqY, hga, by linarith⟩
  have hq₀D : q₀ ∈ {x | x ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E x.val) = a ∧
      C.toChain.heightRatio x.val - δ' ≤ 4 * Δ} := ⟨hq₀.1, hq₀.2.1, by linarith [hq₀.2.2]⟩
  have h := hconst q hqD q₀ hq₀D
  have hff : C.toChain.stageMap 1 q.val = C.toChain.stageMap 1 q₀.val := by
    rw [C.toChain.final_factor_V2_BAUGD 1 q.val, h, ← C.toChain.final_factor_V2_BAUGD 1 q₀.val]
  refine ⟨q₀.val, ⟨?_, fun _ => by linarith [hq₀.2.2]⟩, hff.symm⟩
  rw [← hff]
  exact hp.1

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
