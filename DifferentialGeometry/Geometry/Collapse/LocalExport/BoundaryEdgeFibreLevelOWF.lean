import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeWholeDiskOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleFibreLevel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesFinalSubmersion

/-!
# O-WF G6c: the whole edge fibre is the adjusted disk; no merging at the edge stage

On `C : BoundaryGaf02ChainE DP …` with the BASES core sources `X₁ = C.baseSource_BBP 1` and
bases `B₁ = C.baseSet_BBP 1` (lane S-BASES-PORT2), with the adjusted edge disks of
`edge_wholeDisk_OWF`:

* `isPreconnected_range_closedCell_OWF`, `isPreconnected_edgeDisk_OWF`: the adjusted disks
  `D(a, δ) = {q ∈ Y_j : g = a, T ≤ 4Δ + δ}` are preconnected;
* `edge_native_const_OWF`: the native map `f₁⁰` is CONSTANT on every preconnected subset of a
  level `{q ∈ Y_j : κ_j(f₁ q) = a}` (local one-sheet `native_localInverse_OWF` on the plateau with
  the edge stage submersion `stage_submersion_edge_BBP`);
* **`edge_fibre_eq_disk_OWF`**: for `y ∈ B₁` in the ratio piece of chart `j`, the WHOLE fibre
  `{x ∈ W° | x ∈ X₁, f₁ x = y}` EQUALS the adjusted disk `D(κ_j y, 0)` — closed twin
  `edp04_original_fibre_C14` / `vertical_eq_FDC`, here without a global chart;
* **`edge_later_isEmbedding_OWF`**: `Θ₁` is a topological embedding of the native base
  `f₁⁰(X₁)` (the `hemb` clause of G11 at `st = 1`).

Register premises: those of `edge_wholeDisk_OWF` (`μ, τ ≤ 10⁻⁸`, `σc ≤ 10⁻³`,
`b ≤ 1/(1000Δ)`, `c₃ < 10⁻⁵`, N76-9, `0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`).
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

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

/-- The image of a closed cell under a continuous map is preconnected. -/
theorem isPreconnected_range_closedCell_OWF {X : Type*} [TopologicalSpace X] {m : ℕ}
    {f : ClosedCell m → X} (hf : Continuous f) : IsPreconnected (range f) := by
  have h : IsPreconnected {x : EuclideanSpace ℝ (Fin m) | ‖x‖ ≤ 1} := by
    have := (convex_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).isPreconnected
    simpa [Metric.closedBall, dist_zero_right] using this
  have : PreconnectedSpace (ClosedCell m) := Subtype.preconnectedSpace h
  rw [← image_univ]
  exact isPreconnected_univ.image f hf.continuousOn

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

include C in
/-- `κ_j(f₁ p) = λ_j(E p)` (the edge stage projection keeps the edge block). -/
theorem edgeKappa_stageMap_OWF (j : S.EdgeIdx_BAUGD) (p : W.Carrier) :
    S.edgeKappa_BBP j (C.toChain.stageMap 1 p) = S.edgeRatio_BAUGD j (C.toChain.E p) :=
  edgeKappa_stageProj_BBP j (C.toChain.E p)

include C in
/-- A source-type point whose final value lies in the ratio piece of chart `j` lies in `Y_j`. -/
theorem edge_mem_Y_of_piece_OWF (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 1 p ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ)
    (hT : C.toChain.heightRatio p ≤ 4 * Δ) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ S.edgeSource_OWF j := by
  obtain ⟨-, hΔ0, -⟩ := C.std
  obtain ⟨q, hq, hd, hη, ht⟩ := C.edge_final_loc_BBP j hp hT
  exact ⟨q, hq, hd, by linarith, by linarith⟩

include C in
/-- Such a point has `|κ_j(f₁ p)| < 4.05Δ`. -/
theorem edge_kappa_lt_OWF (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 1 p ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ)
    (hT : C.toChain.heightRatio p ≤ 4 * Δ) :
    |S.edgeKappa_BBP j (C.toChain.stageMap 1 p)| < 81 / 20 * Δ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  obtain ⟨q, rfl, hd, hη, ht⟩ := C.edge_final_loc_BBP j hp hT
  have hcl := C.edge_value_close_OWF j hd (by linarith) (by linarith)
  rw [C.edgeKappa_stageMap_OWF]
  have h1 := abs_sub_abs_le_abs_sub (S.edgeRatio_BAUGD j (C.toChain.E q.val))
    (S.edgeEta_BIF j.1 q)
  linarith

include C in
/-- **The adjusted edge disks are preconnected and nonempty.** -/
theorem edgeDisk_preconnected_nonempty_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {a δ : ℝ} (ha : |a| < 81 / 20 * Δ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ Δ / 10) :
    IsPreconnected {q | q ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E q.val) = a ∧
        C.toChain.heightRatio q.val - δ ≤ 4 * Δ} ∧
      {q | q ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E q.val) = a ∧
        C.toChain.heightRatio q.val - δ ≤ 4 * Δ}.Nonempty := by
  obtain ⟨φ, hφ, hr, -⟩ := C.edge_wholeDisk_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 j ha
    hδ0 hδ
  rw [← hr]
  exact ⟨isPreconnected_range_closedCell_OWF hφ.isEmbedding.continuous,
    ⟨φ (closedCellCenter 2), mem_range_self _⟩⟩

/-- **The native map is constant on a preconnected part of an adjusted edge level** (see the
module docstring). -/
theorem edge_native_const_OWF (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ))
    (O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1)
      ((actualSlotsV2_BAUGD S).stageCloud 1) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 1)
      (DP.stageRadius 1 (Sg 1)) (DP.stagePlane 1))
    (hO : C.toChain.slot 1 = .active O) (j : S.EdgeIdx_BAUGD) {L : Set (W.pieceInterior ⊤)}
    (hL : IsPreconnected L) (hLY : L ⊆ S.edgeSource_OWF j) {a : ℝ}
    (hLa : ∀ q ∈ L, S.edgeKappa_BBP j (C.toChain.stageMap 1 q.val) = a) :
    ∀ x ∈ L, ∀ x' ∈ L,
      C.toChain.nativeStageMap_BIFc 1 x.val = C.toChain.nativeStageMap_BIFc 1 x'.val := by
  obtain ⟨-, hΔ0, -⟩ := C.std
  have hh : ContinuousOn (fun q : W.pieceInterior ⊤ => C.toChain.nativeStageMap_BIFc 1 q.val) L :=
    ((C.continuous_native_OWF 1).comp continuous_subtype_val).continuousOn
  refine eqOn_of_isPreconnected_of_locInjOn_OWF hL hh (Zs := O.Z) ?_ (S.edgeKappa_BBP j)
    (c := a) ?_ ?_
  · intro q hq
    obtain ⟨hd, hη, ht⟩ := hLY hq
    exact C.toChain.native_scope_V2_BAUGD 1 O hO q.val
      (C.edge_plateau_cutoff_BBP j hd (by linarith) (by linarith))
  · intro q hq
    exact (congrFun (C.edge_kappa_final_eq_BBP j) q.val).symm.trans (hLa q hq)
  · intro q hq
    obtain ⟨hd, hη, ht⟩ := hLY hq
    obtain ⟨V, δ', ζ', hV, hmem, -, -, -, hl⟩ :=
      C.native_localInverse_OWF 1 (S.edgeKappa_BBP j) (fun y => edgeKappa_stageProj_BBP j y)
        (by simp [gafStageDim]) O hO (S.edge_plateau_mem_nhds_BBP j hd (by linarith)
          (by linarith)) (fun q' hq' => C.edge_plateau_cutoff_BBP j hq'.1 hq'.2.1 hq'.2.2)
        (C.stage_submersion_edge_BBP hσ hb j hd (by linarith) (by linarith))
    exact ⟨V, hV, hmem, fun w hw w' hw' heq =>
      (hl w hw).2.symm.trans ((congrArg ζ' heq).trans (hl w' hw').2)⟩

include C in
/-- **The whole edge fibre is the adjusted disk** (see the module docstring). -/
theorem edge_fibre_eq_disk_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 1)
    (hyj : y ∈ ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ) :
    {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 1 ∧ C.toChain.stageMap 1 x.val = y} =
      {q | q ∈ S.edgeSource_OWF j ∧
        S.edgeRatio_BAUGD j (C.toChain.E q.val) = S.edgeKappa_BBP j y ∧
        C.toChain.heightRatio q.val - 0 ≤ 4 * Δ} := by
  obtain ⟨-, hΔ0, -⟩ := C.std
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy
  obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 1 hp₀
  have hpiece₀ : C.toChain.stageMap 1 p₀ ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ := by
    rw [hfp₀]; exact hyj
  have hT₀ : C.toChain.heightRatio p₀ ≤ 4 * Δ := hp₀.2 rfl
  obtain ⟨q₀, hq₀, hq₀Y⟩ := C.edge_mem_Y_of_piece_OWF j hpiece₀ hT₀
  have ha : |S.edgeKappa_BBP j y| < 81 / 20 * Δ := by
    have h := C.edge_kappa_lt_OWF j hpiece₀ hT₀
    rwa [hfp₀] at h
  obtain ⟨hpc, -⟩ := C.edgeDisk_preconnected_nonempty_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1
    hβc1 j ha le_rfl (by positivity)
  have hconst := C.edge_native_const_OWF (by linarith) hb O hO j hpc (fun q hq => hq.1)
    (a := S.edgeKappa_BBP j y) (fun q hq => by rw [C.edgeKappa_stageMap_OWF]; exact hq.2.1)
  have hq₀D : q₀ ∈ {q | q ∈ S.edgeSource_OWF j ∧
      S.edgeRatio_BAUGD j (C.toChain.E q.val) = S.edgeKappa_BBP j y ∧
      C.toChain.heightRatio q.val - 0 ≤ 4 * Δ} :=
    ⟨hq₀Y, by rw [← C.edgeKappa_stageMap_OWF, hq₀, hfp₀], by rw [hq₀, sub_zero]; exact hT₀⟩
  ext x
  constructor
  · rintro ⟨hxX, hxy⟩
    have hpiece : C.toChain.stageMap 1 x.val ∈
        ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ := by
      rw [hxy]; exact hyj
    obtain ⟨q, hq, hqY⟩ := C.edge_mem_Y_of_piece_OWF j hpiece (hxX.2 rfl)
    have hqx : q = x := Subtype.ext hq
    rw [← hqx]
    exact ⟨hqY, by rw [← C.edgeKappa_stageMap_OWF, hq, hxy], by rw [hq, sub_zero]; exact hxX.2 rfl⟩
  · intro hx
    have h := hconst x hx q₀ hq₀D
    have hxy : C.toChain.stageMap 1 x.val = y := by
      rw [C.toChain.final_factor_V2_BAUGD 1 x.val, h,
        ← C.toChain.final_factor_V2_BAUGD 1 q₀.val, hq₀, hfp₀]
    refine ⟨⟨?_, fun _ => by have := hx.2.2; rwa [sub_zero] at this⟩, hxy⟩
    rw [hxy, ← hfp₀]
    exact hp₀.1

include C in
/-- **No merging at the edge stage**: `Θ₁` is a topological embedding of `f₁⁰(X₁)`. -/
theorem edge_later_isEmbedding_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    Topology.IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc 1 '' C.baseSource_BBP 1 =>
      C.toChain.laterV2_BAUGD 1 x) := by
  have hfun : (fun p => C.toChain.laterV2_BAUGD 1 (C.toChain.nativeStageMap_BIFc 1 p)) =
      C.toChain.stageMap 1 := funext fun p => (C.toChain.final_factor_V2_BAUGD 1 p).symm
  refine isEmbedding_of_proper_factor_OWF (C.continuous_native_OWF 1).continuousOn ?_ ?_ ?_
  · rintro _ ⟨p, -, rfl⟩
    exact (C.toChain.later_contDiffAt_V2_BAUGD 1 p).continuousAt.continuousWithinAt
  · intro Kc hK hcK
    rw [hfun]
    have hK' : Kc ⊆ C.baseSet_BBP 1 := by rw [C.baseSet_eq_later_native_BBP 1]; exact hK
    exact C.proper_of_source_eq_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
      (C.baseSource_eq_preimage_BBP (by decide)) C.baseSource_one_eq_preimage_BBP
      (C.baseSource_eq_preimage_BBP (by decide)) 1 Kc hK' hcK
  · intro p hp p' hp' heq
    have hff : C.toChain.stageMap 1 p = C.toChain.stageMap 1 p' := by
      rw [C.toChain.final_factor_V2_BAUGD 1 p, C.toChain.final_factor_V2_BAUGD 1 p']
      exact heq
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
    have hy : C.toChain.stageMap 1 p ∈ C.baseSet_BBP 1 := ⟨p, hp, rfl⟩
    have hfib := C.edge_fibre_eq_disk_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 j hy hj
    obtain ⟨-, hΔ0, -⟩ := C.std
    obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 1 hp
    obtain ⟨q, hq, -⟩ := C.edge_mem_Y_of_piece_OWF j hj (hp.2 rfl)
    have hj' : C.toChain.stageMap 1 p' ∈
        ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ := by
      rw [← hff]; exact hj
    obtain ⟨q', hq', -⟩ := C.edge_mem_Y_of_piece_OWF j hj' (hp'.2 rfl)
    have hqD : q ∈ {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 1 ∧
        C.toChain.stageMap 1 x.val = C.toChain.stageMap 1 p} := ⟨by rw [hq]; exact hp, by rw [hq]⟩
    have hq'D : q' ∈ {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 1 ∧
        C.toChain.stageMap 1 x.val = C.toChain.stageMap 1 p} :=
      ⟨by rw [hq']; exact hp', by rw [hq', hff]⟩
    rw [hfib] at hqD hq'D
    have ha := C.edge_kappa_lt_OWF j hj (hp.2 rfl)
    obtain ⟨hpc, -⟩ := C.edgeDisk_preconnected_nonempty_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1
      hβc1 j ha le_rfl (by positivity)
    have hconst := C.edge_native_const_OWF (by linarith) hb O hO j hpc (fun x hx => hx.1)
      (a := S.edgeKappa_BBP j (C.toChain.stageMap 1 p))
      (fun x hx => by rw [C.edgeKappa_stageMap_OWF]; exact hx.2.1)
    have h := hconst q hqD q' hq'D
    rw [hq, hq'] at h
    exact h

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
