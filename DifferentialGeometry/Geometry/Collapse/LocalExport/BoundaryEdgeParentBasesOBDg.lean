import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bProductionOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOfCore
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOWF

/-!
# The produced edge parent lies in the interior, and A4 exposes it (obstruction O1)

Lane O-BD1 (by S-BD2f, suffix `_OBDg`), group G12b. The BASES exit produced by
`exists_boundaryGaf02BasesV2b_OWF` carries the edge parent `C.edgeParentSet_OWF`, but the
statement forgets it. Here:

* `edgeParentSet_subset_interior_OBDg`: `C.edgeParentSet_OWF ⊆ W°` (a point whose `f₂`-value is in
  an edge ratio piece and with `T < 4.1 Δ` is the value of a point of `W.pieceInterior ⊤`:
  `edge_loc41_OWF`);
* `exists_edgeParent_of_core_eq_OBDg`, `exists_boundaryGaf02BasesV2b_of_parts_eq_OBDg`,
  `exists_boundaryGaf02BasesV2b_edgeParent_OBDg`: the proofs of the original statements with the
  extra conjunct `Bs.edgeParent = U` (resp. `= C.edgeParentSet_OWF`); the proof terms are those of
  `exists_edgeParent_of_core_BAUGD`, `exists_boundaryGaf02BasesV2b_of_parts_BAUGD` and
  `exists_boundaryGaf02BasesV2b_OWF`, the first one keeping the structure it builds.
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

include C in
/-- **The open edge parent `U = f₂⁻¹(O₂) ∩ {T < 4.1Δ}` lies in the interior of `W`.** -/
theorem edgeParentSet_subset_interior_OBDg (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000) :
    C.edgeParentSet_OWF ⊆ (W.interior : Set W.Carrier) := by
  intro p hp
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, hq, -⟩ := C.edge_loc41_OWF hc hC j hj hp.2
  rw [← hq]
  exact q.property.2

include C in
/-- **`exists_edgeParent_of_core_BAUGD` keeping `edgeParent = U`.** -/
theorem exists_edgeParent_of_core_eq_OBDg (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (Bc : BoundaryGaf02BasesCore_BIFc C.toChain) (U : Set W.Carrier) (hU : IsOpen U)
    (hcut : Bc.source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' Bc.base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1) :
    ∃ P : BoundaryEdgeParent_BIFc C.toChain Bc.source Bc.base, P.edgeParent = U := by
  refine ⟨C.edgeParentOfRim_BAUGD Bc.source Bc.base U hU hcut hsub hrk fun p hp hT => ?_, rfl⟩
  have hpX : p ∈ Bc.source 1 := by
    rw [hcut]
    exact ⟨hp, le_of_eq hT⟩
  obtain ⟨q, rfl, j, hj, hd, hη, ht⟩ := Bc.edge_localization p hpX
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  exact C.rim_surjective_BAUGD hc hC hε0 hε hγc hγc1 hβc1
    ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩ hd hη ht hT

include C in
/-- **`exists_boundaryGaf02BasesV2b_of_parts_BAUGD` keeping `edgeParent = U`.** -/
theorem exists_boundaryGaf02BasesV2b_of_parts_eq_OBDg (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (Bc : BoundaryGaf02BasesCore_BIFc C.toChain)
    (hplat : ∀ st, ∀ p ∈ Bc.source st,
      (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc p) = 1)
    (hbase : ∀ st, Bc.base st =
      C.toChain.laterV2_BAUGD st '' (C.toChain.nativeStageMap_BIFc st '' Bc.source st))
    (hemb : ∀ st, Topology.IsEmbedding
      (fun x : C.toChain.nativeStageMap_BIFc st '' Bc.source st => C.toChain.laterV2_BAUGD st x))
    (U : Set W.Carrier) (hU : IsOpen U)
    (hcut : Bc.source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' Bc.base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1)
    (hcirc : ∀ y ∈ Bc.base 0, SmoothProductChartAt_BIFc W.model (𝓡 1) (F := Circle) 2
      (C.toChain.stageMap 0) (Bc.source 0) (Bc.base 0) y)
    (hslim : ∀ y ∈ Bc.base 2,
      SmoothProductChartAt_BIFc W.model (𝓡 2) (F := GC.GraphManifold.ClosureSphere.{0}) 1
          (C.toChain.stageMap 2) (Bc.source 2) (Bc.base 2) y ∨
        SmoothProductChartAt_BIFc W.model ((𝓡 1).prod (𝓡 1)) (F := Circle × Circle) 1
          (C.toChain.stageMap 2) (Bc.source 2) (Bc.base 2) y)
    (hedge : ∀ y ∈ Bc.base 1, SmoothDiskChartAt_BIFc W.model 1 (C.toChain.stageMap 1)
      C.toChain.heightRatio (4 * Δ) (Bc.source 1) (Bc.base 1) y)
    (hbuf : ∀ st, Bc.source st ⊆ {p | ENNReal.ofReal 5 < distanceToBoundary W g p}) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
      Bs.edgeParent = U := by
  obtain ⟨P, hP⟩ := C.exists_edgeParent_of_core_eq_OBDg hc hC hε0 hε hγc hγc1 hβc1 Bc U hU hcut
    hsub hrk
  exact ⟨{ toBoundaryGaf02BasesCore_BIFc := Bc
           split := C.toChain.laterSplit_V2_BAUGD Bc.source Bc.base hplat hbase hemb
           parent := P }, ⟨hcirc, hslim, hedge, hbuf⟩, hP⟩

include C in
/-- **A4 whole (v2b) with the edge parent exposed**: the bases of
`exists_boundaryGaf02BasesV2b_OWF` with `Bs.edgeParent = C.edgeParentSet_OWF`. -/
theorem exists_boundaryGaf02BasesV2b_edgeParent_OBDg (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ))
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
      Bs.edgeParent = C.edgeParentSet_OWF := by
  have hσ : σc ≤ 1 / 4 := by linarith
  have hc' : c 2 < 1 / 1000 := by linarith
  obtain ⟨hU, hcut, hsub, hrk⟩ :=
    C.basesCore_edgeParent_OWF hβ2 hγ hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1
  exact C.exists_boundaryGaf02BasesV2b_of_parts_eq_OBDg hc hC hε0 hε hγc hγc1 hβc1
    (C.basesCore_BBP hβ2 hγ hσ hb) (fun st _ hp => C.baseSource_plateau_BBP st hp)
    C.baseSet_eq_later_native_BBP
    (C.basesCore_hemb_OWF hβ2 hγ hd hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1)
    C.edgeParentSet_OWF hU hcut hsub hrk
    (fun _ hy => C.circle_chart_OWF hc' hβ2 hγ hd hy)
    (fun _ hy => C.slim_chart_OWF hc' hK hy)
    (fun _ hy => C.edge_chart_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 hy)
    (C.basesCore_source_buffered_OWF hβ2 hγ hσ hb hn)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
