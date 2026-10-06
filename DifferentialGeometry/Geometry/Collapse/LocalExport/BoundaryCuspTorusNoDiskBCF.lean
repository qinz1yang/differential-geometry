import DifferentialGeometry.Topology.Surface.Recognition.TorusComponentNoDiskBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalFaceBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b

/-!
# BCF03 `hdisk`: a cusp front off `X₃` meets no horizontal disk (lane S-BCF03b, G27)

The input `hdisk` of `cuspDichotomy_BCF03` (G18) / `cuspDichotomy_of_registers_BCF` (G20), PROVED
from the embedded face partition of the torus component `H_b` (FC40 `diskCount_eq_zero_of_torus`)
and the smooth product `T² × [0, 1]` of BCG06:

* `cuspFront_homeomorph_torus_BCF`: a cusp front is homeomorphic to `S¹ × S¹` (it is the image of
  `T² × {1}` under the diffeomorphism `D` of `labelled_smooth_product`);
* `cuspFront_disjoint_edgePiece_BCF`: for a front off `X₃`, given the partition of every component
  of `∂M₂` (the first conjunct of the frozen G7) and `P_e ∩ R_c = V_e`, the front misses `P_e`.
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A cusp front is homeomorphic to the torus** (the image of `T² × {1}` under the diffeomorphism
`D : T² × [0, 1] ≃ C_b` of BCG06). -/
theorem cuspFront_homeomorph_torus_BCF {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    Nonempty (↥(C.toChain.cuspFront_BIF i) ≃ₜ Circle × Circle) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1 i
  have hfc : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    have h := hcomp.compact_core.isClosed.frontier_subset
    rw [hcomp.relative_frontier_eq] at h
    exact h
  obtain ⟨cs, hcs⟩ := hcomp.labelled_smooth_product
  let _ := cs
  obtain ⟨-, -, -, D, -, hD1⟩ := hcs
  let one : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  let gm : Circle × Circle → W.Carrier := fun t => ((D (t, one) : C.toChain.cuspCore_BIF i) :
    W.Carrier)
  have hgc : Continuous gm :=
    continuous_subtype_val.comp (D.continuous.comp (by fun_prop))
  have hgi : Injective gm := fun t t' h => by
    have := D.injective (Subtype.ext h)
    exact (Prod.mk.inj this).1
  have hemb : IsClosedEmbedding gm := hgc.isClosedEmbedding hgi
  have hrange : range gm = C.toChain.cuspFront_BIF i := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (hD1 (t, one)).mpr rfl
    · intro hx
      obtain ⟨p, hp⟩ := D.surjective ⟨x, hfc hx⟩
      have hp' : ((D p : C.toChain.cuspCore_BIF i) : W.Carrier) = x := congrArg Subtype.val hp
      have hp1 : (p.2 : ℝ) = 1 := (hD1 p).mp (by rw [hp']; exact hx)
      have hp2 : p.2 = one := Subtype.ext hp1
      refine ⟨p.1, ?_⟩
      change ((D (p.1, one) : C.toChain.cuspCore_BIF i) : W.Carrier) = x
      rw [← hp2]
      exact hp'
  exact ⟨((hemb.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm⟩

/-- **`hdisk`: a cusp front off `X₃` misses the edge piece** (PROVED from the partition of the torus
component `H_b` by FC40). `hVe` is `P_e ∩ R_c = V_e` (BCF02) and `hpart` the first conjunct of the
frozen G7 (the embedded face partition of every component of `∂M₂`). -/
theorem cuspFront_disjoint_edgePiece_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hVe : Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace)
    (hpart : ∀ x ∈ frontier Kc.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        ↥(connectedComponentIn (frontier Kc.M₂) x),
      (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
        Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
      Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder)
    (i : Fin S.packet.cusp.count) (hi : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅) :
    Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece := by
  obtain ⟨p, hp⟩ := (C.isConnected_cuspFront_BCF hrd hrd4 hrdc hprem hθ i).nonempty
  obtain ⟨hHF, -, hcomp⟩ := C.cuspFront_component_frontier_M₂_BCF Z hrd hrd4 hrdc hprem hθ
    Kc.slimCut_BIFc i hi hp
  obtain ⟨e⟩ := C.cuspFront_homeomorph_torus_BCF hrd hrd4 hrdc hprem hθ i
  have hY : C.toChain.cuspFront_BIF i = connectedComponentIn (frontier Kc.M₂) p := hcomp
  let φ : ↥(connectedComponentIn (frontier Kc.M₂) p) ≃ₜ Circle × Circle :=
    (Homeomorph.setCongr hY.symm).trans e
  obtain ⟨P, -, hpieces⟩ := hpart p (hHF hp)
  have hM₂c : IsClosed Kc.M₂ := isClosed_sdiff_relInterior_BCF C.toChain.isClosed_M₁_BCF Kc.piece
  have hsat := C.horizontalFace_saturated_BCF Z hrd hrd4 hrdc hprem hθ Kc er
  have hempty := Surface.component_inter_source_eq_empty_of_torus_BCF
    (fib₁ := Bs.fibre 1) (f₂ := C.toChain.stageMap 1) (T := C.toChain.heightRatio) (c := 4 * Δ)
    (X₂ := Bs.source 1) (Bd := frontier Kc.M₂) (Rc := Kc.remainder) (fun _ => rfl)
    (fun q hq z hz hzq => hsat q hq z ⟨hz, hzq⟩)
    (fun q hq => WF.edge_fibre_OWF _ (Bs.image_eq 1 ▸ ⟨q, hq.2, rfl⟩))
    (fun q hq hqR => (hVe ▸ (⟨⟨hM₂c.frontier_subset hq.1, hq.2⟩, hqR⟩ :
      q ∈ Kc.edgePiece ∩ Kc.remainder) : q ∈ Kc.verticalFace).2) φ P hpieces
  refine Set.disjoint_left.mpr fun x hxH hxP => ?_
  have hxY : x ∈ connectedComponentIn (frontier Kc.M₂) p := hY ▸ hxH
  have : x ∈ connectedComponentIn (frontier Kc.M₂) p ∩ Bs.source 1 := ⟨hxY, hxP.2⟩
  rw [hempty] at this
  exact this

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
