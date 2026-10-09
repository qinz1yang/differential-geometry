import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFreeEndOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLandingExitsV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg07RowBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimZeroEndFace74

/-!
# The shared end of a slim arc piece: the end fibre over a face point is a neighbour model face
(lane S-BD2d2, suffix `_OBDd`), group G10e

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. Boundary twin of `zero_end_face74`: for a point
`y = f₃ p`, `p ∈ ∂M₁ ∩ X₃`, the whole slim fibre `X₃ ∩ f₃⁻¹{y}` is ONE zero face or ONE cusp front
(`frontier_M₁_BGR`, F5z `zeroFace_eq_slimFibre_direct_V2b_BGR`, F5
`cuspFront_eq_slimFibre_direct_V2b_BGR`), hence a neighbour face of the zero / cusp exit `zc`:

* a cusp front is the internal model face of the cusp core (`zc.cusp_link`);
* a zero face is the model boundary `pieceBoundary (zero.piece i)` of the zero piece
  (`zc.zero_link`, `boundary_eq`, `face_eq`); a preconnected fibre is then a single model
  face (`exists_zeroFace_of_preconnected74`).

* `BoundaryGaf02ChainE.exists_neighbourFace_of_face_OBDd`: the statement, with the preconnectedness
  of the fibre (the image of a standard whole fibre) as hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **A cusp front that is one whole slim fibre is the neighbour set of the internal model face
of its cusp core.** -/
theorem cuspFront_eq_neighbourSet_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (i : Fin S.packet.cusp.count) :
    ∃ F : NeighbourFace zc.zero zc.cusp, neighbourSet F = C.toChain.cuspFront_BIF i :=
  ⟨Sum.inr ⟨i, ⟨zc.cusp.internalModelFace i, rfl⟩⟩, by
    change (zc.cusp.piece i).map '' (zc.cusp.internalModelFace i).1 = _
    rw [zc.cusp.internalModelFace_eq i, ← (zc.cusp_link i).2.1, ← range_comp]
    rfl⟩

include C in
/-- **A zero face that is one whole slim fibre, with preconnected fibre, is a neighbour model
face of the zero exit.** -/
theorem zeroFace_neighbourFace_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (k : S.ZeroIdx_BAUGC) {s : Set W.Carrier}
    (hs : IsPreconnected s) (hne : s.Nonempty) (hk : s = C.toChain.actualZeroFace_BIFc k) :
    ∃ F : NeighbourFace zc.zero zc.cusp, s = neighbourSet F := by
  obtain ⟨σ, hσ⟩ := zc.zero_link
  refine exists_zeroFace_of_preconnected74 (σ.symm k) hs hne ?_
  rw [hk, zc.zero.boundary_eq, dec.zero.face_eq]
  have h2 := (hσ (σ.symm k)).2
  rw [σ.apply_symm_apply] at h2
  rw [h2]

include C in
/-- **The whole slim fibre over a face point is a neighbour model face**: for `y ∈ f₃(∂M₁ ∩ X₃)`
with preconnected fibre (the image of a standard whole fibre), `X₃ ∩ f₃⁻¹{y} = neighbourSet F` for a
neighbour face `F` (a zero model face or the internal model face of a cusp core). -/
theorem exists_neighbourFace_of_face_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))
    (hs : IsPreconnected (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y})) :
    ∃ F : NeighbourFace zc.zero zc.cusp,
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} = neighbourSet F := by
  obtain ⟨p, ⟨hpf, hpX⟩, rfl⟩ := hy
  have hne : (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {C.toChain.stageMap 2 p}).Nonempty :=
    ⟨p, hpX, rfl⟩
  rw [C.frontier_M₁_BGR dec.zero hrd hrd4 hrdc hprem hθ] at hpf
  rcases hpf with hz | hc
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    obtain ⟨y', -, hfib⟩ := C.zeroFace_eq_slimFibre_direct_V2b_BGR dec.fibres hεr k ⟨p, hk, hpX⟩
    have hpy : p ∈ dec.bases.fibre 2 y' := hfib ▸ hk
    have hy' : C.toChain.stageMap 2 p = y' := hpy.2
    have hfy : dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {C.toChain.stageMap 2 p} =
        C.toChain.actualZeroFace_BIFc k := by
      rw [hfib, hy']
      rfl
    exact C.zeroFace_neighbourFace_OBDd dec zc k hs hne hfy
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hc
    obtain ⟨y', -, hfib⟩ := C.cuspFront_eq_slimFibre_direct_V2b_BGR dec.fibres hrd hrd4 hrdc hprem
      hθ i ⟨p, hi, hpX⟩
    have hpy : p ∈ dec.bases.fibre 2 y' := hfib ▸ hi
    have hy' : C.toChain.stageMap 2 p = y' := hpy.2
    have hfy : dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {C.toChain.stageMap 2 p} =
        C.toChain.cuspFront_BIF i := by
      rw [hfib, hy']
      rfl
    obtain ⟨F, hF⟩ := C.cuspFront_eq_neighbourSet_OBDd dec zc i
    exact ⟨F, hfy.trans hF.symm⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
