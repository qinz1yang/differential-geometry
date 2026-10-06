import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcExitOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimPiecesOBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimExitOfArcPiecesOBDd

/-!
# `SlimExit74` of the boundary cut, with the end classification exposed (lane S-BD2d2, `_OBDd`),
group G10f

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. Boundary twin of `exists_slimExit_rel3_OCL`
(closed route, clause (b) of the gate with the end classification): over the sub-arcs `γ i` of
`exists_slimD3Arcs_OBDd` (the components of `D₃ = K₃ ∩ C₃`, no loops) the slim exit of the cut
`P.cut` of a stage geometry `P`, one sphere / torus arc exit per component, with

* the projection identity `f₃ (a.F z) = γ i z.2` and both end slices the whole end fibres
  `X₃ ∩ f₃⁻¹{γ i (iccEnd b)}` (rel3, clause 2);
* for every free end a smooth `e` with `a.ends.fn b y = e (f₃ y)` on `a.ends.near b`
  (rel3, clause 1);
* the end `b` is free iff the end value is not a face point `f₃(∂M₁ ∩ X₃)` (rel3, clause 3);
* the end values are face points or arc ends of `dec.slim`, and an arc end of `dec.slim` is never a
  face point.

`BoundaryGaf02ChainE.exists_slimExit_rel3_OBDd`.
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
/-- **The slim exit over given sub-arcs `γ'`** (the kernel `exists_slimExit74_of_arcPieces_OBDd`
fed with the arc exits of `exists_slimArcExit_OBDd`). -/
theorem slimExit_of_arcs_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
    {N : ℕ} (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (hdisj : Pairwise fun i j => Disjoint ((γ' i).toFun '' Icc 0 1) ((γ' j).toFun '' Icc 0 1))
    (hU : ⋃ i, (γ' i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc)
    (Psub : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, Psub.toFun x = C.slimF_OBDd x)
    (hface : ∀ y ∈ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2),
      IsPreconnected (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y}) →
      ∃ F : NeighbourFace P.stageGeometry.zero P.stageGeometry.cusp,
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} = neighbourSet F) :
    ∃ Xe : SlimExit74 P.stageGeometry P.cut,
      (∀ i : Fin N, ∃ jx : Fin Xe.count,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 ∧
        ((∃ a : SphereArcExit74 P.stageGeometry.zero P.stageGeometry.cusp,
            Xe.exit jx = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 P.stageGeometry.zero P.stageGeometry.cusp, Xe.exit jx = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)))) ∧
      ∀ jx : Fin Xe.count, ∃ i : Fin N,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 := by
  have harc := fun i => C.exists_slimArcExit_OBDd dec Psub hP hface (γ' i)
  have hcpt : ∀ i, IsCompact ((γ' i).toFun '' Icc 0 1) := fun i =>
    isCompact_Icc.image_of_continuousOn (γ' i).smooth.continuousOn
  have hpre : ∀ i, IsPreconnected ((γ' i).toFun '' Icc 0 1) := fun i =>
    isPreconnected_Icc.image _ (γ' i).smooth.continuousOn
  have hne : ∀ i, ((γ' i).toFun '' Icc 0 1).Nonempty := fun i =>
    ⟨(γ' i).toFun 0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  exact exists_slimExit74_of_arcPieces_OBDd
    (A := P.stageGeometry) (D := P.cut) (pc := fun i => (γ' i).toFun '' Icc 0 1)
    P.slim_ident hcpt hpre hne hdisj hU P.comp P.comp_eq
    (fun i x => ((∃ a : SphereArcExit74 P.stageGeometry.zero P.stageGeometry.cusp,
        x = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 P.stageGeometry.zero P.stageGeometry.cusp, x = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)))) harc

include C in
/-- **The slim exit over the sub-arcs of `D₃`, with the produced slim submersion and face lemma
(helper of `exists_slimExit_rel3_OBDd`).** -/
theorem slimExit_rel3_of_arcs_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {N : ℕ} (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (hdisj : Pairwise fun i j => Disjoint ((γ' i).toFun '' Icc 0 1) ((γ' j).toFun '' Icc 0 1))
    (hU : ⋃ i, (γ' i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) :
    ∃ Xe : SlimExit74 P.stageGeometry P.cut,
      (∀ i : Fin N, ∃ jx : Fin Xe.count,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 ∧
        ((∃ a : SphereArcExit74 P.stageGeometry.zero P.stageGeometry.cusp,
            Xe.exit jx = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 P.stageGeometry.zero P.stageGeometry.cusp, Xe.exit jx = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)))) ∧
      ∀ jx : Fin Xe.count, ∃ i : Fin N,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 := by
  obtain ⟨Psub, hP⟩ := C.exists_slimSubmersion_OBDd dec
  exact C.slimExit_of_arcs_OBDd dec zc P γ' hdisj hU Psub hP
    (fun y hy hs => C.exists_neighbourFace_of_face_OBDd dec zc hεr hrd hrd4 hrdc hprem hθ hy hs)

include C in
/-- **The slim exit of the boundary cut with the end classification** (`rel3`, boundary form). -/
theorem exists_slimExit_rel3_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (N : ℕ) (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
      (Xe : SlimExit74 P.stageGeometry P.cut),
      (Pairwise fun i j => Disjoint ((γ' i).toFun '' Icc 0 1) ((γ' j).toFun '' Icc 0 1)) ∧
      (⋃ i, (γ' i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) ∧
      (∀ (i : Fin N) (b : Bool),
        (γ' i).toFun (iccEnd b) ∈ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) ∨
          ∃ (k : Fin dec.slim.arcCount) (b' : Bool),
            (γ' i).toFun (iccEnd b) = dec.slim.arc k (iccEnd b')) ∧
      (∀ (k : Fin dec.slim.arcCount) (b : Bool),
        dec.slim.arc k (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
      (∀ i : Fin N, ∃ jx : Fin Xe.count,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 ∧
        ((∃ a : SphereArcExit74 P.stageGeometry.zero P.stageGeometry.cusp,
            Xe.exit jx = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 P.stageGeometry.zero P.stageGeometry.cusp, Xe.exit jx = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = (γ' i).toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = dec.bases.source 2 ∩
            C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)))) ∧
      ∀ jx : Fin Xe.count, ∃ i : Fin N,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 := by
  obtain ⟨N, γ', hdisj, hU, hend, hnotface⟩ :=
    C.exists_slimD3Arcs_OBDd dec hεr hrd hrd4 hrdc hprem hθ
  refine ⟨N, γ', ?_⟩
  exact (C.slimExit_rel3_of_arcs_OBDd dec zc P hεr hrd hrd4 hrdc hprem hθ γ' hdisj hU).imp
    fun Xe h => ⟨hdisj, hU, hend, hnotface, h.1, h.2⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
