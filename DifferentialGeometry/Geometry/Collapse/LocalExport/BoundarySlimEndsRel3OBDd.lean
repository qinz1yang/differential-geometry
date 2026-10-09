import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimPiecesRel3OBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimEndDataOfExitsOBDd

/-!
# The ends of the slim pieces of the boundary cut: classification, end sets, defining functions
(lane S-BD2d2, `_OBDd`), group G10f

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. End-level corollaries of
`exists_slimExit_rel3_OBDd` for the pieces `(slimCutPieces_of_exit74 Xe).pieces` (the boundary twins
of `slimEnd_free_iff_OCL`, `exists_slimEnd_of_arcEnd_OCL`, `exists_newEnd_of_arcEnd_OCL` and
`slimEnd_coord_OCL`):

* every end `e` lies over some sub-arc `γ i` (its component is the arc image), its end set is the
  whole fibre `X₃ ∩ f₃⁻¹{γ i (iccEnd e.1.2)}`, and `e` is a new end iff that end value is not a
  face point;
* every new end has its defining function of the form `e ∘ f₃` on an open set of the base;
* conversely every end value of every sub-arc carries an end of the pieces, a new one if the end
  value is not a face point.
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
/-- **The end-level facts of the slim pieces of an exit `Xe` carrying the arc exits of the
sub-arcs `γ'`** (from the exit-level `rel3` clauses `harc` and the cover `hcov`). -/
theorem slimEnds_of_exit_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc) {N : ℕ}
    (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (Xe : SlimExit74 P.stageGeometry P.cut)
    (harc : ∀ i : Fin N, ∃ jx : Fin Xe.count,
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
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))))
    (hcov : ∀ jx : Fin Xe.count, ∃ i : Fin N,
      (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1) :
    (∀ e : (slimCutPieces_of_exit74 Xe).pieces.End, ∃ i : Fin N,
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd e.1.2)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd e.1.2) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) ∧
    (∀ en : (slimCutPieces_of_exit74 Xe).pieces.NewEnd,
      ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
        IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
        (∀ y ∈ ((slimCutPieces_of_exit74 Xe).pieces.endNear en : Set W.Carrier),
          C.toChain.stageMap 2 y ∈ Ne) ∧
        ∀ y ∈ ((slimCutPieces_of_exit74 Xe).pieces.endNear en : Set W.Carrier),
          (slimCutPieces_of_exit74 Xe).pieces.endFn en y = e (C.toChain.stageMap 2 y)) ∧
    (∀ (i : Fin N) (b : Bool), ∃ e : (slimCutPieces_of_exit74 Xe).pieces.End, e.1.2 = b ∧
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) := by
  have hex := exit_of_component_OBDd P.comp Xe (fun i => (γ' i).toFun '' Icc 0 1)
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
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)))) harc hcov
  refine ⟨fun e => ?_, fun en => ?_, fun i b => ?_⟩
  · obtain ⟨i, hi, hQ⟩ := hex e.1.1
    have hd := slimPieceExit_endData_OBDd (C.toChain.stageMap 2) (dec.bases.source 2)
      (γ' i).toFun (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))
      (Xe.exit e.1.1) hQ e.1.2 e.2
    exact ⟨i, hi, ((Xe.exit e.1.1).image_end_eq e.1.2 e.2).trans hd.1, hd.2.1⟩
  · obtain ⟨i, hi, hQ⟩ := hex en.1.1.1
    exact (slimPieceExit_endData_OBDd (C.toChain.stageMap 2) (dec.bases.source 2)
      (γ' i).toFun (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))
      (Xe.exit en.1.1.1) hQ en.1.1.2 en.1.2).2.2 en.2
  · obtain ⟨jx, hjx, hQ⟩ := harc i
    have hI : slimModelIsInterval (Xe.exit jx).model := by
      rcases hQ with ⟨a, ha, -⟩ | ⟨a, ha, -⟩
      · exact slimPieceExit_isInterval_OBDd _ (Or.inl ⟨a, ha⟩)
      · exact slimPieceExit_isInterval_OBDd _ (Or.inr ⟨a, ha⟩)
    have hd := slimPieceExit_endData_OBDd (C.toChain.stageMap 2) (dec.bases.source 2)
      (γ' i).toFun (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))
      (Xe.exit jx) hQ b hI
    exact ⟨⟨(jx, b), hI⟩, rfl, hjx, ((Xe.exit jx).image_end_eq b hI).trans hd.1, hd.2.1⟩

include C in
/-- **`SlimCutPieces74` of the boundary cut with the `rel3` end data** (the boundary twin of
`exists_slimExit_rel3_OCL` + `slimEnd_free_iff_OCL` + `exists_newEnd_of_arcEnd_OCL`): the slim exit
`Xe` (`slimCutPieces_of_exit74 Xe : SlimCutPieces74 P.stageGeometry P.cut`) over the sub-arcs `γ'`
of the components of `D₃` (`exists_slimD3Arcs_OBDd`), with the arc exits of
`exists_slimExit_rel3_OBDd` and the end-level facts of `slimEnds_of_exit_OBDd`
and the converse for new ends. -/
theorem exists_slimCutPieces_rel3_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
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
    (∀ e : (slimCutPieces_of_exit74 Xe).pieces.End, ∃ i : Fin N,
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd e.1.2)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd e.1.2) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) ∧
    (∀ en : (slimCutPieces_of_exit74 Xe).pieces.NewEnd,
      ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
        IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
        (∀ y ∈ ((slimCutPieces_of_exit74 Xe).pieces.endNear en : Set W.Carrier),
          C.toChain.stageMap 2 y ∈ Ne) ∧
        ∀ y ∈ ((slimCutPieces_of_exit74 Xe).pieces.endNear en : Set W.Carrier),
          (slimCutPieces_of_exit74 Xe).pieces.endFn en y = e (C.toChain.stageMap 2 y)) ∧
    (∀ (i : Fin N) (b : Bool), ∃ e : (slimCutPieces_of_exit74 Xe).pieces.End, e.1.2 = b ∧
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) ∧
    (∀ (i : Fin N) (b : Bool),
      (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) →
      ∃ en : (slimCutPieces_of_exit74 Xe).pieces.NewEnd, en.1.1.2 = b ∧
        (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv en.1.1.1)).1 =
          (γ' i).toFun '' Icc 0 1 ∧
        (slimCutPieces_of_exit74 Xe).pieces.endSet en.1 =
          dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) := by
  refine (C.exists_slimExit_rel3_OBDd dec zc P hεr hrd hrd4 hrdc hprem hθ).imp
    fun N hN => hN.imp fun γ' hγ => hγ.imp fun Xe hX => ?_
  have h5 := C.slimEnds_of_exit_OBDd dec zc P γ' Xe hX.2.2.2.2.1 hX.2.2.2.2.2
  refine ⟨hX.1, hX.2.1, hX.2.2.1, hX.2.2.2.1, h5.1, h5.2.1, h5.2.2, fun i b hf => ?_⟩
  obtain ⟨e, hb, hc, hs, hk⟩ := h5.2.2 i b
  exact ⟨⟨e, hk.mpr hf⟩, hb, hc, hs⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
