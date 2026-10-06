import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcExitGlobOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFaceEndOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimSubArcsOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimPiecesConsumerRel3OBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimEndDataOfExitsOBDd

/-!
# `SlimCutPieces74` with the global free-end form, the end-level classification and `hend`
(lane S-BD2d2, suffix `_OBDd`), group G10g

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. The final form of G10 for the consumers of the
junction facts (S-BD2e): over the sub-arcs `γ'` of `exists_slimD3SubArcs_OBDd` a slim exit `Xe`
(`slimCutPieces_of_exit74 Xe : SlimCutPieces74 P.stageGeometry P.cut`) whose ends satisfy

* (E1) every end `e` lies over a sub-arc `γ' i`, `endSet e = X₃ ∩ f₃⁻¹{γ' i (iccEnd e.1.2)}`, and
  `endKind e = none ↔ γ' i (iccEnd e.1.2) ∉ f₃(∂M₁ ∩ X₃)`;
* (E2g) every new end has the GLOBAL defining function `endFn en y = a (f₃ y)`, `a` smooth on the
  whole ambient base space;
* (E3) every `(i, b)` carries an end; (E4) a free `(i, b)` carries a NEW end;
* (hend) every `x ∈ slimSet ∩ ∂M₁` lies in the end set of a SHARED end (`endKind e = some F'`).

`BoundaryGaf02ChainE.exists_slimCutPieces_glob_OBDd`.
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
/-- **The slim exit over given sub-arcs `γ'`, `rel3` data in the exit's own vocabulary.** -/
theorem slimExit_glob_of_arcs_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc) {N : ℕ}
      (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
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
        ∃ hI : slimModelIsInterval (Xe.exit jx).model, ∀ b : Bool,
          (Xe.exit jx).slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
            {(γ' i).toFun (iccEnd b)} ∧
          ((Xe.exit jx).endKind b hI = none ↔ (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
          ((Xe.exit jx).endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
            (Fin S.packet.cusp.count) → ℝ,
            ContDiff ℝ ∞ a ∧ ∀ y, (Xe.exit jx).endFn b hI y = a (C.toChain.stageMap 2 y))) ∧
      ∀ jx : Fin Xe.count, ∃ i : Fin N,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 := by
  have harc := fun i => C.exists_slimArcExit_glob_OBDd dec Psub hP hface (γ' i)
  have hcpt : ∀ i, IsCompact ((γ' i).toFun '' Icc 0 1) := fun i =>
    isCompact_Icc.image_of_continuousOn (γ' i).smooth.continuousOn
  have hpre : ∀ i, IsPreconnected ((γ' i).toFun '' Icc 0 1) := fun i =>
    isPreconnected_Icc.image _ (γ' i).smooth.continuousOn
  have hne : ∀ i, ((γ' i).toFun '' Icc 0 1).Nonempty := fun i =>
    ⟨(γ' i).toFun 0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  exact exists_slimExit74_of_arcPieces_OBDd
    (A := P.stageGeometry) (D := P.cut) (pc := fun i => (γ' i).toFun '' Icc 0 1)
    P.slim_ident hcpt hpre hne hdisj hU P.comp P.comp_eq
    (fun i x => ∃ hI : slimModelIsInterval x.model, ∀ b : Bool,
          x.slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
          (x.endKind b hI = none ↔ (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
          (x.endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
            (Fin S.packet.cusp.count) → ℝ,
            ContDiff ℝ ∞ a ∧ ∀ y, x.endFn b hI y = a (C.toChain.stageMap 2 y))) harc

include C in
/-- **The slim exit over given sub-arcs, with the produced slim submersion and face lemma.** -/
theorem slimExit_glob_rel3_of_arcs_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
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
        ∃ hI : slimModelIsInterval (Xe.exit jx).model, ∀ b : Bool,
          (Xe.exit jx).slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
            {(γ' i).toFun (iccEnd b)} ∧
          ((Xe.exit jx).endKind b hI = none ↔ (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
          ((Xe.exit jx).endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
            (Fin S.packet.cusp.count) → ℝ,
            ContDiff ℝ ∞ a ∧ ∀ y, (Xe.exit jx).endFn b hI y = a (C.toChain.stageMap 2 y))) ∧
      ∀ jx : Fin Xe.count, ∃ i : Fin N,
        (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 := by
  obtain ⟨Psub, hP⟩ := C.exists_slimSubmersion_OBDd dec
  exact C.slimExit_glob_of_arcs_OBDd dec zc P γ' hdisj hU Psub hP
    (fun y hy hs => C.exists_neighbourFace_of_face_OBDd dec zc hεr hrd hrd4 hrdc hprem hθ hy hs)

include C in
/-- **The end-level facts (E1), (E2g), (E3) of the slim pieces of `Xe`.** -/
theorem slimEnds_glob_of_exit_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc) {N : ℕ}
      (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (Xe : SlimExit74 P.stageGeometry P.cut)
    (harc : ∀ i : Fin N, ∃ jx : Fin Xe.count,
      (P.comp (Xe.componentEquiv jx)).1 = (γ' i).toFun '' Icc 0 1 ∧
      ∃ hI : slimModelIsInterval (Xe.exit jx).model, ∀ b : Bool,
          (Xe.exit jx).slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
            {(γ' i).toFun (iccEnd b)} ∧
          ((Xe.exit jx).endKind b hI = none ↔ (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
          ((Xe.exit jx).endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
            (Fin S.packet.cusp.count) → ℝ,
            ContDiff ℝ ∞ a ∧ ∀ y, (Xe.exit jx).endFn b hI y = a (C.toChain.stageMap 2 y)))
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
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
      ContDiff ℝ ∞ a ∧ ∀ y, (slimCutPieces_of_exit74 Xe).pieces.endFn en y = a
        (C.toChain.stageMap 2 y)) ∧
    (∀ (i : Fin N) (b : Bool), ∃ e : (slimCutPieces_of_exit74 Xe).pieces.End, e.1.2 = b ∧
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) := by
  have hex := exit_of_component_OBDd P.comp Xe (fun i => (γ' i).toFun '' Icc 0 1)
    (fun i x => ∃ hI : slimModelIsInterval x.model, ∀ b : Bool,
          x.slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
          (x.endKind b hI = none ↔ (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
            (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
          (x.endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
            (Fin S.packet.cusp.count) → ℝ,
            ContDiff ℝ ∞ a ∧ ∀ y, x.endFn b hI y = a (C.toChain.stageMap 2 y))) harc hcov
  refine ⟨fun e => ?_, fun en => ?_, fun i b => ?_⟩
  · obtain ⟨i, hi, hI, hb⟩ := hex e.1.1
    exact ⟨i, hi, ((Xe.exit e.1.1).image_end_eq e.1.2 e.2).trans (hb e.1.2).1, (hb e.1.2).2.1⟩
  · obtain ⟨i, hi, hI, hb⟩ := hex en.1.1.1
    exact (hb en.1.1.2).2.2 en.2
  · obtain ⟨jx, hjx, hI, hb⟩ := harc i
    exact ⟨⟨(jx, b), hI⟩, rfl, hjx, ((Xe.exit jx).image_end_eq b hI).trans (hb b).1,
      (hb b).2.1⟩

include C in
/-- **`hend`: every point of `slimSet ∩ ∂M₁` lies in the end set of a SHARED end** (a face point of
`D₃` is an end value of a sub-arc, `faceValue_isEnd_OBDd`, and its end is shared). -/
theorem hend_of_slimEnds_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
      (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {N : ℕ} (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (hU : ⋃ i, (γ' i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc)
    (hsub : ∀ i : Fin N, ∃ (k : Fin dec.slim.arcCount) (s e : ℝ), 0 ≤ s ∧ s < e ∧ e ≤ 1 ∧
      ∀ u, (γ' i).toFun u = dec.slim.arc k (s + (e - s) * u))
    (Xe : SlimExit74 P.stageGeometry P.cut)
    (hE3 : (∀ (i : Fin N) (b : Bool), ∃ e : (slimCutPieces_of_exit74 Xe).pieces.End, e.1.2 = b ∧
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)))) :
    (∀ x ∈ P.cut.slimSet ∩ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp),
      ∃ (e : (slimCutPieces_of_exit74 Xe).pieces.End) (F' : NeighbourFace P.stageGeometry.zero
        P.stageGeometry.cusp),
        (slimCutPieces_of_exit74 Xe).pieces.endKind e = some F' ∧
          x ∈ (slimCutPieces_of_exit74 Xe).pieces.endSet e) := by
  rintro x ⟨hxS, hxf⟩
  have hxf' : x ∈ frontier C.toChain.M₁_BIFc := (C.regionM1_eq_OBD zc) ▸ hxf
  have hS := stageSetSrc_LND74 P.slim_ident P.cut.D₃
  rw [P.cut_D₃] at hS
  obtain ⟨hxX, hxD⟩ := hS.subset hxS
  obtain ⟨i, b, hib⟩ := C.faceValue_isEnd_OBDd dec hεr hrd hrd4 hrdc hprem hθ γ' hU hsub hxf' hxD
  obtain ⟨e, -, -, hs, hk⟩ := hE3 i b
  have hF : C.toChain.stageMap 2 x ∈ C.toChain.stageMap 2 ''
      (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) := ⟨x, ⟨hxf', hxX⟩, rfl⟩
  have hkne : (slimCutPieces_of_exit74 Xe).pieces.endKind e ≠ none := fun h0 => (hk.1 h0) (hib ▸ hF)
  obtain ⟨F', hF'⟩ := Option.ne_none_iff_exists'.1 hkne
  exact ⟨e, F', hF', hs ▸ ⟨hxX, hib.symm⟩⟩

include C in
/-- **`SlimCutPieces74` of the boundary cut: end-level classification, global free-end form,
converse for new ends, and `hend`** (the form consumed by the junction facts). -/
theorem exists_slimCutPieces_glob_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (N : ℕ) (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
      (Xe : SlimExit74 P.stageGeometry P.cut),
      (Pairwise fun i j => Disjoint ((γ' i).toFun '' Icc 0 1) ((γ' j).toFun '' Icc 0 1)) ∧
      (⋃ i, (γ' i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) ∧
      (∀ i : Fin N, ∃ (k : Fin dec.slim.arcCount) (s e : ℝ), 0 ≤ s ∧ s < e ∧ e ≤ 1 ∧
        ∀ u, (γ' i).toFun u = dec.slim.arc k (s + (e - s) * u)) ∧
      (∀ (i : Fin N) (b : Bool),
        (γ' i).toFun (iccEnd b) ∈ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) ∨
          ∃ (k : Fin dec.slim.arcCount) (b' : Bool),
            (γ' i).toFun (iccEnd b) = dec.slim.arc k (iccEnd b')) ∧
      (∀ (k : Fin dec.slim.arcCount) (b : Bool), dec.slim.arc k (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
      (∀ e : (slimCutPieces_of_exit74 Xe).pieces.End, ∃ i : Fin N,
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd e.1.2)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd e.1.2) ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) ∧
      (∀ en : (slimCutPieces_of_exit74 Xe).pieces.NewEnd,
        ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
      ContDiff ℝ ∞ a ∧ ∀ y, (slimCutPieces_of_exit74 Xe).pieces.endFn en y = a
        (C.toChain.stageMap 2 y)) ∧
      (∀ (i : Fin N) (b : Bool), ∃ e : (slimCutPieces_of_exit74 Xe).pieces.End, e.1.2 = b ∧
      (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv e.1.1)).1 = (γ' i).toFun '' Icc 0 1 ∧
      (slimCutPieces_of_exit74 Xe).pieces.endSet e =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)} ∧
      ((slimCutPieces_of_exit74 Xe).pieces.endKind e = none ↔
        (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) ∧
      (∀ (i : Fin N) (b : Bool), (γ' i).toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
        (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) →
      ∃ en : (slimCutPieces_of_exit74 Xe).pieces.NewEnd, en.1.1.2 = b ∧
        (P.comp ((slimCutPieces_of_exit74 Xe).componentEquiv en.1.1.1)).1 = (γ' i).toFun '' Icc 0 1
          ∧
        (slimCutPieces_of_exit74 Xe).pieces.endSet en.1 =
          dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ' i).toFun (iccEnd b)}) ∧
      (∀ x ∈ P.cut.slimSet ∩ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp),
      ∃ (e : (slimCutPieces_of_exit74 Xe).pieces.End) (F' : NeighbourFace P.stageGeometry.zero
        P.stageGeometry.cusp),
        (slimCutPieces_of_exit74 Xe).pieces.endKind e = some F' ∧
          x ∈ (slimCutPieces_of_exit74 Xe).pieces.endSet e) := by
  obtain ⟨N, γ', hdisj, hU, hend0, hnotface, hsub⟩ :=
    C.exists_slimD3SubArcs_OBDd dec hεr hrd hrd4 hrdc hprem hθ
  refine ⟨N, γ', ?_⟩
  exact (C.slimExit_glob_rel3_of_arcs_OBDd dec zc P hεr hrd hrd4 hrdc hprem hθ γ' hdisj hU).imp
    fun Xe h => by
      have h5 := C.slimEnds_glob_of_exit_OBDd dec zc P γ' Xe h.1 h.2
      refine ⟨hdisj, hU, hsub, hend0, hnotface, h5.1, h5.2.1, h5.2.2, fun i b hf => ?_,
        C.hend_of_slimEnds_OBDd dec zc P hεr hrd hrd4 hrdc hprem hθ γ' hU hsub Xe h5.2.2⟩
      obtain ⟨e, hb, hc, hs, hk⟩ := h5.2.2 i b
      exact ⟨⟨e, hk.mpr hf⟩, hb, hc, hs⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
