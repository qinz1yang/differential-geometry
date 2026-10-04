import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryDescentLedger
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOrientation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

/-!
# Actual quotient orientation from the original cut orientation

The orientation pushed through the actual quotient fold agrees on identified representatives.
Actual inverse patch maps give smooth local representatives of this orientation field. Seam
orientations supply the required representatives on the paired zero sections.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff
universe u

namespace GC.Seifert

private theorem surgeryOrientation_reindex_cancel {F : Type*}
    [AddCommGroup F] [Module ℝ F] {n m : ℕ} (h : n = m)
    (o : Orientation ℝ F (Fin m)) :
    Orientation.reindex ℝ F (finCongr h)
      (Orientation.reindex ℝ F (finCongr h.symm) o) = o := by
  have he : (finCongr h.symm).symm = finCongr h := by
    ext i
    rfl
  rw [← he, ← Orientation.reindex_symm]
  exact Equiv.symm_apply_apply _ _

section Local

variable {F H M Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {k : CarrierModel} [TopologicalSpace Q]
  [ChartedSpace k.Space Q] [IsManifold k.model ∞ Q]

private theorem surgeryOrientation_local_of_patch
    (d : PartialDiffeomorph I k.model M Q ∞) (o : ManifoldOrientation I M 3)
    (f : Q → Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3))
    (hf : ∀ x (hx : x ∈ d.source), Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv d hx) (o.orientation x) = f (d x)) :
    ∃ a : SmoothOrientation k.model (⟨d.target, d.open_target⟩ : Opens Q),
      ∀ y, a.val y = Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
        (finCongr finrank_euclideanSpace_fin.symm) (f y.val) := by
  let s := smoothOrientationOfManifoldOrientation I
    (OrientationAssembly.reindexManifoldOrientation I (finCongr o.dimension_eq.symm) o)
  let U : Opens Q := ⟨d.target, d.open_target⟩
  let a : SmoothOrientation k.model U :=
    DifferentialGeometry.PartialDiffeomorph.pullbackSmoothOrientation d.symm
      (fun y hy => hy) s
  refine ⟨a, ?_⟩
  intro y
  let x := d.symm y.val
  have hx : x ∈ d.source := d.toOpenPartialHomeomorph.map_target y.property
  have hxy : d x = y.val := d.toOpenPartialHomeomorph.right_inv y.property
  have hs := (tangentOrientationEquiv_reindex_eq_iff
    (carrierSurgeryPatchTangentEquiv d hx) o.dimension_eq finrank_euclideanSpace_fin
    (o.orientation x) (f (d x))).mpr (hf x hx)
  change tangentOrientationEquiv (carrierSurgeryPatchTangentEquiv d hx) (s.val x) =
    Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
      (finCongr finrank_euclideanSpace_fin.symm) (f (d x)) at hs
  have hi := carrierSurgeryPatchTangentEquiv_symm d.symm y.property
  change carrierSurgeryPatchTangentEquiv d hx =
    (carrierSurgeryPatchTangentEquiv d.symm y.property).symm at hi
  have ha := DifferentialGeometry.PartialDiffeomorph.pullbackSmoothOrientation_apply
    d.symm (fun z hz => hz) s y
  change a.val y = tangentOrientationEquiv
    (carrierSurgeryPatchTangentEquiv d.symm y.property).symm (s.val x) at ha
  exact ha.trans ((congrArg (fun L => tangentOrientationEquiv L (s.val x)) hi.symm).trans
    (hs.trans (congrArg (fun z => Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
      (finCongr finrank_euclideanSpace_fin.symm) (f z)) hxy)))

end Local

end GC.Seifert


namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}} (P : TorusPairing C) (D : C.Components) {n : ℕ}
  (E : BoundaryTori C n)
  (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
    (P.surgerySideCollar j).target)
  (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
  (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
  {k : CarrierModel} [ChartedSpace k.Space P.QuotientSpace]
  [IsManifold k.model ∞ P.QuotientSpace]
  (hpatch : ∀ i, ContMDiffOn (P.surgeryPatchModel n i) k.model ∞
      (P.surgeryPatch D E hd he hb i) (P.surgeryPatch D E hd he hb i).source ∧
    ContMDiffOn k.model (P.surgeryPatchModel n i) ∞
      (P.surgeryPatch D E hd he hb i).symm (P.surgeryPatch D E hd he hb i).target)

omit [IsManifold k.model ∞ P.QuotientSpace] in
private theorem surgeryOrientation_fold_patch
    (d : PartialDiffeomorph C.model k.model C.Carrier P.QuotientSpace ∞)
    (heq : ∀ x, x ∈ d.source → d x = P.quotientMap x)
    {x : C.Carrier} (hx : x ∈ d.source) :
    P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x =
      carrierSurgeryPatchTangentEquiv d hx := by
  have hlocal : P.quotientMap =ᶠ[𝓝 x] (d : C.Carrier → P.QuotientSpace) := by
    filter_upwards [d.open_source.mem_nhds hx] with y hy
    exact (heq y hy).symm
  ext v
  exact congrArg (fun A => A v) (hlocal.mfderiv_eq (I := C.model) (I' := k.model))

set_option backward.isDefEq.respectTransparency false in
private theorem surgeryOrientation_seam_local
    (o : Fin P.count → ManifoldOrientation signedCollarModel surgerySignedDomain 3)
    (ho : ∀ (j : Fin P.count) (x : C.Carrier)
      (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target),
      Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
        (C.orientation.orientation x) =
        (o j).orientation ⟨P.surgerySeamInverseCoordinates j x,
          P.surgerySeamInverseCoordinates_mem j hx⟩)
    (f : P.QuotientSpace → Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3))
    (hf : ∀ x, f (P.quotientMap x) = Orientation.map (Fin 3)
      (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
      (C.orientation.orientation x))
    (j : Fin P.count) (q : P.QuotientSpace)
    (hq : q ∈ (P.surgerySignedSeam hd j).target) :
    ∃ U : Opens P.QuotientSpace, q ∈ U ∧
      ∃ a : SmoothOrientation k.model U, ∀ y, a.val y =
        Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
          (finCongr finrank_euclideanSpace_fin.symm) (f y.val) := by
  classical
  have hnonempty : Nonempty surgerySignedDomain :=
    ⟨⟨(1, 0), by constructor <;> norm_num⟩⟩
  let v := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := signedCollarModel) surgerySignedDomain hnonempty
  let s := P.surgerySeamDiffeomorphism D E hd he hb hpatch j
  let d := v.trans s
  have htarget : q ∈ d.target := by
    refine ⟨hq, ?_⟩
    change s.symm q ∈ v.target
    rw [show v.target = surgerySignedDomain from
      surgerySignedDomain.openPartialHomeomorphSubtypeCoe_target hnonempty]
    exact (P.surgerySignedSeam_source hd j).subset (s.map_target hq)
  have htransport : ∀ z (hz : z ∈ d.source),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hz)
        ((o j).orientation z) = f (d z) := by
    intro z hz
    obtain ⟨x, hxq⟩ := P.surgery_quotientMap_surjective (d z)
    have hxs : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
      have hxqmem : P.quotientMap x ∈ (P.surgerySignedSeam hd j).target := by
        rw [hxq]
        exact d.map_source hz |>.1
      rw [P.surgerySignedSeam_target] at hxqmem
      exact (P.surgerySeamMap_preimage_range hd j).subset hxqmem
    have hg : P.surgerySeamInverseCoordinates j x = z.val := by
      rw [← P.surgerySignedSeam_symm_quotientMap hd j hxs, hxq]
      exact s.left_inv hz.2
    have hsub : (⟨P.surgerySeamInverseCoordinates j x,
        P.surgerySeamInverseCoordinates_mem j hxs⟩ : surgerySignedDomain) = z :=
      Subtype.ext hg
    have hv : carrierSurgeryPatchTangentEquiv v hz.1 =
        LinearEquiv.refl ℝ ((EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1)) × ℝ) := by
      apply LinearEquiv.ext
      intro w
      exact DifferentialGeometry.mfderiv_subtype_val_apply surgerySignedDomain z w
    rw [← hxq, hf, P.surgeryQuotientFoldTangentEquiv_seam D E hd he hb hpatch j hxs,
      DifferentialGeometry.orientation_map_trans, ho j x hxs, hsub,
      carrierSurgeryPatchTangentEquiv_trans, hv, LinearEquiv.refl_trans]
    exact congrArg (fun A => Orientation.map (Fin 3) A ((o j).orientation z))
      (carrierSurgeryPatchTangentEquiv_congr s hz.2
        ((P.surgerySignedSeam_source hd j).symm.subset
          (P.surgerySeamInverseCoordinates_mem j hxs)) hg.symm)
  obtain ⟨a, ha⟩ := GC.Seifert.surgeryOrientation_local_of_patch d (o j) f htransport
  exact ⟨⟨d.target, d.open_target⟩, htarget, a, ha⟩


set_option backward.isDefEq.respectTransparency false in
theorem exists_surgeryQuotientOrientation
    (o : Fin P.count → ManifoldOrientation signedCollarModel surgerySignedDomain 3)
    (ho : ∀ (j : Fin P.count) (x : C.Carrier)
      (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target),
      Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
        (C.orientation.orientation x) =
        (o j).orientation ⟨P.surgerySeamInverseCoordinates j x,
          P.surgerySeamInverseCoordinates_mem j hx⟩) :
    ∃ O : ManifoldOrientation k.model P.QuotientSpace 3, ∀ x,
      Orientation.map (Fin 3)
        (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
        (C.orientation.orientation x) = O.orientation (P.quotientMap x) := by
  classical
  let f : P.QuotientSpace → Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) :=
    Quotient.lift (fun x => Orientation.map (Fin 3)
      (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
      (C.orientation.orientation x)) (fun x y hxy =>
        P.surgeryFoldOrientation_wellDefined D E hd he hb hpatch o ho (Quotient.sound hxy))
  have hf : ∀ x, f (P.quotientMap x) = Orientation.map (Fin 3)
      (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
      (C.orientation.orientation x) := fun x => rfl
  let fRank : P.QuotientSpace → Orientation ℝ (EuclideanSpace ℝ (Fin 3))
      (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) :=
    fun q => Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
    (finCongr finrank_euclideanSpace_fin.symm) (f q)
  have hlocal : ∀ q : P.QuotientSpace, ∃ U : Opens P.QuotientSpace, q ∈ U ∧
      ∃ a : SmoothOrientation k.model U, ∀ y, a.val y = fRank y.val := by
    intro q
    rcases P.surgeryPatches_cover D E hd he hb q with hi | hs | hext
    · let d := P.surgeryInteriorDiffeomorphism D E hd he hb hpatch
      have hdq : q ∈ d.target := hi
      have happly : ∀ x, x ∈ d.source → d x = P.quotientMap x := by
        intro x hx
        exact P.surgeryInteriorPatch_apply D (P.surgeryCoreBoundarySubset E hb)
          ((P.surgeryInteriorPatch_source D (P.surgeryCoreBoundarySubset E hb)).subset hx)
      have htransport : ∀ x (hx : x ∈ d.source),
          Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hx)
            (C.orientation.orientation x) = f (d x) := by
        intro x hx
        rw [happly x hx, hf,
          P.surgeryOrientation_fold_patch D E hd he hb hpatch d happly hx]
        rfl
      obtain ⟨a, ha⟩ := GC.Seifert.surgeryOrientation_local_of_patch d C.orientation f htransport
      exact ⟨⟨d.target, d.open_target⟩, hdq, a, ha⟩
    · obtain ⟨j, hj⟩ := hs
      exact P.surgeryOrientation_seam_local D E hd he hb hpatch o ho f hf j q hj
    · obtain ⟨j, hj⟩ := hext
      let s := P.surgeryExternalDiffeomorphism D E hd he hb hpatch j
      let d := (E.collar j).symm.trans s
      have hdq : q ∈ d.target := by
        refine ⟨hj, ?_⟩
        exact (E.source_eq j).symm.subset
          ((P.surgeryExternalCollar_source E he j).subset (s.map_target hj))
      have happly : ∀ x, x ∈ d.source → d x = P.quotientMap x := by
        intro x hx
        change P.surgeryExternalCollar E he j ((E.collar j).symm x) = P.quotientMap x
        have hm : (E.collar j).symm x ∈ halfCollarSource :=
          (P.surgeryExternalCollar_source E he j).subset hx.2
        exact (P.surgeryExternalCollar_apply E he j hm).trans
          (congrArg P.quotientMap ((E.collar j).right_inv' hx.1))
      have htransport : ∀ x (hx : x ∈ d.source),
          Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv d hx)
            (C.orientation.orientation x) = f (d x) := by
        intro x hx
        rw [happly x hx, hf,
          P.surgeryOrientation_fold_patch D E hd he hb hpatch d happly hx]
        rfl
      obtain ⟨a, ha⟩ := GC.Seifert.surgeryOrientation_local_of_patch d C.orientation f htransport
      exact ⟨⟨d.target, d.open_target⟩, hdq, a, ha⟩
  let S := smoothOrientationOfOpenRestrictions k.model fRank hlocal
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_smoothOrientation k.model S
  refine ⟨OrientationAssembly.reindexManifoldOrientation k.model
    (finCongr finrank_euclideanSpace_fin) O, ?_⟩
  intro x
  change Orientation.map (Fin 3)
    (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
    (C.orientation.orientation x) = Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
      (finCongr finrank_euclideanSpace_fin) (O.orientation (P.quotientMap x))
  rw [hO]
  exact (hf x).symm.trans
    (GC.Seifert.surgeryOrientation_reindex_cancel finrank_euclideanSpace_fin
      (f (P.quotientMap x))).symm

end GC.GraphManifold.TorusPairing
