import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryQuotientAtlas

/-!
Smooth patch parametrizations and the actual quotient fold in the newly installed surgery atlas.
The fold is computed locally through interior, signed seam and retained half-collar coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

attribute [local instance] uliftChartedSpace isManifold_ulift

namespace GC.Seifert

section Unlift

variable {E F H K M N Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace M]
  [TopologicalSpace N] [TopologicalSpace Q]
  [ChartedSpace H M] [ChartedSpace H N] [ChartedSpace K Q]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

theorem surgery_unlift_contMDiffOn (a : M ≃ₘ⟮I, I⟯ N)
    (e : OpenPartialHomeomorph M Q)
    (hs : ContMDiffOn I J ∞ (a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e)
      (a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).source) :
    ContMDiffOn I J ∞ e e.source := by
  intro x hx
  have hm : a x ∈ (a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).source := by
    refine ⟨mem_univ _, ?_⟩
    change a.symm (a x) ∈ e.source
    rwa [a.symm_apply_apply]
  have h := (hs.contMDiffAt
    ((a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).open_source.mem_nhds hm)).comp x
      a.contMDiff.contMDiffAt
  apply h.contMDiffWithinAt.congr
  · intro y hy
    change e y = e (a.symm (a y))
    rw [a.symm_apply_apply]
  · change e x = e (a.symm (a x))
    rw [a.symm_apply_apply]

theorem surgery_unlift_inverse_contMDiffOn (a : M ≃ₘ⟮I, I⟯ N)
    (e : OpenPartialHomeomorph M Q)
    (hs : ContMDiffOn J I ∞ (a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).symm
      (a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).target) :
    ContMDiffOn J I ∞ e.symm e.target := by
  intro q hq
  have hm : q ∈ (a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).target := by
    exact ⟨hq, mem_univ _⟩
  have h := a.symm.contMDiff.contMDiffAt.comp q
    (hs.contMDiffAt
      ((a.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).open_target.mem_nhds hm))
  apply h.contMDiffWithinAt.congr
  · intro y hy
    change e.symm y = a.symm (a (e.symm y))
    rw [a.symm_apply_apply]
  · change e.symm q = a.symm (a (e.symm q))
    rw [a.symm_apply_apply]

end Unlift

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

def surgeryInteriorDiffeomorphism : PartialDiffeomorph C.model k.model
    C.Carrier P.QuotientSpace ∞ where
  __ := P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)
  contMDiffOn_toFun := (hpatch (.inl none)).1
  contMDiffOn_invFun := (hpatch (.inl none)).2

def surgerySeamDiffeomorphism (j : Fin P.count) :
    PartialDiffeomorph signedCollarModel k.model (Torus × ℝ) P.QuotientSpace ∞ where
  __ := P.surgerySignedSeam hd j
  contMDiffOn_toFun := surgery_unlift_contMDiffOn
    (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ))
    (P.surgerySignedSeam hd j) (hpatch (.inl (some j))).1
  contMDiffOn_invFun := surgery_unlift_inverse_contMDiffOn
    (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ))
    (P.surgerySignedSeam hd j) (hpatch (.inl (some j))).2

def surgeryExternalDiffeomorphism (j : Fin n) :
    PartialDiffeomorph halfCollarModel k.model (Torus × EuclideanHalfSpace 1)
      P.QuotientSpace ∞ where
  __ := P.surgeryExternalCollar E he j
  contMDiffOn_toFun := surgery_unlift_contMDiffOn
    (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1))
    (P.surgeryExternalCollar E he j) (hpatch (.inr j)).1
  contMDiffOn_invFun := surgery_unlift_inverse_contMDiffOn
    (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1))
    (P.surgeryExternalCollar E he j) (hpatch (.inr j)).2

include D E hd he hb hpatch in
omit [IsManifold k.model ∞ P.QuotientSpace] in
theorem surgeryQuotientFold_contMDiff : ContMDiff C.model k.model ∞ P.quotientMap := by
  intro x
  rcases P.surgeryPatches_cover D E hd he hb (P.quotientMap x) with hi | hs | hext
  · have hx : x ∈ C.interior := (P.surgeryInteriorPatch_preimage_target D
      (P.surgeryCoreBoundarySubset E hb)).subset hi
    let hdif := P.surgeryInteriorDiffeomorphism (k := k) D E hd he hb hpatch
    have hm : x ∈ hdif.source := by
      change x ∈ (P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)).source
      exact (P.surgeryInteriorPatch_source D
        (P.surgeryCoreBoundarySubset E hb)).symm.subset hx
    apply (hdif.contMDiffOn.contMDiffAt (hdif.open_source.mem_nhds hm)).congr_of_eventuallyEq
    filter_upwards [C.interior.isOpen.mem_nhds hx] with y hy
    change P.quotientMap y = P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb) y
    exact (P.surgeryInteriorPatch_apply D (P.surgeryCoreBoundarySubset E hb) hy).symm
  · obtain ⟨j, hj⟩ := hs
    have hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
      rw [P.surgerySignedSeam_target] at hj
      exact (P.surgerySeamMap_preimage_range hd j).subset hj
    have hcoord := (P.surgerySeamInverseCoordinates_contMDiffOn hd j).contMDiffAt
      (((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx)
    have hm : P.surgerySeamInverseCoordinates j x ∈
        (P.surgerySeamDiffeomorphism (k := k) D E hd he hb hpatch j).source :=
      (P.surgerySignedSeam_source hd j).symm.subset (P.surgerySeamInverseCoordinates_mem j hx)
    let hdif := P.surgerySeamDiffeomorphism (k := k) D E hd he hb hpatch j
    have h := (hdif.contMDiffOn.contMDiffAt
      (hdif.open_source.mem_nhds (by simpa only [hdif] using hm))).comp x hcoord
    apply h.congr_of_eventuallyEq
    filter_upwards
      [((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx] with y hy
    exact ((P.surgerySignedSeam_apply hd j _ (P.surgerySeamInverseCoordinates_mem j hy)).trans
      (P.surgerySeamInverseCoordinates_fold j hy)).symm
  · obtain ⟨j, hj⟩ := hext
    have hx : x ∈ (E.collar j).target :=
      (P.surgeryExternalCollar_preimage_target E he j).subset hj
    have hcoord : ContMDiffAt C.model halfCollarModel ∞
        ((E.collar j).symm : C.Carrier → Torus × EuclideanHalfSpace 1) x :=
      (E.collar j).symm.contMDiffOn.contMDiffAt ((E.collar j).open_target.mem_nhds hx)
    have hm : (E.collar j).symm x ∈
        (P.surgeryExternalDiffeomorphism (k := k) D E hd he hb hpatch j).source := by
      rw [show (P.surgeryExternalDiffeomorphism (k := k) D E hd he hb hpatch j).source =
        halfCollarSource from P.surgeryExternalCollar_source E he j]
      exact (E.source_eq j).subset ((E.collar j).map_target hx)
    let hdif := P.surgeryExternalDiffeomorphism (k := k) D E hd he hb hpatch j
    have h := (hdif.contMDiffOn.contMDiffAt
      (hdif.open_source.mem_nhds (by simpa only [hdif] using hm))).comp x hcoord
    apply h.congr_of_eventuallyEq
    filter_upwards [(E.collar j).open_target.mem_nhds hx] with y hy
    have hs : (E.collar j).symm y ∈ halfCollarSource :=
      (E.source_eq j).subset ((E.collar j).map_target hy)
    change P.quotientMap y = P.surgeryExternalCollar E he j ((E.collar j).symm y)
    rw [P.surgeryExternalCollar_apply E he j hs]
    exact congrArg P.quotientMap ((E.collar j).right_inv' hy).symm

end GC.GraphManifold.TorusPairing
