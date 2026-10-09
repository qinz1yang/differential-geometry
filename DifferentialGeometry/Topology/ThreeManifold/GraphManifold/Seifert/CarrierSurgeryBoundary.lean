import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryDifferential
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!+# Intrinsic boundary of the actual torus surgery quotient

The actual signed seams and interior patches lie in the intrinsic quotient interior. The free
half collars meet the intrinsic boundary exactly at zero height, so the quotient boundary is
precisely the image of the original retained tori. This ledger applies to both quotient models.
-/

set_option autoImplicit false
noncomputable section
open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff
universe u

namespace GC.Seifert

theorem surgeryHalfCollar_isBoundaryPoint_iff (p : Torus × EuclideanHalfSpace 1) :
    halfCollarModel.IsBoundaryPoint p ↔ p.2.val 0 = 0 := by
  have hi : halfCollarModel.IsInteriorPoint p ↔ 0 < p.2.val 0 := by
    change p ∈ halfCollarModel.interior (Torus × EuclideanHalfSpace 1) ↔ 0 < p.2.val 0
    rw [ModelWithCorners.interior_prod]
    constructor
    · intro hp
      have hh := hp.2
      change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint p.2 at hh
      rw [ModelWithCorners.IsInteriorPoint,
        interior_range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh
    · intro hp
      refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
      change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint p.2
      rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
      exact hp
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, hi, not_lt]
  exact ⟨fun hp => le_antisymm hp p.2.property, fun hp => hp.le⟩

end GC.Seifert

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}} (P : TorusPairing C) (D : C.Components) {n : ℕ}
  (E : BoundaryTori C n)
  (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
    (P.surgerySideCollar j).target)
  (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
  (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
  {k : CarrierModel} [ChartedSpace k.Space P.QuotientSpace]
  (hpatch : ∀ i, ContMDiffOn (P.surgeryPatchModel n i) k.model ∞
      (P.surgeryPatch D E hd he hb i) (P.surgeryPatch D E hd he hb i).source ∧
    ContMDiffOn k.model (P.surgeryPatchModel n i) ∞
      (P.surgeryPatch D E hd he hb i).symm (P.surgeryPatch D E hd he hb i).target)

include D E hd he hb hpatch in
theorem surgerySignedSeam_target_interior (j : Fin P.count) :
    (P.surgerySignedSeam hd j).target ⊆ k.model.interior P.QuotientSpace := by
  intro q hq
  let S := P.surgerySeamDiffeomorphism D E hd he hb hpatch j
  have hqs : q ∈ S.symm.source := hq
  exact ((S.symm.isLocalDiffeomorphAt k.model signedCollarModel ∞ hqs).isInteriorPoint_iff
    (by simp)).mpr BoundarylessManifold.isInteriorPoint

include D E hd he hb hpatch in
theorem surgeryInteriorPatch_target_interior :
    (P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)).target ⊆
      k.model.interior P.QuotientSpace := by
  intro q hq
  let S := P.surgeryInteriorDiffeomorphism D E hd he hb hpatch
  have hqs : q ∈ S.symm.source := hq
  have hx : C.model.IsInteriorPoint (S.symm q) := by
    have hh := S.toOpenPartialHomeomorph.map_target hq
    change S.symm q ∈ (P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)).source at hh
    rw [P.surgeryInteriorPatch_source] at hh
    exact hh
  exact ((S.symm.isLocalDiffeomorphAt k.model C.model ∞ hqs).isInteriorPoint_iff
    (by simp)).mpr hx

include D E hd he hb hpatch in
theorem surgeryExternalDiffeomorphism_boundary_iff (j : Fin n)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    k.model.IsBoundaryPoint (P.surgeryExternalDiffeomorphism D E hd he hb hpatch j p) ↔
      p.2.val 0 = 0 := by
  let S := P.surgeryExternalDiffeomorphism D E hd he hb hpatch j
  have hps : p ∈ S.source := by
    change p ∈ (P.surgeryExternalCollar E he j).source
    rwa [P.surgeryExternalCollar_source]
  exact ((S.isLocalDiffeomorphAt halfCollarModel k.model ∞ hps).isBoundaryPoint_iff
    (by simp)).symm.trans (surgeryHalfCollar_isBoundaryPoint_iff p)

include D E hd he hb hpatch in
theorem surgeryExternal_zero_boundary (j : Fin n) (t : Torus) :
    k.model.IsBoundaryPoint (P.quotientMap (E.torusMap j t)) := by
  have hh := (P.surgeryExternalDiffeomorphism_boundary_iff D E hd he hb hpatch j
    (zero_mem_halfCollarSource t)).mpr rfl
  change k.model.IsBoundaryPoint (P.surgeryExternalCollar E he j (t, halfZero)) at hh
  rw [P.surgeryExternalCollar_apply E he j (zero_mem_halfCollarSource t)] at hh
  exact hh

include D E hd he hb hpatch in
theorem surgeryQuotient_boundary :
    k.model.boundary P.QuotientSpace = P.quotientMap '' E.image := by
  ext q
  constructor
  · intro hq
    rcases P.surgeryPatches_cover D E hd he hb q with hi | hs | hext
    · exact False.elim (k.model.disjoint_interior_boundary.le_bot
        ⟨P.surgeryInteriorPatch_target_interior D E hd he hb hpatch hi, hq⟩)
    · obtain ⟨j, hj⟩ := hs
      exact False.elim (k.model.disjoint_interior_boundary.le_bot
        ⟨P.surgerySignedSeam_target_interior D E hd he hb hpatch j hj, hq⟩)
    · obtain ⟨j, hj⟩ := hext
      let S := P.surgeryExternalDiffeomorphism D E hd he hb hpatch j
      let p := S.symm q
      have hp : p ∈ halfCollarSource := by
        have hh := S.toOpenPartialHomeomorph.map_target hj
        change p ∈ (P.surgeryExternalCollar E he j).source at hh
        rwa [P.surgeryExternalCollar_source] at hh
      have hSq : S p = q := S.toOpenPartialHomeomorph.right_inv hj
      have h0 : p.2.val 0 = 0 :=
        (P.surgeryExternalDiffeomorphism_boundary_iff D E hd he hb hpatch j hp).mp (hSq.symm ▸ hq)
      have hp0 : p = (p.1, halfZero) :=
        Prod.ext rfl (halfPoint_eq_self p.2 le_rfl h0.symm).symm
      refine ⟨E.torusMap j p.1, mem_iUnion.mpr ⟨j, ⟨p.1, rfl⟩⟩, ?_⟩
      rw [hp0] at hSq
      change P.surgeryExternalCollar E he j (p.1, halfZero) = q at hSq
      rw [P.surgeryExternalCollar_apply E he j (zero_mem_halfCollarSource p.1)] at hSq
      exact hSq
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hx
    exact P.surgeryExternal_zero_boundary D E hd he hb hpatch j t

end GC.GraphManifold.TorusPairing
