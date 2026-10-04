import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryPatches

/-!
Smooth source-side transition ledgers for the actual torus quotient patches. Signed seam inverse
coordinates and exterior and interior inverse maps are computed on the original carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

theorem surgerySignedSeam_symm_quotientMap (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    (P.surgerySignedSeam hd j).symm (P.quotientMap x) =
      P.surgerySeamInverseCoordinates j x := by
  have hs := P.surgerySeamInverseCoordinates_mem j hx
  have hf : P.surgerySignedSeam hd j (P.surgerySeamInverseCoordinates j x) =
      P.quotientMap x := (P.surgerySignedSeam_apply hd j _ hs).trans
        (P.surgerySeamInverseCoordinates_fold j hx)
  rw [← hf]
  exact (P.surgerySignedSeam hd j).left_inv ((P.surgerySignedSeam_source hd j).symm ▸ hs)

theorem surgerySeamInverseCoordinates_contMDiffOn (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : ContMDiffOn C.model signedCollarModel ∞
      (P.surgerySeamInverseCoordinates j) ((P.leftCollar j).target ∪ (P.rightCollar j).target) := by
  classical
  intro x hx
  rcases hx with hx | hx
  · have hc := (P.leftCollar j).contMDiffOn_invFun.contMDiffAt
      ((P.leftCollar j).open_target.mem_nhds hx)
    have hs : ContMDiffAt C.model signedCollarModel ∞
        (fun y => (((P.leftCollar j).symm y).1, -((P.leftCollar j).symm y).2.1 0)) x :=
      hc.fst.prodMk ((contMDiff_halfSpaceOneCoordinate.contMDiffAt.comp x hc.snd).neg)
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(P.leftCollar j).open_target.mem_nhds hx] with y hy
    simp only [surgerySeamInverseCoordinates, hy, ↓reduceIte]
  · have hc := (P.rightCollar j).contMDiffOn_invFun.contMDiffAt
      ((P.rightCollar j).open_target.mem_nhds hx)
    have hs : ContMDiffAt C.model signedCollarModel ∞
        (fun y => ((P.matching j).symm ((P.rightCollar j).symm y).1,
          ((P.rightCollar j).symm y).2.1 0)) x :=
      ((P.matching j).symm.contMDiff.contMDiffAt.comp x hc.fst).prodMk
        (contMDiff_halfSpaceOneCoordinate.contMDiffAt.comp x hc.snd)
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(P.rightCollar j).open_target.mem_nhds hx] with y hy
    have hyl : y ∉ (P.leftCollar j).target := fun hl =>
      (hd (Sum.inl_ne_inr : Sum.inl j ≠ Sum.inr j)).le_bot ⟨hl, hy⟩
    simp only [surgerySeamInverseCoordinates, hyl, ↓reduceIte]

theorem contMDiffOn_surgerySignedSeam_symm_quotientMap (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : ContMDiffOn C.model signedCollarModel ∞
      (fun x => (P.surgerySignedSeam hd j).symm (P.quotientMap x))
      ((P.leftCollar j).target ∪ (P.rightCollar j).target) :=
  (P.surgerySeamInverseCoordinates_contMDiffOn hd j).congr
    (fun x hx => P.surgerySignedSeam_symm_quotientMap hd j (x := x) hx)

theorem surgeryInteriorPatch_symm_quotientMap (P : TorusPairing C) (D : C.Components)
    (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    {x : C.Carrier} (hx : x ∈ C.interior) :
    (P.surgeryInteriorPatch D hb).symm (P.quotientMap x) = x := by
  rw [← P.surgeryInteriorPatch_apply D hb hx]
  exact (P.surgeryInteriorPatch D hb).left_inv ((P.surgeryInteriorPatch_source D hb).symm ▸ hx)

theorem contMDiffOn_surgeryInteriorPatch_symm_quotientMap (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier) :
    ContMDiffOn C.model C.model ∞
      (fun x => (P.surgeryInteriorPatch D hb).symm (P.quotientMap x)) C.interior :=
  contMDiffOn_id.congr (fun x hx => P.surgeryInteriorPatch_symm_quotientMap D hb (x := x) hx)

theorem surgeryExternalPatch_symm_quotientMap (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) {x : C.Carrier} (hx : x ∈ (E.collar i).target) :
    (P.surgeryExternalPatch E he i).symm (P.quotientMap x) = x := by
  rw [← P.surgeryExternalPatch_apply E he i hx]
  exact (P.surgeryExternalPatch E he i).left_inv
    ((P.surgeryExternalPatch_source E he i).symm ▸ hx)

theorem contMDiffOn_surgeryExternalPatch_symm_quotientMap (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : ContMDiffOn C.model C.model ∞
      (fun x => (P.surgeryExternalPatch E he i).symm (P.quotientMap x)) (E.collar i).target :=
  contMDiffOn_id.congr (fun x hx => P.surgeryExternalPatch_symm_quotientMap E he i (x := x) hx)

theorem surgeryInteriorPatch_preimage_target (P : TorusPairing C) (D : C.Components)
    (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier) :
    P.quotientMap ⁻¹' (P.surgeryInteriorPatch D hb).target = C.interior := by
  rw [P.surgeryInteriorPatch_target]
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he : y = x := P.gluing.eq_of_rel_of_notMem (by
      intro j hj
      exact C.model.disjoint_interior_boundary.le_bot
        ⟨hy, hb (mem_iUnion.mpr ⟨j, hj⟩)⟩) ((P.surgery_quotientMap_eq_iff y x).mp hyx)
    exact he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem contMDiffOn_surgeryInteriorPatch_trans_seam_symm (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : ContMDiffOn C.model signedCollarModel ∞
      ((P.surgeryInteriorPatch D hb).trans (P.surgerySignedSeam hd j).symm)
      ((P.surgeryInteriorPatch D hb).trans (P.surgerySignedSeam hd j).symm).source := by
  have hsub : ((P.surgeryInteriorPatch D hb).trans (P.surgerySignedSeam hd j).symm).source ⊆
      (P.leftCollar j).target ∪ (P.rightCollar j).target := by
    intro x hx
    have hxi : x ∈ C.interior := (P.surgeryInteriorPatch_source D hb).subset hx.1
    have hq : P.quotientMap x ∈ range (P.surgerySeamMap j) := by
      have hh := hx.2
      change P.surgeryInteriorPatch D hb x ∈ (P.surgerySignedSeam hd j).target at hh
      rwa [P.surgerySignedSeam_target, P.surgeryInteriorPatch_apply D hb hxi] at hh
    exact (P.surgerySeamMap_preimage_range hd j).subset hq
  apply ((P.surgerySeamInverseCoordinates_contMDiffOn hd j).mono hsub).congr
  intro x hx
  have hxi : x ∈ C.interior := (P.surgeryInteriorPatch_source D hb).subset hx.1
  change (P.surgerySignedSeam hd j).symm (P.surgeryInteriorPatch D hb x) =
    P.surgerySeamInverseCoordinates j x
  rw [P.surgeryInteriorPatch_apply D hb hxi]
  exact P.surgerySignedSeam_symm_quotientMap hd j (hsub hx)

theorem surgerySeamInteriorTransition_height_ne_zero (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {p : Torus × ℝ}
    (hp : p ∈ ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm).source) :
    p.2 ≠ 0 := by
  intro hz
  have hq := hp.2
  change P.surgerySignedSeam hd j p ∈ (P.surgeryInteriorPatch D hb).target at hq
  have hpzero : p = (p.1, 0) := Prod.ext rfl hz
  rw [hpzero, P.surgerySignedSeam_zero] at hq
  have hi : (P.leftParam j p.1).val ∈ C.interior :=
    (P.surgeryInteriorPatch_preimage_target D hb).subset hq
  have hbound := hb (mem_iUnion.mpr ⟨j, Or.inl (P.leftParam j p.1).property⟩)
  exact C.model.disjoint_interior_boundary.le_bot ⟨hi, hbound⟩

theorem surgerySeamInteriorTransition_negative (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {p : Torus × ℝ}
    (hp : p ∈ ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm).source)
    (hs : p.2 ≤ 0) :
    ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm) p =
      P.leftCollar j (p.1, halfSpaceOneLift (-p.2)) := by
  have hps := (P.surgerySignedSeam_source hd j).subset hp.1
  have hf := P.surgerySignedSeam_apply hd j p hps
  simp only [surgerySeamMap, hs, ↓reduceIte] at hf
  have hq : P.quotientMap (P.leftCollar j (p.1, halfSpaceOneLift (-p.2))) ∈
      (P.surgeryInteriorPatch D hb).target := by
    have hh := hp.2
    change P.surgerySignedSeam hd j p ∈ (P.surgeryInteriorPatch D hb).target at hh
    rwa [hf] at hh
  have hi : P.leftCollar j (p.1, halfSpaceOneLift (-p.2)) ∈ C.interior :=
    (P.surgeryInteriorPatch_preimage_target D hb).subset hq
  change (P.surgeryInteriorPatch D hb).symm (P.surgerySignedSeam hd j p) = _
  rw [hf]
  exact P.surgeryInteriorPatch_symm_quotientMap D hb hi

theorem surgerySeamInteriorTransition_positive (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {p : Torus × ℝ}
    (hp : p ∈ ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm).source)
    (hs : 0 < p.2) :
    ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm) p =
      P.rightCollar j (P.matching j p.1, halfSpaceOneLift p.2) := by
  have hps := (P.surgerySignedSeam_source hd j).subset hp.1
  have hf := P.surgerySignedSeam_apply hd j p hps
  simp only [surgerySeamMap, not_le.mpr hs, ↓reduceIte] at hf
  have hq : P.quotientMap (P.rightCollar j (P.matching j p.1, halfSpaceOneLift p.2)) ∈
      (P.surgeryInteriorPatch D hb).target := by
    have hh := hp.2
    change P.surgerySignedSeam hd j p ∈ (P.surgeryInteriorPatch D hb).target at hh
    rwa [hf] at hh
  have hi : P.rightCollar j (P.matching j p.1, halfSpaceOneLift p.2) ∈ C.interior :=
    (P.surgeryInteriorPatch_preimage_target D hb).subset hq
  change (P.surgeryInteriorPatch D hb).symm (P.surgerySignedSeam hd j p) = _
  rw [hf]
  exact P.surgeryInteriorPatch_symm_quotientMap D hb hi

theorem contMDiffOn_surgerySeam_trans_interior_symm (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : ContMDiffOn signedCollarModel C.model ∞
      ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm)
      ((P.surgerySignedSeam hd j).trans (P.surgeryInteriorPatch D hb).symm).source := by
  intro p hp
  have hps := (P.surgerySignedSeam_source hd j).subset hp.1
  have hn := P.surgerySeamInteriorTransition_height_ne_zero D hb hd j hp
  by_cases hs : p.2 < 0
  · have hm : (p.1, halfSpaceOneLift (-p.2)) ∈ (P.leftCollar j).source := by
      rw [P.left_source]
      change max (-p.2) 0 < 1
      exact max_lt (by linarith [hps.1]) zero_lt_one
    have hlift : ContMDiffAt 𝓘(ℝ) (𝓡∂ 1) ∞ halfSpaceOneLift (-p.2) :=
      Manifold.contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds (neg_pos.mpr hs))
    have hneg : ContMDiffAt signedCollarModel 𝓘(ℝ) ∞
        (fun q : Torus × ℝ => -q.2) p := contMDiffAt_snd.neg
    have hl : ContMDiffAt signedCollarModel halfCollarModel ∞
        (fun q : Torus × ℝ => (q.1, halfSpaceOneLift (-q.2))) p :=
      contMDiffAt_fst.prodMk
        (hlift.comp (f := fun q : Torus × ℝ => -q.2) (g := halfSpaceOneLift) p hneg)
    have hf := ((P.leftCollar j).contMDiffOn.contMDiffAt
      ((P.leftCollar j).open_source.mem_nhds hm)).comp p hl
    apply (hf.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((P.surgerySignedSeam hd j).trans
      (P.surgeryInteriorPatch D hb).symm).open_source.mem_nhds hp,
      (isOpen_lt continuous_snd continuous_const).mem_nhds hs] with q hq hqs
    exact P.surgerySeamInteriorTransition_negative D hb hd j hq hqs.le
  · have hspos : 0 < p.2 := lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm hn)
    have hm : (P.matching j p.1, halfSpaceOneLift p.2) ∈ (P.rightCollar j).source := by
      rw [P.right_source]
      change max p.2 0 < 1
      exact max_lt hps.2 zero_lt_one
    have hlift : ContMDiffAt 𝓘(ℝ) (𝓡∂ 1) ∞ halfSpaceOneLift p.2 :=
      Manifold.contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds hspos)
    have hl : ContMDiffAt signedCollarModel halfCollarModel ∞
        (fun q : Torus × ℝ => (P.matching j q.1, halfSpaceOneLift q.2)) p :=
      ((P.matching j).contMDiff.contMDiffAt.comp p contMDiffAt_fst).prodMk
        (hlift.comp (f := fun q : Torus × ℝ => q.2) (g := halfSpaceOneLift) p
          contMDiffAt_snd)
    have hf := ((P.rightCollar j).contMDiffOn.contMDiffAt
      ((P.rightCollar j).open_source.mem_nhds hm)).comp p hl
    apply (hf.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((P.surgerySignedSeam hd j).trans
      (P.surgeryInteriorPatch D hb).symm).open_source.mem_nhds hp,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hspos] with q hq hqs
    exact P.surgerySeamInteriorTransition_positive D hb hd j hq hqs

end GC.GraphManifold.TorusPairing
