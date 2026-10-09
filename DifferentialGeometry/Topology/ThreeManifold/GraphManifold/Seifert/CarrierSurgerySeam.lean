import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryCollars
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryTopology

/-!
Actual signed seam maps into abstract torus-pairing quotients. The two half-collar maps agree at
the zero section through the given matching, and therefore define a continuous signed fold.
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

private theorem surgeryHalfLift_continuous : Continuous halfSpaceOneLift := by
  have he : halfSpaceOneLift = fun t : ℝ =>
      halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ :=
    funext halfSpaceOneLift_eq
  rw [he]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t))

private theorem surgeryHalfLift_zero : halfSpaceOneLift 0 = halfZero :=
  (halfSpaceOneLift_coord halfZero).trans rfl

theorem surgery_matched_sides_equal (P : TorusPairing C) (j : Fin P.count) (t : Torus) :
    P.quotientMap (P.leftParam j t) = P.quotientMap (P.rightParam j (P.matching j t)) := by
  rw [← P.matching_eq]
  exact Quotient.sound' (P.gluing.rel_of_mem_left (P.leftParam j t).property)

def surgerySignedDomain : TopologicalSpace.Opens (Torus × ℝ) :=
  ⟨signedCollarSource, isOpen_Ioo.preimage continuous_snd⟩

def surgerySeamMap (P : TorusPairing C) (j : Fin P.count)
    (p : surgerySignedDomain) : P.QuotientSpace :=
  if p.val.2 ≤ 0 then P.quotientMap (P.leftCollar j
    (p.val.1, halfSpaceOneLift (-p.val.2)))
  else P.quotientMap (P.rightCollar j (P.matching j p.val.1, halfSpaceOneLift p.val.2))

theorem surgerySeamMap_zero (P : TorusPairing C) (j : Fin P.count) (t : Torus) :
    P.surgerySeamMap j ⟨(t, 0), by constructor <;> norm_num⟩ =
      P.quotientMap (P.leftParam j t) := by
  simp only [surgerySeamMap, le_refl, ↓reduceIte, neg_zero, surgeryHalfLift_zero, P.left_zero]

theorem surgerySeamMap_continuous (P : TorusPairing C) (j : Fin P.count) :
    Continuous (P.surgerySeamMap j) := by
  have hcoord : Continuous (fun p : surgerySignedDomain => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hfst : Continuous (fun p : surgerySignedDomain => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hleft : Continuous (fun p : surgerySignedDomain => P.quotientMap
      (P.leftCollar j (p.val.1, halfSpaceOneLift (-p.val.2)))) := by
    apply P.quotientMap.continuous.comp
    apply (P.leftCollar j).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (hfst.prodMk (surgeryHalfLift_continuous.comp hcoord.neg))
    intro p
    change (p.val.1, halfSpaceOneLift (-p.val.2)) ∈ (P.leftCollar j).source
    rw [P.left_source]
    change max (-p.val.2) 0 < 1
    exact max_lt (by linarith [p.property.1]) zero_lt_one
  have hright : Continuous (fun p : surgerySignedDomain => P.quotientMap
      (P.rightCollar j (P.matching j p.val.1, halfSpaceOneLift p.val.2))) := by
    apply P.quotientMap.continuous.comp
    apply (P.rightCollar j).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (((P.matching j).contMDiff.continuous.comp hfst).prodMk
        (surgeryHalfLift_continuous.comp hcoord))
    intro p
    change (P.matching j p.val.1, halfSpaceOneLift p.val.2) ∈ (P.rightCollar j).source
    rw [P.right_source]
    change max p.val.2 0 < 1
    exact max_lt p.property.2 zero_lt_one
  apply Continuous.if ?_ hleft hright
  intro p hp
  have hbound := hcoord.frontier_preimage_subset (Iic (0 : ℝ)) hp
  have hz : p.val.2 = 0 := by
    simpa only [mem_preimage, frontier_Iic, mem_singleton_iff, Function.comp_apply] using hbound
  rw [hz, neg_zero, surgeryHalfLift_zero, P.left_zero, P.right_zero]
  exact P.surgery_matched_sides_equal j p.val.1

private theorem surgerySideCollar_zero_mem_target (P : TorusPairing C)
    (i : Fin P.count ⊕ Fin P.count) (t : Torus) :
    P.surgerySideCollar i (t, halfZero) ∈ (P.surgerySideCollar i).target := by
  apply (P.surgerySideCollar i).map_source'
  rw [P.surgerySideCollar_source]
  change (0 : ℝ) < 1
  exact zero_lt_one

private theorem surgerySideCollar_core_index (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    {i j : Fin P.count ⊕ Fin P.count} {x : C.Carrier}
    (hx : x ∈ (P.surgerySideCollar i).target)
    (hj : x ∈ range fun t => P.surgerySideCollar j (t, halfZero)) : i = j := by
  obtain ⟨t, rfl⟩ := hj
  by_contra hij
  exact (hd hij).le_bot ⟨hx, P.surgerySideCollar_zero_mem_target j t⟩

theorem surgery_quotientMap_injOn_sideCollar (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (i : Fin P.count ⊕ Fin P.count) :
    InjOn P.quotientMap (P.surgerySideCollar i).target := by
  intro x hx y hy hxy
  rcases (P.surgery_quotientMap_eq_iff x y).mp hxy with h | ⟨j, hj, hjy⟩
  · exact h
  · rcases hj with hj | hj
    · have hxl : x ∈ range fun t => P.surgerySideCollar (.inl j) (t, halfZero) := by
        change x ∈ range fun t => P.leftCollar j (t, halfZero)
        rwa [P.leftCollar_zero_range]
      have hyr : y ∈ range fun t => P.surgerySideCollar (.inr j) (t, halfZero) := by
        change y ∈ range fun t => P.rightCollar j (t, halfZero)
        rw [P.rightCollar_zero_range, hjy, P.gluing.flip_of_mem_left hj]
        exact (P.gluing.attaching j ⟨x, hj⟩).property
      have hi := P.surgerySideCollar_core_index hd hx hxl
      have hi' := P.surgerySideCollar_core_index hd hy hyr
      exact (Sum.inl_ne_inr (hi.symm.trans hi')).elim
    · have hxr : x ∈ range fun t => P.surgerySideCollar (.inr j) (t, halfZero) := by
        change x ∈ range fun t => P.rightCollar j (t, halfZero)
        rwa [P.rightCollar_zero_range]
      have hyl : y ∈ range fun t => P.surgerySideCollar (.inl j) (t, halfZero) := by
        change y ∈ range fun t => P.leftCollar j (t, halfZero)
        rw [P.leftCollar_zero_range, hjy, P.gluing.flip_of_mem_right hj]
        exact ((P.gluing.attaching j).symm ⟨x, hj⟩).property
      have hi := P.surgerySideCollar_core_index hd hx hxr
      have hi' := P.surgerySideCollar_core_index hd hy hyl
      exact (Sum.inr_ne_inl (hi.symm.trans hi')).elim

private theorem surgery_halfZero_source : (halfZero : EuclideanHalfSpace 1).1 0 < 1 :=
  zero_lt_one

theorem surgery_quotientMap_cross_collar (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {p q : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hq : q ∈ halfCollarSource)
    (hxy : P.quotientMap (P.leftCollar j p) = P.quotientMap (P.rightCollar j q)) :
    p.2 = halfZero ∧ q.2 = halfZero ∧ q.1 = P.matching j p.1 := by
  have hpl : p ∈ (P.leftCollar j).source := (P.left_source j).symm ▸ hp
  have hqr : q ∈ (P.rightCollar j).source := (P.right_source j).symm ▸ hq
  have hxl := (P.leftCollar j).map_source' hpl
  have hyr := (P.rightCollar j).map_source' hqr
  rcases (P.surgery_quotientMap_eq_iff _ _).mp hxy with he | ⟨k, hk, he⟩
  · have hdj := hd (Sum.inl_ne_inr : Sum.inl j ≠ Sum.inr j)
    exact (hdj.le_bot ⟨hxl, he.symm ▸ hyr⟩).elim
  · rcases hk with hk | hk
    · have hcore : P.leftCollar j p ∈ range fun t =>
          P.surgerySideCollar (.inl k) (t, halfZero) := by
        change P.leftCollar j p ∈ range fun t => P.leftCollar k (t, halfZero)
        rwa [P.leftCollar_zero_range]
      have hjk : j = k := Sum.inl.inj (P.surgerySideCollar_core_index hd (i := Sum.inl j) hxl hcore)
      subst k
      let t := (P.leftParam j).symm ⟨P.leftCollar j p, hk⟩
      have htp : P.leftCollar j (t, halfZero) = P.leftCollar j p := by
        rw [P.left_zero]
        exact congrArg Subtype.val
          ((P.leftParam j).apply_symm_apply ⟨P.leftCollar j p, hk⟩)
      have htz : (t, halfZero) ∈ (P.leftCollar j).source := by
        rw [P.left_source]
        exact surgery_halfZero_source
      have hpe : p = (t, halfZero) := ((P.leftCollar j).injOn htz hpl htp).symm
      rw [hpe, P.left_zero] at he
      rw [P.gluing.flip_of_mem_left (P.leftParam j t).property] at he
      have hmatch := congrArg Subtype.val (P.matching_eq j t)
      have hqe : P.rightCollar j q = P.rightCollar j (P.matching j t, halfZero) :=
        he.trans (hmatch.trans (P.right_zero j (P.matching j t)).symm)
      have hqz : (P.matching j t, halfZero) ∈ (P.rightCollar j).source := by
        rw [P.right_source]
        exact surgery_halfZero_source
      have hqeq := (P.rightCollar j).injOn hqr hqz hqe
      rw [hpe, hqeq]
      exact ⟨rfl, rfl, rfl⟩
    · have hcore : P.leftCollar j p ∈ range fun t =>
          P.surgerySideCollar (.inr k) (t, halfZero) := by
        change P.leftCollar j p ∈ range fun t => P.rightCollar k (t, halfZero)
        rwa [P.rightCollar_zero_range]
      have hi := P.surgerySideCollar_core_index hd (i := Sum.inl j) hxl hcore
      exact (Sum.inl_ne_inr hi).elim

private theorem surgeryHalfLift_nonpos {s : ℝ} (hs : halfSpaceOneLift s = halfZero) : s ≤ 0 := by
  have hcoord := congrArg (fun h : EuclideanHalfSpace 1 => h.1 0) hs
  change max s 0 = 0 at hcoord
  exact (le_max_left s 0).trans hcoord.le

private theorem surgerySigned_left_source (P : TorusPairing C) (j : Fin P.count)
    (p : surgerySignedDomain) :
    (p.val.1, halfSpaceOneLift (-p.val.2)) ∈ (P.leftCollar j).source := by
  rw [P.left_source]
  change max (-p.val.2) 0 < 1
  exact max_lt (by linarith [p.property.1]) zero_lt_one

private theorem surgerySigned_right_source (P : TorusPairing C) (j : Fin P.count)
    (p : surgerySignedDomain) :
    (P.matching j p.val.1, halfSpaceOneLift p.val.2) ∈ (P.rightCollar j).source := by
  rw [P.right_source]
  change max p.val.2 0 < 1
  exact max_lt p.property.2 zero_lt_one

theorem surgerySeamMap_injective (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : Function.Injective (P.surgerySeamMap j) := by
  intro p q hpq
  by_cases hp : p.val.2 ≤ 0
  · by_cases hq : q.val.2 ≤ 0
    · simp only [surgerySeamMap, hp, hq, ↓reduceIte] at hpq
      have he := P.surgery_quotientMap_injOn_sideCollar hd (.inl j)
        ((P.leftCollar j).map_source' (P.surgerySigned_left_source j p))
        ((P.leftCollar j).map_source' (P.surgerySigned_left_source j q)) hpq
      have he' := (P.leftCollar j).injOn (P.surgerySigned_left_source j p)
        (P.surgerySigned_left_source j q) he
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.1) he'
      · have hc := congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.2.1 0) he'
        change max (-p.val.2) 0 = max (-q.val.2) 0 at hc
        rw [max_eq_left (neg_nonneg.mpr hp), max_eq_left (neg_nonneg.mpr hq)] at hc
        linarith
    · simp only [surgerySeamMap, hp, hq, ↓reduceIte] at hpq
      have hcross := P.surgery_quotientMap_cross_collar hd j
        ((P.left_source j) ▸ P.surgerySigned_left_source j p)
        ((P.right_source j) ▸ P.surgerySigned_right_source j q) hpq
      exact (hq (surgeryHalfLift_nonpos hcross.2.1)).elim
  · by_cases hq : q.val.2 ≤ 0
    · simp only [surgerySeamMap, hp, hq, ↓reduceIte] at hpq
      have hcross := P.surgery_quotientMap_cross_collar hd j
        ((P.left_source j) ▸ P.surgerySigned_left_source j q)
        ((P.right_source j) ▸ P.surgerySigned_right_source j p) hpq.symm
      exact (hp (surgeryHalfLift_nonpos hcross.2.1)).elim
    · simp only [surgerySeamMap, hp, hq, ↓reduceIte] at hpq
      have he := P.surgery_quotientMap_injOn_sideCollar hd (.inr j)
        ((P.rightCollar j).map_source' (P.surgerySigned_right_source j p))
        ((P.rightCollar j).map_source' (P.surgerySigned_right_source j q)) hpq
      have he' := (P.rightCollar j).injOn (P.surgerySigned_right_source j p)
        (P.surgerySigned_right_source j q) he
      apply Subtype.ext
      apply Prod.ext
      · exact (P.matching j).injective (congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.1) he')
      · have hc := congrArg (fun z : Torus × EuclideanHalfSpace 1 => z.2.1 0) he'
        change max p.val.2 0 = max q.val.2 0 at hc
        rw [max_eq_left (le_of_not_ge hp), max_eq_left (le_of_not_ge hq)] at hc
        exact hc

theorem surgerySeamMap_range (P : TorusPairing C) (j : Fin P.count) :
    range (P.surgerySeamMap j) =
      P.quotientMap '' ((P.leftCollar j).target ∪ (P.rightCollar j).target) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : p.val.2 ≤ 0
    · simp only [surgerySeamMap, hp, ↓reduceIte]
      exact ⟨P.leftCollar j (p.val.1, halfSpaceOneLift (-p.val.2)),
        Or.inl ((P.leftCollar j).map_source' (P.surgerySigned_left_source j p)), rfl⟩
    · simp only [surgerySeamMap, hp, ↓reduceIte]
      exact ⟨P.rightCollar j (P.matching j p.val.1, halfSpaceOneLift p.val.2),
        Or.inr ((P.rightCollar j).map_source' (P.surgerySigned_right_source j p)), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · let v := (P.leftCollar j).symm y
      have hv := (P.leftCollar j).map_target' hy
      have hv1 : v.2.1 0 < 1 := by rwa [P.left_source] at hv
      let p : surgerySignedDomain := ⟨(v.1, -v.2.1 0), by
        constructor <;> linarith [v.2.property]⟩
      refine ⟨p, ?_⟩
      simp only [surgerySeamMap, p, neg_nonpos.mpr v.2.property, ↓reduceIte, neg_neg]
      rw [halfSpaceOneLift_coord]
      exact congrArg P.quotientMap ((P.leftCollar j).right_inv' hy)
    · let v := (P.rightCollar j).symm y
      have hv := (P.rightCollar j).map_target' hy
      have hv1 : v.2.1 0 < 1 := by rwa [P.right_source] at hv
      by_cases hv0 : 0 < v.2.1 0
      · let p : surgerySignedDomain := ⟨((P.matching j).symm v.1, v.2.1 0), by
          constructor <;> linarith [v.2.property]⟩
        refine ⟨p, ?_⟩
        simp only [surgerySeamMap, p, not_le.mpr hv0, ↓reduceIte,
          Diffeomorph.apply_symm_apply]
        rw [halfSpaceOneLift_coord]
        exact congrArg P.quotientMap ((P.rightCollar j).right_inv' hy)
      · have hzero : v.2.1 0 = 0 := le_antisymm (le_of_not_gt hv0) v.2.property
        have hve : v.2 = halfZero := by
          rw [← halfSpaceOneLift_coord v.2, hzero]
          exact surgeryHalfLift_zero
        refine ⟨⟨((P.matching j).symm v.1, 0), by constructor <;> norm_num⟩, ?_⟩
        rw [P.surgerySeamMap_zero, P.surgery_matched_sides_equal,
          Diffeomorph.apply_symm_apply]
        apply congrArg P.quotientMap
        rw [← P.right_zero]
        have he : (v.1, halfZero) = v := Prod.ext rfl hve.symm
        exact (congrArg (P.rightCollar j) he).trans ((P.rightCollar j).right_inv' hy)

private theorem surgerySideCollar_core_mem_target (P : TorusPairing C)
    (i : Fin P.count ⊕ Fin P.count) {x : C.Carrier}
    (hx : x ∈ range fun t => P.surgerySideCollar i (t, halfZero)) :
    x ∈ (P.surgerySideCollar i).target := by
  obtain ⟨t, rfl⟩ := hx
  exact P.surgerySideCollar_zero_mem_target i t

private theorem surgerySeamUnion_rel (P : TorusPairing C)
    (hd : Pairwise fun i k => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar k).target)
    (j : Fin P.count) {x y : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target)
    (hxy : P.gluing.rel x y) :
    y ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
  rcases hxy with rfl | ⟨k, hk, hy⟩
  · exact hx
  · rcases hx with hx | hx
    · rcases hk with hk | hk
      · have hcore : x ∈ range fun t => P.surgerySideCollar (.inl k) (t, halfZero) := by
          change x ∈ range fun t => P.leftCollar k (t, halfZero)
          rwa [P.leftCollar_zero_range]
        have hjk : j = k := Sum.inl.inj
          (P.surgerySideCollar_core_index hd (i := Sum.inl j) hx hcore)
        subst k
        right
        apply P.surgerySideCollar_core_mem_target (.inr j)
        change y ∈ range fun t => P.rightCollar j (t, halfZero)
        rw [P.rightCollar_zero_range, hy, P.gluing.flip_of_mem_left hk]
        exact (P.gluing.attaching j ⟨x, hk⟩).property
      · have hcore : x ∈ range fun t => P.surgerySideCollar (.inr k) (t, halfZero) := by
          change x ∈ range fun t => P.rightCollar k (t, halfZero)
          rwa [P.rightCollar_zero_range]
        exact (Sum.inl_ne_inr
          (P.surgerySideCollar_core_index hd (i := Sum.inl j) hx hcore)).elim
    · rcases hk with hk | hk
      · have hcore : x ∈ range fun t => P.surgerySideCollar (.inl k) (t, halfZero) := by
          change x ∈ range fun t => P.leftCollar k (t, halfZero)
          rwa [P.leftCollar_zero_range]
        exact (Sum.inr_ne_inl
          (P.surgerySideCollar_core_index hd (i := Sum.inr j) hx hcore)).elim
      · have hcore : x ∈ range fun t => P.surgerySideCollar (.inr k) (t, halfZero) := by
          change x ∈ range fun t => P.rightCollar k (t, halfZero)
          rwa [P.rightCollar_zero_range]
        have hjk : j = k := Sum.inr.inj
          (P.surgerySideCollar_core_index hd (i := Sum.inr j) hx hcore)
        subst k
        left
        apply P.surgerySideCollar_core_mem_target (.inl j)
        change y ∈ range fun t => P.leftCollar j (t, halfZero)
        rw [P.leftCollar_zero_range, hy, P.gluing.flip_of_mem_right hk]
        exact ((P.gluing.attaching j).symm ⟨x, hk⟩).property

theorem surgerySeamMap_isOpen_range (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : IsOpen (range (P.surgerySeamMap j)) := by
  rw [P.surgerySeamMap_range]
  apply isOpen_quotient_mk_image_of_saturated
  · intro x y hxy
    exact ⟨fun hx => P.surgerySeamUnion_rel hd j hx hxy,
      fun hy => P.surgerySeamUnion_rel hd j hy (P.gluing.setoid.symm hxy)⟩
  · exact (P.leftCollar j).open_target.union (P.rightCollar j).open_target

theorem surgerySeamMap_preimage_range (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : P.quotientMap ⁻¹' range (P.surgerySeamMap j) =
      (P.leftCollar j).target ∪ (P.rightCollar j).target := by
  rw [P.surgerySeamMap_range]
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact P.surgerySeamUnion_rel hd j hy ((P.surgery_quotientMap_eq_iff y x).mp hyx)
  · intro hx
    exact ⟨x, hx, rfl⟩

def surgerySeamInverseCoordinates (P : TorusPairing C) (j : Fin P.count)
    (x : C.Carrier) : Torus × ℝ := by
  classical
  exact if x ∈ (P.leftCollar j).target then
    (((P.leftCollar j).symm x).1, -((P.leftCollar j).symm x).2.1 0)
  else ((P.matching j).symm ((P.rightCollar j).symm x).1,
    ((P.rightCollar j).symm x).2.1 0)

theorem surgerySeamInverseCoordinates_continuousOn (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : ContinuousOn (P.surgerySeamInverseCoordinates j)
      ((P.leftCollar j).target ∪ (P.rightCollar j).target) := by
  intro x hx
  rcases hx with hx | hx
  · have hc := (P.leftCollar j).toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      ((P.leftCollar j).open_target.mem_nhds hx)
    have hs : ContinuousAt (fun y => (((P.leftCollar j).symm y).1,
        -((P.leftCollar j).symm y).2.1 0)) x := hc.fst.prodMk
      ((contMDiff_halfSpaceOneCoordinate.continuous.continuousAt.comp hc.snd).neg)
    apply (hs.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(P.leftCollar j).open_target.mem_nhds hx] with y hy
    simp only [surgerySeamInverseCoordinates, hy, ↓reduceIte]
  · have hc := (P.rightCollar j).toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      ((P.rightCollar j).open_target.mem_nhds hx)
    have hs : ContinuousAt (fun y => ((P.matching j).symm ((P.rightCollar j).symm y).1,
        ((P.rightCollar j).symm y).2.1 0)) x :=
      ((P.matching j).symm.contMDiff.continuous.continuousAt.comp hc.fst).prodMk
        (contMDiff_halfSpaceOneCoordinate.continuous.continuousAt.comp hc.snd)
    apply (hs.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(P.rightCollar j).open_target.mem_nhds hx] with y hy
    have hyl : y ∉ (P.leftCollar j).target := fun hl =>
      (hd (Sum.inl_ne_inr : Sum.inl j ≠ Sum.inr j)).le_bot ⟨hl, hy⟩
    simp only [surgerySeamInverseCoordinates, hyl, ↓reduceIte]

theorem surgerySeamInverseCoordinates_mem (P : TorusPairing C) (j : Fin P.count)
    {x : C.Carrier} (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    P.surgerySeamInverseCoordinates j x ∈ signedCollarSource := by
  classical
  by_cases hxl : x ∈ (P.leftCollar j).target
  · have hs := (P.leftCollar j).map_target' hxl
    rw [P.left_source] at hs
    change ((P.leftCollar j).symm x).2.1 0 < 1 at hs
    have hn := ((P.leftCollar j).symm x).2.property
    simp only [surgerySeamInverseCoordinates, hxl, ↓reduceIte, signedCollarSource, mem_ofPred_eq]
    constructor <;> linarith
  · have hxr := hx.resolve_left hxl
    have hs := (P.rightCollar j).map_target' hxr
    rw [P.right_source] at hs
    change ((P.rightCollar j).symm x).2.1 0 < 1 at hs
    have hn := ((P.rightCollar j).symm x).2.property
    simp only [surgerySeamInverseCoordinates, hxl, ↓reduceIte, signedCollarSource, mem_ofPred_eq]
    constructor <;> linarith

theorem surgerySeamInverseCoordinates_fold (P : TorusPairing C) (j : Fin P.count)
    {x : C.Carrier} (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    P.surgerySeamMap j
      ⟨P.surgerySeamInverseCoordinates j x, P.surgerySeamInverseCoordinates_mem j hx⟩ =
        P.quotientMap x := by
  classical
  by_cases hxl : x ∈ (P.leftCollar j).target
  · simp only [surgerySeamInverseCoordinates, hxl, ↓reduceIte, surgerySeamMap]
    rw [ite_eq_left (neg_nonpos.mpr ((P.leftCollar j).symm x).2.property), neg_neg,
      halfSpaceOneLift_coord]
    exact congrArg P.quotientMap ((P.leftCollar j).right_inv' hxl)
  · have hxr := hx.resolve_left hxl
    simp only [surgerySeamInverseCoordinates, hxl, ↓reduceIte, surgerySeamMap]
    by_cases hzero : ((P.rightCollar j).symm x).2.1 0 ≤ 0
    · rw [ite_eq_left hzero]
      have hezero : ((P.rightCollar j).symm x).2.1 0 = 0 :=
        le_antisymm hzero ((P.rightCollar j).symm x).2.property
      rw [hezero, neg_zero, surgeryHalfLift_zero, P.left_zero,
        P.surgery_matched_sides_equal, Diffeomorph.apply_symm_apply]
      apply congrArg P.quotientMap
      rw [← P.right_zero]
      have hv : ((P.rightCollar j).symm x).2 = halfZero := by
        rw [← halfSpaceOneLift_coord ((P.rightCollar j).symm x).2, hezero]
        exact surgeryHalfLift_zero
      have he : (((P.rightCollar j).symm x).1, halfZero) = (P.rightCollar j).symm x :=
        Prod.ext rfl hv.symm
      exact (congrArg (P.rightCollar j) he).trans ((P.rightCollar j).right_inv' hxr)
    · rw [ite_eq_right hzero, Diffeomorph.apply_symm_apply, halfSpaceOneLift_coord]
      exact congrArg P.quotientMap ((P.rightCollar j).right_inv' hxr)

def surgerySeamHomeomorph (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : surgerySignedDomain ≃ₜ range (P.surgerySeamMap j) := by
  classical
  let e := Equiv.ofInjective (P.surgerySeamMap j) (P.surgerySeamMap_injective hd j)
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact (P.surgerySeamMap_continuous j).subtype_mk (fun p => mem_range_self p)
  · let V := range (P.surgerySeamMap j)
    have hquot : IsQuotientMap P.quotientMap := isQuotientMap_quotient_mk'
    have hquotV := hquot.restrictPreimage_isOpen (P.surgerySeamMap_isOpen_range hd j)
    have hxU : ∀ x : P.quotientMap ⁻¹' V,
        x.val ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
      intro x
      have hx : x.val ∈ P.quotientMap ⁻¹' range (P.surgerySeamMap j) := x.property
      exact (P.surgerySeamMap_preimage_range hd j).subset hx
    have hc : Continuous (fun x : P.quotientMap ⁻¹' V =>
        P.surgerySeamInverseCoordinates j x.val) :=
      (P.surgerySeamInverseCoordinates_continuousOn hd j).comp_continuous
        continuous_subtype_val hxU
    have heq : (fun x : P.quotientMap ⁻¹' V =>
        (e.symm (V.restrictPreimage P.quotientMap x)).val) =
        fun x => P.surgerySeamInverseCoordinates j x.val := by
      funext x
      have he : e.symm (V.restrictPreimage P.quotientMap x) =
          ⟨P.surgerySeamInverseCoordinates j x.val,
            P.surgerySeamInverseCoordinates_mem j (hxU x)⟩ := by
        apply e.injective
        rw [e.apply_symm_apply]
        apply Subtype.ext
        exact (P.surgerySeamInverseCoordinates_fold j (hxU x)).symm
      exact congrArg Subtype.val he
    apply hquotV.continuous_iff.mpr
    apply continuous_induced_rng.2
    change Continuous (fun x : P.quotientMap ⁻¹' V =>
      (e.symm (V.restrictPreimage P.quotientMap x)).val)
    rw [heq]
    exact hc

private theorem surgerySignedDomain_nonempty : Nonempty surgerySignedDomain :=
  ⟨⟨((1, 1), 0), by constructor <;> norm_num⟩⟩

def surgerySignedSeam (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : OpenPartialHomeomorph (Torus × ℝ) P.QuotientSpace :=
  let V : TopologicalSpace.Opens P.QuotientSpace :=
    ⟨range (P.surgerySeamMap j), P.surgerySeamMap_isOpen_range hd j⟩
  let e := P.surgerySeamHomeomorph hd j
  let hV : Nonempty V := Nonempty.map e surgerySignedDomain_nonempty
  ((surgerySignedDomain.openPartialHomeomorphSubtypeCoe
    surgerySignedDomain_nonempty).symm.trans e.toOpenPartialHomeomorph).trans
      (V.openPartialHomeomorphSubtypeCoe hV)

theorem surgerySignedSeam_source (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : (P.surgerySignedSeam hd j).source = signedCollarSource := by
  simp only [surgerySignedSeam, OpenPartialHomeomorph.trans_source,
    Opens.openPartialHomeomorphSubtypeCoe_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, OpenPartialHomeomorph.symm_source,
    Opens.openPartialHomeomorphSubtypeCoe_target]
  rfl

theorem surgerySignedSeam_apply (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    P.surgerySignedSeam hd j p = P.surgerySeamMap j ⟨p, hp⟩ := by
  let a := surgerySignedDomain.openPartialHomeomorphSubtypeCoe surgerySignedDomain_nonempty
  have hpa : p ∈ a.target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hp
  have ha : a.symm p = ⟨p, hp⟩ := Subtype.ext (a.right_inv hpa)
  change (P.surgerySeamHomeomorph hd j (a.symm p)).val = P.surgerySeamMap j ⟨p, hp⟩
  rw [ha]
  rfl

theorem surgerySignedSeam_target (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) : (P.surgerySignedSeam hd j).target = range (P.surgerySeamMap j) := by
  simp only [surgerySignedSeam, OpenPartialHomeomorph.trans_target,
    Opens.openPartialHomeomorphSubtypeCoe_target, Homeomorph.toOpenPartialHomeomorph_target,
    OpenPartialHomeomorph.symm_target, Opens.openPartialHomeomorphSubtypeCoe_source,
    preimage_univ, inter_univ]
  rfl

theorem surgerySignedSeam_disjoint (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) :
    Pairwise fun i j => Disjoint (P.surgerySignedSeam hd i).target
      (P.surgerySignedSeam hd j).target := by
  intro i j hij
  rw [P.surgerySignedSeam_target hd i, P.surgerySignedSeam_target hd j,
    P.surgerySeamMap_range i, P.surgerySeamMap_range j, disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxj := P.surgerySeamUnion_rel hd j hy ((P.surgery_quotientMap_eq_iff y x).mp hyx)
  rcases hx with hx | hx
  · rcases hxj with hxj | hxj
    · exact (hd (fun h => hij (Sum.inl.inj h))).le_bot ⟨hx, hxj⟩
    · exact (hd (Sum.inl_ne_inr : Sum.inl i ≠ Sum.inr j)).le_bot ⟨hx, hxj⟩
  · rcases hxj with hxj | hxj
    · exact (hd (Sum.inr_ne_inl : Sum.inr i ≠ Sum.inl j)).le_bot ⟨hx, hxj⟩
    · exact (hd (fun h => hij (Sum.inr.inj h))).le_bot ⟨hx, hxj⟩

private theorem surgeryHalfLift_halfPoint (s : ℝ) (hs : 0 ≤ s) :
    halfSpaceOneLift s = halfPoint s hs :=
  (halfPoint_eq_self (halfSpaceOneLift s) hs (max_eq_left hs).symm).symm

theorem surgerySignedSeam_zero (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) (t : Torus) :
    P.surgerySignedSeam hd j (t, 0) = P.quotientMap (P.leftParam j t) := by
  rw [P.surgerySignedSeam_apply hd j (t, 0) (by constructor <;> norm_num)]
  exact P.surgerySeamMap_zero j t

theorem surgerySignedSeam_negative (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) (t : Torus) (s : ℝ) (hs : s ≤ 0) (hs1 : -1 < s) :
    P.surgerySignedSeam hd j (t, s) =
      P.quotientMap (P.leftCollar j (t, halfPoint (-s) (neg_nonneg.mpr hs))) := by
  rw [P.surgerySignedSeam_apply hd j (t, s) ⟨hs1, hs.trans_lt zero_lt_one⟩]
  simp only [surgerySeamMap, hs, ↓reduceIte, surgeryHalfLift_halfPoint (-s) (neg_nonneg.mpr hs)]

theorem surgerySignedSeam_positive (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) (t : Torus) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    P.surgerySignedSeam hd j (t, s) =
      P.quotientMap (P.rightCollar j (P.matching j t, halfPoint s hs)) := by
  by_cases hzero : s ≤ 0
  · have he : s = 0 := le_antisymm hzero hs
    subst s
    rw [P.surgerySignedSeam_zero hd j t, P.surgery_matched_sides_equal]
    change P.quotientMap (P.rightParam j (P.matching j t)) =
      P.quotientMap (P.rightCollar j (P.matching j t, halfZero))
    rw [P.right_zero]
  · rw [P.surgerySignedSeam_apply hd j (t, s) ⟨(by linarith), hs1⟩]
    simp only [surgerySeamMap, hzero, ↓reduceIte, surgeryHalfLift_halfPoint s hs]

end GC.GraphManifold.TorusPairing
