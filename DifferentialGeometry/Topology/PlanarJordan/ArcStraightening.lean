/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.CrosscutFamily
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarArcNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DiskFrontierPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplement

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies PiecewiseLinear

private theorem exists_interval_subarc_in_interior {f : ℝ → Plane} {D : Set Plane}
    (hf : ContinuousOn f unitInterval) (h0 : f 0 ∉ interior D) (h1 : f 1 ∉ interior D)
    {t : ℝ} (ht : t ∈ unitInterval) (htD : f t ∈ interior D) :
    ∃ a ∈ unitInterval, ∃ b ∈ unitInterval, a < t ∧ t < b ∧
      f a ∈ frontier D ∧ f b ∈ frontier D ∧ f '' Ioo a b ⊆ interior D := by
  have hleft : IsCompact (Icc 0 t ∩ f ⁻¹' (interior D)ᶜ) :=
    isCompact_Icc.of_isClosed_subset
      ((hf.mono (Icc_subset_Icc_right ht.2)).preimage_isClosed_of_isClosed
        isClosed_Icc isOpen_interior.isClosed_compl) inter_subset_left
  have hright : IsCompact (Icc t 1 ∩ f ⁻¹' (interior D)ᶜ) :=
    isCompact_Icc.of_isClosed_subset
      ((hf.mono (Icc_subset_Icc_left ht.1)).preimage_isClosed_of_isClosed
        isClosed_Icc isOpen_interior.isClosed_compl) inter_subset_left
  obtain ⟨a, ha, hmax⟩ := hleft.exists_isGreatest ⟨0, ⟨le_rfl, ht.1⟩, h0⟩
  obtain ⟨b, hb, hmin⟩ := hright.exists_isLeast ⟨1, ⟨ht.2, le_rfl⟩, h1⟩
  have hat : a < t := lt_of_le_of_ne ha.1.2 (fun heq => ha.2 (heq.symm ▸ htD))
  have htb : t < b := lt_of_le_of_ne hb.1.1 (fun heq => hb.2 (heq ▸ htD))
  have hab := hat.trans htb
  have haI : a ∈ unitInterval := ⟨ha.1.1, ha.1.2.trans ht.2⟩
  have hbI : b ∈ unitInterval := ⟨ht.1.trans hb.1.1, hb.1.2⟩
  have hsub : Ioo a b ⊆ unitInterval := fun u hu => ⟨haI.1.trans hu.1.le, hu.2.le.trans hbI.2⟩
  have hint : ∀ u ∈ Ioo a b, f u ∈ interior D := by
    intro u hu
    by_contra hnot
    rcases le_total u t with hut | htu
    · exact (not_le_of_gt hu.1) (hmax ⟨⟨haI.1.trans hu.1.le, hut⟩, hnot⟩)
    · exact (not_le_of_gt hu.2) (hmin ⟨⟨htu, hu.2.le.trans hbI.2⟩, hnot⟩)
  have hfa : f a ∈ closure (interior D) := ((hf a haI).mono hsub).mem_closure
    (by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩) hint
  have hfb : f b ∈ closure (interior D) := ((hf b hbI).mono hsub).mem_closure
    (by rw [closure_Ioo hab.ne]; exact ⟨hab.le, le_rfl⟩) hint
  exact ⟨a, haI, b, hbI, hat, htb, ⟨closure_mono interior_subset hfa, ha.2⟩,
    ⟨closure_mono interior_subset hfb, hb.2⟩, image_subset_iff.mpr hint⟩

theorem exists_homeomorph_polygonal_arc_of_finite_frontier_inter
    {A D : Set Plane} {p q : Plane} (hA : IsArcBetween A p q) (hD : IsPLBall 2 D)
    (hp : p ∉ interior D) (hq : q ∉ interior D)
    (hfin : (A ∩ frontier D).Finite) (hout : IsPolyhedron (A \ interior D)) :
    ∃ e : Plane ≃ₜ Plane, IsPolygonal (e '' A) ∧ EqOn e id (interior D)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam D := by
  classical
  obtain ⟨f, hf, hi, himage, hf0, hf1⟩ := hA
  let F := unitInterval ∩ f ⁻¹' frontier D
  have hF : F.Finite := (hfin.subset (show f '' F ⊆ A ∩ frontier D from by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨himage ▸ mem_image_of_mem f ht.1, ht.2⟩)).of_finite_image (hi.mono inter_subset_left)
  let _ : Finite F := hF.to_subtype
  let I := {ab : F × F // ab.1.1 < ab.2.1 ∧ f '' Ioo ab.1.1 ab.2.1 ⊆ interior D}
  let _ : Fintype I := Fintype.ofFinite I
  let B (i : I) := f '' Icc i.1.1.1 i.1.2.1
  let a (i : I) := f i.1.1.1
  let b (i : I) := f i.1.2.1
  have hBI (i : I) : Icc i.1.1.1 i.1.2.1 ⊆ unitInterval :=
    Icc_subset_Icc i.1.1.2.1.1 i.1.2.2.1.2
  have hB (i : I) : IsArcBetween (B i) (a i) (b i) := by
    simpa only [uIcc_of_le i.2.1.le] using
      isArcBetween_subarc_of_injOn_I hf hi i.1.1.2.1 i.1.2.2.1 i.2.1.ne
  have hBp (i : I) : a i ∈ frontier D := i.1.1.2.2
  have hBq (i : I) : b i ∈ frontier D := i.1.2.2.2
  have hBinside (i : I) : B i \ {a i, b i} ⊆ interior D := by
    rintro x ⟨⟨u, hu, rfl⟩, hends⟩
    apply i.2.2
    refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_⟩, rfl⟩
    · rintro rfl
      exact hends (Or.inl rfl)
    · rintro rfl
      exact hends (Or.inr rfl)
  have hBdis : Pairwise fun i j : I => B i ∩ B j ⊆ frontier D := by
    intro i j hij x hx
    obtain ⟨u, hu, rfl⟩ := hx.1
    obtain ⟨v, hv, hvu⟩ := hx.2
    have huv := hi (hBI j hv) (hBI i hu) hvu
    subst v
    by_contra hxF
    have hia : i.1.1.1 < u := lt_of_le_of_ne hu.1 (fun h => hxF (h ▸ hBp i))
    have hib : u < i.1.2.1 := lt_of_le_of_ne hu.2 (fun h => hxF (h.symm ▸ hBq i))
    have hja : j.1.1.1 < u := lt_of_le_of_ne hv.1 (fun h => hxF (h ▸ hBp j))
    have hjb : u < j.1.2.1 := lt_of_le_of_ne hv.2 (fun h => hxF (h.symm ▸ hBq j))
    have hleft : i.1.1.1 = j.1.1.1 := by
      rcases lt_trichotomy i.1.1.1 j.1.1.1 with h | h | h
      · exact ((hBp j).2 (i.2.2 ⟨j.1.1.1, ⟨h, hja.trans hib⟩, rfl⟩)).elim
      · exact h
      · exact ((hBp i).2 (j.2.2 ⟨i.1.1.1, ⟨h, hia.trans hjb⟩, rfl⟩)).elim
    have hright : i.1.2.1 = j.1.2.1 := by
      rcases lt_trichotomy i.1.2.1 j.1.2.1 with h | h | h
      · exact ((hBq i).2 (j.2.2 ⟨i.1.2.1, ⟨hja.trans hib, h⟩, rfl⟩)).elim
      · exact h
      · exact ((hBq j).2 (i.2.2 ⟨j.1.2.1, ⟨hia.trans hjb, h⟩, rfl⟩)).elim
    exact hij (Subtype.ext (Prod.ext (Subtype.ext hleft) (Subtype.ext hright)))
  have hcover : A = (A \ interior D) ∪ ⋃ i : I, B i := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxI : x ∈ interior D
      · obtain ⟨t, ht, rfl⟩ := himage.symm ▸ hx
        obtain ⟨l, hl, u, hu, hlt, htu, hlf, huf, hint⟩ :=
          exists_interval_subarc_in_interior hf (hf0.symm ▸ hp) (hf1.symm ▸ hq) ht hxI
        let i : I := ⟨(⟨l, hl, hlf⟩, ⟨u, hu, huf⟩), hlt.trans htu, hint⟩
        exact Or.inr (mem_iUnion.mpr ⟨i, t, ⟨hlt.le, htu.le⟩, rfl⟩)
      · exact Or.inl ⟨hx, hxI⟩
    · refine union_subset sdiff_subset (iUnion_subset fun i => ?_)
      exact (image_mono (hBI i)).trans himage.subset
  obtain ⟨e, heB, hefix, hedist⟩ := exists_homeomorph_polygonal_crosscuts_in_disk
    (Finset.univ : Finset I) hD (fun i _ => hB i) (fun i _ => hBp i) (fun i _ => hBq i)
    (fun i _ => hBinside i) (fun i _ j _ hij => hBdis hij)
  have himagepoly : IsPolyhedron (e '' A) := by
    rw [hcover]
    rw [image_union, image_iUnion, (hefix.mono (show A \ interior D ⊆ (interior D)ᶜ from
      fun _ hx => hx.2)).image_eq, image_id]
    exact hout.union (IsPolyhedron.iUnion fun i =>
      (isPLBall_one_of_isArcBetween_of_isPolygonal (isArcBetween_image e (hB i))
        (heB i (Finset.mem_univ i))).isPolyhedron)
  have hA : IsArcBetween A p q := ⟨f, hf, hi, himage, hf0, hf1⟩
  exact ⟨e, himagepoly.isPolygonal_of_isArcBetween (isArcBetween_image e hA), hefix, hedist⟩

theorem exists_homeomorph_polygonal_arc_of_polygonal_ends
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hl : IsPolygonal (f '' Icc 0 a)) (hr : IsPolygonal (f '' Icc b 1))
    {U : Set Plane} (hU : U ∈ 𝓝ˢ (f '' Icc a b)) :
    ∃ D, IsPLBall 2 D ∧ f '' Icc a b ⊆ interior D ∧ D ⊆ U ∧
      Disjoint D {f 0, f 1} ∧ ∃ e : Plane ≃ₜ Plane,
        IsPolygonal (e '' (f '' unitInterval)) ∧ EqOn e id (interior D)ᶜ ∧
        ∀ x, dist (e x) x ≤ Metric.diam D := by
  have haI : a ∈ unitInterval := ⟨ha.le, hab.le.trans hb.le⟩
  have hbI : b ∈ unitInterval := ⟨ha.le.trans hab.le, hb.le⟩
  have hCI : Icc a b ⊆ unitInterval := Icc_subset_Icc ha.le hb.le
  have hCA : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    simpa only [uIcc_of_le hab.le] using
      isArcBetween_subarc_of_injOn_I hf hi haI hbI hab.ne
  have hlA : IsArcBetween (f '' Icc 0 a) (f 0) (f a) := by
    simpa only [uIcc_of_le ha.le] using
      isArcBetween_subarc_of_injOn_I hf hi zero_mem_I haI ha.ne
  have hrA : IsArcBetween (f '' Icc b 1) (f b) (f 1) := by
    simpa only [uIcc_of_le hb.le] using
      isArcBetween_subarc_of_injOn_I hf hi hbI one_mem_I hb.ne
  let T := (f '' Icc 0 a) ∪ (f '' Icc b 1)
  have hlB := isPLBall_one_of_isArcBetween_of_isPolygonal hlA hl
  have hrB := isPLBall_one_of_isArcBetween_of_isPolygonal hrA hr
  have hT : IsPolyhedron T := hlB.isPolyhedron.union hrB.isPolyhedron
  have hTI : interior T = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hlB.isPolyhedron.isClosed
      (hrB.interior_eq_empty_of_lt_finrank (by simp))]
    exact hlB.interior_eq_empty_of_lt_finrank (by simp)
  have hTA : T ⊆ f '' unitInterval := union_subset
    (image_mono (Icc_subset_Icc_right haI.2)) (image_mono (Icc_subset_Icc_left hbI.1))
  have hcover : f '' unitInterval ⊆ T ∪ (f '' Icc a b) := by
    rintro x ⟨t, ht, rfl⟩
    by_cases hta : t ≤ a
    · exact Or.inl (Or.inl ⟨t, ⟨ht.1, hta⟩, rfl⟩)
    by_cases hbt : b ≤ t
    · exact Or.inl (Or.inr ⟨t, ⟨hbt, ht.2⟩, rfl⟩)
    exact Or.inr ⟨t, ⟨(lt_of_not_ge hta).le, (lt_of_not_ge hbt).le⟩, rfl⟩
  have hCZ : f '' Icc a b ⊆ ({f 0, f 1} : Set Plane)ᶜ := by
    rintro x ⟨t, ht, rfl⟩ (h0 | h1)
    · have heq := hi (hCI ht) zero_mem_I h0
      linarith [ht.1]
    · have heq := hi (hCI ht) one_mem_I h1
      linarith [ht.2]
  have hZclosed : IsClosed ({f 0, f 1} : Set Plane) := ((finite_singleton (f 1)).insert (f
      0)).isClosed
  obtain ⟨V, hV, hCV, hVU⟩ := mem_nhdsSet_iff_exists.mp hU
  obtain ⟨D, hD, hCD, hDV⟩ := exists_isPLBall_neighborhood_of_isArc hCA.isArc
    ((hV.sdiff hZclosed).mem_nhdsSet.mpr (subset_inter hCV hCZ))
  obtain ⟨D', hD', hCD', hD'V, hD'Z, hfinite⟩ :=
    hD.exists_isPLBall_finite_frontier_inter hCA.isArc.isClosed hCD hZclosed
      (disjoint_left.mpr fun x hx => (hDV hx).2) hT hTI hV
      (hDV.trans inter_subset_left)
  have hfin : ((f '' unitInterval) ∩ frontier D').Finite := hfinite.subset fun x hx =>
    ⟨hx.2, (hcover hx.1).resolve_right fun h => hx.2.2 (hCD' h)⟩
  have hout : IsPolyhedron ((f '' unitInterval) \ interior D') := by
    have heq : (f '' unitInterval) \ interior D' = T \ interior D' :=
      Subset.antisymm (fun _ hx => ⟨(hcover hx.1).resolve_right fun h => hx.2 (hCD' h), hx.2⟩)
        (fun _ hx => ⟨hTA hx.1, hx.2⟩)
    rw [heq]
    exact hT.sdiff_interior_of_isPLBall hD'
  obtain ⟨e, he, hfix, hdist⟩ := exists_homeomorph_polygonal_arc_of_finite_frontier_inter
    ⟨f, hf, hi, rfl, rfl, rfl⟩ hD'
    (fun hx => disjoint_left.mp hD'Z (interior_subset hx) (Or.inl rfl))
    (fun hx => disjoint_left.mp hD'Z (interior_subset hx) (Or.inr rfl)) hfin hout
  exact ⟨D', hD', hCD', hD'V.trans hVU, hD'Z, e, he, hfix, hdist⟩
end DifferentialGeometry.Topology.PlanarJordan
