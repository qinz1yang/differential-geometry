import DifferentialGeometry.Topology.PlanarJordan.PolygonalCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalArcBall

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies PiecewiseLinear

private theorem mapsTo_of_eqOn_compl (e : Plane ≃ₜ Plane) {U : Set Plane}
    (he : EqOn e id Uᶜ) : MapsTo e U U := by
  intro x hx
  by_contra hnot
  have heq : e x = x := e.injective (he hnot)
  exact hnot (heq.symm ▸ hx)

private theorem arc_subset_of_diff_subset {R U : Set Plane} {p q : Plane}
    (hR : IsArcBetween R p q) (hU : IsClosed U) (hsub : R \ {p, q} ⊆ U) : R ⊆ U := by
  have hclose := closure_minimal hsub hU
  intro x hx
  by_cases he : x ∈ ({p, q} : Set Plane)
  · rcases he with rfl | rfl
    · exact hclose hR.left_mem_closure_diff
    · exact hclose hR.right_mem_closure_diff
  · exact hsub ⟨hx, he⟩

private theorem crosscut_subset_or_subset {D U V Q R : Set Plane} {p q : Plane}
    (hU : IsPLBall 2 U) (hV : IsPLBall 2 V) (hunion : U ∪ V = D) (hinter : U ∩ V = Q)
    (hUF : frontier U ⊆ frontier D ∪ Q) (hVF : frontier V ⊆ frontier D ∪ Q)
    (hQU : Q ⊆ frontier U) (hR : IsArcBetween R p q)
    (hRI : R \ {p, q} ⊆ interior D) (hRQ : Disjoint (R \ {p, q}) Q) : R ⊆ U ∨ R ⊆ V := by
  have hdis : Disjoint (interior U) (interior V) := by
    refine disjoint_left.mpr fun x hxU hxV => ?_
    exact (hQU (hinter ▸ ⟨interior_subset hxU, interior_subset hxV⟩)).2 hxU
  have hcover : R \ {p, q} ⊆ interior U ∪ interior V := by
    intro x hx
    have hxQ : x ∉ Q := fun hxQ => disjoint_left.mp hRQ hx hxQ
    have hxD := hRI hx
    rcases hunion.symm ▸ interior_subset hxD with hxU | hxV
    · refine Or.inl ((mem_interior_iff_notMem_frontier hxU).mpr fun hxF => ?_)
      exact (hUF hxF).elim (fun h => h.2 hxD) hxQ
    · refine Or.inr ((mem_interior_iff_notMem_frontier hxV).mpr fun hxF => ?_)
      exact (hVF hxF).elim (fun h => h.2 hxD) hxQ
  exact (hR.isPreconnected_diff.subset_or_subset isOpen_interior isOpen_interior hdis hcover).imp
    (fun h => arc_subset_of_diff_subset hR hU.isPolyhedron.isClosed (h.trans interior_subset))
    (fun h => arc_subset_of_diff_subset hR hV.isPolyhedron.isClosed (h.trans interior_subset))

private theorem exists_polygonal_crosscut_family {ι : Type*} (s : Finset ι)
    {D : Set Plane} {P : ι → Set Plane} {p q : ι → Plane}
    (hD : IsPLBall 2 D) (hP : ∀ i ∈ s, IsArcBetween (P i) (p i) (q i))
    (hp : ∀ i ∈ s, p i ∈ frontier D) (hq : ∀ i ∈ s, q i ∈ frontier D)
    (hPI : ∀ i ∈ s, P i \ {p i, q i} ⊆ interior D)
    (hdis : (s : Set ι).Pairwise fun i j => P i ∩ P j ⊆ frontier D) :
    ∃ e : Plane ≃ₜ Plane, (∀ i ∈ s, IsPolygonal (e '' P i)) ∧ EqOn e id (interior D)ᶜ := by
  classical
  induction s using Finset.strongInductionOn generalizing D P p q with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨Homeomorph.refl Plane, by simp, fun _ _ => rfl⟩
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨e, hepoly, hefix, _⟩ := exists_homeomorph_polygonal_crosscut
      hD (hP a ha) (hp a ha) (hq a ha) (hPI a ha)
    let R (i : ι) := e '' P i
    have hep (i : ι) (hi : i ∈ s) : e (p i) = p i := hefix (hp i hi).2
    have heq (i : ι) (hi : i ∈ s) : e (q i) = q i := hefix (hq i hi).2
    have hR (i : ι) (hi : i ∈ s) : IsArcBetween (R i) (p i) (q i) := by
      simpa only [hep i hi, heq i hi] using isArcBetween_image e (hP i hi)
    have hRI (i : ι) (hi : i ∈ s) : R i \ {p i, q i} ⊆ interior D := by
      rintro y ⟨⟨x, hx, rfl⟩, hends⟩
      apply mapsTo_of_eqOn_compl e hefix
      apply hPI i hi
      refine ⟨hx, ?_⟩
      rintro (rfl | rfl)
      · exact hends (Or.inl (hep i hi))
      · exact hends (Or.inr (heq i hi))
    have hRdis : (s : Set ι).Pairwise fun i j => R i ∩ R j ⊆ frontier D := by
      intro i hi j hj hij y hy
      obtain ⟨x, hx, rfl⟩ := hy.1
      obtain ⟨z, hz, hzx⟩ := hy.2
      have hxF := hdis hi hj hij ⟨hx, e.injective hzx ▸ hz⟩
      rw [hefix hxF.2]
      exact hxF
    have hcross : IsCrosscut (frontier D) (R a) (p a) (q a) :=
      ⟨isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier, hR a ha, hepoly,
        hp a ha, hq a ha, by rw [← hD.interior_eq_inside_frontier]; exact hRI a ha⟩
    obtain ⟨U, V, hU, hV, hunion, hinter, hUF, hVF, hQU, hQV, _⟩ :=
      exists_isPLBall_pair_of_isCrosscut hD
        (isPLBall_one_of_isArcBetween_of_isPolygonal (hR a ha) hepoly) hcross
    have hUD : U ⊆ D := subset_union_left.trans hunion.subset
    have hVD : V ⊆ D := subset_union_right.trans hunion.subset
    have hside (i : ι) (hi : i ∈ s.erase a) : R i ⊆ U ∨ R i ⊆ V :=
      crosscut_subset_or_subset hU hV hunion hinter hUF hVF hQU
        (hR i (Finset.mem_erase.mp hi).2) (hRI i (Finset.mem_erase.mp hi).2)
        (disjoint_left.mpr fun x hx hxQ =>
          (hRdis (Finset.mem_erase.mp hi).2 ha (Finset.mem_erase.mp hi).1 ⟨hx.1, hxQ⟩).2
            (hRI i (Finset.mem_erase.mp hi).2 hx))
    let t := (s.erase a).filter fun i => R i ⊆ U
    let u := (s.erase a).filter fun i => ¬R i ⊆ U
    have ht : t ⊂ s := (Finset.filter_subset _ _).trans_ssubset (Finset.erase_ssubset ha)
    have hu : u ⊂ s := (Finset.filter_subset _ _).trans_ssubset (Finset.erase_ssubset ha)
    have htU (i : ι) (hi : i ∈ t) : R i ⊆ U := (Finset.mem_filter.mp hi).2
    have huV (i : ι) (hi : i ∈ u) : R i ⊆ V :=
      (hside i (Finset.mem_filter.mp hi).1).resolve_left (Finset.mem_filter.mp hi).2
    have htrace {W : Set Plane} (hW : W ⊆ D) {i : ι} (hi : i ∈ s) (hRW : R i ⊆ W) :
        p i ∈ frontier W ∧ q i ∈ frontier W := by
      exact ⟨⟨subset_closure (hRW (hR i hi).left_mem),
          fun hx => (hp i hi).2 (interior_mono hW hx)⟩,
        ⟨subset_closure (hRW (hR i hi).right_mem),
          fun hx => (hq i hi).2 (interior_mono hW hx)⟩⟩
    have hopen {W : Set Plane} (hWF : frontier W ⊆ frontier D ∪ R a)
        {i : ι} (hi : i ∈ s.erase a) (hRW : R i ⊆ W) :
        R i \ {p i, q i} ⊆ interior W := by
      intro x hx
      apply (mem_interior_iff_notMem_frontier (hRW hx.1)).mpr
      intro hxF
      rcases hWF hxF with hxD | hxQ
      · exact hxD.2 (hRI i (Finset.mem_erase.mp hi).2 hx)
      · exact (hRdis (Finset.mem_erase.mp hi).2 ha (Finset.mem_erase.mp hi).1
          ⟨hx.1, hxQ⟩).2 (hRI i (Finset.mem_erase.mp hi).2 hx)
    obtain ⟨f, hfpoly, hffix⟩ := ih t ht hU (fun i hi => hR i (ht.subset hi))
      (fun i hi => (htrace hUD (ht.subset hi) (htU i hi)).1)
      (fun i hi => (htrace hUD (ht.subset hi) (htU i hi)).2)
      (fun i hi => hopen hUF (Finset.mem_filter.mp hi).1 (htU i hi))
      (fun i hi j hj hij x hx =>
        ⟨subset_closure (htU i hi hx.1), fun hxU =>
          (hRdis (ht.subset hi) (ht.subset hj) hij hx).2 (interior_mono hUD hxU)⟩)
    obtain ⟨g, hgpoly, hgfix⟩ := ih u hu hV (fun i hi => hR i (hu.subset hi))
      (fun i hi => (htrace hVD (hu.subset hi) (huV i hi)).1)
      (fun i hi => (htrace hVD (hu.subset hi) (huV i hi)).2)
      (fun i hi => hopen hVF (Finset.mem_filter.mp hi).1 (huV i hi))
      (fun i hi j hj hij x hx =>
        ⟨subset_closure (huV i hi hx.1), fun hxV =>
          (hRdis (hu.subset hi) (hu.subset hj) hij hx).2 (interior_mono hVD hxV)⟩)
    have hfV : EqOn f id V := by
      intro x hxV
      apply hffix
      intro hxU
      exact (hQU (hinter ▸ ⟨interior_subset hxU, hxV⟩)).2 hxU
    have hgU : EqOn g id U := by
      intro x hxU
      apply hgfix
      intro hxV
      exact (hQV (hinter ▸ ⟨hxU, interior_subset hxV⟩)).2 hxV
    have hfU : MapsTo f U U := mapsTo_of_eqOn_compl f
      (hffix.mono (compl_subset_compl.mpr interior_subset))
    refine ⟨(e.trans f).trans g, ?_, ?_⟩
    · intro i hi
      change IsPolygonal ((g ∘ f ∘ e) '' P i)
      rw [image_comp, image_comp]
      change IsPolygonal (g '' (f '' R i))
      by_cases hia : i = a
      · subst i
        rw [((hfV.mono (hQV.trans hV.isPolyhedron.isClosed.frontier_subset)).image_eq),
          image_id, ((hgU.mono (hQU.trans hU.isPolyhedron.isClosed.frontier_subset)).image_eq),
          image_id]
        exact hepoly
      · have hierase : i ∈ s.erase a := Finset.mem_erase.mpr ⟨hia, hi⟩
        by_cases hiU : R i ⊆ U
        · have hit : i ∈ t := Finset.mem_filter.mpr ⟨hierase, hiU⟩
          rw [(hgU.mono (hfU.image_subset.trans' (image_mono hiU))).image_eq, image_id]
          exact hfpoly i hit
        · have hiu : i ∈ u := Finset.mem_filter.mpr ⟨hierase, hiU⟩
          rw [(hfV.mono (huV i hiu)).image_eq, image_id]
          exact hgpoly i hiu
    · intro x hx
      change g (f (e x)) = x
      rw [hefix hx, id_eq, hffix (fun hxU => hx (interior_mono hUD hxU)), id_eq,
        hgfix (fun hxV => hx (interior_mono hVD hxV))]
      rfl

theorem exists_homeomorph_polygonal_crosscuts_in_disk {ι : Type*} (s : Finset ι)
    {D : Set Plane} {P : ι → Set Plane} {p q : ι → Plane}
    (hD : IsPLBall 2 D) (hP : ∀ i ∈ s, IsArcBetween (P i) (p i) (q i))
    (hp : ∀ i ∈ s, p i ∈ frontier D) (hq : ∀ i ∈ s, q i ∈ frontier D)
    (hPI : ∀ i ∈ s, P i \ {p i, q i} ⊆ interior D)
    (hdis : (s : Set ι).Pairwise fun i j => P i ∩ P j ⊆ frontier D) :
    ∃ e : Plane ≃ₜ Plane, (∀ i ∈ s, IsPolygonal (e '' P i)) ∧
      EqOn e id (interior D)ᶜ ∧ ∀ x, dist (e x) x ≤ Metric.diam D := by
  obtain ⟨e, he, hefix⟩ := exists_polygonal_crosscut_family s hD hP hp hq hPI hdis
  refine ⟨e, he, hefix, fun x => ?_⟩
  by_cases hx : x ∈ D
  · exact Metric.dist_le_diam_of_mem hD.isPolyhedron.isCompact.isBounded
      (mapsTo_of_eqOn_compl e (hefix.mono (compl_subset_compl.mpr interior_subset)) hx) hx
  · rw [hefix (fun h => hx (interior_subset h)), id_eq, dist_self]
    exact Metric.diam_nonneg

end DifferentialGeometry.Topology.PlanarJordan
