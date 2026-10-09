/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrosscutExtension
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

theorem ne_of_isArcBetween {S : Set Plane} {a b : Plane} (h : IsArcBetween S a b) : a ≠ b := by
  obtain ⟨f, -, hi, -, h0, h1⟩ := h
  intro hab
  exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
    (h0.trans (hab.trans h1.symm)))

theorem isCrosscut_union_of_opposite_spokes {D T₀ T₂ : Set Plane} {c v₀ v₂ : Plane}
    (hD : IsPLBall 2 D) (h0 : IsPLBall 1 T₀) (h2 : IsPLBall 1 T₂)
    (ha0 : IsArcBetween T₀ c v₀) (ha2 : IsArcBetween T₂ c v₂)
    (h0D : T₀ ⊆ D) (h2D : T₂ ⊆ D)
    (hf0 : T₀ ∩ frontier D = {v₀}) (hf2 : T₂ ∩ frontier D = {v₂})
    (hmeet : T₀ ∩ T₂ = {c}) :
    IsPLBall 1 (T₀ ∪ T₂) ∧ IsCrosscut (frontier D) (T₀ ∪ T₂) v₀ v₂ := by
  have hmeet' : ∀ z ∈ T₀, z ∈ T₂ → z = c := fun z hz hz' => hmeet.subset ⟨hz, hz'⟩
  have harc : IsArcBetween (T₀ ∪ T₂) v₀ v₂ := ha0.reverse.concatenate ha2 hmeet'
  have hball : IsPLBall 1 (T₀ ∪ T₂) :=
    isPLBall_union_of_isArcBetween h0 h2 ha0.reverse ha2 hmeet'
  have hkey : ∀ (T : Set Plane) (w z : Plane), T ⊆ D → T ∩ frontier D = {w} → z ∈ T →
      z ≠ w → z ∈ interior D := by
    intro T w z hTD hTf hzT hzw
    exact (mem_interior_iff_notMem_frontier (hTD hzT)).mpr fun hzf => hzw (hTf.subset ⟨hzT, hzf⟩)
  refine ⟨hball, isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier, harc,
    hball.isPolyhedron.isPolygonal_of_isArcBetween harc,
    (hf0.symm.subset rfl).2, (hf2.symm.subset rfl).2, ?_⟩
  rw [← hD.interior_eq_inside_frontier]
  rintro z ⟨hz, hzpq⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzpq
  exact hz.elim (fun h => hkey T₀ v₀ z h0D hf0 h hzpq.1) fun h => hkey T₂ v₂ z h2D hf2 h hzpq.2

theorem subset_inside_arc_union_of_isPreconnected {J A A₁ A₂ S : Set Plane} {p q w : Plane}
    (hcross : IsCrosscut J A p q) (hcut : IsCutPair J p q A₁ A₂)
    (hS : IsPreconnected S) (hSJ : S ⊆ inside J) (hSA : ∀ z ∈ S, z ∉ A)
    (hw : w ∈ closure S) (hwA₁ : w ∈ A₁) (hwp : w ≠ p) (hwq : w ≠ q) :
    S ⊆ inside (A₁ ∪ A) := by
  have hj : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S :=
    fun _ => Schoenflies.jordan_curve_theorem
  have hcover : S ⊆ inside (A₁ ∪ A) ∪ inside (A₂ ∪ A) := by
    rw [← hcross.inside_diff_eq hj hcut hcross.hasArcCollars]
    exact fun x hx => ⟨hSJ hx, hSA x hx⟩
  refine (IsPreconnected.subset_or_subset (hcross.isSeparating_union hj hcut).isOpen_inside
    (hcross.isSeparating_union hj hcut.symm).isOpen_inside
    (hcross.disjoint_sides hj hcut) hcover hS).resolve_right fun h2 => ?_
  have hwmem : w ∈ closure (inside (A₂ ∪ A)) ∩ J :=
    ⟨closure_mono h2 hw, hcut.fst_subset hwA₁⟩
  rw [hcross.closure_side_inter hj hcut.symm] at hwmem
  exact (hcut.inter_eq.subset ⟨hwA₁, hwmem⟩).elim hwp hwq

theorem isCrosscut_spoke_of_isCutPair {D T₀ T₁ T₂ A₁ A₂ : Set Plane} {c v₀ v₁ v₂ : Plane}
    (hD : IsPLBall 2 D) (h1 : IsPLBall 1 T₁) (hA : IsPLBall 1 (T₀ ∪ T₂))
    (ha1 : IsArcBetween T₁ c v₁) (h1D : T₁ ⊆ D) (hf1 : T₁ ∩ frontier D = {v₁})
    (h10 : T₁ ∩ T₀ = {c}) (h12 : T₁ ∩ T₂ = {c}) (hc : c ∈ T₀ ∪ T₂)
    (hcrossA : IsCrosscut (frontier D) (T₀ ∪ T₂) v₀ v₂)
    (hcut : IsCutPair (frontier D) v₀ v₂ A₁ A₂)
    (hv1 : v₁ ∈ A₁) (hne0 : v₁ ≠ v₀) (hne2 : v₁ ≠ v₂) :
    IsCrosscut (A₁ ∪ (T₀ ∪ T₂)) T₁ c v₁ := by
  have hsphere := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hA hcrossA hcut
  refine ⟨isJordanCurve_of_isPLSphere_one hsphere, ha1,
    h1.isPolyhedron.isPolygonal_of_isArcBetween ha1, Or.inr hc, Or.inl hv1, ?_⟩
  refine subset_inside_arc_union_of_isPreconnected hcrossA hcut ha1.isPreconnected_diff ?_ ?_
    (h1.subset_closure_sdiff_finite ((finite_singleton v₁).insert c) ha1.right_mem) hv1 hne0 hne2
  · rw [← hD.interior_eq_inside_frontier]
    rintro z ⟨hz, hzm⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzm
    exact (mem_interior_iff_notMem_frontier (h1D hz)).mpr fun hzf => hzm.2 (hf1.subset ⟨hz, hzf⟩)
  · rintro z ⟨hz, hzm⟩ hzA
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzm
    exact hzA.elim (fun h => hzm.1 (h10.subset ⟨hz, h⟩)) fun h => hzm.1 (h12.subset ⟨hz, h⟩)

theorem exists_isPLHomeomorphOn_arc_union {J A A₁ A₂ J' A' : Set Plane} {p q : Plane}
    (hcross : IsCrosscut J A p q) (hcut : IsCutPair J p q A₁ A₂)
    (hA₁ : IsPLBall 1 A₁) (hA : IsPLBall 1 A)
    {g k : Plane → Plane} (hg : IsPLHomeomorphOn g J J') (hk : IsPLHomeomorphOn k A A')
    (hcross' : IsCrosscut J' A' (g p) (g q)) (hp : k p = g p) (hq : k q = g q) :
    ∃ f : Plane → Plane, IsPLHomeomorphOn f (A₁ ∪ A) (g '' A₁ ∪ A') ∧
      EqOn f g A₁ ∧ EqOn f k A := by
  have hA₁J : A₁ ⊆ J := hcut.fst_subset
  have hinter : A₁ ∩ A = {p, q} := by
    refine Subset.antisymm (fun x hx => hcross.inter_eq.subset ⟨hx.2, hA₁J hx.1⟩) ?_
    exact pair_subset ⟨hcut.fst.left_mem, hcross.arc.left_mem⟩
      ⟨hcut.fst.right_mem, hcross.arc.right_mem⟩
  have hgA₁J' : g '' A₁ ⊆ J' := by
    rw [← hg.image_eq]
    rintro x ⟨z, hz, rfl⟩
    exact ⟨z, hA₁J hz, rfl⟩
  have hinter' : g '' A₁ ∩ A' = {g p, g q} := by
    refine Subset.antisymm (fun x hx => hcross'.inter_eq.subset ⟨hx.2, hgA₁J' hx.1⟩) ?_
    exact pair_subset ⟨mem_image_of_mem g hcut.fst.left_mem, hcross'.arc.left_mem⟩
      ⟨mem_image_of_mem g hcut.fst.right_mem, hcross'.arc.right_mem⟩
  have hagree : EqOn g k (A₁ ∩ A) := by
    rw [hinter]
    rintro x (rfl | rfl)
    · exact hp.symm
    · exact hq.symm
  have hsurj : SurjOn g (A₁ ∩ A) (g '' A₁ ∩ A') := by
    rw [hinter, hinter']
    rintro y (rfl | rfl)
    · exact ⟨p, by simp, rfl⟩
    · exact ⟨q, by simp, rfl⟩
  exact exists_isPLHomeomorphOn_union hA₁.isPolyhedron hA.isPolyhedron
    (hg.restrict hA₁.isPolyhedron hA₁J) hk hagree hsurj

theorem exists_isPLHomeomorphOn_of_fourSpokeDisk
    {D D' A₁ A₂ : Set Plane} {c c' : Plane} {T T' : Fin 4 → Set Plane} {v v' : Fin 4 → Plane}
    (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hT : ∀ i, IsPLBall 1 (T i)) (hT' : ∀ i, IsPLBall 1 (T' i))
    (harc : ∀ i, IsArcBetween (T i) c (v i)) (harc' : ∀ i, IsArcBetween (T' i) c' (v' i))
    (hTD : ∀ i, T i ⊆ D) (hTD' : ∀ i, T' i ⊆ D')
    (hTf : ∀ i, T i ∩ frontier D = {v i}) (hTf' : ∀ i, T' i ∩ frontier D' = {v' i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c}) (hTT' : ∀ i j, i ≠ j → T' i ∩ T' j = {c'})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂) (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    {π : Equiv.Perm (Fin 4)} {g : Plane → Plane}
    (hg : IsPLHomeomorphOn g (frontier D) (frontier D')) (hgv : ∀ i, g (v i) = v' (π i))
    {q : Fin 4 → Plane → Plane} (hq : ∀ i, IsPLHomeomorphOn (q i) (T i) (T' (π i)))
    (hqc : ∀ i, q i c = c') (hqv : ∀ i, q i (v i) = g (v i)) :
    ∃ F : Plane → Plane, IsPLHomeomorphOn F D D' ∧ EqOn F g (frontier D) ∧
      ∀ i, EqOn F (q i) (T i) := by
  classical
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij h
    have hmem : v i ∈ T i ∩ T j := ⟨(harc i).right_mem, by rw [h]; exact (harc j).right_mem⟩
    rw [hTT i j hij] at hmem
    exact ne_of_isArcBetween (harc i) (mem_singleton_iff.mp hmem).symm
  have hvne' : ∀ i j : Fin 4, i ≠ j → v' i ≠ v' j := by
    intro i j hij h
    have hmem : v' i ∈ T' i ∩ T' j := ⟨(harc' i).right_mem, by rw [h]; exact (harc' j).right_mem⟩
    rw [hTT' i j hij] at hmem
    exact ne_of_isArcBetween (harc' i) (mem_singleton_iff.mp hmem).symm
  have hπ02 : π 0 ≠ π 2 := π.injective.ne (by decide)
  obtain ⟨hAball, hcrossA⟩ := isCrosscut_union_of_opposite_spokes hD (hT 0) (hT 2)
    (harc 0) (harc 2) (hTD 0) (hTD 2) (hTf 0) (hTf 2) (hTT 0 2 (by decide))
  obtain ⟨hA'ball, hcrossA'⟩ := isCrosscut_union_of_opposite_spokes hD' (hT' (π 0)) (hT' (π 2))
    (harc' (π 0)) (harc' (π 2)) (hTD' (π 0)) (hTD' (π 2)) (hTf' (π 0)) (hTf' (π 2))
    (hTT' (π 0) (π 2) hπ02)
  have hcA : c ∈ T 0 ∪ T 2 := Or.inl (harc 0).left_mem
  have hc'A' : c' ∈ T' (π 0) ∪ T' (π 2) := Or.inl (harc' (π 0)).left_mem
  have hcut' : IsCutPair (frontier D') (v' (π 0)) (v' (π 2)) (g '' A₁) (g '' A₂) := by
    have h := hcut.image hg.isPiecewiseAffineOn.continuousOn hg.bijOn.injOn
    rwa [hg.image_eq, hgv 0, hgv 2] at h
  have hA₁ : IsPLBall 1 A₁ :=
    isPLBall_of_isArc_subset_isPLSphere hD.isPLSphere_frontier hcut.fst.isArc hcut.fst_subset
  have hA₂ : IsPLBall 1 A₂ :=
    isPLBall_of_isArc_subset_isPLSphere hD.isPLSphere_frontier hcut.snd.isArc hcut.snd_subset
  have hagreeA : EqOn (q 0) (q 2) (T 0 ∩ T 2) := by
    rw [hTT 0 2 (by decide)]
    rintro x rfl
    rw [hqc 0, hqc 2]
  have hsurjA : SurjOn (q 0) (T 0 ∩ T 2) (T' (π 0) ∩ T' (π 2)) := by
    rw [hTT 0 2 (by decide), hTT' (π 0) (π 2) hπ02]
    rintro y rfl
    exact ⟨c, rfl, hqc 0⟩
  obtain ⟨fA, hfA, hfA0, hfA2⟩ := exists_isPLHomeomorphOn_union (hT 0).isPolyhedron
    (hT 2).isPolyhedron (hq 0) (hq 2) hagreeA hsurjA
  have hfAc : fA c = c' := (hfA0 (harc 0).left_mem).trans (hqc 0)
  have hfAv0 : fA (v 0) = g (v 0) := (hfA0 (harc 0).right_mem).trans (hqv 0)
  have hfAv2 : fA (v 2) = g (v 2) := (hfA2 (harc 2).right_mem).trans (hqv 2)
  have hcrossAg : IsCrosscut (frontier D') (T' (π 0) ∪ T' (π 2)) (g (v 0)) (g (v 2)) := by
    rw [hgv 0, hgv 2]
    exact hcrossA'
  obtain ⟨f₁, hf₁, hf₁g, hf₁A⟩ := exists_isPLHomeomorphOn_arc_union hcrossA hcut hA₁ hAball
    hg hfA hcrossAg hfAv0 hfAv2
  obtain ⟨f₂, hf₂, hf₂g, hf₂A⟩ := exists_isPLHomeomorphOn_arc_union hcrossA hcut.symm hA₂ hAball
    hg hfA hcrossAg hfAv0 hfAv2
  have hcross₁ : IsCrosscut (A₁ ∪ (T 0 ∪ T 2)) (T 1) c (v 1) :=
    isCrosscut_spoke_of_isCutPair hD (hT 1) hAball (harc 1) (hTD 1) (hTf 1)
      (hTT 1 0 (by decide)) (hTT 1 2 (by decide)) hcA hcrossA hcut hv1
      (hvne 1 0 (by decide)) (hvne 1 2 (by decide))
  have hcross₃ : IsCrosscut (A₂ ∪ (T 0 ∪ T 2)) (T 3) c (v 3) :=
    isCrosscut_spoke_of_isCutPair hD (hT 3) hAball (harc 3) (hTD 3) (hTf 3)
      (hTT 3 0 (by decide)) (hTT 3 2 (by decide)) hcA hcrossA hcut.symm hv3
      (hvne 3 0 (by decide)) (hvne 3 2 (by decide))
  have hcross₁' : IsCrosscut (g '' A₁ ∪ (T' (π 0) ∪ T' (π 2))) (T' (π 1)) c' (v' (π 1)) :=
    isCrosscut_spoke_of_isCutPair hD' (hT' (π 1)) hA'ball (harc' (π 1)) (hTD' (π 1))
      (hTf' (π 1)) (hTT' (π 1) (π 0) (π.injective.ne (by decide)))
      (hTT' (π 1) (π 2) (π.injective.ne (by decide))) hc'A' hcrossA' hcut'
      (by rw [← hgv 1]; exact mem_image_of_mem g hv1)
      (hvne' (π 1) (π 0) (π.injective.ne (by decide)))
      (hvne' (π 1) (π 2) (π.injective.ne (by decide)))
  have hcross₃' : IsCrosscut (g '' A₂ ∪ (T' (π 0) ∪ T' (π 2))) (T' (π 3)) c' (v' (π 3)) :=
    isCrosscut_spoke_of_isCutPair hD' (hT' (π 3)) hA'ball (harc' (π 3)) (hTD' (π 3))
      (hTf' (π 3)) (hTT' (π 3) (π 0) (π.injective.ne (by decide)))
      (hTT' (π 3) (π 2) (π.injective.ne (by decide))) hc'A' hcrossA' hcut'.symm
      (by rw [← hgv 3]; exact mem_image_of_mem g hv3)
      (hvne' (π 3) (π 0) (π.injective.ne (by decide)))
      (hvne' (π 3) (π 2) (π.injective.ne (by decide)))
  have hJ₁ : IsPLSphere 1 (A₁ ∪ (T 0 ∪ T 2)) :=
    isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hAball hcrossA hcut
  have hJ₂ : IsPLSphere 1 (A₂ ∪ (T 0 ∪ T 2)) :=
    isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hAball hcrossA hcut.symm
  have hfc₁ : f₁ c = c' := (hf₁A hcA).trans hfAc
  have hfc₂ : f₂ c = c' := (hf₂A hcA).trans hfAc
  have hfv₁ : f₁ (v 1) = v' (π 1) := (hf₁g hv1).trans (hgv 1)
  have hfv₃ : f₂ (v 3) = v' (π 3) := (hf₂g hv3).trans (hgv 3)
  obtain ⟨F₁, hF₁, hF₁f, hF₁q⟩ := exists_isPLHomeomorphOn_eqOn_curve_and_crosscut hJ₁
    (hT 1) hcross₁ hf₁ (hq 1) (by rw [hqc 1, hfc₁])
    ((hqv 1).trans ((hgv 1).trans hfv₁.symm)) (by rw [hfc₁, hfv₁]; exact hcross₁')
  obtain ⟨F₂, hF₂, hF₂f, hF₂q⟩ := exists_isPLHomeomorphOn_eqOn_curve_and_crosscut hJ₂
    (hT 3) hcross₃ hf₂ (hq 3) (by rw [hqc 3, hfc₂])
    ((hqv 3).trans ((hgv 3).trans hfv₃.symm)) (by rw [hfc₂, hfv₃]; exact hcross₃')
  have hD₁ : IsPLBall 2 (closure (inside (A₁ ∪ (T 0 ∪ T 2)))) :=
    isPLBall_closure_inside_of_isPLSphere_one hJ₁
  have hD₂ : IsPLBall 2 (closure (inside (A₂ ∪ (T 0 ∪ T 2)))) :=
    isPLBall_closure_inside_of_isPLSphere_one hJ₂
  have hsub₁ : A₁ ∪ (T 0 ∪ T 2) ⊆ closure (inside (A₁ ∪ (T 0 ∪ T 2))) :=
    (frontier_closure_inside_of_isPLSphere_one hJ₁).symm.subset.trans
      (frontier_subset_closure.trans hD₁.isPolyhedron.isClosed.closure_eq.subset)
  have hsub₂ : A₂ ∪ (T 0 ∪ T 2) ⊆ closure (inside (A₂ ∪ (T 0 ∪ T 2))) :=
    (frontier_closure_inside_of_isPLSphere_one hJ₂).symm.subset.trans
      (frontier_subset_closure.trans hD₂.isPolyhedron.isClosed.closure_eq.subset)
  have hinterD : closure (inside (A₁ ∪ (T 0 ∪ T 2))) ∩ closure (inside (A₂ ∪ (T 0 ∪ T 2))) =
      T 0 ∪ T 2 := PlanarJordan.closure_inside_inter_of_isCrosscut hcrossA hcut
  have hinterD' : closure (inside (g '' A₁ ∪ (T' (π 0) ∪ T' (π 2)))) ∩
      closure (inside (g '' A₂ ∪ (T' (π 0) ∪ T' (π 2)))) = T' (π 0) ∪ T' (π 2) :=
    PlanarJordan.closure_inside_inter_of_isCrosscut hcrossA' hcut'
  have hagreeF : EqOn F₁ F₂ (closure (inside (A₁ ∪ (T 0 ∪ T 2))) ∩
      closure (inside (A₂ ∪ (T 0 ∪ T 2)))) := by
    rw [hinterD]
    intro x hx
    rw [hF₁f (Or.inr hx), hF₂f (Or.inr hx), hf₁A hx, hf₂A hx]
  have hsurjF : SurjOn F₁ (closure (inside (A₁ ∪ (T 0 ∪ T 2))) ∩
      closure (inside (A₂ ∪ (T 0 ∪ T 2))))
      (closure (inside (g '' A₁ ∪ (T' (π 0) ∪ T' (π 2)))) ∩
        closure (inside (g '' A₂ ∪ (T' (π 0) ∪ T' (π 2))))) := by
    rw [hinterD, hinterD']
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hfA.bijOn.surjOn hy
    refine ⟨x, hx, ?_⟩
    rw [hF₁f (Or.inr hx), hf₁A hx]
    exact hxy
  obtain ⟨F, hF, hFD₁, hFD₂⟩ := exists_isPLHomeomorphOn_union hD₁.isPolyhedron hD₂.isPolyhedron
    hF₁ hF₂ hagreeF hsurjF
  have hDeq : closure (inside (frontier D)) = D := by
    rw [← hD.interior_eq_inside_frontier]
    exact hD.closure_interior
  have hD'eq : closure (inside (frontier D')) = D' := by
    rw [← hD'.interior_eq_inside_frontier]
    exact hD'.closure_interior
  rw [PlanarJordan.closure_inside_union_of_isCrosscut hcrossA hcut, hDeq,
    PlanarJordan.closure_inside_union_of_isCrosscut hcrossA' hcut', hD'eq] at hF
  have hT₁sub : T 1 ⊆ closure (inside (A₁ ∪ (T 0 ∪ T 2))) := by
    intro x hx
    by_cases hxm : x ∈ ({c, v 1} : Set Plane)
    · rcases hxm with rfl | rfl
      · exact hsub₁ (Or.inr hcA)
      · exact hsub₁ (Or.inl hv1)
    · exact subset_closure (hcross₁.sdiff_subset ⟨hx, hxm⟩)
  have hT₃sub : T 3 ⊆ closure (inside (A₂ ∪ (T 0 ∪ T 2))) := by
    intro x hx
    by_cases hxm : x ∈ ({c, v 3} : Set Plane)
    · rcases hxm with rfl | rfl
      · exact hsub₂ (Or.inr hcA)
      · exact hsub₂ (Or.inl hv3)
    · exact subset_closure (hcross₃.sdiff_subset ⟨hx, hxm⟩)
  have hspoke0 : EqOn F (q 0) (T 0) := fun x hx =>
    (hFD₁ (hsub₁ (Or.inr (Or.inl hx)))).trans
      ((hF₁f (Or.inr (Or.inl hx))).trans ((hf₁A (Or.inl hx)).trans (hfA0 hx)))
  have hspoke1 : EqOn F (q 1) (T 1) := fun x hx => (hFD₁ (hT₁sub hx)).trans (hF₁q hx)
  have hspoke2 : EqOn F (q 2) (T 2) := fun x hx =>
    (hFD₁ (hsub₁ (Or.inr (Or.inr hx)))).trans
      ((hF₁f (Or.inr (Or.inr hx))).trans ((hf₁A (Or.inr hx)).trans (hfA2 hx)))
  have hspoke3 : EqOn F (q 3) (T 3) := fun x hx => (hFD₂ (hT₃sub hx)).trans (hF₂q hx)
  refine ⟨F, hF, ?_, ?_⟩
  · intro x hx
    rw [← hcut.union_eq] at hx
    rcases hx with hx | hx
    · exact (hFD₁ (hsub₁ (Or.inl hx))).trans ((hF₁f (Or.inl hx)).trans (hf₁g hx))
    · exact (hFD₂ (hsub₂ (Or.inl hx))).trans ((hF₂f (Or.inl hx)).trans (hf₂g hx))
  · intro i
    fin_cases i
    exacts [hspoke0, hspoke1, hspoke2, hspoke3]

theorem image_biUnion_spokes_eq {T : Fin 4 → Set Plane} {T' : Fin 4 → Set Plane}
    {π : Equiv.Perm (Fin 4)} {F : Plane → Plane} {q : Fin 4 → Plane → Plane}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (T i) (T' (π i))) (hF : ∀ i, EqOn F (q i) (T i))
    (S : Set (Fin 4)) : F '' (⋃ i ∈ S, T i) = ⋃ i ∈ S, T' (π i) := by
  rw [image_iUnion₂]
  exact iUnion₂_congr fun i _ => ((hF i).image_eq).trans (hq i).image_eq

end DifferentialGeometry.Topology.PiecewiseLinear
