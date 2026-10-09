/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapSide
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapPrism
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapMap
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapSource
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InnermostCleanDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BranchBoundarySweep
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningJunction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk [T2Space M]
    [HasGroupoid M (plGroupoid 3)]
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q E : Set (EuclideanSpace ℝ (Fin 2))}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsPLSphere 1 J) (hT : IsPLSphere 1 T) (hJT : Disjoint J T)
    (hpre : hD.branchPreimage c = J ∪ T)
    (hQ : IsPLBall 2 Q) (hQsub : Q ⊆ interior D.domain) (hfrontQ : frontier Q = J)
    (hclean : doublePointPreimage (⇑D) D.domain ∩ Q = J) (hinj : InjOn (⇑D) Q)
    (hE : IsPLBall 2 E) (hfrontE : frontier E = T)
    (hk : IsPLHomeomorphOn k E Q) (hkT : k '' T = J) (hkcompat : EqOn (⇑D) (⇑D ∘ k) T)
    (hdisjoint : Disjoint Q E)
    {V : Set M} (hV : IsOpen V) (hQV : ⇑D '' Q ⊆ V) (hVBd : Disjoint V BdM) :
    ∃ (E' : Set (EuclideanSpace ℝ (Fin 2))) (Δ : SingularTwoCell M),
      IsPLBall 2 E' ∧ E ⊆ interior E' ∧ E' ⊆ interior D.domain ∧ Disjoint Q E' ∧
        (E' \ E) ∩ doublePointPreimage (⇑D) D.domain = ∅ ∧
          Δ.domain = E' ∧ InjOn (⇑Δ) E' ∧ ⇑Δ '' E' ⊆ V ∧ EqOn (⇑Δ) (⇑D) (frontier E') ∧
            ⇑Δ '' E' ∩ ⇑D '' D.domain = ⇑D '' frontier E' := by
  classical
  let _ := hVBd
  subst hfrontQ hfrontE
  set J := frontier Q with hJdef
  set T := frontier E with hTdef
  have hQdom : Q ⊆ D.domain := hQsub.trans interior_subset
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hEclosed : IsClosed E := hE.isPolyhedron.isCompact.isClosed
  have hJQ : J ⊆ Q := hQclosed.frontier_subset
  have hTE : T ⊆ E := hEclosed.frontier_subset
  have hJcomp : IsCompact J := hJ.isPolyhedron.isCompact
  have hTcomp : IsCompact T := hT.isPolyhedron.isCompact
  have hTpoly : IsPolyhedron T := hT.isPolyhedron
  have hJTint : J ∪ T ⊆ interior D.domain := by
    rw [← hpre]
    exact hD.branchPreimage_subset_interior_of_not_boundaryBranch hc
  have hEint : E ⊆ interior D.domain :=
    isPLBall_subset_interior_of_frontier_subset_interior hE D.isPLBall_domain
      fun x hx => hJTint (Or.inr hx)
  have hcarrier_pre : ∀ x ∈ D.domain, ⇑D x ∈ hD.singularSet.branchCarrier c → x ∈ J ∪ T := by
    intro x hx hxc
    have hmem : x ∈ hD.branchPreimage c := ⟨hx, hxc⟩
    rwa [hpre] at hmem
  have hcarrier_img : ∀ w ∈ J ∪ T, ⇑D w ∈ hD.singularSet.branchCarrier c := by
    intro w hw
    have hmem : w ∈ hD.branchPreimage c := hpre.symm.subset hw
    exact hmem.2
  have hdpp_of_ne : ∀ x ∈ D.domain, ∀ y ∈ D.domain, x ≠ y → ⇑D x = ⇑D y →
      x ∈ doublePointPreimage (⇑D) D.domain := fun x hx y hy hxy h =>
    ⟨hx, x, hx, y, hy, hxy, rfl, h.symm⟩
  have hkQ : ∀ x ∈ E, k x ∈ Q := fun x hx => hk.bijOn.mapsTo hx
  obtain ⟨C, ρ, hρ, hρJE, hρTQ⟩ :=
    hD.exists_isTwoSidedBranchCollar_of_branchPreimage_eq_union hc hpre hQ rfl hE rfl hdisjoint
  obtain ⟨τ, hτ⟩ := hD.exists_isBranchDeckInvolution_of_branchPreimage_eq c hpre
  obtain ⟨-, -, hCint, -, hCnhds, hρpl, hρ0, hCdpp, hCQ, -, -, -, -⟩ := id hρ
  have hCdom : C ⊆ D.domain := hCint.trans interior_subset
  have hI : ∀ u ∈ Icc (-1 : ℝ) 0, u ∈ Icc (-1 : ℝ) 1 := fun u hu =>
    ⟨hu.1, by linarith [hu.2]⟩
  have hρmaps : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (w, u) ∈ C := fun w hw u hu =>
    hρpl.bijOn.mapsTo ⟨hw, hu⟩
  have hρdom : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (w, u) ∈ D.domain := fun w hw u hu =>
    hCdom (hρmaps w hw u hu)
  have hρinj : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ w' ∈ J ∪ T, ∀ u' ∈ Icc (-1 : ℝ) 1,
      ρ (w, u) = ρ (w', u') → w = w' ∧ u = u' := by
    intro w hw u hu w' hw' u' hu' h
    have h' := hρpl.bijOn.injOn ⟨hw, hu⟩ ⟨hw', hu'⟩ h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hρdpp : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1,
      ρ (w, u) ∈ doublePointPreimage (⇑D) D.domain → u = 0 := by
    intro w hw u hu hd
    have hmem : ρ (w, u) ∈ J ∪ T := hCdpp.subset ⟨hd, hρmaps w hw u hu⟩
    exact (hρinj (ρ (w, u)) hmem 0 ⟨by norm_num, by norm_num⟩ w hw u hu (hρ0 _ hmem)).2.symm
  have hρTQ' : ∀ t ∈ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (t, u) ∉ Q := fun t ht u hu hq =>
    Set.disjoint_left.mp hρTQ ⟨(t, u), ⟨ht, hu⟩, rfl⟩ hq
  have hρJE' : ∀ j ∈ J, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (j, u) ∉ E := fun j hj u hu he =>
    Set.disjoint_left.mp hρJE ⟨(j, u), ⟨hj, hu⟩, rfl⟩ he
  have hρinside : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (w, u) ∈ Q ∪ E → 0 ≤ u := by
    intro w hw u hu hmem
    have hCQE : ρ (w, u) ∈ C ∩ (Q ∪ E) := ⟨hρmaps w hw u hu, hmem⟩
    rw [hCQ] at hCQE
    obtain ⟨⟨w', u'⟩, ⟨hw', hu'⟩, heq⟩ := hCQE
    have h := hρinj w' hw' u' ⟨by linarith [hu'.1], hu'.2⟩ w hw u hu heq
    linarith [hu'.1, h.2]
  have hρoutside : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ u → ρ (w, u) ∈ Q ∪ E := by
    intro w hw u hu hu0
    have hmem : ρ (w, u) ∈ C ∩ (Q ∪ E) := by
      rw [hCQ]
      exact ⟨(w, u), ⟨hw, hu0, hu.2⟩, rfl⟩
    exact hmem.2
  have hρTE : ∀ t ∈ T, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (t, u) ∈ E ↔ 0 ≤ u := by
    intro t ht u hu
    refine ⟨fun h => hρinside t (Or.inr ht) u hu (Or.inr h), fun h => ?_⟩
    rcases hρoutside t (Or.inr ht) u hu h with hq | he
    · exact absurd hq (hρTQ' t ht u hu)
    · exact he
  have hρJQ : ∀ j ∈ J, ∀ u ∈ Icc (-1 : ℝ) 1, ρ (j, u) ∈ Q ↔ 0 ≤ u := by
    intro j hj u hu
    refine ⟨fun h => hρinside j (Or.inl hj) u hu (Or.inl h), fun h => ?_⟩
    rcases hρoutside j (Or.inl hj) u hu h with hq | he
    · exact hq
    · exact absurd he (hρJE' j hj u hu)
  have hρcont : ContinuousOn ρ ((J ∪ T) ×ˢ Icc (-1 : ℝ) 1) :=
    hρpl.isPiecewiseAffineOn.continuousOn
  have hDρcont : ContinuousOn (fun p => ⇑D (ρ p)) ((J ∪ T) ×ˢ Icc (-1 : ℝ) 1) :=
    D.continuousOn.comp hρcont fun p hp => hCdom (hρpl.bijOn.mapsTo hp)
  obtain ⟨sa, hsa, hsa1, hsaC⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact
    (hJcomp.union hTcomp) hρcont isOpen_interior fun x hx => by
      rw [hρ0 x hx]
      exact mem_interior_iff_mem_nhds.mpr (hCnhds x hx)
  obtain ⟨sb, hsb, -, hsbV⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact
    hTcomp (hDρcont.mono (prod_mono subset_union_right Subset.rfl)) hV fun t ht => by
      rw [hρ0 t (Or.inr ht), hkcompat ht]
      exact hQV ⟨k t, hkQ t (hTE ht), rfl⟩
  set s₀ := min sa sb with hs₀def
  have hs₀ : 0 < s₀ := lt_min hsa hsb
  have hs₀a : s₀ ≤ sa := min_le_left _ _
  have hs₀b : s₀ ≤ sb := min_le_right _ _
  have hs₀1 : s₀ ≤ 1 := hs₀a.trans hsa1
  have hs₀C : ∀ w ∈ J ∪ T, ∀ u ∈ Icc (-s₀) s₀, ρ (w, u) ∈ interior C := fun w hw u hu =>
    hsaC w hw u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hs₀V : ∀ t ∈ T, ∀ u ∈ Icc (-s₀) s₀, ⇑D (ρ (t, u)) ∈ V := fun t ht u hu =>
    hsbV t ht u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hρT : IsPLHomeomorphOn ρ (T ×ˢ Icc (-1 : ℝ) 1) (ρ '' (T ×ˢ Icc (-1 : ℝ) 1)) :=
    hρpl.restrict (hTpoly.prod isHPolytope_Icc.isPolyhedron)
      (prod_mono subset_union_right Subset.rfl)
  have hout : ρ '' (T ×ˢ Icc (-1 : ℝ) 0) ∩ E = T := by
    apply Subset.antisymm
    · rintro _ ⟨⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, hEt⟩
      have hu0 : u = 0 := le_antisymm hu.2 ((hρTE t ht u (hI u hu)).mp hEt)
      rw [hu0, hρ0 t (Or.inr ht)]
      exact ht
    · intro t ht
      exact ⟨⟨(t, 0), ⟨ht, by norm_num, le_rfl⟩, hρ0 t (Or.inr ht)⟩, hTE ht⟩
  obtain ⟨hE₂ball, hE₂front, hEE₂⟩ := isPLBall_union_image_outerCollar hE hρT
    (fun x hx => hρ0 x (Or.inr hx)) hout hs₀ hs₀1
  have hs₁ : 0 < s₀ / 2 := half_pos hs₀
  have hs₁1 : s₀ / 2 ≤ 1 := by linarith
  obtain ⟨hE'ball, hE'front, hEE'⟩ := isPLBall_union_image_outerCollar hE hρT
    (fun x hx => hρ0 x (Or.inr hx)) hout hs₁ hs₁1
  set A₂ := ρ '' (T ×ˢ Icc (-s₀) 0) with hA₂def
  set A' := ρ '' (T ×ˢ Icc (-(s₀ / 2)) 0) with hA'def
  have hA₂I : ∀ u ∈ Icc (-s₀) 0, u ∈ Icc (-1 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hA'I : ∀ u ∈ Icc (-(s₀ / 2)) 0, u ∈ Icc (-s₀) 0 := fun u hu =>
    ⟨by linarith [hu.1], hu.2⟩
  have hA'A₂ : A' ⊆ A₂ := image_mono (prod_mono Subset.rfl fun u hu => hA'I u hu)
  have hE'E₂ : E ∪ A' ⊆ interior (E ∪ A₂) := by
    rintro x (hx | ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩)
    · exact hEE₂ hx
    · have hmem : ρ (t, u) ∈ E ∪ A₂ := Or.inr ⟨(t, u), ⟨ht, hA'I u hu⟩, rfl⟩
      refine (mem_interior_iff_notMem_frontier hmem).mpr ?_
      rw [hE₂front]
      rintro ⟨⟨t', u'⟩, ⟨ht', hu'⟩, heq⟩
      have hu'' : u' = -s₀ := hu'
      have h := hρinj t' (Or.inr ht') u' ⟨by linarith, by linarith⟩ t (Or.inr ht) u
        (hA₂I u (hA'I u hu)) heq
      linarith [hu.1, h.2]
  have hTIcc : IsPolyhedron (T ×ˢ Icc (-s₀) 0) := hTpoly.prod isHPolytope_Icc.isPolyhedron
  have hA₂sub : T ×ˢ Icc (-s₀) 0 ⊆ T ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl fun u hu => hA₂I u hu
  have hA₂poly : IsPolyhedron A₂ :=
    hTIcc.image_of_isPiecewiseAffineOn
      (hρT.isPiecewiseAffineOn.mono_of_isPolyhedron hTIcc hA₂sub)
      (hρT.bijOn.injOn.mono hA₂sub)
  have hA₂dom : A₂ ⊆ D.domain := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    exact hρdom t (Or.inr ht) u (hA₂I u hu)
  have hA₂C : A₂ ⊆ C := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    exact hρmaps t (Or.inr ht) u (hA₂I u hu)
  have hEA₂ : E ∩ A₂ ⊆ T := by
    rintro x ⟨hxE, ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩⟩
    have hu0 : u = 0 := le_antisymm hu.2 ((hρTE t ht u (hA₂I u hu)).mp hxE)
    rw [hu0, hρ0 t (Or.inr ht)]
    exact ht
  obtain ⟨β, hβpl, hβE, hβA⟩ : ∃ β : EuclideanSpace ℝ (Fin 2) → M,
      IsPLOn 2 3 β (E ∪ A₂) ∧ EqOn β (⇑D ∘ k) E ∧ EqOn β (⇑D) A₂ := by
    have hf : IsPLOn 2 3 (⇑D ∘ k) E :=
      isPLOn_comp_isPiecewiseAffineOn_of_mapsTo D.isPLOn hk.isPiecewiseAffineOn
        fun x hx => hQdom (hkQ x hx)
    have hg : IsPLOn 2 3 (⇑D) A₂ := D.isPLOn.mono_of_isPolyhedron hA₂poly hA₂dom
    have hfg : EqOn (⇑D ∘ k) (⇑D) (E ∩ A₂) := fun x hx => (hkcompat (hEA₂ hx)).symm
    refine ⟨_, hf.piecewise_of_isClosed hg hEclosed hA₂poly.isClosed hfg,
      fun x hx => ite_eq_left hx, fun x hx => ?_⟩
    by_cases hxE : x ∈ E
    · exact (ite_eq_left hxE).trans (hfg ⟨hxE, hx⟩)
    · exact ite_eq_right hxE
  have hβT : ∀ t ∈ T, β t = ⇑D t := fun t ht => (hβE (hTE ht)).trans (hkcompat ht).symm
  have hβk : ∀ t ∈ E, β t = ⇑D (k t) := fun t ht => hβE ht
  have hβEinj : InjOn β E := by
    intro x hx y hy hxy
    rw [hβE hx, hβE hy] at hxy
    exact hk.bijOn.injOn hx hy (hinj (hkQ x hx) (hkQ y hy) hxy)
  have hA₂dpp : ∀ y ∈ A₂, y ∈ doublePointPreimage (⇑D) D.domain → y ∈ E := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ hd
    rw [hρdpp t (Or.inr ht) u (hA₂I u hu) hd, hρ0 t (Or.inr ht)]
    exact hTE ht
  have hA₂Q : ∀ y ∈ A₂, y ∉ Q := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    exact hρTQ' t ht u (hA₂I u hu)
  have hβinj : InjOn β (E ∪ A₂) := by
    have hmixed : ∀ x ∈ E, ∀ y ∈ A₂, y ∉ E → β x ≠ β y := by
      intro x hx y hy hyE hxy
      rw [hβE hx, hβA hy] at hxy
      have hne : y ≠ k x := fun h => hA₂Q y hy (by rw [h]; exact hkQ x hx)
      exact hyE (hA₂dpp y hy (hdpp_of_ne y (hA₂dom hy) (k x) (hQdom (hkQ x hx)) hne
        hxy.symm))
    intro x hx y hy hxy
    by_cases hxE : x ∈ E <;> by_cases hyE : y ∈ E
    · exact hβEinj hxE hyE hxy
    · exact absurd hxy (hmixed x hxE y (hy.resolve_left hyE) hyE)
    · exact absurd hxy.symm (hmixed y hyE x (hx.resolve_left hxE) hxE)
    · have hxA := hx.resolve_left hxE
      have hyA := hy.resolve_left hyE
      rw [hβA hxA, hβA hyA] at hxy
      by_contra hne
      exact hxE (hA₂dpp x hxA (hdpp_of_ne x (hA₂dom hxA) y (hA₂dom hyA) hne hxy))
  have hβV : β '' (E ∪ A₂) ⊆ V := by
    rintro _ ⟨x, hx | hx, rfl⟩
    · rw [hβE hx]
      exact hQV ⟨k x, hkQ x hx, rfl⟩
    · rw [hβA hx]
      obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ := hx
      exact hs₀V t ht u ⟨hu.1, by linarith [hu.2]⟩
  obtain ⟨prism, b, hPcont, hPinj, hPV, hPnhds, hPcenter, hbmaps, hbpa, hbβ, hPpl⟩ :=
    exists_centeredPrism_of_isPLOn hE'ball hE₂ball hE'E₂ hβpl hβinj hV hβV
  set N := prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) with hNdef
  set Lo := prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) with hLodef
  set Up := prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) with hUpdef
  set Ce := prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) with hCedef
  have hstdc : IsCompact (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)
  have hLoclosed : IsClosed Lo :=
    ((hstdc.prod isCompact_Icc).image_of_continuousOn
      (hPcont.mono (prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num))))).isClosed
  have hUpclosed : IsClosed Up :=
    ((hstdc.prod isCompact_Icc).image_of_continuousOn
      (hPcont.mono (prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)))).isClosed
  have hNLoUp : N = Lo ∪ Up := by
    rw [hNdef, hLodef, hUpdef, ← image_union, ← prod_union,
      Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  have hLoUp : ∀ z ∈ Lo, z ∈ Up → z ∈ Ce := by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hpq' := hPinj ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩
      ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩ hpq
    have h1 : q.2 = p.2 := congrArg Prod.snd hpq'
    refine ⟨p, ⟨hp.1, ?_⟩, rfl⟩
    change p.2 = 0
    linarith [hp.2.2, hq.2.1]
  have hCeβ : Ce ⊆ β '' (E ∪ A₂) := by
    rw [hPcenter]
    exact inter_subset_left
  have hsplit : ∀ S : Set M, IsPreconnected S → S ⊆ N → Disjoint S Ce →
      S ⊆ Upᶜ ∨ S ⊆ Loᶜ := by
    intro S hS hSN hSCe
    refine isPreconnected_iff_subset_of_disjoint.mp hS _ _ hUpclosed.isOpen_compl
      hLoclosed.isOpen_compl ?_ ?_
    · intro z hz
      by_cases hzU : z ∈ Up
      · by_cases hzL : z ∈ Lo
        · exact absurd (hLoUp z hzL hzU) (Set.disjoint_left.mp hSCe hz)
        · exact Or.inr hzL
      · exact Or.inl hzU
    · refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro z ⟨hz, hzU, hzL⟩
      have hzN : z ∈ Lo ∪ Up := by
        rw [← hNLoUp]
        exact hSN hz
      rcases hzN with h | h
      · exact hzL h
      · exact hzU h
  have hsame : ∀ S : Set M, IsPreconnected S → S ⊆ N → Disjoint S Ce → ∀ O : Set M,
      O ⊆ N → (S ∩ O).Nonempty → (O ⊆ Upᶜ → S ⊆ Upᶜ) ∧ (O ⊆ Loᶜ → S ⊆ Loᶜ) := by
    intro S hS hSN hSCe O hON hSO
    obtain ⟨z, hzS, hzO⟩ := hSO
    have hzN : z ∈ Lo ∪ Up := by
      rw [← hNLoUp]
      exact hSN hzS
    rcases hsplit S hS hSN hSCe with h | h
    · refine ⟨fun _ => h, fun hO => ?_⟩
      rcases hzN with hz | hz
      · exact absurd hz (hO hzO)
      · exact absurd hz (h hzS)
    · refine ⟨fun hO => ?_, fun _ => h⟩
      rcases hzN with hz | hz
      · exact absurd hz (h hzS)
      · exact absurd hz (hO hzO)
  obtain ⟨a₀, ha₀⟩ := hJ.nonempty
  have ha₀' : a₀ ∈ k '' T := by
    rw [hkT]
    exact ha₀
  obtain ⟨t₀, ht₀, hkt₀⟩ := ha₀'
  have hDa₀ : ⇑D a₀ ∈ interior N := by
    rw [← hkt₀, ← hβk t₀ (hTE ht₀)]
    exact mem_interior_iff_mem_nhds.mpr (hPnhds t₀ (Or.inl (hTE ht₀)))
  obtain ⟨O, hOW, hOpc, hOdisj, hgermA, b₀, hb₀, hgermB⟩ :=
    hD.exists_isPreconnected_sideGerm_of_isTwoSidedBranchCollar hc hτ hρ hJT hTcomp
      hQ.isPolyhedron.isCompact hQdom hJQ hinj ha₀ isOpen_interior hDa₀
  have hβsub : β '' (E ∪ A₂) ⊆ ⇑D '' (Q ∪ ρ '' (T ×ˢ Icc (-1 : ℝ) 0)) := by
    rintro _ ⟨x, hx | hx, rfl⟩
    · rw [hβE hx]
      exact ⟨k x, Or.inl (hkQ x hx), rfl⟩
    · rw [hβA hx]
      obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ := hx
      exact ⟨ρ (t, u), Or.inr ⟨(t, u), ⟨ht, by linarith [hu.1], hu.2⟩, rfl⟩, rfl⟩
  have hON : O ⊆ N := hOW.trans interior_subset
  have hOCe : Disjoint O Ce := hOdisj.mono_right (hCeβ.trans hβsub)
  have hOside := hsplit O hOpc hON hOCe
  have hJTN : ∀ w ∈ J ∪ T, (fun p => ⇑D (ρ p)) (w, 0) ∈ interior N := by
    rintro w (hw | hw)
    · change ⇑D (ρ (w, 0)) ∈ interior N
      rw [hρ0 w (Or.inl hw)]
      have hw' : w ∈ k '' T := by
        rw [hkT]
        exact hw
      obtain ⟨t, ht, rfl⟩ := hw'
      rw [← hβk t (hTE ht)]
      exact mem_interior_iff_mem_nhds.mpr (hPnhds t (Or.inl (hTE ht)))
    · change ⇑D (ρ (w, 0)) ∈ interior N
      rw [hρ0 w (Or.inr hw), ← hβT w hw]
      exact mem_interior_iff_mem_nhds.mpr (hPnhds w (Or.inl (hTE hw)))
  obtain ⟨ε₀, hε₀, -, hε₀N⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact
    (hJcomp.union hTcomp) hDρcont isOpen_interior hJTN
  set ε := min ε₀ s₀ with hεdef
  have hε : 0 < ε := lt_min hε₀ hs₀
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεs₀ : ε ≤ s₀ := min_le_right _ _
  set A₁ := (fun p => ⇑D (ρ p)) '' (J ×ˢ Ico (-ε) 0) with hA₁def
  set Ain := (fun p => ⇑D (ρ p)) '' (T ×ˢ Ioc 0 ε) with hAindef
  have hIcoI : ∀ u ∈ Ico (-ε) 0, u ∈ Icc (-1 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hIocI : ∀ u ∈ Ioc 0 ε, u ∈ Icc (-1 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hA₁pc : IsPreconnected A₁ :=
    ((IsPLSphere.isConnected (n := 0) hJ).isPreconnected.prod
      (convex_Ico (-ε) (0 : ℝ)).isPreconnected).image _
      (hDρcont.mono (prod_mono subset_union_left fun u hu => hIcoI u hu))
  have hAinpc : IsPreconnected Ain :=
    ((IsPLSphere.isConnected (n := 0) hT).isPreconnected.prod
      (convex_Ioc (0 : ℝ) ε).isPreconnected).image _
      (hDρcont.mono (prod_mono subset_union_right fun u hu => hIocI u hu))
  have hA₁N : A₁ ⊆ N := by
    rintro _ ⟨⟨j, u⟩, ⟨hj, hu⟩, rfl⟩
    exact interior_subset (hε₀N j (Or.inl hj) u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hAinN : Ain ⊆ N := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    exact interior_subset (hε₀N t (Or.inr ht) u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hfarDPP : ∀ x ∈ D.domain, x ∉ Q ∪ ρ '' (T ×ˢ Icc (-1 : ℝ) 0) →
      ⇑D x ∈ ⇑D '' (Q ∪ ρ '' (T ×ˢ Icc (-1 : ℝ) 0)) →
        x ∈ doublePointPreimage (⇑D) D.domain := by
    rintro x hx hxn ⟨y, hy, hyx⟩
    have hydom : y ∈ D.domain := by
      rcases hy with hy | ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      · exact hQdom hy
      · exact hρdom t (Or.inr ht) u (hI u hu)
    exact hdpp_of_ne x hx y hydom (fun h => hxn (by rw [h]; exact hy)) hyx.symm
  have hA₁Ce : Disjoint A₁ Ce := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨j, u⟩, ⟨hj, hu⟩, rfl⟩ hCe
    have huI := hIcoI u hu
    have hnot : ρ (j, u) ∉ Q ∪ ρ '' (T ×ˢ Icc (-1 : ℝ) 0) := by
      rintro (hq | ⟨⟨t, u'⟩, ⟨ht, hu'⟩, heq⟩)
      · have := (hρJQ j hj u huI).mp hq
        linarith [hu.2]
      · have h := hρinj t (Or.inr ht) u' (hI u' hu') j (Or.inl hj) u huI heq
        exact Set.disjoint_left.mp hJT hj (by rw [← h.1]; exact ht)
    have hd := hfarDPP (ρ (j, u)) (hρdom j (Or.inl hj) u huI) hnot (hβsub (hCeβ hCe))
    have := hρdpp j (Or.inl hj) u huI hd
    linarith [hu.2]
  have hAinCe : Disjoint Ain Ce := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ hCe
    have huI := hIocI u hu
    have hnot : ρ (t, u) ∉ Q ∪ ρ '' (T ×ˢ Icc (-1 : ℝ) 0) := by
      rintro (hq | ⟨⟨t', u'⟩, ⟨ht', hu'⟩, heq⟩)
      · exact hρTQ' t ht u huI hq
      · have h := hρinj t' (Or.inr ht') u' (hI u' hu') t (Or.inr ht) u huI heq
        linarith [hu.1, hu'.2, h.2]
    have hd := hfarDPP (ρ (t, u)) (hρdom t (Or.inr ht) u huI) hnot (hβsub (hCeβ hCe))
    have := hρdpp t (Or.inr ht) u huI hd
    linarith [hu.1]
  have hA₁O : (A₁ ∩ O).Nonempty := by
    obtain ⟨s, hs, hsO⟩ := hgermA ε hε
    exact ⟨_, ⟨(a₀, -s), ⟨ha₀, by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩, hsO⟩
  have hAinO : (Ain ∩ O).Nonempty := by
    obtain ⟨s, hs, hsO⟩ := hgermB ε hε
    exact ⟨_, ⟨(b₀, s), ⟨hb₀, hs.1, hs.2.le⟩, rfl⟩, hsO⟩
  obtain ⟨σ, hσ, hσA₁, hσAin⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ∀ t ∈ Ioc (0 : ℝ) 1, prism (p, σ * t) ∉ A₁) ∧
        ∀ p ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ∀ t ∈ Ioc (0 : ℝ) 1, prism (p, σ * t) ∉ Ain := by
    rcases hOside with hO | hO
    · refine ⟨1, Or.inl rfl, fun p hp t ht hmem => ?_, fun p hp t ht hmem => ?_⟩
      · exact (hsame A₁ hA₁pc hA₁N hA₁Ce O hON hA₁O).1 hO hmem
          ⟨(p, 1 * t), ⟨hp, by rw [one_mul]; exact ht.1.le, by rw [one_mul]; exact ht.2⟩, rfl⟩
      · exact (hsame Ain hAinpc hAinN hAinCe O hON hAinO).1 hO hmem
          ⟨(p, 1 * t), ⟨hp, by rw [one_mul]; exact ht.1.le, by rw [one_mul]; exact ht.2⟩, rfl⟩
    · refine ⟨-1, Or.inr rfl, fun p hp t ht hmem => ?_, fun p hp t ht hmem => ?_⟩
      · exact (hsame A₁ hA₁pc hA₁N hA₁Ce O hON hA₁O).2 hO hmem
          ⟨(p, -1 * t), ⟨hp, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
      · exact (hsame Ain hAinpc hAinN hAinCe O hON hAinO).2 hO hmem
          ⟨(p, -1 * t), ⟨hp, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  set O₁ := ρ '' ((J ∪ T) ×ˢ Ioo (-s₀) s₀) with hO₁def
  have hIooI : Ioo (-s₀) s₀ ⊆ Icc (-1 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hO₁open : IsOpen O₁ := by
    have hρpl' : IsPLHomeomorphOn ρ ((J ∪ T) ×ˢ Icc (-1 : ℝ) 1) (C ∩ univ) := by
      rw [inter_univ]
      exact hρpl
    obtain ⟨Ω, hΩ, hΩeq⟩ := hρpl'.exists_image_eq_inter
      ((isOpen_univ.prod isOpen_Ioo :
        IsOpen ((univ : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ Ioo (-s₀) s₀)))
    have hdom : (J ∪ T) ×ˢ Icc (-1 : ℝ) 1 ∩
        (univ : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ Ioo (-s₀) s₀ =
          (J ∪ T) ×ˢ Ioo (-s₀) s₀ := by
      rw [prod_inter_prod, inter_univ, inter_eq_right.mpr hIooI]
    rw [hdom, univ_inter] at hΩeq
    have hO₁int : O₁ ⊆ interior C := by
      rintro _ ⟨⟨w, u⟩, ⟨hw, hu⟩, rfl⟩
      exact hs₀C w hw u ⟨hu.1.le, hu.2.le⟩
    have heq : O₁ = interior C ∩ Ω := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨hO₁int hx, (hΩeq.subset hx).2⟩
      · intro x hx
        exact hΩeq.symm.subset ⟨interior_subset hx.1, hx.2⟩
    rw [heq]
    exact isOpen_interior.inter hΩ
  set F₁ := ⇑D '' (D.domain \ (interior Q ∪ O₁)) with hF₁def
  set F₂ := (fun p => ⇑D (ρ p)) '' (J ×ˢ Icc (-s₀) (-ε)) with hF₂def
  set F₃ := (fun p => ⇑D (ρ p)) '' (T ×ˢ Icc ε s₀) with hF₃def
  have hF₁c : IsCompact F₁ :=
    (D.isPLBall_domain.isPolyhedron.isCompact.diff
      (isOpen_interior.union hO₁open)).image_of_continuousOn (D.continuousOn.mono sdiff_subset)
  have hF₂c : IsCompact F₂ :=
    (hJcomp.prod isCompact_Icc).image_of_continuousOn
      (hDρcont.mono (prod_mono subset_union_left fun u hu =>
        ⟨by linarith [hu.1], by linarith [hu.2]⟩))
  have hF₃c : IsCompact F₃ :=
    (hTcomp.prod isCompact_Icc).image_of_continuousOn
      (hDρcont.mono (prod_mono subset_union_right fun u hu =>
        ⟨by linarith [hu.1], by linarith [hu.2]⟩))
  have hFclosed : IsClosed (F₁ ∪ F₂ ∪ F₃) := ((hF₁c.union hF₂c).union hF₃c).isClosed
  have hSrcD : ∀ z ∈ β '' (E ∪ A'), ∃ y ∈ Q ∪ A', ⇑D y = z := by
    rintro _ ⟨x, hx | hx, rfl⟩
    · exact ⟨k x, Or.inl (hkQ x hx), (hβE hx).symm⟩
    · exact ⟨x, Or.inr hx, (hβA (hA'A₂ hx)).symm⟩
  have hSrcO₁ : ∀ y ∈ Q ∪ A', y ∈ interior Q ∪ O₁ := by
    rintro y (hy | ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩)
    · by_cases hyi : y ∈ interior Q
      · exact Or.inl hyi
      · have hyJ : y ∈ J := ⟨subset_closure hy, hyi⟩
        exact Or.inr ⟨(y, 0), ⟨Or.inl hyJ, by linarith, hs₀⟩, hρ0 y (Or.inl hyJ)⟩
    · exact Or.inr ⟨(t, u), ⟨Or.inr ht, by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
  have hSrcDPP : ∀ y ∈ Q ∪ A', y ∈ doublePointPreimage (⇑D) D.domain → y ∈ J ∪ T := by
    rintro y (hy | ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩) hd
    · exact Or.inl (hclean.subset ⟨hd, hy⟩)
    · rw [hρdpp t (Or.inr ht) u (hA₂I u (hA'I u hu)) hd, hρ0 t (Or.inr ht)]
      exact Or.inr ht
  have hSrcdom : ∀ y ∈ Q ∪ A', y ∈ D.domain := by
    rintro y (hy | hy)
    · exact hQdom hy
    · exact hA₂dom (hA'A₂ hy)
  have hFdisj : ∀ z ∈ β '' (E ∪ A'), z ∉ F₁ ∪ F₂ ∪ F₃ := by
    intro z hz hzF
    obtain ⟨y, hy, hyz⟩ := hSrcD z hz
    have hydom := hSrcdom y hy
    rcases hzF with (⟨x, ⟨hxdom, hxn⟩, hxz⟩ | ⟨⟨j, u⟩, ⟨hj, hu⟩, hxz⟩) |
      ⟨⟨t, u⟩, ⟨ht, hu⟩, hxz⟩
    · have hne : y ≠ x := fun h => hxn (by rw [← h]; exact hSrcO₁ y hy)
      have hyJT := hSrcDPP y hy (hdpp_of_ne y hydom x hxdom hne (hyz.trans hxz.symm))
      have hxJT := hcarrier_pre x hxdom (by rw [hxz, ← hyz]; exact hcarrier_img y hyJT)
      exact hxn (Or.inr ⟨(x, 0), ⟨hxJT, by linarith, hs₀⟩, hρ0 x hxJT⟩)
    · have huI : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hne : ρ (j, u) ∉ Q ∪ A' := by
        rintro (hq | ⟨⟨t, u'⟩, ⟨ht, hu'⟩, heq⟩)
        · have := (hρJQ j hj u huI).mp hq
          linarith [hu.2]
        · have h := hρinj t (Or.inr ht) u' (hA₂I u' (hA'I u' hu')) j (Or.inl hj) u huI heq
          exact Set.disjoint_left.mp hJT hj (by rw [← h.1]; exact ht)
      have hd := hdpp_of_ne (ρ (j, u)) (hρdom j (Or.inl hj) u huI) y hydom
        (fun h => hne (by rw [h]; exact hy)) (hxz.trans hyz.symm)
      have := hρdpp j (Or.inl hj) u huI hd
      linarith [hu.2]
    · have huI : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hne : ρ (t, u) ∉ Q ∪ A' := by
        rintro (hq | ⟨⟨t', u'⟩, ⟨ht', hu'⟩, heq⟩)
        · exact hρTQ' t ht u huI hq
        · have h := hρinj t' (Or.inr ht') u' (hA₂I u' (hA'I u' hu')) t (Or.inr ht) u huI heq
          linarith [hu.1, hu'.2, h.2]
      have hd := hdpp_of_ne (ρ (t, u)) (hρdom t (Or.inr ht) u huI) y hydom
        (fun h => hne (by rw [h]; exact hy)) (hxz.trans hyz.symm)
      have := hρdpp t (Or.inr ht) u huI hd
      linarith [hu.1]
  have hKc : IsCompact (b '' (E ∪ A')) :=
    hE'ball.isPolyhedron.isCompact.image_of_continuousOn hbpa.continuousOn
  have hKstd : b '' (E ∪ A') ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hbmaps hx
  obtain ⟨h₀, hh₀, hh₀1, hh₀F⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact hKc
    (hPcont.mono (prod_mono hKstd Subset.rfl)) hFclosed.isOpen_compl (by
      rintro _ ⟨x, hx, rfl⟩
      rw [hbβ x hx]
      exact hFdisj (β x) ⟨x, hx, rfl⟩)
  have hρA' : IsPLHomeomorphOn ρ (T ×ˢ Icc (-(s₀ / 2)) 0) A' :=
    hρT.restrict (hTpoly.prod isHPolytope_Icc.isPolyhedron)
      (prod_mono Subset.rfl fun u hu => hA₂I u (hA'I u hu))
  have hA'E : A' ∩ E = T := by
    apply Subset.antisymm
    · intro x hx
      exact hEA₂ ⟨hx.2, hA'A₂ hx.1⟩
    · intro t ht
      exact ⟨⟨(t, 0), ⟨ht, by linarith, le_rfl⟩, hρ0 t (Or.inr ht)⟩, hTE ht⟩
  have hE'E₂' : E ∪ A' ⊆ E ∪ A₂ := union_subset_union_right E hA'A₂
  have hbinj : InjOn b (E ∪ A') := by
    intro x hx y hy hxy
    apply hβinj (hE'E₂' hx) (hE'E₂' hy)
    rw [← hbβ x hx, ← hbβ y hy, hxy]
  obtain ⟨F, hFpl, hFinj, hFbd, hFrange⟩ := exists_capMap_of_centeredPrism hE hs₁ hρA'
    (fun x hx => hρ0 x (Or.inr hx)) hA'E hh₀ hh₀1 hσ hPinj (fun x hx => hbmaps hx) hbpa
    hbinj hPpl
  have hbdA' : ρ '' (T ×ˢ {-(s₀ / 2)}) ⊆ A' :=
    image_mono (prod_mono Subset.rfl fun u hu => ⟨le_of_eq hu.symm, by
      rw [show u = -(s₀ / 2) from hu]
      linarith⟩)
  have hFD : ∀ x ∈ frontier (E ∪ A'), F x = ⇑D x := by
    intro x hx
    rw [hE'front] at hx
    rw [hFbd x hx, hbβ x (Or.inr (hbdA' hx)), hβA (hA'A₂ (hbdA' hx))]
  have hQβ : ∀ y ∈ Q, ⇑D y ∈ β '' (E ∪ A₂) := by
    intro y hy
    obtain ⟨e, he, hke⟩ := hk.bijOn.surjOn hy
    refine ⟨e, Or.inl he, ?_⟩
    rw [hβE he]
    change ⇑D (k e) = ⇑D y
    rw [hke]
  have hσt : ∀ t ∈ Icc (0 : ℝ) h₀, σ * t ∈ Icc (-h₀) h₀ := by
    intro t ht
    rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith [ht.1, ht.2]
  have hσt1 : ∀ t ∈ Icc (0 : ℝ) h₀, σ * t ∈ Icc (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [(hσt t ht).1], by linarith [(hσt t ht).2]⟩
  have hFnot : ∀ x ∈ E ∪ A', x ∉ frontier (E ∪ A') → ∀ y ∈ D.domain, F x ≠ ⇑D y := by
    intro x hx hxb y hy hxy
    rw [hE'front] at hxb
    obtain ⟨t, ht, hFx, htpos⟩ := hFrange x hx
    have ht0 := htpos hxb
    have hbx := hbmaps hx
    have hyz : ⇑D y = prism (b x, σ * t) := hxy.symm.trans hFx
    have hzN : ⇑D y ∈ N := by
      rw [hyz]
      exact ⟨(b x, σ * t), ⟨hbx, hσt1 t ht⟩, rfl⟩
    have hzF : ⇑D y ∉ F₁ ∪ F₂ ∪ F₃ := by
      rw [hyz]
      exact hh₀F (b x) ⟨x, hx, rfl⟩ (σ * t) (hσt t ht)
    have hzβ : ⇑D y ∉ β '' (E ∪ A₂) := by
      intro hzb
      have hzCe : ⇑D y ∈ Ce := by
        rw [hPcenter]
        exact ⟨hzb, hzN⟩
      rw [hyz] at hzCe
      obtain ⟨p, hp, hpz⟩ := hzCe
      have hp2 : p.2 = 0 := hp.2
      have h := hPinj ⟨hp.1, by rw [hp2]; exact ⟨by norm_num, by norm_num⟩⟩ ⟨hbx, hσt1 t ht⟩ hpz
      have h2 : p.2 = σ * t := congrArg Prod.snd h
      rcases hσ with hσ1 | hσ1 <;> rw [hσ1] at h2 <;> linarith
    have htI : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, ht.2.trans hh₀1⟩
    by_cases hyfar : y ∈ interior Q ∪ O₁
    · rcases hyfar with hyQ | ⟨⟨w, u⟩, ⟨hw, hu⟩, rfl⟩
      · exact hzβ (hQβ y (interior_subset hyQ))
      · have huI := hIooI hu
        rcases hw with hj | ht'
        · by_cases hu0 : 0 ≤ u
          · exact hzβ (hQβ _ ((hρJQ w hj u huI).mpr hu0))
          · by_cases hue : -ε ≤ u
            · refine hσA₁ (b x) hbx t htI ?_
              rw [← hyz]
              exact ⟨(w, u), ⟨hj, hue, lt_of_not_ge hu0⟩, rfl⟩
            · exact hzF (Or.inl (Or.inr ⟨(w, u), ⟨hj, hu.1.le, (lt_of_not_ge hue).le⟩, rfl⟩))
        · by_cases hu0 : u ≤ 0
          · exact hzβ ⟨ρ (w, u), Or.inr ⟨(w, u), ⟨ht', hu.1.le, hu0⟩, rfl⟩,
              hβA ⟨(w, u), ⟨ht', hu.1.le, hu0⟩, rfl⟩⟩
          · by_cases hue : u ≤ ε
            · refine hσAin (b x) hbx t htI ?_
              rw [← hyz]
              exact ⟨(w, u), ⟨ht', lt_of_not_ge hu0, hue⟩, rfl⟩
            · exact hzF (Or.inr ⟨(w, u), ⟨ht', (lt_of_not_ge hue).le, hu.2.le⟩, rfl⟩)
    · exact hzF (Or.inl (Or.inl ⟨y, ⟨hy, hyfar⟩, rfl⟩))
  have hE'dom : E ∪ A' ⊆ D.domain := union_subset (hEint.trans interior_subset)
    fun x hx => hA₂dom (hA'A₂ hx)
  refine ⟨E ∪ A', ⟨E ∪ A', hE'ball, F, hFpl⟩, hE'ball, hEE', ?_, ?_, ?_, rfl, hFinj, ?_,
    hFD, ?_⟩
  · exact union_subset hEint fun x hx => hCint (hA₂C (hA'A₂ hx))
  · refine Set.disjoint_union_right.mpr ⟨hdisjoint, Set.disjoint_left.mpr fun x hxQ hxA =>
      hA₂Q x (hA'A₂ hxA) hxQ⟩
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨⟨hxU, hxE⟩, hxd⟩
    have hxA : x ∈ A' := hxU.resolve_left hxE
    exact hxE (hA₂dpp x (hA'A₂ hxA) hxd)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hFx, -⟩ := hFrange x hx
    change F x ∈ V
    rw [hFx]
    exact hPV ⟨(b x, σ * t), ⟨hbmaps hx, hσt1 t ht⟩, rfl⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
      by_cases hxb : x ∈ frontier (E ∪ A')
      · exact ⟨x, hxb, (hFD x hxb).symm⟩
      · exact absurd hyx.symm (hFnot x hx hxb y hy)
    · rintro _ ⟨x, hxb, rfl⟩
      have hxE' : x ∈ E ∪ A' := hE'ball.isPolyhedron.isCompact.isClosed.frontier_subset hxb
      exact ⟨⟨x, hxE', hFD x hxb⟩, ⟨x, hE'dom hxE', rfl⟩⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
