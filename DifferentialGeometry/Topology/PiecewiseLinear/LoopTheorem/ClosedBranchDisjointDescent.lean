/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAdaptation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchNestedCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem branchCarrier_subset_or_disjoint_doublePointSet_sdiff_interior [T2Space M]
    (hD : NormalSingularCellData D BdM B) {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsClosed K) (hfront : Disjoint (frontier K) (doublePointPreimage (⇑D) D.domain))
    (b : hD.singularSet.Branch) :
    hD.singularSet.branchCarrier b ⊆ doublePointSet D (D.domain \ interior K) ∨
      Disjoint (hD.singularSet.branchCarrier b) (doublePointSet D (D.domain \ interior K)) := by
  have hpreD : hD.branchPreimage b ⊆ D.domain := fun _ hx => hx.1
  have hPD : D.domain \ interior K ⊆ D.domain := Set.sdiff_subset
  have hpiece : ∀ V : Set (EuclideanSpace ℝ (Fin 2)), V ⊆ hD.branchPreimage b →
      IsPreconnected V → V ⊆ D.domain \ interior K ∨ Disjoint V (D.domain \ interior K) := by
    intro V hV hVconn
    have hVsplit : V ⊆ interior K ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · by_cases hxi : x ∈ interior K
        · exact Or.inl hxi
        · exfalso
          have hxf : x ∈ frontier K := by
            rw [hK.frontier_eq]
            exact ⟨hxK, hxi⟩
          exact Set.disjoint_left.mp hfront hxf
            (hD.branchPreimage_subset_doublePointPreimage b (hV hx))
      · exact Or.inr hxK
    rcases hVconn.subset_or_subset isOpen_interior hK.isOpen_compl
        (Set.disjoint_left.mpr fun x hxi hxc => hxc (interior_subset hxi)) hVsplit with
      h | h
    · exact Or.inr (Set.disjoint_left.mpr fun x hx hxP => hxP.2 (h hx))
    · exact Or.inl fun x hx => ⟨hpreD (hV hx), fun hxi => h hx (interior_subset hxi)⟩
  rcases hD.branchProjection_connected_or_two_components b with hconn | hcomp
  · have hpreconn : IsPreconnected (hD.branchPreimage b) :=
      (isConnected_iff_connectedSpace.mpr hconn).isPreconnected
    rcases hpiece (hD.branchPreimage b) Subset.rfl hpreconn with h | h
    · exact Or.inl (hD.branchCarrier_subset_doublePointSet_of_branchPreimage_subset b h)
    · exact Or.inr (hD.disjoint_branchCarrier_doublePointSet_of_subset_image b hpreD hPD
        (hD.branchCarrier_subset_image_branchPreimage b) h)
  · obtain ⟨x, y, -, hunivcc, ⟨e₁, he₁⟩, e₂, he₂⟩ := hcomp
    have hcomponent : ∀ (z : hD.branchPreimage b)
        (e : connectedComponent z ≃ₜ (hD.singularSet.branchComplex b).space),
        (∀ w : connectedComponent z, e w = hD.branchProjection b w) →
        hD.singularSet.branchCarrier b ⊆ D '' (Subtype.val '' connectedComponent z) := by
      intro z e he w hw
      obtain ⟨t, ht, htw⟩ := (hD.singularSet.branchPieceIn b).bijOn.surjOn hw
      obtain ⟨v, hv⟩ : ∃ v : connectedComponent z, e v = ⟨t, ht⟩ :=
        ⟨e.symm ⟨t, ht⟩, e.apply_symm_apply _⟩
      have hproj : hD.branchProjection b (v : hD.branchPreimage b) = ⟨t, ht⟩ :=
        (he v).symm.trans hv
      have hcoord : hD.branchCoordinate b
          ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2)) = t :=
        congrArg Subtype.val hproj
      have hmem : ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2)) ∈
          hD.branchPreimage b := (v : hD.branchPreimage b).2
      refine ⟨((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2)),
        ⟨(v : hD.branchPreimage b), v.2, rfl⟩, ?_⟩
      calc D ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2))
          = (hD.singularSet.branchPieceIn b).map
              (hD.branchCoordinate b
                ((v : hD.branchPreimage b) : EuclideanSpace ℝ (Fin 2))) :=
            (hD.branchPieceIn_map_branchCoordinate b hmem).symm
        _ = (hD.singularSet.branchPieceIn b).map t := by rw [hcoord]
        _ = w := htw
    have hsubcc : ∀ z : hD.branchPreimage b,
        Subtype.val '' connectedComponent z ⊆ hD.branchPreimage b := by
      rintro z - ⟨w, -, rfl⟩
      exact w.2
    have hconncc : ∀ z : hD.branchPreimage b,
        IsPreconnected (Subtype.val '' connectedComponent z) := fun z =>
      isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    have hunioncc : Subtype.val '' connectedComponent x ∪ Subtype.val '' connectedComponent y =
        hD.branchPreimage b := by
      rw [← Set.image_union, hunivcc]
      simp
    rcases hpiece _ (hsubcc x) (hconncc x) with hx' | hx'
    · rcases hpiece _ (hsubcc y) (hconncc y) with hy' | hy'
      · refine Or.inl (hD.branchCarrier_subset_doublePointSet_of_branchPreimage_subset b ?_)
        rw [← hunioncc]
        exact Set.union_subset hx' hy'
      · exact Or.inr (hD.disjoint_branchCarrier_doublePointSet_of_subset_image b
          ((hsubcc y).trans hpreD) hPD (hcomponent y e₂ he₂) hy')
    · exact Or.inr (hD.disjoint_branchCarrier_doublePointSet_of_subset_image b
        ((hsubcc x).trans hpreD) hPD (hcomponent x e₁ he₁) hx')

open Classical in
theorem exists_descendingSurgery_of_adaptedCleanCap [T2Space M]
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q E E' : Set (EuclideanSpace ℝ (Fin 2))}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsPLSphere 1 J) (hT : IsPLSphere 1 T) (hJT : Disjoint J T)
    (hpre : hD.branchPreimage c = J ∪ T)
    (hQ : IsPLBall 2 Q) (hQsub : Q ⊆ interior D.domain) (hfrontQ : frontier Q = J)
    (hclean : doublePointPreimage (⇑D) D.domain ∩ Q = J) (hinj : InjOn (⇑D) Q)
    (hE : IsPLBall 2 E) (hfrontE : frontier E = T)
    (hk : IsPLHomeomorphOn k E Q) (hkT : k '' T = J) (hkcompat : EqOn (⇑D) (⇑D ∘ k) T)
    (hdisjoint : Disjoint Q E)
    {C : Set M} (hside : IsPLBoundarySide D C BdM)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (Δ : SingularTwoCell M)
    (hE' : IsPLBall 2 E') (hEE' : E ⊆ interior E') (hE'int : E' ⊆ interior D.domain)
    (hQE' : Disjoint Q E') (hE'clean : (E' \ E) ∩ doublePointPreimage (⇑D) D.domain = ∅)
    (hΔdom : Δ.domain = E') (hΔinj : InjOn (⇑Δ) E')
    (hΔside : ⇑Δ '' E' ⊆ interior (C \ BdM)) (hΔbd : EqOn (⇑Δ) (⇑D) (frontier E'))
    (hΔmeet : ⇑Δ '' E' ∩ ⇑D '' D.domain = ⇑D '' frontier E')
    {Θ : Type v} [TopologicalSpace Θ] {Y : Type w} {ρ : M → Y} {γ : Θ → Y}
    (e : Θ ≃ₜ frontier D.domain) (hloop : ∀ θ, ρ (⇑D (e θ)) = γ θ) :
    ∃ Sg : hD.DescendingSurgery, MapsTo (⇑Sg.cell) Sg.cell.domain C ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
        ∃ e' : Θ ≃ₜ frontier Sg.cell.domain, ∀ θ, ρ (⇑Sg.cell (e' θ)) = γ θ := by
  let _ := hc
  let _ := hJ
  let _ := hT
  let _ := hJT
  let _ := hQsub
  let _ := hclean
  let _ := hk
  let _ := hkT
  let _ := hkcompat
  let _ := hdisjoint
  let _ := hQE'
  have hDclosed : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isCompact.isClosed
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hEclosed : IsClosed E := hE.isPolyhedron.isCompact.isClosed
  have hE'closed : IsClosed E' := hE'.isPolyhedron.isCompact.isClosed
  have hE'D : E' ⊆ D.domain := hE'int.trans interior_subset
  have hJQ : J ⊆ Q := by
    rw [← hfrontQ]
    exact hQclosed.frontier_subset
  have hTint : T ⊆ interior E' := by
    rw [← hfrontE]
    exact hEclosed.frontier_subset.trans hEE'
  have hfrontE' : ∀ x ∈ E', x ∉ interior E' → x ∈ frontier E' := by
    intro x hx hxi
    rw [hE'closed.frontier_eq]
    exact ⟨hx, hxi⟩
  have hfront : Disjoint (frontier E') (doublePointPreimage (⇑D) D.domain) := by
    refine Set.disjoint_left.mpr fun x hx hxd => ?_
    have hmem : x ∈ (E' \ E) ∩ doublePointPreimage (⇑D) D.domain :=
      ⟨⟨hE'closed.frontier_subset hx, fun hxE => hx.2 (hEE' hxE)⟩, hxd⟩
    rw [hE'clean] at hmem
    exact hmem
  have hOpoly : IsPolyhedron (D.domain \ interior E') :=
    D.isPLBall_domain.isPolyhedron.sdiff_interior_of_isPLBall hE'
  have hOclosed : IsClosed (D.domain \ interior E') := hDclosed.sdiff isOpen_interior
  have hseam : E' ∩ (D.domain \ interior E') = frontier E' := by
    refine Subset.antisymm (fun x hx => hfrontE' x hx.1 hx.2.2) fun x hx => ?_
    have hxE' : x ∈ E' := hE'closed.frontier_subset hx
    exact ⟨hxE', hE'D hxE', hx.2⟩
  have hcover : E' ∪ (D.domain \ interior E') = D.domain := by
    refine Subset.antisymm (union_subset hE'D Set.sdiff_subset) fun x hx => ?_
    by_cases hxi : x ∈ interior E'
    · exact Or.inl (interior_subset hxi)
    · exact Or.inr ⟨hx, hxi⟩
  have hΔPL : IsPLOn 2 3 (⇑Δ) E' := by
    rw [← hΔdom]
    exact Δ.isPLOn
  have hΔcont : ContinuousOn (⇑Δ) E' := by
    rw [← hΔdom]
    exact Δ.continuousOn
  have hDPL : IsPLOn 2 3 (⇑D) (D.domain \ interior E') :=
    D.isPLOn.mono_of_isPolyhedron hOpoly Set.sdiff_subset
  have hagree : EqOn (⇑Δ) (⇑D) (E' ∩ (D.domain \ interior E')) := by
    rw [hseam]
    exact hΔbd
  have hPL : IsPLOn 2 3 (E'.piecewise (⇑Δ) (⇑D)) D.domain := by
    have h := IsPLOn.piecewise_of_isClosed hΔPL hDPL hE'closed hOclosed hagree
    rwa [hcover] at h
  obtain ⟨G, hGdom, hGE', hGout⟩ : ∃ G : SingularTwoCell M, G.domain = D.domain ∧
      (∀ x ∈ E', ⇑G x = ⇑Δ x) ∧ ∀ x, x ∉ E' → ⇑G x = ⇑D x :=
    ⟨⟨D.domain, D.isPLBall_domain, E'.piecewise (⇑Δ) (⇑D), hPL⟩, rfl,
      fun x hx => Set.piecewise_eq_of_mem _ _ _ hx,
      fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx⟩
  have hGO : ∀ x ∈ D.domain \ interior E', ⇑G x = ⇑D x := by
    intro x hx
    by_cases hxE' : x ∈ E'
    · rw [hGE' x hxE']
      exact hΔbd (hfrontE' x hxE' hx.2)
    · exact hGout x hxE'
  have hGcont : ContinuousOn (⇑G) D.domain := by
    rw [← hGdom]
    exact G.continuousOn
  have hmix : ∀ x ∈ interior E', ∀ y ∈ D.domain, ⇑Δ x ≠ ⇑D y := by
    intro x hx y hy hxy
    have hmem : ⇑Δ x ∈ ⇑Δ '' E' ∩ ⇑D '' D.domain :=
      ⟨⟨x, interior_subset hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩
    rw [hΔmeet] at hmem
    obtain ⟨z, hz, hzx⟩ := hmem
    have hzx' : z = x :=
      hΔinj (hE'closed.frontier_subset hz) (interior_subset hx) ((hΔbd hz).trans hzx)
    exact hz.2 (hzx' ▸ hx)
  have hdps : doublePointSet (⇑G) G.domain = doublePointSet (⇑D) (D.domain \ interior E') := by
    ext y
    constructor
    · rintro ⟨u, hu, v, hv, huv, huy, hvy⟩
      rw [hGdom] at hu hv
      by_cases hui : u ∈ interior E' <;> by_cases hvi : v ∈ interior E'
      · exact absurd (hΔinj (interior_subset hui) (interior_subset hvi)
          ((hGE' u (interior_subset hui)).symm.trans
            (huy.trans (hvy.symm.trans (hGE' v (interior_subset hvi)))))) huv
      · exact absurd ((hGE' u (interior_subset hui)).symm.trans
          (huy.trans (hvy.symm.trans (hGO v ⟨hv, hvi⟩)))) (hmix u hui v hv)
      · exact absurd ((hGE' v (interior_subset hvi)).symm.trans
          (hvy.trans (huy.symm.trans (hGO u ⟨hu, hui⟩)))) (hmix v hvi u hu)
      · exact ⟨u, ⟨hu, hui⟩, v, ⟨hv, hvi⟩, huv, (hGO u ⟨hu, hui⟩).symm.trans huy,
          (hGO v ⟨hv, hvi⟩).symm.trans hvy⟩
    · rintro ⟨u, hu, v, hv, huv, huy, hvy⟩
      have hu' : u ∈ G.domain := by
        rw [hGdom]
        exact hu.1
      have hv' : v ∈ G.domain := by
        rw [hGdom]
        exact hv.1
      exact ⟨u, hu', v, hv', huv, (hGO u hu).trans huy, (hGO v hv).trans hvy⟩
  have hdsub : doublePointSet (⇑G) G.domain ⊆ doublePointSet (⇑D) D.domain := by
    rw [hdps]
    rintro z ⟨u, hu, v, hv, huv, huz, hvz⟩
    exact ⟨u, hu.1, v, hv.1, huv, huz, hvz⟩
  have hdoubleOut : ∀ u ∈ D.domain \ interior E', ∀ v ∈ D.domain \ interior E', u ≠ v →
      ⇑D u = ⇑D v → u ∉ E' := by
    intro u hu v hv huv huv' huE'
    exact Set.disjoint_left.mp hfront (hfrontE' u huE' hu.2)
      ⟨hu.1, u, hu.1, v, hv.1, huv, rfl, huv'.symm⟩
  have hfibreOut : ∀ y ∈ doublePointSet (⇑G) G.domain,
      D.domain ∩ ⇑D ⁻¹' {y} ⊆ D.domain \ E' := by
    intro y hy
    rw [hdps] at hy
    obtain ⟨u, hu, v, hv, huv, huy, hvy⟩ := hy
    have hfib := fiber_eq_pair_of_encard_le_two (⇑D) D.domain hu.1 hv.1 huv huy hvy
      (hD.fiber_le_two y)
    rw [hfib]
    rintro w (rfl | rfl)
    · exact ⟨hu.1, hdoubleOut w hu v hv huv (huy.trans hvy.symm)⟩
    · exact ⟨hv.1, hdoubleOut w hv u hu (Ne.symm huv) (hvy.trans huy.symm)⟩
  have hΔnot : ∀ y ∈ doublePointSet (⇑G) G.domain, y ∉ ⇑Δ '' E' := by
    intro y hy hyΔ
    have hyD : y ∈ ⇑D '' D.domain := by
      have hy' := hy
      rw [hdps] at hy'
      obtain ⟨u, hu, -, -, -, huy, -⟩ := hy'
      exact ⟨u, hu.1, huy⟩
    have hmem : y ∈ ⇑Δ '' E' ∩ ⇑D '' D.domain := ⟨hyΔ, hyD⟩
    rw [hΔmeet] at hmem
    obtain ⟨z, hz, hzy⟩ := hmem
    have hzE' : z ∈ E' := hE'closed.frontier_subset hz
    exact (hfibreOut y hy ⟨hE'D hzE', hzy⟩).2 hzE'
  have hΔclosed : IsClosed (⇑Δ '' E') :=
    (hE'.isPolyhedron.isCompact.image_of_continuousOn hΔcont).isClosed
  have hfibreEq : ∀ y ∈ doublePointSet (⇑G) G.domain,
      ∀ᶠ z in 𝓝 y, D.domain ∩ ⇑D ⁻¹' {z} = D.domain ∩ ⇑G ⁻¹' {z} := by
    intro y hy
    obtain ⟨a, b, hab, hfib⟩ := hD.exists_fiber_eq_pair (hdsub hy)
    have hsub := hfibreOut y hy
    rw [hfib] at hsub
    have ha : a ∈ D.domain \ E' := hsub (Or.inl rfl)
    have hb : b ∈ D.domain \ E' := hsub (Or.inr rfl)
    have hnhdsa : D.domain \ E' ∈ 𝓝[D.domain] a :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hE'closed.isOpen_compl.mem_nhds ha.2))
    have hnhdsb : D.domain \ E' ∈ 𝓝[D.domain] b :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hE'closed.isOpen_compl.mem_nhds hb.2))
    filter_upwards [eventually_preimage_subset_union_of_fiber_eq_pair (⇑D)
      D.isPLBall_domain.isPolyhedron.isCompact D.continuousOn hfib hnhdsa hnhdsb,
      hΔclosed.isOpen_compl.mem_nhds (hΔnot y hy)] with z hz hzΔ
    have hzout : D.domain ∩ ⇑D ⁻¹' {z} ⊆ D.domain \ E' := fun w hw => (hz hw).elim id id
    refine Subset.antisymm (fun w hw => ⟨hw.1, ?_⟩) fun w hw => ⟨hw.1, ?_⟩
    · change ⇑G w = z
      rw [hGout w (hzout hw).2]
      exact hw.2
    · have hwz : ⇑G w = z := hw.2
      have hwE' : w ∉ E' := fun hwE' => hzΔ ⟨w, hwE', (hGE' w hwE').symm.trans hwz⟩
      change ⇑D w = z
      rw [← hGout w hwE']
      exact hwz
  have hinjtransfer : ∀ U : Set (EuclideanSpace ℝ (Fin 2)), U ⊆ D.domain → InjOn (⇑D) U →
      InjOn (⇑G) U := by
    intro U hUD hU x hx y hy hxy
    by_cases hxi : x ∈ interior E' <;> by_cases hyi : y ∈ interior E'
    · exact hΔinj (interior_subset hxi) (interior_subset hyi)
        ((hGE' x (interior_subset hxi)).symm.trans (hxy.trans (hGE' y (interior_subset hyi))))
    · exact absurd ((hGE' x (interior_subset hxi)).symm.trans
        (hxy.trans (hGO y ⟨hUD hy, hyi⟩))) (hmix x hxi y (hUD hy))
    · exact absurd ((hGE' y (interior_subset hyi)).symm.trans
        (hxy.symm.trans (hGO x ⟨hUD hx, hxi⟩))) (hmix y hyi x (hUD hx))
    · exact hU hx hy ((hGO x ⟨hUD hx, hxi⟩).symm.trans (hxy.trans (hGO y ⟨hUD hy, hyi⟩)))
  have hloc : ∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, InjOn (⇑G) W := by
    rw [hGdom]
    intro x hx
    obtain ⟨U, hU, hUinj⟩ := hD.locallyInjective x hx
    exact ⟨U ∩ D.domain, Filter.inter_mem hU self_mem_nhdsWithin,
      hinjtransfer _ inter_subset_right (hUinj.mono inter_subset_left)⟩
  have hfibre : ∀ y : M, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2 := by
    intro y
    rw [hGdom]
    by_cases hyΔ : y ∈ ⇑Δ '' E'
    · obtain ⟨x₀, hx₀, hx₀y⟩ := hyΔ
      have hsub : D.domain ∩ ⇑G ⁻¹' {y} ⊆ {x₀} := by
        rintro w ⟨hwD, hwy⟩
        have hwy' : ⇑G w = y := hwy
        by_cases hwE' : w ∈ E'
        · exact hΔinj hwE' hx₀ ((hGE' w hwE').symm.trans (hwy'.trans hx₀y.symm))
        · exfalso
          have hDw : ⇑D w = y := (hGout w hwE').symm.trans hwy'
          have hmem : y ∈ ⇑Δ '' E' ∩ ⇑D '' D.domain := ⟨⟨x₀, hx₀, hx₀y⟩, ⟨w, hwD, hDw⟩⟩
          rw [hΔmeet] at hmem
          obtain ⟨z, hz, hzy⟩ := hmem
          have hzE' : z ∈ E' := hE'closed.frontier_subset hz
          have hzw : z ≠ w := fun h => hwE' (h ▸ hzE')
          exact Set.disjoint_left.mp hfront hz
            ⟨hE'D hzE', z, hE'D hzE', w, hwD, hzw, rfl, hDw.trans hzy.symm⟩
      calc (D.domain ∩ ⇑G ⁻¹' {y}).encard
          ≤ ({x₀} : Set (EuclideanSpace ℝ (Fin 2))).encard := Set.encard_mono hsub
        _ = 1 := Set.encard_singleton x₀
        _ ≤ 2 := by norm_num
    · have hsub : D.domain ∩ ⇑G ⁻¹' {y} ⊆ D.domain ∩ ⇑D ⁻¹' {y} := by
        rintro w ⟨hwD, hwy⟩
        have hwy' : ⇑G w = y := hwy
        have hwE' : w ∉ E' := fun hwE' => hyΔ ⟨w, hwE', (hGE' w hwE').symm.trans hwy'⟩
        exact ⟨hwD, (hGout w hwE').symm.trans hwy'⟩
      exact (Set.encard_mono hsub).trans (hD.fiber_le_two y)
  have hfrontsub : frontier D.domain ⊆ D.domain \ E' := by
    intro x hx
    have hxD : x ∈ D.domain := D.frontier_subset_domain hx
    exact ⟨hxD, fun hxE' => (mem_interior_iff_notMem_frontier hxD).mp (hE'int hxE') hx⟩
  have hoff : EqOn (⇑G) (⇑D) (D.domain \ E') := fun x hx => hGout x hx.2
  have hrangeim : ∀ H : SingularTwoCell M, Set.range H.boundary = ⇑H '' frontier H.domain := by
    intro H
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrange : Set.range G.boundary = Set.range D.boundary := by
    rw [hrangeim G, hrangeim D, hGdom]
    exact Set.image_congr fun x hx => hoff (hfrontsub hx)
  have himage : ⇑G '' G.domain ⊆ ⇑D '' D.domain ∪ ⇑Δ '' E' := by
    rw [hGdom]
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxE' : x ∈ E'
    · exact Or.inr ⟨x, hxE', (hGE' x hxE').symm⟩
    · exact Or.inl ⟨x, hx, (hGout x hxE').symm⟩
  have hΔBd : Disjoint (⇑Δ '' E') BdM :=
    Set.disjoint_left.mpr fun y hy hyB => (interior_subset (hΔside hy)).2 hyB
  have hrangeB : Set.range G.boundary ⊆ B := by
    rw [hrange]
    exact hD.boundary_image_subset
  have hinterBd : ⇑G '' G.domain ∩ BdM = Set.range G.boundary := by
    refine Subset.antisymm (fun y hy => ?_) fun y hy => ⟨?_, ?_⟩
    · rcases himage hy.1 with hyD | hyΔ
      · rw [hrange, ← hD.image_inter_boundary]
        exact ⟨hyD, hy.2⟩
      · exact absurd hy.2 (Set.disjoint_left.mp hΔBd hyΔ)
    · rw [hrangeim G] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, G.frontier_subset_domain hx, rfl⟩
    · have hyD : y ∈ ⇑D '' D.domain ∩ BdM := by
        rw [hD.image_inter_boundary, ← hrange]
        exact hy
      exact hyD.2
  have hmiss : Disjoint (doublePointSet (⇑G) G.domain) (hD.singularSet.branchCarrier c) := by
    rw [hdps]
    refine Set.disjoint_left.mpr fun y hy hycar => ?_
    obtain ⟨u, hu, v, hv, huv, huy, hvy⟩ := hy
    have hpreJ : ∀ w ∈ D.domain \ interior E', ⇑D w = y → w ∈ J := by
      intro w hw hwy
      have hwcar : ⇑D w ∈ hD.singularSet.branchCarrier c := by
        rw [hwy]
        exact hycar
      have hwpre : w ∈ hD.branchPreimage c := ⟨hw.1, hwcar⟩
      rw [hpre] at hwpre
      exact hwpre.resolve_right fun hwT => hw.2 (hTint hwT)
    exact huv (hinj (hJQ (hpreJ u hu huy)) (hJQ (hpreJ v hv hvy)) (huy.trans hvy.symm))
  have hcross : ∀ y ∈ doublePointSet (⇑G) G.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (⇑e '' (e.source ∩ BdM)) (e y) := by
    intro y hy
    obtain ⟨e, he, hye, hcr⟩ := hD.crossing y (hdsub hy)
    refine ⟨e, he, hye, ?_⟩
    rw [hGdom]
    exact HasPLNormalDoubleCrossingAt.of_eventually_eq_fiber
      (e.continuousOn.comp (hGcont.mono inter_subset_left) fun _ hx => hx.2)
      (eventually_eq_inter_fiber_comp_openPartialHomeomorph e D.domain hye (hfibreEq y hy)) hcr
  have hcompact : IsCompact (doublePointSet (⇑G) G.domain) :=
    isCompact_doublePointSet_of_isLocallyInjective
      G.isPLBall_domain.isPolyhedron.isCompact G.continuousOn
      (Covering.isLocallyInjective_domRestrict_iff.mpr hloc)
  have hSclosed : IsClosed (⇑D '' frontier E') :=
    ((hE'.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier
      hE'closed.frontier_subset).image_of_continuousOn
        (D.continuousOn.mono (hE'closed.frontier_subset.trans hE'D))).isClosed
  have hSdisj : Disjoint (doublePointSet (⇑D) (D.domain \ interior E'))
      (⇑D '' frontier E') := by
    refine Set.disjoint_left.mpr fun y hy hyS => ?_
    have hyG : y ∈ doublePointSet (⇑G) G.domain := by
      rw [hdps]
      exact hy
    obtain ⟨z, hz, hzy⟩ := hyS
    have hzE' : z ∈ E' := hE'closed.frontier_subset hz
    exact (hfibreOut y hyG ⟨hE'D hzE', hzy⟩).2 hzE'
  have hopenO := doublePointSet_mem_nhdsWithin_of_pullback (r := id)
    (O := D.domain \ interior E') (Q := D.domain \ interior E') (S := ⇑D '' frontier E')
    D.isPLBall_domain.isPolyhedron.isCompact D.continuousOn hD.fiber_le_two
    (fun x hx => hx.1) (fun _ _ => rfl) (injOn_id _) (fun _ hx => hx)
    (fun x hx hxS => by
      have hxE' : x ∉ E' := fun hxE' => hxS ⟨x, hfrontE' x hxE' hx.2, rfl⟩
      exact Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (hE'closed.isOpen_compl.mem_nhds hxE')))
        fun w hw => ⟨hw.1, fun hwi => hw.2 (interior_subset hwi)⟩)
    (fun x hx _ => ⟨x, hx, rfl⟩) hSclosed hSdisj
  have hopenin : ∀ y ∈ doublePointSet (⇑G) G.domain,
      doublePointSet (⇑G) G.domain ∈ 𝓝[doublePointSet (⇑D) D.domain] y := by
    rw [hdps]
    exact hopenO
  let hG : NormalSingularCellData G BdM B :=
    { locallyInjective := hloc
      fiber_le_two := hfibre
      boundary_image_subset := hrangeB
      image_inter_boundary := hinterBd
      singularSet := Classical.choice
        (hD.singularSet.restrict_to_clopen_doublePointSet hdsub hcompact hopenin)
      crossing := hcross }
  have hwhole : ∀ a : hD.singularSet.Branch,
      hD.singularSet.branchCarrier a ⊆ doublePointSet (⇑G) G.domain ∨
        Disjoint (hD.singularSet.branchCarrier a) (doublePointSet (⇑G) G.domain) := by
    intro a
    rw [hdps]
    exact hD.branchCarrier_subset_or_disjoint_doublePointSet_sdiff_interior hE'closed hfront a
  refine ⟨DescendingSurgery.ofBranchInjection hD hG
    (hD.singularSet.branchOrigin hG.singularSet hdsub)
    (hD.singularSet.injective_branchOrigin_of_subset_or_disjoint hG.singularSet hdsub hwhole)
    (hD.singularSet.branchOrigin_ne hG.singularSet hdsub hmiss), ?_, ?_, ?_⟩
  · change MapsTo (⇑G) G.domain C
    rw [hGdom]
    intro x hx
    by_cases hxE' : x ∈ E'
    · rw [hGE' x hxE']
      exact (interior_subset (hΔside ⟨x, hxE', rfl⟩)).1
    · rw [hGout x hxE']
      exact hside.1 ⟨x, hx, rfl⟩
  · intro z hz
    exact hbuffer z (hrange.subset hz)
  · change ∃ e' : Θ ≃ₜ frontier G.domain, ∀ θ, ρ (⇑G (e' θ)) = γ θ
    refine ⟨e.trans (Homeomorph.setCongr (congrArg frontier hGdom).symm), fun θ => ?_⟩
    change ρ (⇑G ((e θ : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = γ θ
    rw [hoff (hfrontsub (e θ).property)]
    exact hloop θ

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
