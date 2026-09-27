/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchNestedCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

theorem subset_interior_or_disjoint_of_isPreconnected {X : Type*} [TopologicalSpace X]
    {S E : Set X} (hS : IsPreconnected S) (hE : IsClosed E)
    (hdisjoint : Disjoint S (frontier E)) : S ⊆ interior E ∨ Disjoint S E := by
  by_cases hin : (S ∩ E).Nonempty
  · refine Or.inl fun x hx => ?_
    by_contra hxi
    obtain ⟨y, hyS, hyE, hyout⟩ :=
      isPreconnected_closed_iff.mp hS E (interior E)ᶜ hE isOpen_interior.isClosed_compl
        (fun z _ => by
          by_cases hz : z ∈ E
          · exact Or.inl hz
          · exact Or.inr fun hzi => hz (interior_subset hzi))
        hin ⟨x, hx, hxi⟩
    refine Set.disjoint_left.mp hdisjoint hyS ?_
    rw [hE.frontier_eq]
    exact ⟨hyE, hyout⟩
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hin))

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_innermost_cleanDisk_replacement_of_exists_not_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch, ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch, ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧ IsPLBall 2 Q ∧
        Q ⊆ interior D.domain ∧ frontier Q = J ∧
          doublePointPreimage (⇑D) D.domain ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ (T E : Set (EuclideanSpace ℝ (Fin 2)))
                  (k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T ∧ InjOn (⇑D) Q ∧
                  IsPLBall 2 E ∧ frontier E = T ∧ IsPLHomeomorphOn k E Q ∧ k '' T = J ∧
                    EqOn (⇑D) (⇑D ∘ k) T ∧ (Q ⊆ interior E ∨ Disjoint Q E)) := by
  obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontQ, hclean, hsplit⟩ :=
    hD.exists_innermost_isPLBall_doublePointPreimage_decomposition_with_coordinate hclosed
  have hQD : Q ⊆ D.domain := hQsub.trans interior_subset
  rcases hsplit with hsingle | ⟨T, hT, hJT, hpre, hJcoord, hTcoord⟩
  · exact ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontQ, hclean, Or.inl hsingle⟩
  · have hJsub : J ⊆ hD.branchPreimage c := by
      rw [hpre]
      exact subset_union_left
    have hTsub : T ⊆ hD.branchPreimage c := by
      rw [hpre]
      exact subset_union_right
    have hinj : InjOn (⇑D) Q :=
      hD.injOn_of_doublePointPreimage_inter_eq_of_branchCoordinate hJsub hQD hclean hJcoord
    obtain ⟨g, hg, hgcompat⟩ :=
      hD.exists_isPLHomeomorphOn_eqOn_of_branchCoordinate c hTsub hJsub hTcoord hJcoord
    obtain ⟨E, hE, hfrontE, -⟩ := isPLBall_of_isPLSphere_one hT
    have hgfrontier : IsPLHomeomorphOn g (frontier E) (frontier Q) := by
      rw [hfrontE, hfrontQ]
      exact hg
    obtain ⟨k, hk, hkg⟩ := exists_isPLHomeomorphOn_of_frontier hE hQ hgfrontier
    have hkT : k '' T = J := by
      rw [← hfrontE, Set.image_congr fun x hx => hkg hx, hfrontE, hg.bijOn.image_eq]
    have hkcompat : EqOn (⇑D) (⇑D ∘ k) T := by
      intro x hx
      have hxfront : x ∈ frontier E := by rwa [hfrontE]
      calc ⇑D x = ⇑D (g x) := hgcompat hx
        _ = (⇑D ∘ k) x := congrArg (⇑D) (hkg hxfront).symm
    have hTQ : Disjoint T Q :=
      Set.disjoint_left.mpr fun x hxT hxQ =>
        Set.disjoint_left.mp hJT
          (hclean.subset ⟨hD.branchPreimage_subset_doublePointPreimage c (hTsub hxT), hxQ⟩) hxT
    have hdich : Q ⊆ interior E ∨ Disjoint Q E := by
      refine subset_interior_or_disjoint_of_isPreconnected hQ.isConnected.isPreconnected
        hE.isPolyhedron.isCompact.isClosed ?_
      rw [hfrontE]
      exact hTQ.symm
    exact ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontQ, hclean,
      Or.inr ⟨T, E, k, hT, hJT, hpre, hinj, hE, hfrontE, hk, hkT, hkcompat, hdich⟩⟩

theorem exists_branchOrigin_of_isNestedDiskReplacementCell [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hGc : hD.IsNestedDiskReplacementCell c G) (hG : NormalSingularCellData G BdM B) :
    ∃ origin : hG.singularSet.Branch → hD.singularSet.Branch,
      Function.Injective origin ∧ ∀ b, origin b ≠ c := by
  obtain ⟨J, T, Q, E, -, -, -, -, hJT, hpre, hQ, hfrontQ, hclean, -, hE, hEint, hfrontE,
    hnested, -, -, -, -, -, -, -, -, -, -, -, hdps, hdsub, hmiss, -⟩ := hGc
  have hDclosed : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isCompact.isClosed
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hEclosed : IsClosed E := hE.isPolyhedron.isCompact.isClosed
  have hQE : Q ⊆ E := hnested.trans interior_subset
  have hED : E ⊆ D.domain := hEint.trans interior_subset
  have hQD : Q ⊆ D.domain := hQE.trans hED
  have hTE : T ⊆ E := by
    rw [← hfrontE]
    exact hEclosed.frontier_subset
  have hJQ : J ⊆ Q := by
    rw [← hfrontQ]
    exact hQclosed.frontier_subset
  have hTQ : Disjoint T Q :=
    Set.disjoint_left.mpr fun x hxT hxQ =>
      Set.disjoint_left.mp hJT
        (hclean.subset
          ⟨hD.branchPreimage_subset_doublePointPreimage c (hpre ▸ Or.inr hxT), hxQ⟩) hxT
  have hwhole : ∀ a : hD.singularSet.Branch,
      hD.singularSet.branchCarrier a ⊆ doublePointSet (⇑G) G.domain ∨
        Disjoint (hD.singularSet.branchCarrier a) (doublePointSet (⇑G) G.domain) := by
    intro a
    by_cases hac : a = c
    · refine Or.inr ?_
      rw [hac]
      exact hmiss.symm
    · rw [hdps]
      refine hD.branchCarrier_subset_or_disjoint_doublePointSet
        (A := J ∪ T) (C := ∅) (P := (D.domain \ E) ∪ Q)
        (U₁ := Q ∪ (D.domain \ interior E)) (U₂ := E \ interior Q) (U₃ := ∅)
        (hQclosed.union (hDclosed.sdiff isOpen_interior))
        (hEclosed.sdiff isOpen_interior) isClosed_empty
        (by rw [hpre, union_empty])
        ?_ ?_ (inter_empty _) (union_subset Set.sdiff_subset hQD) ?_ ?_ hac
      · refine Subset.antisymm ?_ fun x hx => ?_
        · exact union_subset
            (union_subset (union_subset hQD Set.sdiff_subset)
              (Set.sdiff_subset.trans hED)) (empty_subset _)
        · by_cases hxE : x ∈ interior E
          · by_cases hxQ : x ∈ interior Q
            · exact Or.inl (Or.inl (Or.inl (interior_subset hxQ)))
            · exact Or.inl (Or.inr ⟨interior_subset hxE, hxQ⟩)
          · exact Or.inl (Or.inl (Or.inr ⟨hx, hxE⟩))
      · refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
        · rcases hx.1 with hxQ | hxout
          · refine Or.inl ?_
            rw [← hfrontQ, hQclosed.frontier_eq]
            exact ⟨hxQ, hx.2.2⟩
          · refine Or.inr ?_
            rw [← hfrontE, hEclosed.frontier_eq]
            exact ⟨hx.2.1, hxout.2⟩
        · rcases hx with hxJ | hxT
          · have hxQ : x ∈ Q := hJQ hxJ
            refine ⟨Or.inl hxQ, hQE hxQ, ?_⟩
            have : x ∈ frontier Q := by rwa [hfrontQ]
            rw [hQclosed.frontier_eq] at this
            exact this.2
          · have hxE : x ∈ E := hTE hxT
            have hxfront : x ∈ frontier E := by rwa [hfrontE]
            rw [hEclosed.frontier_eq] at hxfront
            exact ⟨Or.inr ⟨hED hxE, hxfront.2⟩, hxE,
              fun hxQ => Set.disjoint_left.mp hTQ hxT (interior_subset hxQ)⟩
      · rintro x ⟨hxD, hxU⟩
        by_cases hxE : x ∈ E
        · refine Or.inr ?_
          by_contra hxQ
          exact hxU ⟨hxE, fun hxi => hxQ (interior_subset hxi)⟩
        · exact Or.inl ⟨hxD, hxE⟩
      · refine Set.disjoint_left.mpr ?_
        rintro x (⟨-, hxE⟩ | hxQ) ⟨⟨hxE', hxQ'⟩, hxA⟩
        · exact hxE hxE'
        · refine hxA (Or.inl ?_)
          rw [← hfrontQ, hQclosed.frontier_eq]
          exact ⟨hxQ, hxQ'⟩
  exact ⟨hD.singularSet.branchOrigin hG.singularSet hdsub,
    hD.singularSet.injective_branchOrigin_of_subset_or_disjoint hG.singularSet hdsub hwhole,
    hD.singularSet.branchOrigin_ne hG.singularSet hdsub hmiss⟩

theorem exists_descendingSurgery_of_isNestedDiskReplacementCell [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hGc : hD.IsNestedDiskReplacementCell c G) {C : Set M}
    (hside : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    {Θ : Type v} [TopologicalSpace Θ] {Y : Type w} {ρ : M → Y} {γ : Θ → Y}
    (e : Θ ≃ₜ frontier D.domain) (hloop : ∀ θ, ρ (⇑D (e θ)) = γ θ) :
    ∃ Sg : hD.DescendingSurgery, MapsTo (⇑Sg.cell) Sg.cell.domain C ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
        ∃ e' : Θ ≃ₜ frontier Sg.cell.domain, ∀ θ, ρ (⇑Sg.cell (e' θ)) = γ θ := by
  obtain ⟨hG⟩ := hD.nonempty_normalSingularCellData_of_isNestedDiskReplacementCell hGc
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isNestedDiskReplacementCell hGc hG
  obtain ⟨E, hE, hEint, hoff⟩ := hD.exists_isPLBall_eqOn_of_isNestedDiskReplacementCell hGc
  have hdom : G.domain = D.domain := hD.domain_eq_of_isNestedDiskReplacementCell hGc
  have hrange : Set.range G.boundary = Set.range D.boundary :=
    hD.range_boundary_eq_of_isNestedDiskReplacementCell hGc
  have himage : ⇑G '' G.domain ⊆ ⇑D '' D.domain :=
    hD.image_subset_of_isNestedDiskReplacementCell hGc
  have hfrontsub : frontier D.domain ⊆ D.domain \ E := by
    intro x hx
    have hxD : x ∈ D.domain := D.frontier_subset_domain hx
    exact ⟨hxD, fun hxE => (mem_interior_iff_notMem_frontier hxD).mp (hEint hxE) hx⟩
  refine ⟨DescendingSurgery.ofBranchInjection hD hG origin hinj hmiss, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, hwx⟩ := himage ⟨x, hx, rfl⟩
    exact hwx ▸ hside hw
  · intro z hz
    exact hbuffer z (hrange.subset hz)
  · change ∃ e' : Θ ≃ₜ frontier G.domain, ∀ θ, ρ (⇑G (e' θ)) = γ θ
    refine ⟨e.trans (Homeomorph.setCongr (congrArg frontier hdom).symm), fun θ => ?_⟩
    change ρ (⇑G ((e θ : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = γ θ
    rw [hoff (hfrontsub (e θ).property)]
    exact hloop θ

theorem exists_descendingSurgery_of_nested_innermost_cleanDisk [T2Space M]
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q E : Set (EuclideanSpace ℝ (Fin 2))}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsPLSphere 1 J) (hT : IsPLSphere 1 T) (hJT : Disjoint J T)
    (hpre : hD.branchPreimage c = J ∪ T)
    (hQ : IsPLBall 2 Q) (hfrontQ : frontier Q = J)
    (hclean : doublePointPreimage (⇑D) D.domain ∩ Q = J) (hinj : InjOn (⇑D) Q)
    (hE : IsPLBall 2 E) (hfrontE : frontier E = T)
    (hk : IsPLHomeomorphOn k E Q) (hkT : k '' T = J) (hkcompat : EqOn (⇑D) (⇑D ∘ k) T)
    (hnested : Q ⊆ interior E)
    {C : Set M} (hside : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    {Θ : Type v} [TopologicalSpace Θ] {Y : Type w} {ρ : M → Y} {γ : Θ → Y}
    (e : Θ ≃ₜ frontier D.domain) (hloop : ∀ θ, ρ (⇑D (e θ)) = γ θ) :
    ∃ Sg : hD.DescendingSurgery, MapsTo (⇑Sg.cell) Sg.cell.domain C ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
        ∃ e' : Θ ≃ₜ frontier Sg.cell.domain, ∀ θ, ρ (⇑Sg.cell (e' θ)) = γ θ := by
  obtain ⟨G, hGc⟩ := hD.exists_isNestedDiskReplacementCell hc hJ hT hJT hpre hQ hfrontQ hclean
    hinj hE hfrontE hk hkT hkcompat hnested
  exact hD.exists_descendingSurgery_of_isNestedDiskReplacementCell hGc hside hbuffer e hloop

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
