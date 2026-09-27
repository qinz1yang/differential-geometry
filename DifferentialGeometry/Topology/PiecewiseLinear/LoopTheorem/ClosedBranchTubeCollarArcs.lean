/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarSourceCharts
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCrossingArcs
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSurfaceSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_crossHalfPlane_of_mem_crossPlanes {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ crossPlanes) : ∃ i : Fin 4, p ∈ crossHalfPlane i := by
  rcases hp with hx | hy
  · rcases le_total 0 p.1.2 with h | h
    · exact ⟨1, p.1.2, h, by ext <;> simp [fourSpokeModelLeaf, hx]⟩
    · exact ⟨3, -p.1.2, neg_nonneg.mpr h, by ext <;> simp [fourSpokeModelLeaf, hx]⟩
  · rcases le_total 0 p.1.1 with h | h
    · exact ⟨0, p.1.1, h, by ext <;> simp [fourSpokeModelLeaf, hy]⟩
    · exact ⟨2, -p.1.1, neg_nonneg.mpr h, by ext <;> simp [fourSpokeModelLeaf, hy]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_subdivision_branchSurface_arcs_in_source_charts
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
        {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
        {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
        {sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)},
        hD.IsMarkedBranchCollar c J Q C τ ρ sheet →
        ∀ R₀ : Geometry.SimplicialComplex ℝ E, Finite R₀.faces → IsSubdivision R₀ L →
          ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R R₀ ∧ R.faces.Finite ∧
            (PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)).space =
              Subtype.val '' hD.singularSet.branchCarrier c ∧
            let Γ := PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)
            ∀ s ∈ Γ.faces, ∀ y₀ y₁ : E,
              Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y₀, y₁} →
              ∃ a ∈ J, ∃ (A₀ A₁ : Set (EuclideanSpace ℝ (Fin 2))) (U : Set L.space),
                IsCompact A₀ ∧ IsCompact A₁ ∧ A₀ ⊆ C ∧ A₁ ⊆ C ∧ Disjoint A₀ A₁ ∧
                InjOn D A₀ ∧ InjOn D A₁ ∧ U ⊆ (sheet a).source ∧
                (derivedNeighborhoodCell R s).space ⊆ Subtype.val '' U ∧
                (∀ x ∈ D.domain, D x ∈ U → x ∈ A₀ ∪ A₁) ∧
                (∀ y ∈ U, y ∈ D '' A₀ ↔ (sheet a y).2.2 = 0) ∧
                (∀ y ∈ U, y ∈ D '' A₁ ↔ (sheet a y).2.1 = 0) ∧
                (∀ y ∈ U, y ∈ hD.singularSet.branchCarrier c ↔ (sheet a y).2 = 0) ∧
                (∀ x ∈ A₀, 0 < (sheet a (D x)).2.1 ↔
                  ∃ v ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, v)) ∧
                (∀ x ∈ A₁, 0 < (sheet a (D x)).2.2 ↔
                  ∃ v ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, v)) ∧
                ∃ (P : Fin 4 → Set E) (γ : Fin 4 → ℝ → E),
                  (∀ x ∈ (derivedNeighborhoodCell R s).space,
                    x ∈ Subtype.val '' (D '' D.domain) ↔ ∃ i, x ∈ P i) ∧
                  (∀ i, IsPLBall 2 (P i) ∧ P i ⊆ Subtype.val '' (D '' D.domain) ∧
                    (PiecewiseLinear.restrict R (P i)).space = P i ∧
                    IsPLHomeomorphOn (γ i) (Icc 0 1)
                      ((derivedNeighborhoodCellBase R s).space ∩ P i) ∧
                    γ i 0 = y₀ ∧ γ i 1 = y₁ ∧
                    ∀ t ∈ Γ.faces, (s ⊆ t ∨ t ⊆ s) →
                      t ∈ (boundaryComplex 2 (PiecewiseLinear.restrict R (P i))).faces) ∧
                  (∀ i j, i ≠ j →
                    ((derivedNeighborhoodCellBase R s).space ∩ P i) ∩
                      ((derivedNeighborhoodCellBase R s).space ∩ P j) = {y₀, y₁}) ∧
                  ∀ i : Fin 4,
                    ∀ V ⊆ (derivedNeighborhoodCellBase R s).space \
                      (((derivedNeighborhoodCellBase R s).space ∩ P i) ∪
                        ((derivedNeighborhoodCellBase R s).space ∩ P (i + 2))),
                      IsPreconnected V →
                      (V ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 1))).Nonempty →
                      (V ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 3))).Nonempty →
                        False := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J Q C τ ρ sheet hmarked R₀ hR₀fin hR₀L
  let _ : Finite R₀.faces := hR₀fin
  choose A₀ A₁ U hA₀ hA₁ hA₀C hA₁C hAA ha₀ ha₁ hinj₀ hinj₁ hU haU hUsource hpre
    hread₀ hread₁ hreadΓ hpos₀ hpos₁ using
      (fun a : J => hD.exists_compact_source_sheets_of_markedCrossingChart
        hmarked.1 hmarked.2.1 (hmarked.2.2 a.1 a.2))
  choose O hO hOU using (fun a : J => isOpen_induced_iff.mp (hU a))
  let Γ₀ := Subtype.val '' hD.singularSet.branchCarrier c
  have hΓpoly : IsPolyhedron Γ₀ :=
    (isPLSphere_one_val_image_branchCarrier L hL D BdM hD.singularSet c hc).isPolyhedron
  have hΓR₀ : Γ₀ ⊆ R₀.space := by
    rintro x ⟨y, -, rfl⟩
    exact hR₀L.space_eq.symm ▸ y.2
  let V : Option J → Set E := Option.elim' Γ₀ᶜ O
  have hV : ∀ j, IsOpen (Subtype.val ⁻¹' V j : Set R₀.space) := by
    intro j
    cases j with
    | none => exact hΓpoly.isClosed.isOpen_compl.preimage continuous_subtype_val
    | some a => exact (hO a).preimage continuous_subtype_val
  have hcover : R₀.space ⊆ ⋃ j, V j := by
    intro x _
    by_cases hx : x ∈ Γ₀
    · obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨a, haD, b, hbD, hab, hay, hby⟩ :=
        hD.singularSet.branchCarrier_subset_doublePointSet c hy
      have haJ : a ∈ J := hmarked.1.1 ▸ (show a ∈ hD.branchPreimage c from ⟨haD, by
        change D a ∈ hD.singularSet.branchCarrier c
        rwa [hay]⟩)
      refine mem_iUnion.mpr ⟨some ⟨a, haJ⟩, ?_⟩
      change (y : E) ∈ O ⟨a, haJ⟩
      have hyU : y ∈ U ⟨a, haJ⟩ := hay ▸ haU ⟨a, haJ⟩
      rwa [← hOU ⟨a, haJ⟩] at hyU
    · exact mem_iUnion.mpr ⟨none, hx⟩
  obtain ⟨R₁, hR₁R₀, hR₁fin, hΓR₁, hstars⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover R₀ (fun _ : Unit => Γ₀)
      (fun _ => hΓpoly) (fun _ => hΓR₀) V hV hcover
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  obtain ⟨t, R, ψ, Vχ, Ω, W, P, q, hRR₁, hRfin, hΓR, hcharts, hcells⟩ :=
    exists_subdivision_branchSurface_disks L hL hD hc R₁ inferInstance (hR₁R₀.trans hR₀L)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRL : R.space = L.space := ((hRR₁.trans hR₁R₀).trans hR₀L).space_eq
  have hstarsR := hRR₁.closedStars_subset_cover hstars
  refine ⟨R, hRR₁.trans hR₁R₀, hRfin, hΓR, ?_⟩
  dsimp only
  intro s hs y₀ y₁ hpoles
  have hsR := (mem_restrict_faces_iff R Γ₀).mp hs
  have hcell : (derivedNeighborhoodCell R s).space ⊆ ⋃ v ∈ s, closedStar R v := by
    rw [derivedNeighborhoodCell_space_eq_closedStar R hsR.1]
    exact (closedStar_subset_of_isSubdivision (secondDerived_isSubdivision R) _).trans
      (closedStar_subset_biUnion_of_mem_convexHull R hsR.1
        (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hsR.1)))
  obtain ⟨j, hj⟩ := hstarsR s hsR.1
  have hcentroidCell : s.centroid ℝ id ∈ (derivedNeighborhoodCell R s).space := by
    rw [derivedNeighborhoodCell_space_eq_coneSet R hsR.1]
    exact mem_coneSet_iff.mpr (Or.inl rfl)
  cases j with
  | none =>
    exact (hj (hcell hcentroidCell)
      (hsR.2 (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hsR.1)))).elim
  | some a =>
    have hcellU : (derivedNeighborhoodCell R s).space ⊆ Subtype.val '' U a := by
      intro x hx
      have hxR : x ∈ R.space :=
        (derivedNeighborhoodCell_space_subset R s) hx
      have hxL : x ∈ L.space := hRL ▸ hxR
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [← hOU a]
      exact hj (hcell hx)
    refine ⟨a.1, a.2, A₀ a, A₁ a, U a, hA₀ a, hA₁ a, hA₀C a, hA₁C a, hAA a,
      hinj₀ a, hinj₁ a, hUsource a, hcellU, ?_, hread₀ a, hread₁ a, hreadΓ a,
      hpos₀ a, hpos₁ a, ?_⟩
    · intro x hx hxU
      exact (hpre a x hx hxU).elim (fun h => Or.inl (interior_subset h))
        (fun h => Or.inr (interior_subset h))
    · let Γ := PiecewiseLinear.restrict R Γ₀
      have hΓsp : Γ.space = Γ₀ := hΓR
      have hΓfaces : Γ.faces ⊆ R.faces := restrict_faces_subset R _
      obtain ⟨j, hstar, hcellχ⟩ := hcells s hs
      obtain ⟨-, -, -, hWΩ, hψ, hF, hΓchart, hdata⟩ := hcharts j
      have hψR : IsPLHomeomorphOn (ψ j) (Vχ j) (R.space ∩ Ω j) := hRL.symm ▸ hψ
      have hΓχ : ∀ p ∈ Vχ j, ψ j p ∈ Γ.space ↔ p.1 = 0 := by
        rw [hΓsp]
        exact hΓchart
      have hread : ∀ x ∈ R.space ∩ W j, ∀ i,
          x ∈ P j i ↔ Function.invFunOn (ψ j) (Vχ j) x ∈ crossHalfPlane i := by
        intro x hx i
        rw [hRL] at hx
        exact ((hdata i).2.2.2 x hx).1
      have hbd : ∀ x ∈ R.space ∩ W j, ∀ i,
          x ∈ q j i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space := by
        intro x hx i
        rw [hRL] at hx
        rw [hΓsp]
        exact ((hdata i).2.2.2 x hx).2
      obtain ⟨γ, hγ, hγ0, hγ1, hTT, hsep⟩ := exists_fourArcTrace_of_crossHalfPlane_disks R Γ
        hΓfaces hs hψR hWΩ hΓχ (fun i => (hdata i).1) (fun i => (hdata i).2.2.1)
        hread hbd hcellχ hpoles
      refine ⟨P j, γ, ?_, fun i => ?_, hTT, hsep⟩
      · intro x hx
        have hxW : x ∈ R.space ∩ W j :=
          ⟨derivedNeighborhoodCell_space_subset R s hx, hcellχ hx⟩
        have hxΩ : x ∈ R.space ∩ Ω j := ⟨hxW.1, hWΩ hxW.2⟩
        obtain ⟨p, hp, hpx⟩ := hψR.bijOn.surjOn hxΩ
        constructor
        · intro hxF
          obtain ⟨i, hi⟩ := exists_crossHalfPlane_of_mem_crossPlanes
            ((hF p hp).mp (hpx.symm ▸ hxF))
          refine ⟨i, (hread x hxW i).mpr ?_⟩
          rw [← hpx, hψR.bijOn.invOn_invFunOn.1 hp]
          exact hi
        · rintro ⟨i, hi⟩
          exact ((hdata i).2.1 hi).2
      · refine ⟨⟨q j i, (hdata i).1⟩, fun x hx => ((hdata i).2.1 hx).2,
          (hdata i).2.2.1, hγ i, hγ0 i, hγ1 i, fun u hu hcomp => ?_⟩
        let A := PiecewiseLinear.restrict R (P j i)
        let _ : Finite A.faces := (restrict_faces_finite R _).to_subtype
        have hAsp : A.space = P j i := (hdata i).2.2.1
        have hAbd := (hdata i).1.image_stdSimplexBoundary_eq_boundaryComplex A hAsp
        have hcommon : ∃ v, v ∈ s ∧ v ∈ u := by
          rcases hcomp with h | h
          · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hs
            exact ⟨v, hv, h hv⟩
          · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hu
            exact ⟨v, h hv, hv⟩
        obtain ⟨v, hvs, hvu⟩ := hcommon
        have hcentroidHull : u.centroid ℝ id ∈ convexHull ℝ (u : Set E) :=
          u.centroid_mem_convexHull (Γ.nonempty_of_mem_faces hu)
        have hcentroidW : u.centroid ℝ id ∈ W j :=
          hstar (mem_iUnion₂.mpr ⟨v, hvs, mem_iUnion₂.mpr
            ⟨u, ⟨hΓfaces hu, subset_convexHull ℝ _ hvu⟩, hcentroidHull⟩⟩)
        apply mem_faces_of_mem_openSimplex_of_mem_space
          ((boundaryComplex_faces_subset 2 A).trans (restrict_faces_subset R _)) (hΓfaces hu)
          (centroid_mem_openSimplex_of_mem_faces R u (hΓfaces hu))
        rw [← hAbd]
        exact (hbd _ ⟨R.convexHull_subset_space (hΓfaces hu) hcentroidHull, hcentroidW⟩ i).mpr
          (Γ.convexHull_subset_space hu hcentroidHull)

end DifferentialGeometry.Topology.PiecewiseLinear
