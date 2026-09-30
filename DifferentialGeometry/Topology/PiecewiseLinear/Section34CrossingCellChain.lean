import DifferentialGeometry.Topology.PiecewiseLinear.Section34CircleCellChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleMarkedCell
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
structure Section34CrossingCellChain (R Γ : Geometry.SimplicialComplex ℝ E) (A B N : Set E) where
  count : ℕ
  countGe : 2 ≤ count
  face : ℕ → Finset E
  faceMem : ∀ k, face k ∈ Γ.faces
  cellMap : ℕ → (ℝ × ℝ) × ℝ → E
  cellChart : ∀ k, IsPLHomeomorphOn (cellMap k) spliceCylinder
    (derivedNeighborhoodCell R (face k)).space
  centerValue : ∀ k, cellMap k (0, 1 / 2) = (face k).centroid ℝ id
  centerInterior : ∀ k, (face k).centroid ℝ id ∈
    interior (derivedNeighborhoodCell R (face k)).space
  cellInside : ∀ k, (derivedNeighborhoodCell R (face k)).space ⊆ N
  capMatch : ∀ k < count, cellMap k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
    cellMap (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ))
  capClose : cellMap count '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
    cellMap 0 '' (spliceSquare ×ˢ ({0} : Set ℝ))
  adjacent : ∀ k < count, (derivedNeighborhoodCell R (face k)).space ∩
    (derivedNeighborhoodCell R (face (k + 1))).space =
      cellMap k '' (spliceSquare ×ˢ ({1} : Set ℝ))
  closing : (derivedNeighborhoodCell R (face count)).space ∩
    (derivedNeighborhoodCell R (face 0)).space =
      cellMap 0 '' (spliceSquare ×ˢ ({0} : Set ℝ))
  farDisjoint : ∀ j k, j + 1 < k → k ≤ count → (j ≠ 0 ∨ k ≠ count) →
    Disjoint (derivedNeighborhoodCell R (face j)).space (derivedNeighborhoodCell R (face k)).space
  cellCover : (⋃ k ≤ count, (derivedNeighborhoodCell R (face k)).space) =
    (derivedNeighborhood R Γ).space
  coreTrace : ∀ k, cellMap k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
    (derivedNeighborhoodCell R (face k)).space ∩ Γ.space
  firstSheet : ∀ k, cellMap k ''
    ((segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ×ˢ Icc (0 : ℝ) 1) ∪
      (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 2) ×ˢ Icc (0 : ℝ) 1)) =
        (derivedNeighborhoodCell R (face k)).space ∩ A
  secondSheet : ∀ k, cellMap k ''
    ((segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) ×ˢ Icc (0 : ℝ) 1) ∪
      (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 3) ×ˢ Icc (0 : ℝ) 1)) =
        (derivedNeighborhoodCell R (face k)).space ∩ B

open Classical in
theorem exists_crossing_cell_chain_of_chart_cover [FiniteDimensional ℝ E]
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite Γ.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hdim : Module.finrank ℝ E = 3)
    (hΓ : IsPLSphere 1 Γ.space) (hΓR : Γ.faces ⊆ R.faces)
    (hΓint : Γ.space ⊆ interior R.space)
    {ι : Type*} {A B N : Set E}
    {ψ : ι → (ℝ × ℝ) × ℝ → E} {V : ι → Set ((ℝ × ℝ) × ℝ)} {Ω W : ι → Set E}
    {P : ι → Fin 4 → Set E} {q : ι → Fin 4 → (Fin 3 → ℝ) → E}
    (hcharts : ∀ j, W j ⊆ Ω j ∧ Ω j ⊆ N ∧
      IsPLHomeomorphOn (ψ j) (V j) (R.space ∩ Ω j) ∧
      (∀ p ∈ V j, (ψ j p ∈ A ↔ p.1.2 = 0) ∧ (ψ j p ∈ B ↔ p.1.1 = 0)) ∧
      (∀ p ∈ V j, ψ j p ∈ Γ.space ↔ p.1 = 0) ∧
      ∀ i, IsPLHomeomorphOn (q j i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P j i) ∧
        (PiecewiseLinear.restrict R (P j i)).space = P j i ∧
        ∀ x ∈ R.space ∩ W j,
          (x ∈ P j i ↔ Function.invFunOn (ψ j) (V j) x ∈ crossHalfPlane i) ∧
          (x ∈ q j i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space))
    (hcover : ∀ s ∈ Γ.faces, ∃ j, (⋃ v ∈ s, closedStar R v) ⊆ W j ∧
      (derivedNeighborhoodCell R s).space ⊆ W j) :
    Nonempty (Section34CrossingCellChain R Γ A B N) := by
  obtain ⟨x, hx⟩ := hΓ.nonempty
  obtain ⟨s₀, hs₀, -⟩ := Γ.mem_space_iff.mp hx
  obtain ⟨m, s, D₀, D₁, q₀, q₁, y₀, y₁, hm, -, hs, -, -, -, hq₀, hq₁,
      hD₀S, hD₁S, hdis, hcap, hcapc, hadj, hadjc, hfar, hN,
      -, -, hpoles, -, t, ht, hne, hcomp, hD₀, hD₁, hy₀, hy₁⟩ :=
    exists_interior_circle_cell_chain R Γ hR hdim hΓint hΓR
      hΓ.isCombinatorialManifold hΓ.isConnected hs₀
  have hΓbd : Disjoint Γ.space (boundaryComplex 3 R).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim R hR]
    exact disjoint_interior_frontier.mono_left hΓint
  have hsB (k : ℕ) : s k ∉ (boundaryComplex 3 R).faces := by
    intro hb
    obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces (hs k)
    exact disjoint_left.mp hΓbd (Γ.subset_space (hs k) hv)
      ((boundaryComplex 3 R).subset_space hb hv)
  choose j hstar hcell using fun k => hcover (s k) (hs k)
  have hdata (k : ℕ) : ∃ G : (ℝ × ℝ) × ℝ → E,
      IsPLHomeomorphOn G spliceCylinder (derivedNeighborhoodCell R (s k)).space ∧
      G (0, 1 / 2) = (s k).centroid ℝ id ∧
      G '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
        (derivedNeighborhoodCell R (s k)).space ∩ Γ.space ∧
      G '' (spliceSquare ×ˢ ({0} : Set ℝ)) = D₀ k ∧
      G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = D₁ k ∧
      G '' ((segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ×ˢ Icc (0 : ℝ) 1) ∪
        (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 2) ×ˢ Icc (0 : ℝ) 1)) =
          (derivedNeighborhoodCell R (s k)).space ∩ A ∧
      G '' ((segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) ×ˢ Icc (0 : ℝ) 1) ∪
        (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 3) ×ˢ Icc (0 : ℝ) 1)) =
          (derivedNeighborhoodCell R (s k)).space ∩ B := by
    obtain ⟨hWΩ, -, hψ, hsheets, haxis, hP⟩ := hcharts (j k)
    have hread := fun x hx i => ((hP i).2.2 x hx).1
    have hbd := fun x hx i => ((hP i).2.2 x hx).2
    obtain ⟨γ, hγ, hzero, hone, hTT, hsep⟩ :=
      exists_fourArcTrace_of_crossHalfPlane_disks R Γ hΓR (hs k) hψ hWΩ haxis
        (fun i => (hP i).1) (fun i => (hP i).2.1) hread hbd (hcell k) (hpoles k)
    let D : Fin 2 → Set E := ![D₀ k, D₁ k]
    let qcap : Fin 2 → (Fin 3 → ℝ) → E := ![q₀ k, q₁ k]
    let y : Fin 2 → E := ![y₀ k, y₁ k]
    obtain ⟨G, hG, hGc, -, -, hGcore, hGcap, -, -, -, hGA, hGB⟩ :=
      exists_marked_derived_crossing_cell R Γ hR hΓR (hs k) (hsB k)
        (ht k) (hne k) (hcomp k)
        (D := D) (fun l => by fin_cases l <;> simp [D, hD₀, hD₁])
        (qcap := qcap) (fun l => by
          fin_cases l
          · exact hq₀ k
          · exact hq₁ k)
        (fun l => by
          fin_cases l
          · exact hD₀S k
          · exact hD₁S k) (hdis k)
        (y := y) (fun l => by fin_cases l <;> simp [y, hy₀, hy₁])
        (fun i => (hP i).1) (fun i => (hP i).2.1) hbd (hstar k)
        hγ hzero hone (hpoles k) hTT hsep hψ hWΩ haxis hsheets hread (hcell k)
    exact ⟨G, hG, hGc, hGcore, by simpa [D] using hGcap 0,
      by simpa [D] using hGcap 1, hGA, hGB⟩
  choose G hG hGc hGcore hG0 hG1 hGA hGB using hdata
  refine ⟨{
    count := m
    countGe := hm
    face := s
    faceMem := hs
    cellMap := G
    cellChart := hG
    centerValue := hGc
    centerInterior := fun k => ?_
    cellInside := fun k => (hcell k).trans ((hcharts (j k)).1.trans (hcharts (j k)).2.1)
    capMatch := fun k hk => (hG1 k).trans ((hcap k hk).trans (hG0 (k + 1)).symm)
    capClose := (hG1 m).trans (hcapc.trans (hG0 0).symm)
    adjacent := fun k hk => (hadj k hk).trans (hG1 k).symm
    closing := hadjc.trans (hG0 0).symm
    farDisjoint := hfar
    cellCover := hN
    coreTrace := hGcore
    firstSheet := hGA
    secondSheet := hGB }⟩
  exact (hG k).image_interior_subset (by simp [hdim])
    ⟨(0, 1 / 2), tubeCellCentre_mem_interior, hGc k⟩

end DifferentialGeometry.Topology.PiecewiseLinear
