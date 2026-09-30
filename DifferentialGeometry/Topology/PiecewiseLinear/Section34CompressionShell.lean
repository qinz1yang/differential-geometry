/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionSide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_shell_of_pocket {P D J Es Eb Ys Yb Ls Lb Bs Bb As Ab Cs Cb Ts Tb : Set E3}
    {qBb : (Fin 3 → ℝ) → E3} (hP : IsPLBall 3 P) (hYs : IsPLBall 3 Ys) (hYb : IsPLBall 3 Yb)
    (hYsf : frontier Ys = D ∪ Es) (hYbf : frontier Yb = D ∪ Eb) (hPYs : P ∪ Ys = Yb)
    (hPs : Disjoint (interior P) Ys) (hE : Es ∪ Eb = frontier P) (hEsb : Es ∩ Eb = J)
    (hDP : D ∩ P = J) (hJne : J.Nonempty)
    (hLs : IsPLBall 2 Ls) (hSs : IsPLSphere 2 (Ls ∪ Bs)) (hTs : IsPLBall 3 Ts)
    (hTsf : frontier Ts = D ∪ As ∪ Ls) (hEsB : Es = Bs ∪ As) (hLBs : Ls ∩ Bs = Cs)
    (hBAs : Bs ∩ As = Cs) (hLPs : Ls ∩ P = Cs) (hBsJ : Disjoint Bs J) (hLsD : Disjoint Ls D)
    (hTPs : Ts ∩ P = As) (hsideS : Disjoint (interior P) Ys → interior Ts ⊆ interior Ys)
    (hDAb : IsPLBall 2 (D ∪ Ab)) (hSb : IsPLSphere 2 (Lb ∪ Bb)) (hTb : IsPLBall 3 Tb)
    (hTbf : frontier Tb = D ∪ Ab ∪ Lb) (hEbB : Eb = Bb ∪ Ab) (hLBb : Lb ∩ Bb = Cb)
    (hBAb : Bb ∩ Ab = Cb) (hLPb : Lb ∩ P = Cb)
    (hqBb : IsPLHomeomorphOn qBb (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Bb)
    (hqBbC : qBb '' stdSimplexBoundary 2 = Cb) (hBbJ : Disjoint Bb J) (hLbD : Disjoint Lb D)
    (hTPb : Tb ∩ P = Ab) (hsideB : interior P ⊆ Yb → Disjoint (interior Tb) Yb) :
    ∃ W X : Set E3, IsPLBall 3 W ∧ IsPLBall 3 X ∧ X ⊆ interior W ∧
      Disjoint (interior P) X ∧ W = P ∪ X ∪ Ts ∪ Tb ∧ frontier W = Lb ∪ Bb ∧
      frontier X = Ls ∪ Bs ∧ X ∪ Ts = Ys ∧ Disjoint Tb (interior Yb) := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hYsc : IsClosed Ys := hYs.isPolyhedron.isClosed
  have hYbc : IsClosed Yb := hYb.isPolyhedron.isClosed
  have hTsc : IsClosed Ts := hTs.isPolyhedron.isClosed
  have hTbc : IsClosed Tb := hTb.isPolyhedron.isClosed
  have hPreg : closure (interior P) = P := hP.closure_interior_of_finrank hdim
  have hTsreg : closure (interior Ts) = Ts := hTs.closure_interior_of_finrank hdim
  have hTbreg : closure (interior Tb) = Tb := hTb.closure_interior_of_finrank hdim
  have hEsP : Es ⊆ P := fun z hz => hPc.frontier_subset (hE ▸ Or.inl hz)
  have hEbP : Eb ⊆ P := fun z hz => hPc.frontier_subset (hE ▸ Or.inr hz)
  have hJD : J ⊆ D := fun z hz => (hDP ▸ hz : z ∈ D ∩ P).1
  have hTsYs : Ts ⊆ Ys := by
    rw [← hTsreg]
    exact closure_minimal ((hsideS hPs).trans interior_subset) hYsc
  obtain ⟨Ws, hWs, hWsf, -⟩ := hSs.exists_isPLBall_frontier_eq
  have hWsc : IsClosed Ws := hWs.isPolyhedron.isClosed
  have hLsTs : Ls ⊆ Ts := fun z hz => hTsc.frontier_subset (hTsf ▸ Or.inr hz)
  have hWsYs : Ws ⊆ Ys := by
    refine hYs.subset_of_isCompact_frontier_subset hWs.isPolyhedron.isCompact ?_
    rw [hWsf]
    refine union_subset (hLsTs.trans hTsYs) fun z hz => ?_
    exact hYsc.frontier_subset (hYsf ▸ Or.inr (hEsB ▸ Or.inl hz))
  have hnotWs : ∀ z ∈ D ∪ Es, z ∉ Ls ∪ Bs → z ∉ Ws := by
    intro z hz hzS hzW
    have hzi : z ∈ interior Ws := (mem_interior_iff_notMem_frontier hzW).mpr (hWsf ▸ hzS)
    exact (hYsf ▸ hz : z ∈ frontier Ys).2 (interior_mono hWsYs hzi)
  have hDWs : Disjoint D Ws := by
    refine Set.disjoint_left.mpr fun z hzD hzW => hnotWs z (Or.inl hzD) ?_ hzW
    rintro (hzL | hzB)
    · exact Set.disjoint_left.mp hLsD hzL hzD
    · have hzJ : z ∈ J := hDP ▸ ⟨hzD, hEsP (hEsB ▸ Or.inl hzB)⟩
      exact Set.disjoint_left.mp hBsJ hzB hzJ
  have hAsWs : As ∩ Ws ⊆ Cs := by
    rintro z ⟨hzA, hzW⟩
    by_contra hzC
    refine hnotWs z (Or.inr (hEsB ▸ Or.inr hzA)) ?_ hzW
    rintro (hzL | hzB)
    · exact hzC (hLPs ▸ ⟨hzL, hEsP (hEsB ▸ Or.inr hzA)⟩)
    · exact hzC (hBAs ▸ ⟨hzB, hzA⟩)
  obtain ⟨p, hp⟩ := hJne
  have hpWs : p ∉ Ws := fun h => Set.disjoint_left.mp hDWs (hJD hp) h
  have hintTsWs : Disjoint (interior Ts) Ws := by
    have hTconn := (hTs.isConnected_interior_of_finrank hdim).isPreconnected
    have hdisj : Disjoint (interior Ts) (frontier Ws) := by
      rw [hWsf]
      refine Set.disjoint_left.mpr fun z hzi hz => ?_
      rcases hz with hzL | hzB
      · exact (hTsf ▸ Or.inr hzL : z ∈ frontier Ts).2 hzi
      · have hzA : z ∈ As := hTPs ▸ ⟨interior_subset hzi, hEsP (hEsB ▸ Or.inl hzB)⟩
        exact (hTsf ▸ Or.inl (Or.inr hzA) : z ∈ frontier Ts).2 hzi
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hWsc hTconn hdisj with h | h
    · exfalso
      have hpc : p ∈ closure (interior Ts) := by
        rw [hTsreg]
        exact hTsc.frontier_subset (hTsf ▸ Or.inl (Or.inl (hJD hp)))
      obtain ⟨z, hz, hzi⟩ := mem_closure_iff.mp hpc Wsᶜ hWsc.isOpen_compl hpWs
      exact hz (interior_subset (h hzi))
    · exact Set.disjoint_left.mpr fun z hz hzW => h hz hzW
  have hTsWs : Ts ∩ Ws = Ls := by
    apply Subset.antisymm
    · rintro z ⟨hzT, hzW⟩
      by_cases hzi : z ∈ interior Ts
      · exact absurd hzW (Set.disjoint_left.mp hintTsWs hzi)
      · have hzf : z ∈ frontier Ts := ⟨subset_closure hzT, hzi⟩
        rw [hTsf] at hzf
        rcases hzf with (hzD | hzA) | hzL
        · exact absurd hzW (Set.disjoint_left.mp hDWs hzD)
        · exact (hLBs ▸ (hAsWs ⟨hzA, hzW⟩) : z ∈ Ls ∩ Bs).1
        · exact hzL
    · exact fun z hz => ⟨hLsTs hz, hWsc.frontier_subset (hWsf ▸ Or.inl hz)⟩
  have hWsTs : IsPLBall 3 (Ws ∪ Ts) := by
    refine isPLBall_union_of_inter_isPLBall_two hWs hTs ?_ ?_ ?_
    · rw [inter_comm, hTsWs]
      exact hLs
    · rw [inter_comm, hTsWs, hWsf]
      exact subset_union_left
    · rw [inter_comm, hTsWs, hTsf]
      exact subset_union_right
  have hYsWT : Ys = Ws ∪ Ts := by
    apply Subset.antisymm
    · refine hWsTs.subset_of_isCompact_frontier_subset hYs.isPolyhedron.isCompact ?_
      rw [hYsf, hEsB]
      rintro z (hzD | hzB | hzA)
      · exact Or.inr (hTsc.frontier_subset (hTsf ▸ Or.inl (Or.inl hzD)))
      · exact Or.inl (hWsc.frontier_subset (hWsf ▸ Or.inr hzB))
      · exact Or.inr (hTsc.frontier_subset (hTsf ▸ Or.inl (Or.inr hzA)))
    · exact union_subset hWsYs hTsYs
  have hPYb : interior P ⊆ Yb := fun z hz => hPYs ▸ Or.inl (interior_subset hz)
  have hintTb := hsideB hPYb
  have hLbTb : Lb ⊆ Tb := fun z hz => hTbc.frontier_subset (hTbf ▸ Or.inr hz)
  have hLbYb : Lb ∩ Yb ⊆ Cb := by
    rintro z ⟨hzL, hzY⟩
    by_contra hzC
    have hzP : z ∉ P := fun hzP => hzC (hLPb ▸ ⟨hzL, hzP⟩)
    have hzfr : z ∉ frontier Yb := by
      rw [hYbf]
      rintro (hzD | hzE)
      · exact Set.disjoint_left.mp hLbD hzL hzD
      · exact hzP (hEbP hzE)
    have hzi : z ∈ interior Yb := (mem_interior_iff_notMem_frontier hzY).mpr hzfr
    have hzc : z ∈ closure (interior Tb) := by
      rw [hTbreg]
      exact hLbTb hzL
    obtain ⟨w, hwY, hwT⟩ := mem_closure_iff.mp hzc _ isOpen_interior hzi
    exact Set.disjoint_left.mp hintTb hwT (interior_subset hwY)
  have hCbAb : Cb ⊆ Ab := fun z hz => (hBAb ▸ hz : z ∈ Bb ∩ Ab).2
  have hYbTb : Yb ∩ Tb = D ∪ Ab := by
    apply Subset.antisymm
    · rintro z ⟨hzY, hzT⟩
      by_cases hzi : z ∈ interior Tb
      · exact absurd hzY (Set.disjoint_left.mp hintTb hzi)
      · have hzf : z ∈ frontier Tb := ⟨subset_closure hzT, hzi⟩
        rw [hTbf] at hzf
        rcases hzf with hz | hzL
        · exact hz
        · exact Or.inr (hCbAb (hLbYb ⟨hzL, hzY⟩))
    · rintro z (hzD | hzA)
      · exact ⟨hYbc.frontier_subset (hYbf ▸ Or.inl hzD),
          hTbc.frontier_subset (hTbf ▸ Or.inl (Or.inl hzD))⟩
      · exact ⟨hYbc.frontier_subset (hYbf ▸ Or.inr (hEbB ▸ Or.inr hzA)),
          hTbc.frontier_subset (hTbf ▸ Or.inl (Or.inr hzA))⟩
  have hYT : IsPLBall 3 (Yb ∪ Tb) := by
    refine isPLBall_union_of_inter_isPLBall_two hYb hTb (hYbTb ▸ hDAb) ?_ ?_
    · rw [hYbTb, hYbf, hEbB]
      exact union_subset_union_right _ subset_union_right
    · rw [hYbTb, hTbf]
      exact subset_union_left
  obtain ⟨Wb, hWb, hWbf, -⟩ := hSb.exists_isPLBall_frontier_eq
  have hWbc : IsClosed Wb := hWb.isPolyhedron.isClosed
  have hWbsub : Wb ⊆ Yb ∪ Tb := by
    refine hYT.subset_of_isCompact_frontier_subset hWb.isPolyhedron.isCompact ?_
    rw [hWbf]
    rintro z (hzL | hzB)
    · exact Or.inr (hLbTb hzL)
    · exact Or.inl (hYbc.frontier_subset (hYbf ▸ Or.inr (hEbB ▸ Or.inl hzB)))
  have hBbTb : Bb ∩ Tb ⊆ Cb := by
    rintro z ⟨hzB, hzT⟩
    have hzA : z ∈ Ab := hTPb ▸ ⟨hzT, hEbP (hEbB ▸ Or.inl hzB)⟩
    exact hBAb ▸ ⟨hzB, hzA⟩
  have hnotint : ∀ z ∈ Bb, z ∉ Cb → z ∉ interior (Yb ∪ Tb) := by
    intro z hzB hzC hzi
    have hzT : z ∉ Tb := fun h => hzC (hBbTb ⟨hzB, h⟩)
    have hzfr : z ∈ frontier Yb := hYbf ▸ Or.inr (hEbB ▸ Or.inl hzB)
    refine hzfr.2 (mem_interior.mpr ⟨interior (Yb ∪ Tb) ∩ Tbᶜ, ?_,
      isOpen_interior.inter hTbc.isOpen_compl, hzi, hzT⟩)
    rintro w ⟨hw, hwT⟩
    rcases interior_subset hw with h | h
    · exact h
    · exact absurd h hwT
  have hCbint : ∀ z ∈ Cb, z ∉ interior (Yb ∪ Tb) := by
    intro z hzC hzi
    have hzc : z ∈ closure (Bb \ qBb '' stdSimplexBoundary 2) :=
      mem_closure_sdiff_image_stdSimplexBoundary hqBb (hqBbC ▸ hzC)
    rw [hqBbC] at hzc
    obtain ⟨w, hwi, hwB⟩ := mem_closure_iff.mp hzc _ isOpen_interior hzi
    exact hnotint w hwB.1 hwB.2 hwi
  have hdisjW : Disjoint (interior (Yb ∪ Tb)) (frontier Wb) := by
    rw [hWbf]
    refine Set.disjoint_left.mpr fun z hzi hz => ?_
    by_cases hzC : z ∈ Cb
    · exact hCbint z hzC hzi
    rcases hz with hzL | hzB
    · have hzY : z ∉ Yb := fun h => hzC (hLbYb ⟨hzL, h⟩)
      have hzfr : z ∈ frontier Tb := hTbf ▸ Or.inr hzL
      refine hzfr.2 (mem_interior.mpr ⟨interior (Yb ∪ Tb) ∩ Ybᶜ, ?_,
        isOpen_interior.inter hYbc.isOpen_compl, hzi, hzY⟩)
      rintro w ⟨hw, hwY⟩
      rcases interior_subset hw with h | h
      · exact absurd h hwY
      · exact h
    · exact hnotint z hzB hzC hzi
  have hWbeq : Wb = Yb ∪ Tb := by
    refine Subset.antisymm hWbsub (hYT.subset_of_disjoint_interior_frontier hWbc hdisjW ?_)
    obtain ⟨w, hw⟩ := hWb.interior_nonempty
    exact ⟨w, interior_mono hWbsub hw, interior_subset hw⟩
  have hYsEb : Ys ∩ Eb ⊆ J := by
    rintro z ⟨hzY, hzE⟩
    by_contra hzJ
    have hzfr : z ∉ frontier Ys := by
      rw [hYsf]
      rintro (hzD | hzEs)
      · exact hzJ (hDP ▸ ⟨hzD, hEbP hzE⟩)
      · exact hzJ (hEsb ▸ ⟨hzEs, hzE⟩)
    have hzi : z ∈ interior Ys := (mem_interior_iff_notMem_frontier hzY).mpr hzfr
    have hzc : z ∈ closure (interior P) := by
      rw [hPreg]
      exact hEbP hzE
    obtain ⟨w, hwY, hwP⟩ := mem_closure_iff.mp hzc _ isOpen_interior hzi
    exact Set.disjoint_left.mp hPs hwP (interior_subset hwY)
  have hXW : Ws ⊆ interior Wb := by
    intro z hz
    have hzYb : z ∈ Yb := hPYs ▸ Or.inr (hWsYs hz)
    have hzW : z ∈ Wb := hWbeq ▸ Or.inl hzYb
    refine (mem_interior_iff_notMem_frontier hzW).mpr ?_
    rw [hWbf]
    rintro (hzL | hzB)
    · have hzC : z ∈ Cb := hLbYb ⟨hzL, hzYb⟩
      have hzBb : z ∈ Bb := (hLBb ▸ hzC : z ∈ Lb ∩ Bb).2
      exact Set.disjoint_left.mp hBbJ hzBb (hYsEb ⟨hWsYs hz, hEbB ▸ Or.inl hzBb⟩)
    · exact Set.disjoint_left.mp hBbJ hzB (hYsEb ⟨hWsYs hz, hEbB ▸ Or.inl hzB⟩)
  have hTbYb : Disjoint Tb (interior Yb) := by
    refine Set.disjoint_left.mpr fun z hzT hzY => ?_
    by_cases hzi : z ∈ interior Tb
    · exact Set.disjoint_left.mp hintTb hzi (interior_subset hzY)
    · have hzf : z ∈ frontier Tb := ⟨subset_closure hzT, hzi⟩
      have hzfrY : z ∉ frontier Yb := fun h => h.2 hzY
      rw [hTbf] at hzf
      rcases hzf with (hzD | hzA) | hzL
      · exact hzfrY (hYbf ▸ Or.inl hzD)
      · exact hzfrY (hYbf ▸ Or.inr (hEbB ▸ Or.inr hzA))
      · have hzC := hLbYb ⟨hzL, interior_subset hzY⟩
        exact hzfrY (hYbf ▸ Or.inr (hEbB ▸ Or.inl (hLBb ▸ hzC : z ∈ Lb ∩ Bb).2))
  refine ⟨Wb, Ws, hWb, hWs, hXW, hPs.mono_right hWsYs, ?_, hWbf, hWsf, hYsWT.symm, hTbYb⟩
  rw [hWbeq, ← hPYs, hYsWT, ← union_assoc]

theorem exists_compressionShell {P V D F O : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hP : IsPLBall 3 P) (hV : IsPLBall 3 V) (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDV : D ⊆ frontier V) (hDP : D ∩ P = q '' stdSimplexBoundary 2)
    (hcross : ∀ p ∈ q '' stdSimplexBoundary 2, HasPLCrossingAt (frontier V) (frontier P) p)
    (hF : IsClosed F) (hFD : Disjoint F D) (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ (W X Ein Eout Bin Bout Ain Aout Lin Lout Tin Tout : Set E3),
      IsPLBall 3 W ∧ IsPLBall 3 X ∧ X ⊆ interior W ∧ Disjoint (interior P) X ∧
      W = P ∪ X ∪ Tin ∪ Tout ∧ frontier W = Lout ∪ Bout ∧ frontier X = Lin ∪ Bin ∧
      Ein ∪ Eout = frontier P ∧ Ein ∩ Eout = q '' stdSimplexBoundary 2 ∧
      Ein = Bin ∪ Ain ∧ Eout = Bout ∪ Aout ∧ Bin ∩ Ain ⊆ Lin ∧ Bout ∩ Aout ⊆ Lout ∧
      Disjoint Bin (q '' stdSimplexBoundary 2) ∧ Disjoint Bout (q '' stdSimplexBoundary 2) ∧
      IsClosed Ein ∧ IsClosed Eout ∧ IsClosed Ain ∧ IsClosed Aout ∧ IsClosed Lin ∧
      IsClosed Lout ∧ IsClosed Bin ∧ IsClosed Bout ∧ Ain ∪ Aout ∪ Lin ∪ Lout ∪ Tin ∪ Tout ⊆ O ∧
      (Ain ∪ Aout) ∩ (frontier V ∪ F) ⊆ q '' stdSimplexBoundary 2 ∧
      Disjoint (Lin ∪ Lout) (frontier V ∪ F) ∧ Lin ∩ P ⊆ Bin ∧ Lout ∩ P ⊆ Bout ∧
      IsPLBall 3 (X ∪ Tin) ∧ frontier (X ∪ Tin) = D ∪ Ein ∧
      ∃ (R Lr : Set E3) (g : E3 → E3), IsOpen R ∧ R ⊆ O ∧ Lr ⊆ O ∧
        Tout ⊆ R ∪ (D ∪ Aout) ∧ closure R ⊆ R ∪ (D ∪ Aout) ∪ Lr ∧ ContinuousOn g (R ∪ Lr) ∧
        (∀ y ∈ Lr, g y = y) ∧ MapsTo g R R ∧ (∀ y ∈ R, g y ∉ Tout) ∧ Disjoint R P ∧
        Disjoint R (frontier V ∪ F) ∧ (R ⊆ V ∨ Disjoint R V) ∧ Disjoint R (X ∪ Tin) ∧
        Disjoint (closure R) (interior (X ∪ Tin)) ∧
      ∃ (R' Lr' : Set E3) (g' : E3 → E3), IsOpen R' ∧ R' ⊆ O ∧ Lr' ⊆ O ∧
        Tin ⊆ R' ∪ (D ∪ Ain) ∧ closure R' ⊆ R' ∪ (D ∪ Ain) ∪ Lr' ∧ ContinuousOn g' (R' ∪ Lr') ∧
        (∀ y ∈ Lr', g' y = y) ∧ MapsTo g' R' R' ∧ (∀ y ∈ R', g' y ∉ Tin) ∧ Disjoint R' P ∧
        Disjoint R' (frontier V ∪ F) ∧ (R' ⊆ V ∨ Disjoint R' V) ∧ R' ⊆ interior (X ∪ Tin) ∧
        Disjoint Tout (interior (X ∪ Tin)) ∧ IsPLBall 3 Tout ∧ frontier Tout = D ∪ Aout ∪ Lout ∧
        Tout ∩ P = Aout ∧ Lin ⊆ Tin := by
  classical
  set J := q '' stdSimplexBoundary 2 with hJdef
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hJsph : IsPLSphere 1 J := hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hDc : IsClosed D := (IsPLBall.isPolyhedron ⟨q, hq⟩).isClosed
  have hJS : J ⊆ frontier P := by
    intro p hp
    have hpP : p ∈ P := (hDP ▸ hp : p ∈ D ∩ P).2
    refine ⟨subset_closure hpP, fun hpi => ?_⟩
    have hpc := mem_closure_sdiff_image_stdSimplexBoundary hq hp
    obtain ⟨z, hzi, hzD, hzJ⟩ := mem_closure_iff.mp hpc _ isOpen_interior hpi
    exact hzJ (hDP.subset ⟨hzD, interior_subset hzi⟩)
  obtain ⟨E₁, E₂, q₁, q₂, hq₁, hq₂, hq₁J, hq₂J, hEu, hEi⟩ :=
    exists_isPLBall_pair_of_isPLSphere_two hP.isPLSphere_frontier hJsph hJS
  have hE₁c : IsClosed E₁ := (IsPLBall.isPolyhedron ⟨q₁, hq₁⟩).isClosed
  have hE₂c : IsClosed E₂ := (IsPLBall.isPolyhedron ⟨q₂, hq₂⟩).isClosed
  obtain ⟨L₁, B₁, A₁, C₁, T₁, ε₁, hL₁, hDA₁, hS₁, hT₁, hT₁f, hE₁B, hLB₁, hBA₁, hLP₁,
    ⟨qB₁, hqB₁, hqB₁C⟩, hB₁J, hL₁D, hTP₁, hT₁O, hA₁VF, hL₁VF, -, -, -, hside₁, R₁, Lr₁, g₁,
    hR₁o, hR₁O, hLr₁O, hT₁R, hclR₁, hg₁c, hg₁Lr, hg₁R, hg₁T, hR₁P, hR₁VF, hR₁V, hR₁Y⟩ :=
    exists_compressionSide hP hV hq hDV hDP hcross hq₁ hq₁J hq₂ hq₂J hEu hEi hF hFD hO hDO
  obtain ⟨L₂, B₂, A₂, C₂, T₂, ε₂, hL₂, hDA₂, hS₂, hT₂, hT₂f, hE₂B, hLB₂, hBA₂, hLP₂,
    ⟨qB₂, hqB₂, hqB₂C⟩, hB₂J, hL₂D, hTP₂, hT₂O, hA₂VF, hL₂VF, -, -, -, hside₂, R₂, Lr₂, g₂,
    hR₂o, hR₂O, hLr₂O, hT₂R, hclR₂, hg₂c, hg₂Lr, hg₂R, hg₂T, hR₂P, hR₂VF, hR₂V, hR₂Y⟩ :=
    exists_compressionSide hP hV hq hDV hDP hcross hq₂ hq₂J hq₁ hq₁J
      (by rw [union_comm]; exact hEu) (by rw [inter_comm]; exact hEi) hF hFD hO hDO
  have hDE : ∀ (Ei : Set E3) (qi : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn qi (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ei → qi '' stdSimplexBoundary 2 = J →
      Ei ⊆ frontier P → D ∩ Ei = J := by
    intro Ei qi hqi hqiJ hEi
    apply Subset.antisymm
    · exact fun z hz => hDP ▸ ⟨hz.1, hPc.frontier_subset (hEi hz.2)⟩
    · intro z hz
      refine ⟨hJD hz, ?_⟩
      rw [← hqiJ] at hz
      exact hqi.image_eq.subset (image_mono (fun _ hx => hx.1) hz)
  have hE₁S : E₁ ⊆ frontier P := hEu ▸ subset_union_left
  have hE₂S : E₂ ⊆ frontier P := hEu ▸ subset_union_right
  have hZ₁ : IsPLSphere 2 (D ∪ E₁) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hq hq₁ (hDE E₁ q₁ hq₁ hq₁J hE₁S)
      hq₁J
  have hZ₂ : IsPLSphere 2 (D ∪ E₂) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hq hq₂ (hDE E₂ q₂ hq₂ hq₂J hE₂S)
      hq₂J
  obtain ⟨Y₁, hY₁, hY₁f, -⟩ := hZ₁.exists_isPLBall_frontier_eq
  obtain ⟨Y₂, hY₂, hY₂f, -⟩ := hZ₂.exists_isPLBall_frontier_eq
  obtain ⟨p, hp⟩ := hJsph.nonempty
  have hE₁J : (E₁ \ J).Nonempty := by
    have h := mem_closure_sdiff_image_stdSimplexBoundary hq₁ (hq₁J ▸ hp)
    rw [hq₁J] at h
    exact closure_nonempty_iff.mp ⟨p, h⟩
  have hT₁c : IsClosed T₁ := hT₁.isPolyhedron.isClosed
  have hT₂c : IsClosed T₂ := hT₂.isPolyhedron.isClosed
  have hA₁T : A₁ ⊆ T₁ := fun z hz => (hTP₁ ▸ hz : z ∈ T₁ ∩ P).1
  have hA₂T : A₂ ⊆ T₂ := fun z hz => (hTP₂ ▸ hz : z ∈ T₂ ∩ P).1
  have hL₁T : L₁ ⊆ T₁ := fun z hz => hT₁c.frontier_subset (hT₁f ▸ Or.inr hz)
  have hL₂T : L₂ ⊆ T₂ := fun z hz => hT₂c.frontier_subset (hT₂f ▸ Or.inr hz)
  have hA₁O : A₁ ⊆ O := hA₁T.trans hT₁O
  have hA₂O : A₂ ⊆ O := hA₂T.trans hT₂O
  have hL₁O : L₁ ⊆ O := hL₁T.trans hT₁O
  have hL₂O : L₂ ⊆ O := hL₂T.trans hT₂O
  have hAVF : (A₁ ∪ A₂) ∩ (frontier V ∪ F) ⊆ J := by
    rintro z ⟨hz | hz, hzVF⟩
    · exact hA₁VF ⟨hz, hzVF⟩
    · exact hA₂VF ⟨hz, hzVF⟩
  have hLVF : Disjoint (L₁ ∪ L₂) (frontier V ∪ F) := disjoint_union_left.mpr ⟨hL₁VF, hL₂VF⟩
  have hBAL₁ : B₁ ∩ A₁ ⊆ L₁ := by
    rw [hBA₁, ← hLB₁]
    exact inter_subset_left
  have hBAL₂ : B₂ ∩ A₂ ⊆ L₂ := by
    rw [hBA₂, ← hLB₂]
    exact inter_subset_left
  have hLPB₁ : L₁ ∩ P ⊆ B₁ := by
    rw [hLP₁, ← hLB₁]
    exact inter_subset_right
  have hLPB₂ : L₂ ∩ P ⊆ B₂ := by
    rw [hLP₂, ← hLB₂]
    exact inter_subset_right
  have hA₁c : IsClosed A₁ := hTP₁ ▸ hT₁c.inter hPc
  have hA₂c : IsClosed A₂ := hTP₂ ▸ hT₂c.inter hPc
  have hL₁c : IsClosed L₁ := hL₁.isPolyhedron.isClosed
  have hL₂c : IsClosed L₂ := hL₂.isPolyhedron.isClosed
  have hB₁c : IsClosed B₁ := (IsPLBall.isPolyhedron ⟨qB₁, hqB₁⟩).isClosed
  have hB₂c : IsClosed B₂ := (IsPLBall.isPolyhedron ⟨qB₂, hqB₂⟩).isClosed
  have hVside : ∀ (R : Set E3) (ε : ℝ), (∀ y ∈ R, y ∈ V ↔ ε = -1) → R ⊆ V ∨ Disjoint R V := by
    intro R ε h
    by_cases hε : ε = -1
    · exact Or.inl fun y hy => (h y hy).mpr hε
    · exact Or.inr (Set.disjoint_left.mpr fun y hy hyV => hε ((h y hy).mp hyV))
  rcases union_eq_and_disjoint_or_of_theta hP hY₁ hY₂ hEu hEi hDP hY₁f hY₂f hE₁c hE₂c hDc
    hE₁J with ⟨hPY, hPs⟩ | ⟨hPY, hPs⟩
  · obtain ⟨W, X, hW, hX, hXW, hPX, hWeq, hWf, hXf, hXT, hTbY⟩ :=
      exists_shell_of_pocket hP hY₁ hY₂ hY₁f hY₂f hPY hPs hEu hEi hDP ⟨p, hp⟩ hL₁ hS₁ hT₁
        hT₁f hE₁B hLB₁ hBA₁ hLP₁ hB₁J hL₁D hTP₁ (hside₁ Y₁ hY₁ hY₁f).1 hDA₂ hS₂ hT₂ hT₂f
        hE₂B hLB₂ hBA₂ hLP₂ hqB₂ hqB₂C hB₂J hL₂D hTP₂ (hside₂ Y₂ hY₂ hY₂f).2
    have hRY : Disjoint R₂ Y₂ :=
      (hR₂Y Y₂ hY₂ hY₂f).2 fun z hz => hPY.subset (Or.inl (interior_subset hz))
    have hR'Y : R₁ ⊆ interior (X ∪ T₁) := by
      rw [hXT]
      exact (hR₁Y Y₁ hY₁ hY₁f).1 hPs
    have hYsub : X ∪ T₁ ⊆ Y₂ := by
      rw [hXT]
      exact subset_union_right.trans hPY.subset
    have hcl : Disjoint (closure R₂) (interior (X ∪ T₁)) :=
      ((hRY.mono_right interior_subset).closure_left isOpen_interior).mono_right
        (interior_mono hYsub)
    refine ⟨W, X, E₁, E₂, B₁, B₂, A₁, A₂, L₁, L₂, T₁, T₂, hW, hX, hXW, hPX, hWeq, hWf, hXf,
      hEu, hEi, hE₁B, hE₂B, hBAL₁, hBAL₂, hB₁J, hB₂J, hE₁c, hE₂c, hA₁c, hA₂c, hL₁c, hL₂c,
      hB₁c, hB₂c,
      union_subset (union_subset (union_subset (union_subset (union_subset hA₁O hA₂O) hL₁O) hL₂O)
        hT₁O) hT₂O, hAVF, hLVF, hLPB₁, hLPB₂, by rw [hXT]; exact hY₁, by rw [hXT, hY₁f],
      R₂, Lr₂, g₂, hR₂o, hR₂O, hLr₂O, hT₂R, hclR₂, hg₂c, hg₂Lr, hg₂R, hg₂T, hR₂P, hR₂VF,
      hVside R₂ ε₂ hR₂V, hRY.mono_right hYsub, hcl, R₁, Lr₁, g₁, hR₁o, hR₁O, hLr₁O, hT₁R, hclR₁,
      hg₁c, hg₁Lr, hg₁R, hg₁T, hR₁P, hR₁VF, hVside R₁ ε₁ hR₁V, hR'Y,
      hTbY.mono_right (interior_mono hYsub), hT₂, hT₂f, hTP₂, hL₁T⟩
  · obtain ⟨W, X, hW, hX, hXW, hPX, hWeq, hWf, hXf, hXT, hTbY⟩ :=
      exists_shell_of_pocket hP hY₂ hY₁ hY₂f hY₁f hPY hPs (by rw [union_comm]; exact hEu)
        (by rw [inter_comm]; exact hEi) hDP ⟨p, hp⟩ hL₂ hS₂ hT₂ hT₂f hE₂B hLB₂ hBA₂ hLP₂
        hB₂J hL₂D hTP₂ (hside₂ Y₂ hY₂ hY₂f).1 hDA₁ hS₁ hT₁ hT₁f hE₁B hLB₁ hBA₁ hLP₁ hqB₁
        hqB₁C hB₁J hL₁D hTP₁ (hside₁ Y₁ hY₁ hY₁f).2
    have hRY : Disjoint R₁ Y₁ :=
      (hR₁Y Y₁ hY₁ hY₁f).2 fun z hz => hPY.subset (Or.inl (interior_subset hz))
    have hR'Y : R₂ ⊆ interior (X ∪ T₂) := by
      rw [hXT]
      exact (hR₂Y Y₂ hY₂ hY₂f).1 hPs
    have hYsub : X ∪ T₂ ⊆ Y₁ := by
      rw [hXT]
      exact subset_union_right.trans hPY.subset
    have hcl : Disjoint (closure R₁) (interior (X ∪ T₂)) :=
      ((hRY.mono_right interior_subset).closure_left isOpen_interior).mono_right
        (interior_mono hYsub)
    refine ⟨W, X, E₂, E₁, B₂, B₁, A₂, A₁, L₂, L₁, T₂, T₁, hW, hX, hXW, hPX, hWeq, hWf, hXf,
      by rw [union_comm]; exact hEu, by rw [inter_comm]; exact hEi, hE₂B, hE₁B, hBAL₂, hBAL₁,
      hB₂J, hB₁J, hE₂c, hE₁c, hA₂c, hA₁c, hL₂c, hL₁c, hB₂c, hB₁c,
      union_subset (union_subset (union_subset (union_subset (union_subset hA₂O hA₁O) hL₂O) hL₁O)
        hT₂O) hT₁O, ?_, ?_, hLPB₂, hLPB₁, by rw [hXT]; exact hY₂, by rw [hXT, hY₂f],
      R₁, Lr₁, g₁, hR₁o, hR₁O, hLr₁O, hT₁R, hclR₁, hg₁c, hg₁Lr, hg₁R, hg₁T, hR₁P, hR₁VF,
      hVside R₁ ε₁ hR₁V, hRY.mono_right hYsub, hcl, R₂, Lr₂, g₂, hR₂o, hR₂O, hLr₂O, hT₂R, hclR₂,
      hg₂c, hg₂Lr, hg₂R, hg₂T, hR₂P, hR₂VF, hVside R₂ ε₂ hR₂V, hR'Y,
      hTbY.mono_right (interior_mono hYsub), hT₁, hT₁f, hTP₁, hL₂T⟩
    · rw [union_comm]
      exact hAVF
    · rw [union_comm]
      exact hLVF

end DifferentialGeometry.Topology.PiecewiseLinear
