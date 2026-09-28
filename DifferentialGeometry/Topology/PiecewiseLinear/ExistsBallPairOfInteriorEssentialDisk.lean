/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_ball_pair_of_interior_essential_disk
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hT : IsPLTorus (frontier R.space))
    {D : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDR : D ⊆ R.space)
    (hmeet : D ∩ frontier R.space = r '' stdSimplexBoundary 2)
    (hess : ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ frontier R.space,
      ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
        C(r '' stdSimplexBoundary 2, frontier R.space)).Nullhomotopic) :
    ∃ (A B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (hAfin : A.faces.Finite) (hBfin : B.faces.Finite),
      letI := hAfin.to_subtype
      letI := hBfin.to_subtype
      IsPLBall 3 A.space ∧ IsPLBall 3 B.space ∧ A.space ∪ B.space = R.space ∧
      ∃ D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3)),
        IsPLBall 2 D₀ ∧ IsPLBall 2 D₁ ∧ Disjoint D₀ D₁ ∧
        D₀ ⊆ frontier A.space ∧ D₁ ⊆ frontier A.space ∧
        D₀ ⊆ frontier B.space ∧ D₁ ⊆ frontier B.space ∧
        A.space ∩ B.space = D₀ ∪ D₁ := by
  obtain ⟨K, hKfin, hK, hKR⟩ :=
    hR.exists_isCombinatorialManifold_space_eq_frontier (n := 2) (by simp)
  let _ : Finite K.faces := hKfin.to_subtype
  have hKc : IsConnected K.space := by
    rw [hKR]
    exact hT.isPathConnected.isConnected
  have hβ : Homology.bettiOne K.space ≤ 2 := by
    rw [hKR]
    exact hT.bettiOne_le_two
  rw [← hKR] at hmeet hess
  obtain ⟨hJK, hnon⟩ := hess
  obtain ⟨N, W, D₀, D₁, _, ρ, r₀, r₁, hN, -, -, hinside, -, -, -, -, hwall, -, -, -, hρ,
    hρzero, -, hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩ :=
    hK.exists_compression_neighborhood_of_spanning_disk K hKc (by simp) hr hmeet isOpen_univ
      (subset_univ D)
  have hSig := hK.isPLSphere_closure_sdiff_union_of_bettiOne_le_two K hKc (by simp) hβ
    hr.isPLSphere_image_stdSimplexBoundary hJK hρ hρzero hnon hN hwall hr₀ hr₁ hdis hfront
    hmeet₀ hmeet₁ hbd₀ hbd₁
  have hWK : W ⊆ K.space := hwall.symm.subset.trans inter_subset_left
  have hWN : W ⊆ N := hwall.symm.subset.trans inter_subset_right
  obtain ⟨_, RK, -, -, -, -, hAspace, hRKspace, -, -, hAR, -⟩ :=
    hK.exists_annulus_complement K hr.isPLSphere_image_stdSimplexBoundary
      (by norm_num : (-1 : ℝ) < 1) hρ hWK
  have hrim : W ∩ closure (K.space \ W) ⊆ D₀ ∪ D₁ := by
    rw [← hRKspace, ← hAspace, hAR]
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    rcases ht with ht | ht
    · have hmem : ρ (x, t) ∈ r₀ '' stdSimplexBoundary 2 := by
        rw [hbd₀]
        exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hmem
      rw [← hyx]
      exact Or.inl (hr₀.bijOn.mapsTo hy.1)
    · have hmem : ρ (x, t) ∈ r₁ '' stdSimplexBoundary 2 := by
        rw [hbd₁]
        exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hmem
      rw [← hyx]
      exact Or.inr (hr₁.bijOn.mapsTo hy.1)
  set P := closure (K.space \ W) ∪ D₀ ∪ D₁ with hPdef
  have hRclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hNclosed : IsClosed N := hN.isPolyhedron.isClosed
  have hKclosed : IsClosed K.space := (isPolyhedron_space K).isClosed
  have hPclosed : IsClosed P := hSig.isPolyhedron.isClosed
  have hD₀ : IsPLBall 2 D₀ := ⟨r₀, hr₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  have hKsub : K.space ⊆ R.space := by
    rw [hKR]
    exact hRclosed.frontier_subset
  have hcapsN : D₀ ∪ D₁ ⊆ frontier N := by
    rw [hfront]
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hNreg : closure (interior N) = N := hN.closure_interior_of_finrank (by simp)
  have hintN : IsConnected (interior N) := hN.isConnected_interior_of_finrank (by simp)
  have hRreg : R.space ⊆ closure (interior R.space) :=
    hR.subset_closure_interior_space (by simp)
  have hintNK : Disjoint (interior N) K.space := by
    rw [disjoint_left]
    intro y hyN hyK
    have hyF : y ∈ frontier N := by
      rw [hfront]
      exact Or.inl (Or.inl (hwall.subset ⟨hyK, interior_subset hyN⟩))
    exact hyF.2 hyN
  have hintNR : interior N ⊆ interior R.space := by
    obtain ⟨p, hpD, hpJ⟩ := hr.isConnected_sdiff_image_stdSimplexBoundary.nonempty
    have hpK : p ∉ K.space := fun h => hpJ (hmeet.subset ⟨hpD, h⟩)
    have hsub : interior N ⊆ interior R.space ∪ R.spaceᶜ := by
      intro y hy
      by_cases hyR : y ∈ R.space
      · refine Or.inl ((mem_interior_iff_notMem_frontier hyR).mpr ?_)
        rw [← hKR]
        exact disjoint_left.mp hintNK hy
      · exact Or.inr hyR
    rcases hintN.isPreconnected.subset_or_subset isOpen_interior hRclosed.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hsub with h | h
    · exact h
    · exact (h (hinside ⟨hpD, hpK⟩) (hDR hpD)).elim
  have hNR : N ⊆ R.space := by
    rw [← hNreg]
    exact closure_minimal (hintNR.trans interior_subset) hRclosed
  have hcloseN : Disjoint (closure (R.space \ N)) (interior N) := by
    rw [disjoint_left]
    intro y hy hyN
    have hy' : y ∈ closure Nᶜ := closure_mono (fun _ hz => hz.2) hy
    rw [closure_compl] at hy'
    exact hy' hyN
  have hlocal (y : EuclideanSpace ℝ (Fin 3)) (hyW : y ∈ W) (hyP : y ∉ P) :
      y ∉ closure (R.space \ N) := by
    obtain ⟨C, hC, hCP, A, B, hA, hB, hAB, -, -⟩ :=
      hK.exists_connected_neighborhood_pair_sdiff K (by simp) (hWK hyW)
        (hPclosed.isOpen_compl.mem_nhds hyP)
    have hpieceN (Q : Set (EuclideanSpace ℝ (Fin 3))) (hQ : Q ⊆ C \ K.space) :
        Disjoint Q (frontier N) := by
      rw [disjoint_left, hfront]
      rintro z hz ((hzW | hz₀) | hz₁)
      · exact (hQ hz).2 (hWK hzW)
      · exact hCP (hQ hz).1 (Or.inl (Or.inr hz₀))
      · exact hCP (hQ hz).1 (Or.inr hz₁)
    have hpieceR (Q : Set (EuclideanSpace ℝ (Fin 3))) (hQ : Q ⊆ C \ K.space) :
        Disjoint Q (frontier R.spaceᶜ) := by
      rw [frontier_compl, ← hKR, disjoint_left]
      exact fun z hz => (hQ hz).2
    have hAsub : A ⊆ C \ K.space := hAB ▸ subset_union_left
    have hBsub : B ⊆ C \ K.space := hAB ▸ subset_union_right
    have hintc : interior R.spaceᶜ = R.spaceᶜ := hRclosed.isOpen_compl.interior_eq
    obtain ⟨a, haC, haN⟩ : (C ∩ interior N).Nonempty := by
      have hyN : y ∈ closure (interior N) := by
        rw [hNreg]
        exact hWN hyW
      exact mem_closure_iff_nhds.mp hyN C hC
    obtain ⟨b, hbC, hbR⟩ : (C ∩ R.spaceᶜ).Nonempty := by
      have hyF : y ∈ frontier R.space := by
        rw [← hKR]
        exact hWK hyW
      rw [frontier_eq_closure_inter_closure] at hyF
      exact mem_closure_iff_nhds.mp hyF.2 C hC
    have hab : a ∈ A ∪ B := by
      rw [hAB]
      exact ⟨haC, disjoint_left.mp hintNK haN⟩
    have hbb : b ∈ A ∪ B := by
      rw [hAB]
      exact ⟨hbC, fun hbK => hbR (hKsub hbK)⟩
    have hbN : b ∉ interior N := fun h => hbR (hNR (interior_subset h))
    have hbR' : b ∈ interior R.spaceᶜ := by
      rw [hintc]
      exact hbR
    have hcover : A ∪ B ⊆ interior N ∪ R.spaceᶜ := by
      rcases hab with haA | haB <;> rcases hbb with hbA | hbB
      · exact (hbN (IsPreconnected.subset_interior_of_disjoint_frontier hA.isPreconnected
          (hpieceN A hAsub) ⟨a, haA, haN⟩ hbA)).elim
      · refine union_subset
          ((IsPreconnected.subset_interior_of_disjoint_frontier hA.isPreconnected
            (hpieceN A hAsub) ⟨a, haA, haN⟩).trans subset_union_left) ?_
        rw [← hintc]
        exact (IsPreconnected.subset_interior_of_disjoint_frontier hB.isPreconnected
          (hpieceR B hBsub) ⟨b, hbB, hbR'⟩).trans subset_union_right
      · refine union_subset ?_
          ((IsPreconnected.subset_interior_of_disjoint_frontier hB.isPreconnected
            (hpieceN B hBsub) ⟨a, haB, haN⟩).trans subset_union_left)
        rw [← hintc]
        exact (IsPreconnected.subset_interior_of_disjoint_frontier hA.isPreconnected
          (hpieceR A hAsub) ⟨b, hbA, hbR'⟩).trans subset_union_right
      · exact (hbN (IsPreconnected.subset_interior_of_disjoint_frontier hB.isPreconnected
          (hpieceN B hBsub) ⟨a, haB, haN⟩ hbB)).elim
    intro hycl
    obtain ⟨z, hzC, hzR, hzN⟩ := mem_closure_iff_nhds.mp hycl C hC
    by_cases hzK : z ∈ K.space
    · apply hzN (hWN _)
      by_contra hzW
      exact hCP hzC (Or.inl (Or.inl (subset_closure ⟨hzK, hzW⟩)))
    · have hz' : z ∈ A ∪ B := by
        rw [hAB]
        exact ⟨hzC, hzK⟩
      rcases hcover hz' with h | h
      · exact hzN (interior_subset h)
      · exact h hzR
  set Bs := closure (R.space \ N) ∪ D₀ ∪ D₁ with hBsdef
  have hBsR : closure (R.space \ N) ⊆ R.space := closure_minimal sdiff_subset hRclosed
  have hsdiff : Bs \ P = interior R.space \ N := by
    ext z
    constructor
    · rintro ⟨hzB, hzP⟩
      have hzcl : z ∈ closure (R.space \ N) := by
        rcases hzB with (h | h) | h
        · exact h
        · exact (hzP (Or.inl (Or.inr h))).elim
        · exact (hzP (Or.inr h)).elim
      have hzN : z ∉ N := by
        intro hzN
        have hzF : z ∈ frontier N := ⟨subset_closure hzN, disjoint_left.mp hcloseN hzcl⟩
        rw [hfront] at hzF
        rcases hzF with (h | h) | h
        · exact hlocal z h hzP hzcl
        · exact hzP (Or.inl (Or.inr h))
        · exact hzP (Or.inr h)
      have hzK : z ∉ K.space := by
        intro hzK
        apply hzN (hWN _)
        by_contra hzW
        exact hzP (Or.inl (Or.inl (subset_closure ⟨hzK, hzW⟩)))
      refine ⟨(mem_interior_iff_notMem_frontier (hBsR hzcl)).mpr ?_, hzN⟩
      rw [← hKR]
      exact hzK
    · rintro ⟨hzR, hzN⟩
      have hzK : z ∉ K.space := by
        intro hzK
        have hzF : z ∈ frontier R.space := by
          rw [← hKR]
          exact hzK
        exact hzF.2 hzR
      refine ⟨Or.inl (Or.inl (subset_closure ⟨interior_subset hzR, hzN⟩)), ?_⟩
      rintro ((h | h) | h)
      · exact hzK (closure_minimal sdiff_subset hKclosed h)
      · exact hzN (hNclosed.frontier_subset (hcapsN (Or.inl h)))
      · exact hzN (hNclosed.frontier_subset (hcapsN (Or.inr h)))
  have hPB : P ⊆ Bs := by
    rintro z ((h | h) | h)
    · refine Or.inl (Or.inl (closure_mono ?_ h))
      rintro w ⟨hwK, hwW⟩
      exact ⟨hKsub hwK, fun hwN => hwW (hwall.subset ⟨hwK, hwN⟩)⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hKW : (K.space \ W).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hconn := hSig.isConnected
    rw [hPdef, hempty, closure_empty, empty_union] at hconn
    obtain ⟨z₀, hz₀⟩ := hD₀.isConnected.nonempty
    obtain ⟨z₁, hz₁⟩ := hD₁.isConnected.nonempty
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected D₀ D₁
        hD₀.isPolyhedron.isClosed hD₁.isPolyhedron.isClosed subset_rfl
        (by rw [hdis.inter_eq, inter_empty]) with h | h
    · exact disjoint_left.mp hdis (h (Or.inr hz₁)) hz₁
    · exact disjoint_left.mp hdis hz₀ (h (Or.inl hz₀))
  have hBne : (Bs \ P).Nonempty := by
    rw [hsdiff]
    obtain ⟨w, hwK, hwW⟩ := hKW
    have hwN : w ∉ N := fun hwN => hwW (hwall.subset ⟨hwK, hwN⟩)
    obtain ⟨z, hzN, hzR⟩ := mem_closure_iff_nhds.mp (hRreg (hKsub hwK)) Nᶜ
      (hNclosed.isOpen_compl.mem_nhds hwN)
    exact ⟨z, hzR, hzN⟩
  have hBsc : IsCompact Bs :=
    (((isPolyhedron_space R).isCompact.of_isClosed_subset isClosed_closure hBsR).union
      hD₀.isPolyhedron.isCompact).union hD₁.isPolyhedron.isCompact
  have hopen : IsOpen (Bs \ P) := by
    rw [hsdiff]
    exact isOpen_interior.sdiff hNclosed
  obtain ⟨hBs, hBsfront⟩ := hSig.isPLBall_of_isOpen_sdiff hBsc hPB hopen hBne
  have hD₀N : D₀ ⊆ N := (subset_union_left.trans hcapsN).trans hNclosed.frontier_subset
  have hD₁N : D₁ ⊆ N := (subset_union_right.trans hcapsN).trans hNclosed.frontier_subset
  have hunion : N ∪ Bs = R.space := by
    apply Subset.antisymm
    · exact union_subset hNR
        (union_subset (union_subset hBsR (hD₀N.trans hNR)) (hD₁N.trans hNR))
    · intro z hz
      by_cases hzN : z ∈ N
      · exact Or.inl hzN
      · exact Or.inr (Or.inl (Or.inl (subset_closure ⟨hz, hzN⟩)))
  have hinter : N ∩ Bs = D₀ ∪ D₁ := by
    apply Subset.antisymm
    · rintro z ⟨hzN, (hzcl | hz₀) | hz₁⟩
      · have hzF : z ∈ frontier N := ⟨subset_closure hzN, disjoint_left.mp hcloseN hzcl⟩
        rw [hfront] at hzF
        rcases hzF with (hzW | hz₀) | hz₁
        · by_cases hzP : z ∈ P
          · rcases hzP with (h | h) | h
            · exact hrim ⟨hzW, h⟩
            · exact Or.inl h
            · exact Or.inr h
          · exact (hlocal z hzW hzP hzcl).elim
        · exact Or.inl hz₀
        · exact Or.inr hz₁
      · exact Or.inl hz₀
      · exact Or.inr hz₁
    · rintro z (hz | hz)
      · exact ⟨hD₀N hz, Or.inl (Or.inr hz)⟩
      · exact ⟨hD₁N hz, Or.inr hz⟩
  obtain ⟨A, hAfin, hAspace⟩ := hN.isPolyhedron.exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ := hBs.isPolyhedron.exists_simplicialComplex
  refine ⟨A, B, hAfin, hBfin, ?_⟩
  rw [hAspace, hBspace, hBsfront]
  exact ⟨hN, hBs, hunion, D₀, D₁, hD₀, hD₁, hdis, subset_union_left.trans hcapsN,
    subset_union_right.trans hcapsN, fun _ h => Or.inl (Or.inr h), fun _ h => Or.inr h, hinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
