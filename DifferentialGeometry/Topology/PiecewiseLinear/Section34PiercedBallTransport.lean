import DifferentialGeometry.Topology.PiecewiseLinear.CenteredPrismBallPair
import DifferentialGeometry.Topology.PiecewiseLinear.PLPieceBallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnPolyhedralBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallModel
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapSource

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_pierced_cell_pair_in_prism {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O : Set M} (T : PLPieceIn ((ℝ × ℝ) × ℝ) 3 M (C₀ ∪ C₁))
    (hT : T.complex.space = Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
    (hT₀ : T.map '' (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) = C₀)
    (hT₁ : T.map '' (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = C₁)
    (hTm : T.map '' (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ {(0 : ℝ)}) = C₀ ∩ C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKP : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1)) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      T.map '' (K ×ˢ Ioo (-1 : ℝ) 1) ⊆ interior A ∪ interior B ∧
      A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      ∀ p₀ ∈ T.map '' (K ×ˢ {(0 : ℝ)}), ∀ p₁ ∈ T.map '' (K ×ˢ {(0 : ℝ)}), p₀ ≠ p₁ →
        ∃ (L₀ L₁ : Set M) (q₀ q₁ : M), IsCompact L₀ ∧ IsCompact L₁ ∧
          IsConnected L₀ ∧ IsConnected L₁ ∧ Disjoint L₀ L₁ ∧
          p₀ ∈ L₀ ∧ q₀ ∈ L₀ ∧ p₁ ∈ L₁ ∧ q₁ ∈ L₁ ∧
          L₀ ⊆ interior A ∩ O ∧ L₁ ⊆ interior B ∩ O ∧ q₀ ∉ B ∧ q₁ ∉ A := by
  let P := Metric.closedBall (0 : ℝ × ℝ) 1
  have hP : IsPLBall 2 P := isPLBall_square_closedBall zero_lt_one
  have hcont : ContinuousOn T.map (P ×ˢ Icc (-1 : ℝ) 1) := hT ▸ T.continuousOn
  obtain ⟨a, ha, ha1, hslab⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact
    hP.isPolyhedron.isCompact hcont hO (fun x hx => hDO (hTm.subset ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩))
  obtain ⟨A, B, -, -, hA, hB, -, -, -, -, hnonempty, hcircle, hmid, hlens,
    hAB, hcover, hAeq, hBeq, hroutes⟩ := exists_pierced_square_ball_pair hK hKP ha ha1
  have hAT : A ⊆ T.complex.space :=
    subset_union_left.trans (hAB.trans hT.symm.subset)
  have hBT : B ⊆ T.complex.space :=
    subset_union_right.trans (hAB.trans hT.symm.subset)
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd]
  have hAf := T.frontier_image_of_isPLBall hdim hA hAT
  have hBf := T.frontier_image_of_isPLBall hdim hB hBT
  have hAi := T.image_interior_of_isPLBall hdim hA hAT
  have hBi := T.image_interior_of_isPLBall hdim hB hBT
  have hfrontAT : frontier A ⊆ T.complex.space :=
    hA.isPolyhedron.isClosed.frontier_subset.trans hAT
  have hfrontBT : frontier B ⊆ T.complex.space :=
    hB.isPolyhedron.isClosed.frontier_subset.trans hBT
  have hfront : frontier (T.map '' A) ∩ frontier (T.map '' B) =
      T.map '' (frontier A ∩ frontier B) :=
    (congrArg₂ (· ∩ ·) hAf hBf).trans (T.bijOn.injOn.image_inter hfrontAT hfrontBT).symm
  have hsphere : IsPolyhedralSphere (n := 3) 1 (T.map '' (frontier A ∩ frontier B)) := by
    obtain ⟨S, hS, -⟩ := T.exists_restrict_of_isPolyhedron hcircle.isPolyhedron
      (inter_subset_left.trans hfrontAT)
    exact isPolyhedralSphere_of_pieceIn S (hS.symm ▸ hcircle)
  have houtside {D E : Set ((ℝ × ℝ) × ℝ)} (hD : D ⊆ T.complex.space)
      (heq : D \ (univ ×ˢ Ioo (-a) a) = E \ (univ ×ˢ Ioo (-a) a)) :
      T.map '' D \ O ⊆ T.map '' E \ O := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hn : x ∉ univ ×ˢ Ioo (-a) a := by
      intro ht
      exact hy (hslab x.1 (hT.subset (hD hx)).1 x.2 ⟨ht.2.1.le, ht.2.2.le⟩)
    exact ⟨⟨x, (heq.subset ⟨hx, hn⟩).1, rfl⟩, hy⟩
  have hlow : P ×ˢ Icc (-1 : ℝ) 0 ⊆ T.complex.space := by
    rw [hT]
    exact prod_mono Subset.rfl (Icc_subset_Icc le_rfl zero_le_one)
  have hupp : P ×ˢ Icc (0 : ℝ) 1 ⊆ T.complex.space := by
    rw [hT]
    exact prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)
  refine ⟨T.map '' A, T.map '' B, (T.isPolyhedralBall_image hA hAT).isPLCellOn,
    (T.isPolyhedralBall_image hB hBT).isPLCellOn, ?_, hfront.symm ▸ hsphere,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hxA, hxB⟩ := hnonempty
    exact ⟨T.map x, hAi.subset ⟨x, hxA, rfl⟩, hBi.subset ⟨x, hxB, rfl⟩⟩
  · exact hfront.subset.trans ((image_mono hmid).trans hTm.subset)
  · rw [← T.bijOn.injOn.image_inter hAT hBT]
    rintro y ⟨x, hx, rfl⟩
    have hs := hlens hx
    exact hslab x.1 (interior_subset hs.1) x.2 ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
  · exact union_subset (image_subset_iff.mpr fun _ hx => T.bijOn.mapsTo (hAT hx))
      (image_subset_iff.mpr fun _ hx => T.bijOn.mapsTo (hBT hx))
  · simpa only [image_union, hAi, hBi] using image_mono (f := T.map) hcover
  · exact (Subset.antisymm (houtside hAT hAeq) (houtside hlow hAeq.symm)).trans
      (congrArg (fun S => S \ O) hT₀)
  · exact (Subset.antisymm (houtside hBT hBeq) (houtside hupp hBeq.symm)).trans
      (congrArg (fun S => S \ O) hT₁)
  · rintro p₀ ⟨x₀, hx₀, rfl⟩ p₁ ⟨x₁, hx₁, rfl⟩ hne
    obtain ⟨L₀, L₁, q₀, q₁, hL₀, hL₁, hc₀, hc₁, hd, hp₀, hq₀, hp₁, hq₁,
      hsub₀, hsub₁, hq₀B, hq₁A⟩ := hroutes x₀ hx₀ x₁ hx₁
        (fun he => hne (congrArg T.map he))
    have hLT₀ : L₀ ⊆ T.complex.space :=
      fun x hx => hAT (interior_subset (hsub₀ hx).1)
    have hLT₁ : L₁ ⊆ T.complex.space :=
      fun x hx => hBT (interior_subset (hsub₁ hx).1)
    have hLc₀ := T.continuousOn.mono hLT₀
    have hLc₁ := T.continuousOn.mono hLT₁
    refine ⟨T.map '' L₀, T.map '' L₁, T.map q₀, T.map q₁,
      hL₀.image_of_continuousOn hLc₀, hL₁.image_of_continuousOn hLc₁,
      hc₀.image T.map hLc₀, hc₁.image T.map hLc₁, hd.image T.bijOn.injOn hLT₀ hLT₁,
      ⟨x₀, hp₀, rfl⟩, ⟨q₀, hq₀, rfl⟩, ⟨x₁, hp₁, rfl⟩, ⟨q₁, hq₁, rfl⟩,
      ?_, ?_, ?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      have hs := hsub₀ hx
      exact ⟨hAi.subset ⟨x, hs.1, rfl⟩,
        hslab x.1 (hT.subset (hLT₀ hx)).1 x.2 ⟨hs.2.2.1.le, hs.2.2.2.le⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      have hs := hsub₁ hx
      exact ⟨hBi.subset ⟨x, hs.1, rfl⟩,
        hslab x.1 (hT.subset (hLT₁ hx)).1 x.2 ⟨hs.2.2.1.le, hs.2.2.2.le⟩⟩
    · rintro ⟨x, hx, he⟩
      exact hq₀B ((T.bijOn.injOn (hBT hx) (hLT₀ hq₀) he) ▸ hx)
    · rintro ⟨x, hx, he⟩
      exact hq₁A ((T.bijOn.injOn (hAT hx) (hLT₁ hq₁) he) ▸ hx)

theorem exists_pierced_cell_pair_covering_compact {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      ∀ p₀ ∈ G ∩ (C₀ ∩ C₁), ∀ p₁ ∈ G ∩ (C₀ ∩ C₁), p₀ ≠ p₁ →
        ∃ (L₀ L₁ : Set M) (q₀ q₁ : M), IsCompact L₀ ∧ IsCompact L₁ ∧
          IsConnected L₀ ∧ IsConnected L₁ ∧ Disjoint L₀ L₁ ∧
          p₀ ∈ L₀ ∧ q₀ ∈ L₀ ∧ p₁ ∈ L₁ ∧ q₁ ∈ L₁ ∧
          L₀ ⊆ interior A ∩ O ∧ L₁ ⊆ interior B ∩ O ∧ q₀ ∉ B ∧ q₁ ∉ A := by
  let P := Metric.closedBall (0 : ℝ × ℝ) 1
  have hP : IsPLBall 2 P := isPLBall_square_closedBall zero_lt_one
  obtain ⟨T, hT, hT₀, hT₁, hTm⟩ :=
    exists_centered_prism_piece_of_boundary_disk_pair hP h₀ h₁ hD hD₀ hD₁
  let L := T.complex.space ∩ T.map ⁻¹' G
  have hL : IsCompact L := T.isPolyhedron_space.isCompact.of_isClosed_subset
    (T.continuousOn.preimage_isClosed_of_isClosed T.isPolyhedron_space.isClosed hG.isClosed)
    inter_subset_left
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd]
  have hprism : IsPLBall 3 T.complex.space :=
    hT.symm ▸ isPLBall_three_prod hP (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1))
  have hInt : T.map '' interior T.complex.space = interior (C₀ ∪ C₁) := by
    have ht := T.image_interior_of_isPLBall hdim hprism Subset.rfl
    rwa [T.bijOn.image_eq] at ht
  have hLI : ∀ x ∈ L, x.1 ∈ interior P ∧ x.2 ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hInt.symm.subset (hGC hx.2)
    have heq := T.bijOn.injOn (interior_subset hy) hx.1 hyx
    have hxI : x ∈ interior T.complex.space := heq ▸ hy
    rwa [hT, interior_prod_eq, interior_Icc] at hxI
  let K := Prod.fst '' L
  have hK : IsCompact K := hL.image continuous_fst
  have hKP : K ⊆ interior P := by
    rintro x ⟨z, hz, rfl⟩
    exact (hLI z hz).1
  obtain ⟨A, B, hA, hB, hnonempty, hcircle, hmid, hlens, hAB, hcover, hAeq, hBeq, hroutes⟩ :=
    exists_pierced_cell_pair_in_prism T hT hT₀ hT₁ hTm hO hDO hK hKP
  refine ⟨A, B, hA, hB, hnonempty, hcircle, hmid, hlens, hAB, ?_, hAeq, hBeq, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (interior_subset (hGC hy))
    have hxL : x ∈ L := ⟨hx, hy⟩
    exact hcover ⟨x, ⟨⟨x, hxL, rfl⟩, (hLI x hxL).2⟩, rfl⟩
  · have hmidK : G ∩ (C₀ ∩ C₁) ⊆ T.map '' (K ×ˢ {(0 : ℝ)}) := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := hTm.symm.subset hp.2
      have hxT : x ∈ T.complex.space := by
        rw [hT]
        exact ⟨hx.1, by have ht : x.2 = 0 := hx.2; rw [ht]; norm_num⟩
      exact ⟨x, ⟨⟨x, ⟨hxT, hp.1⟩, rfl⟩, hx.2⟩, rfl⟩
    exact fun p₀ hp₀ p₁ hp₁ hne => hroutes p₀ (hmidK hp₀) p₁ (hmidK hp₁) hne

end DifferentialGeometry.Topology.PiecewiseLinear
