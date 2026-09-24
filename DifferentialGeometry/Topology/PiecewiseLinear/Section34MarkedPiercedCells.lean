import DifferentialGeometry.Topology.PiecewiseLinear.PLCellMarkerMove
import DifferentialGeometry.Topology.PiecewiseLinear.LocalFrontierCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_marked_pierced_cell_pair_of_mem_intersection {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M}
    (hp₀ : p₀ ∈ C₀ ∩ C₁) (hp₁ : p₁ ∈ C₀ ∩ C₁)
    (hp₀I : p₀ ∈ interior (C₀ ∪ C₁)) (hp₁I : p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      p₀ ∈ interior A ∧ p₀ ∉ B ∧ p₁ ∈ interior B ∧ p₁ ∉ A ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A \ B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B ∩ interior A)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B \ A)) ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ O ∧
        IsPLHomeomorphInto 3 φ₀ C₀ ∧ IsPLHomeomorphInto 3 φ₁ C₁ ∧
        φ₀ '' C₀ = A ∧ φ₁ '' C₁ = B ∧ EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  let H := G ∪ {p₀, p₁}
  have hH : IsCompact H := hG.union (isCompact_singleton.insert p₀)
  have hHC : H ⊆ interior (C₀ ∪ C₁) := by
    refine union_subset hGC ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hp₀I
    · exact (mem_singleton_iff.mp hx).symm ▸ hp₁I
  obtain ⟨A, B, hA, hB, hn, hs, hm, hl, hab, hcover, hAd, hBd,
    hmaps, hinA, houtA, hinB, houtB, hroutes⟩ :=
    exists_crossing_pierced_cell_pair_covering_compact h₀ h₁ hD hD₀ hD₁ hO hDO hH hHC
  have hp₀H : p₀ ∈ H := Or.inr (Or.inl rfl)
  have hp₁H : p₁ ∈ H := Or.inr (Or.inr rfl)
  obtain ⟨K₀, K₁, q₀, q₁, hK₀, hK₁, hc₀, hc₁, hdisj, hp₀K, hq₀K, hp₁K, hq₁K,
    hsub₀, hsub₁, hq₀B, hq₁A⟩ := hroutes p₀ ⟨hp₀H, hp₀⟩ p₁ ⟨hp₁H, hp₁⟩ hne
  obtain ⟨A', B', hA', hB', hp₀A', hp₀B', hp₁B', hp₁A', hu, hi, hf, hdA, hdB, hn',
    hlocal, hcorrection⟩ :=
    exists_marked_cell_pair_preserving_frontier_neighborhood hA hB hO hK₀ hK₁ hc₀ hc₁ hdisj
      hsub₀ hsub₁ hp₀K hq₀K hq₀B hp₁K hq₁K hq₁A
  obtain ⟨V, hV, hCV, heA, heB⟩ := hlocal
  have hcrossA := frontier_sides_of_inter_eq hA.isCompact.isClosed hA'.isCompact.isClosed
    hV hCV heA.symm heB.symm hinA houtA
  have hcrossB := frontier_sides_of_inter_eq hB.isCompact.isClosed hB'.isCompact.isClosed
    hV hCV heB.symm heA.symm hinB houtB
  refine ⟨A', B', hA', hB', hp₀A', hp₀B', hp₁B', hp₁A', hn'.mpr hn,
    hf.symm ▸ hs, hf.subset.trans hm, ?_, hu.subset.trans hab,
    (subset_union_left.trans hcover).trans hi.symm.subset, hdA.trans hAd, hdB.trans hBd,
    hf.subset.trans hcrossA.1, hf.subset.trans hcrossA.2,
    hf.subset.trans hcrossB.1, hf.subset.trans hcrossB.2, ?_⟩
  · intro x hx
    by_contra hxO
    exact hxO (hl ⟨(hdA.subset ⟨hx.1, hxO⟩).1, (hdB.subset ⟨hx.2, hxO⟩).1⟩)
  · obtain ⟨D, φ₀, φ₁, hD, hDO, hφ₀, hφ₁, he₀, he₁, hf₀, hf₁⟩ := hmaps
    obtain ⟨K, ψ₀, ψ₁, hK, hKO, hψ₀, hψ₁, hi₀, hi₁, hg₀, hg₁⟩ := hcorrection
    refine ⟨D ∪ K, φ₀.trans ψ₀.toEquiv, φ₁.trans ψ₁.toEquiv, hD.union hK,
      union_subset hDO hKO, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hψ₀.comp_isPLOn hφ₀.isPLOn).isPLHomeomorphInto h₀.isPLCellOn.isCompact
        (ψ₀.injective.comp φ₀.injective).injOn
    · exact (hψ₁.comp_isPLOn hφ₁.isPLOn).isPLHomeomorphInto h₁.isPLCellOn.isCompact
        (ψ₁.injective.comp φ₁.injective).injOn
    · change (ψ₀ ∘ φ₀) '' C₀ = A'
      rw [image_comp, he₀, hi₀]
    · change (ψ₁ ∘ φ₁) '' C₁ = B'
      rw [image_comp, he₁, hi₁]
    · intro x hx
      change ψ₀ (φ₀ x) = x
      rw [hf₀ (fun hm => hx (Or.inl hm)), id_eq, hg₀ (fun hm => hx (Or.inr hm)), id_eq]
    · intro x hx
      change ψ₁ (φ₁ x) = x
      rw [hf₁ (fun hm => hx (Or.inl hm)), id_eq, hg₁ (fun hm => hx (Or.inr hm)), id_eq]

private theorem exists_ne_mem_disk_interior {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁) (p : M) :
    ∃ q ∈ C₀ ∩ C₁, q ∈ interior (C₀ ∪ C₁) ∧ q ≠ p := by
  let P := Metric.closedBall (0 : ℝ × ℝ) 1
  have hP : IsPLBall 2 P := isPLBall_square_closedBall zero_lt_one
  obtain ⟨T, hT, -, -, hTm⟩ :=
    exists_centered_prism_piece_of_boundary_disk_pair hP h₀ h₁ hD hD₀ hD₁
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd]
  have hprism : IsPLBall 3 T.complex.space :=
    hT.symm ▸ isPLBall_three_prod hP (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1))
  have hInt : T.map '' interior T.complex.space = interior (C₀ ∪ C₁) := by
    have ht := T.image_interior_of_isPLBall hdim hprism Subset.rfl
    rwa [T.bijOn.image_eq] at ht
  have hint (b : ℝ × ℝ) (hb : b ∈ interior P) :
      T.map (b, 0) ∈ C₀ ∩ C₁ ∧ T.map (b, 0) ∈ interior (C₀ ∪ C₁) := by
    refine ⟨hTm.subset ⟨(b, 0), ⟨interior_subset hb, rfl⟩, rfl⟩, hInt.subset ?_⟩
    refine ⟨(b, 0), ?_, rfl⟩
    rw [hT, interior_prod_eq, interior_Icc]
    exact ⟨hb, by norm_num⟩
  have hzero : (0 : ℝ × ℝ) ∈ interior P := by
    rw [interior_closedBall _ one_ne_zero]
    exact Metric.mem_ball_self zero_lt_one
  have hhalf : ((1 / 2 : ℝ), (0 : ℝ)) ∈ interior P := by
    rw [interior_closedBall _ one_ne_zero, mem_ball_zero_iff]
    norm_num [Prod.norm_def]
  have hzeroT : ((0 : ℝ × ℝ), (0 : ℝ)) ∈ T.complex.space := by
    rw [hT]
    exact ⟨interior_subset hzero, by norm_num⟩
  have hhalfT : (((1 / 2 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈ T.complex.space := by
    rw [hT]
    exact ⟨interior_subset hhalf, by norm_num⟩
  by_cases hp : T.map (0, 0) = p
  · refine ⟨T.map ((1 / 2, 0), 0), (hint _ hhalf).1, (hint _ hhalf).2, ?_⟩
    intro he
    have hx := T.bijOn.injOn hzeroT hhalfT (hp.trans he.symm)
    have hx' := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.1) hx
    norm_num at hx'
  · exact ⟨T.map (0, 0), (hint _ hzero).1, (hint _ hzero).2, hp⟩

private theorem exists_pierced_cell_pair_assigning_disk_markers {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M}
    (hp₀I : p₀ ∈ C₀ ∩ C₁ → p₀ ∈ interior (C₀ ∪ C₁))
    (hp₁I : p₁ ∈ C₀ ∩ C₁ → p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      (p₀ ∈ C₀ ∩ C₁ → p₀ ∈ interior A ∧ p₀ ∉ B) ∧
      (p₁ ∈ C₀ ∩ C₁ → p₁ ∈ interior B ∧ p₁ ∉ A) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A \ B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B ∩ interior A)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B \ A)) ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ O ∧
        IsPLHomeomorphInto 3 φ₀ C₀ ∧ IsPLHomeomorphInto 3 φ₁ C₁ ∧
        φ₀ '' C₀ = A ∧ φ₁ '' C₁ = B ∧ EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  by_cases hp₀ : p₀ ∈ C₀ ∩ C₁
  · by_cases hp₁ : p₁ ∈ C₀ ∩ C₁
    · obtain ⟨A, B, hA, hB, hi₀, hn₀, hi₁, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB,
        hinA, houtA, hinB, houtB, hmaps⟩ :=
        exists_marked_pierced_cell_pair_of_mem_intersection h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
          hp₀ hp₁ (hp₀I hp₀) (hp₁I hp₁) hne
      exact ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB,
        fun _ => ⟨hi₀, hn₀⟩, fun _ => ⟨hi₁, hn₁⟩, hinA, houtA, hinB, houtB, hmaps⟩
    · obtain ⟨q, hq, hqI, hqp⟩ := exists_ne_mem_disk_interior h₀ h₁ hD hD₀ hD₁ p₀
      obtain ⟨A, B, hA, hB, hi₀, hn₀, -, -, hn, hs, hm, hl, hu, hc, hdA, hdB,
        hinA, houtA, hinB, houtB, hmaps⟩ :=
        exists_marked_pierced_cell_pair_of_mem_intersection h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
          hp₀ hq (hp₀I hp₀) hqI hqp.symm
      exact ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB,
        fun _ => ⟨hi₀, hn₀⟩, fun h => False.elim (hp₁ h), hinA, houtA, hinB, houtB, hmaps⟩
  · by_cases hp₁ : p₁ ∈ C₀ ∩ C₁
    · obtain ⟨q, hq, hqI, hqp⟩ := exists_ne_mem_disk_interior h₀ h₁ hD hD₀ hD₁ p₁
      obtain ⟨A, B, hA, hB, -, -, hi₁, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB,
        hinA, houtA, hinB, houtB, hmaps⟩ :=
        exists_marked_pierced_cell_pair_of_mem_intersection h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
          hq hp₁ hqI (hp₁I hp₁) hqp
      exact ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB,
        fun h => False.elim (hp₀ h), fun _ => ⟨hi₁, hn₁⟩, hinA, houtA, hinB, houtB, hmaps⟩
    · obtain ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB, hmaps, hinA, houtA, hinB, houtB, -⟩ :=
        exists_crossing_pierced_cell_pair_covering_compact h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
      exact ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB,
        fun h => False.elim (hp₀ h), fun h => False.elim (hp₁ h), hinA, houtA, hinB, houtB, hmaps⟩

theorem exists_crossing_pierced_cell_pair_excluding_opposite_markers
    {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M} (hp₀ : p₀ ∈ C₀) (hp₁ : p₁ ∈ C₁)
    (hp₀I : p₀ ∈ C₀ ∩ C₁ → p₀ ∈ interior (C₀ ∪ C₁))
    (hp₁I : p₁ ∈ C₀ ∩ C₁ → p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (p₀ ∈ interior (C₀ ∪ C₁) → p₀ ∈ interior A) ∧ p₀ ∉ B ∧
      (p₁ ∈ interior (C₀ ∪ C₁) → p₁ ∈ interior B) ∧ p₁ ∉ A ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A \ B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B ∩ interior A)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B \ A)) ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ O ∧
        IsPLHomeomorphInto 3 φ₀ C₀ ∧ IsPLHomeomorphInto 3 φ₁ C₁ ∧
        φ₀ '' C₀ = A ∧ φ₁ '' C₁ = B ∧ EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  let F : Set M := {p₀, p₁} \ (C₀ ∩ C₁)
  have hF : IsCompact F := ((finite_singleton p₁).insert p₀).sdiff.isCompact
  have hDF : Disjoint (C₀ ∩ C₁) F :=
    Set.disjoint_left.mpr fun _ hxD hxF => hxF.2 hxD
  obtain ⟨V, W, hV, hW, hDV, hFW, hVW⟩ := SeparatedNhds.of_isCompact_isCompact
    hD.isPolyhedralManifoldWithBoundary.isCompact hF hDF
  have hDO' : C₀ ∩ C₁ ⊆ O ∩ V := subset_inter hDO hDV
  obtain ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB, hmark₀, hmark₁,
    hinA, houtA, hinB, houtB, hmaps⟩ :=
    exists_pierced_cell_pair_assigning_disk_markers h₀ h₁ hD hD₀ hD₁ (hO.inter hV) hDO'
      hG hGC hp₀I hp₁I hne
  have hout {D C : Set M} (hd : D \ (O ∩ V) = C \ (O ∩ V)) : D \ O = C \ O := by
    ext x
    by_cases hx : x ∈ O
    · simp only [mem_sdiff, hx, not_true_eq_false, and_false]
    · have hx' : x ∉ O ∩ V := fun hx' => hx hx'.1
      simpa only [mem_sdiff, hx, hx', not_false_eq_true, and_true] using Set.ext_iff.mp hd x
  have hmem {D C : Set M} (hd : D \ (O ∩ V) = C \ (O ∩ V)) {x : M} (hx : x ∈ W) :
      x ∈ D ↔ x ∈ C := by
    have hx' : x ∉ O ∩ V := fun hx' => Set.disjoint_left.mp hVW hx'.2 hx
    simpa only [mem_sdiff, hx', not_false_eq_true, and_true] using Set.ext_iff.mp hd x
  have hint {D C : Set M} (hd : D \ (O ∩ V) = C \ (O ∩ V)) {x : M}
      (hx : x ∈ W) (hxC : x ∈ interior C) : x ∈ interior D := by
    have hsub : W ∩ interior C ⊆ D := fun y hy => (hmem hd hy.1).mpr (interior_subset hy.2)
    exact interior_maximal hsub (hW.inter isOpen_interior) ⟨hx, hxC⟩
  have hp₀AB : (p₀ ∈ interior (C₀ ∪ C₁) → p₀ ∈ interior A) ∧ p₀ ∉ B := by
    by_cases hpD : p₀ ∈ C₀ ∩ C₁
    · exact ⟨fun _ => (hmark₀ hpD).1, (hmark₀ hpD).2⟩
    · have hpW : p₀ ∈ W := hFW ⟨Or.inl rfl, hpD⟩
      have hpB : p₀ ∉ C₁ := fun hpB => hpD ⟨hp₀, hpB⟩
      refine ⟨fun hpI => ?_, fun hpB' => hpB ((hmem hdB hpW).mp hpB')⟩
      have hpC : p₀ ∈ interior C₀ := interior_union_inter_interior_compl_right_subset
        ⟨hpI, by rwa [h₁.isPLCellOn.isCompact.isClosed.isOpen_compl.interior_eq]⟩
      exact hint hdA hpW hpC
  have hp₁AB : (p₁ ∈ interior (C₀ ∪ C₁) → p₁ ∈ interior B) ∧ p₁ ∉ A := by
    by_cases hpD : p₁ ∈ C₀ ∩ C₁
    · exact ⟨fun _ => (hmark₁ hpD).1, (hmark₁ hpD).2⟩
    · have hpW : p₁ ∈ W := hFW ⟨Or.inr rfl, hpD⟩
      have hpA : p₁ ∉ C₀ := fun hpA => hpD ⟨hpA, hp₁⟩
      refine ⟨fun hpI => ?_, fun hpA' => hpA ((hmem hdA hpW).mp hpA')⟩
      have hpC : p₁ ∈ interior C₁ := interior_union_inter_interior_compl_left_subset
        ⟨hpI, by rwa [h₀.isPLCellOn.isCompact.isClosed.isOpen_compl.interior_eq]⟩
      exact hint hdB hpW hpC
  obtain ⟨D, φ₀, φ₁, hD, hDO, hφ₀, hφ₁, he₀, he₁, hf₀, hf₁⟩ := hmaps
  exact ⟨A, B, hA, hB, hp₀AB.1, hp₀AB.2, hp₁AB.1, hp₁AB.2, hn, hs, hm,
    hl.trans inter_subset_left, hu, hc, hout hdA, hout hdB, hinA, houtA, hinB, houtB,
    D, φ₀, φ₁, hD, hDO.trans inter_subset_left, hφ₀, hφ₁, he₀, he₁, hf₀, hf₁⟩

theorem exists_crossing_marked_pierced_cell_pair_covering_compact {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M} (hp₀ : p₀ ∈ C₀) (hp₁ : p₁ ∈ C₁)
    (hp₀I : p₀ ∈ interior (C₀ ∪ C₁)) (hp₁I : p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      p₀ ∈ interior A ∧ p₀ ∉ B ∧ p₁ ∈ interior B ∧ p₁ ∉ A ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A \ B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B ∩ interior A)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B \ A)) ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ O ∧
        IsPLHomeomorphInto 3 φ₀ C₀ ∧ IsPLHomeomorphInto 3 φ₁ C₁ ∧
        φ₀ '' C₀ = A ∧ φ₁ '' C₁ = B ∧ EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  obtain ⟨A, B, hA, hB, hi₀, hn₀, hi₁, hn₁, hrest⟩ :=
    exists_crossing_pierced_cell_pair_excluding_opposite_markers h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
      hp₀ hp₁ (fun _ => hp₀I) (fun _ => hp₁I) hne
  exact ⟨A, B, hA, hB, hi₀ hp₀I, hn₀, hi₁ hp₁I, hn₁, hrest⟩

theorem exists_pierced_cell_pair_excluding_opposite_markers {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M} (hp₀ : p₀ ∈ C₀) (hp₁ : p₁ ∈ C₁)
    (hp₀I : p₀ ∈ C₀ ∩ C₁ → p₀ ∈ interior (C₀ ∪ C₁))
    (hp₁I : p₁ ∈ C₀ ∩ C₁ → p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (p₀ ∈ interior (C₀ ∪ C₁) → p₀ ∈ interior A) ∧ p₀ ∉ B ∧
      (p₁ ∈ interior (C₀ ∪ C₁) → p₁ ∈ interior B) ∧ p₁ ∉ A ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ O ∧
        IsPLHomeomorphInto 3 φ₀ C₀ ∧ IsPLHomeomorphInto 3 φ₁ C₁ ∧
        φ₀ '' C₀ = A ∧ φ₁ '' C₁ = B ∧ EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  obtain ⟨A, B, hA, hB, hi₀, hn₀, hi₁, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB,
    -, -, -, -, hmaps⟩ :=
    exists_crossing_pierced_cell_pair_excluding_opposite_markers h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
      hp₀ hp₁ hp₀I hp₁I hne
  exact ⟨A, B, hA, hB, hi₀, hn₀, hi₁, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB, hmaps⟩

theorem exists_marked_pierced_cell_pair_covering_compact {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M} (hp₀ : p₀ ∈ C₀) (hp₁ : p₁ ∈ C₁)
    (hp₀I : p₀ ∈ interior (C₀ ∪ C₁)) (hp₁I : p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      p₀ ∈ interior A ∧ p₀ ∉ B ∧ p₁ ∈ interior B ∧ p₁ ∉ A ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ O ∧
        IsPLHomeomorphInto 3 φ₀ C₀ ∧ IsPLHomeomorphInto 3 φ₁ C₁ ∧
        φ₀ '' C₀ = A ∧ φ₁ '' C₁ = B ∧ EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  obtain ⟨A, B, hA, hB, hi₀, hn₀, hi₁, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB,
    -, -, -, -, hmaps⟩ :=
    exists_crossing_marked_pierced_cell_pair_covering_compact h₀ h₁ hD hD₀ hD₁ hO hDO hG hGC
      hp₀ hp₁ hp₀I hp₁I hne
  exact ⟨A, B, hA, hB, hi₀, hn₀, hi₁, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB, hmaps⟩

end DifferentialGeometry.Topology.PiecewiseLinear
