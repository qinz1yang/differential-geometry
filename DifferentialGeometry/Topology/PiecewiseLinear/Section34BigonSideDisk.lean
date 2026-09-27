import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrosscutExitSides
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem IsPLHomeomorphOn.image_Ioo_subset_interior_of_boundary_inter
    {γ : ℝ → E2} {J N : Set E2} (hγ : IsPLHomeomorphOn γ (Icc 0 1) J)
    (hJN : J ⊆ N) (hends : J ∩ frontier N = {γ 0, γ 1}) :
    γ '' Ioo 0 1 ⊆ interior N := by
  rintro _ ⟨s, hs, rfl⟩
  have hsJ := hγ.bijOn.mapsTo ⟨hs.1.le, hs.2.le⟩
  apply (mem_interior_iff_notMem_frontier (hJN hsJ)).mpr
  intro hsN
  rcases hends.subset ⟨hsJ, hsN⟩ with h | h
  · have := hγ.bijOn.injOn ⟨hs.1.le, hs.2.le⟩ (by norm_num : (0 : ℝ) ∈ Icc 0 1) h
    exact hs.1.ne' this
  · have := hγ.bijOn.injOn ⟨hs.1.le, hs.2.le⟩ (by norm_num : (1 : ℝ) ∈ Icc 0 1) h
    exact hs.2.ne this

theorem exists_bigon_side_disk_of_two_crossing_charts
    {N J L : Set E2} (hN : IsPLBall 2 N) {γ δ : ℝ → E2}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (t : Fin 2 → ℝ) (h₀ : 0 < t 0) (h₀₁ : t 0 < t 1) (h₁ : t 1 < 1)
    (htrace : J ∩ L = {γ (t 0), γ (t 1)})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) E2) (ε : Fin 2 → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = γ (t i))
    (hcurve : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i p ∈ L ↔ p.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J) :
    ∃ A : Set E2, IsPLBall 2 A ∧ A ⊆ N ∧
      A ∩ (L ∪ frontier N) ⊆ frontier A ∧
      γ 0 ∈ frontier A ∧ γ 1 ∈ frontier A ∧ γ 0 ∉ L ∧ γ 1 ∉ L := by
  have hJint := hγ.image_Ioo_subset_interior_of_boundary_inter hJN hJends
  have hLint := hδ.image_Ioo_subset_interior_of_boundary_inter hLN hLends
  have hLball : IsPLBall 1 L :=
    (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ
  have hcut := hδ.isCrosscut_of_image_Ioo_subset_interior hN
    (hLends.symm.subset (by simp)).2 (hLends.symm.subset (by simp)).2 hLint
  obtain ⟨A, B, hA, hB, hAB, -, hFA, -, hLA, hLB, -, -, -⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut hN hLball hcut
  have hAN : A ⊆ N := subset_union_left.trans hAB.subset
  have hBN : B ⊆ N := subset_union_right.trans hAB.subset
  have ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact ⟨h₀, h₀₁.trans h₁⟩
    · exact ⟨h₀.trans h₀₁, h₁⟩
  have hsmall : ∀ i, ∃ η : ℝ, 0 < η ∧ η ≤ ε i ∧
      e i '' (Ioo (-η) η ×ˢ Ioo (-η) η) ⊆ interior N := by
    intro i
    have hzero : (0 : ℝ) ∈ Ioo (-ε i) (ε i) := ⟨neg_neg_of_pos (hε i), hε i⟩
    have he : ContinuousAt (e i) (0, 0) :=
      (e i).continuousOn.continuousAt
        ((e i).open_source.mem_nhds (hsource i ⟨hzero, hzero⟩))
    have hp : e i (0, 0) ∈ interior N :=
      (hcenter i).symm ▸ hJint ⟨t i, ht i, rfl⟩
    obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.mp
      (he.preimage_mem_nhds (isOpen_interior.mem_nhds hp))
    refine ⟨min (ε i) ρ, lt_min (hε i) hρ, min_le_left _ _, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    apply hρN
    have hle := min_le_right (ε i) ρ
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith [hp.1.1], lt_of_lt_of_le hp.1.2 hle⟩,
      ⟨by linarith [hp.2.1], lt_of_lt_of_le hp.2.2 hle⟩⟩
  choose η hη hηε hηN using hsmall
  have hbox (i : Fin 2) : Ioo (-η i) (η i) ⊆ Ioo (-ε i) (ε i) := by
    intro s hs
    exact ⟨lt_of_le_of_lt (neg_le_neg (hηε i)) hs.1, lt_of_lt_of_le hs.2 (hηε i)⟩
  have hfront : ∀ i, ∀ p ∈ Ioo (-η i) (η i) ×ˢ Ioo (-η i) (η i),
      e i p ∈ frontier A ↔ p.2 = 0 := by
    intro i p hp
    have hpN := hηN i ⟨p, hp, rfl⟩
    rw [← hcurve i p ⟨hbox i hp.1, hbox i hp.2⟩]
    refine ⟨fun hx => ?_, fun hx => hLA hx⟩
    exact (hFA hx).resolve_left fun hxN => hxN.2 hpN
  have hsidecover : interior A ∪ Aᶜ = (frontier A)ᶜ := by
    rw [compl_frontier_eq_union_interior, hA.isPolyhedron.isClosed.isOpen_compl.interior_eq]
  have hfrontint : frontier (interior A) = frontier A := by
    rw [frontier, hA.closure_interior, interior_interior, frontier,
      hA.isPolyhedron.isClosed.closure_eq]
  have hparam : ∀ s ∈ Ioo (0 : ℝ) 1, γ s ∈ frontier A → s = t 0 ∨ s = t 1 := by
    intro s hs hsA
    have hsL : γ s ∈ L :=
      (hFA hsA).resolve_left fun hsN => hsN.2 (hJint ⟨s, hs, rfl⟩)
    rcases htrace.subset ⟨hγ.bijOn.mapsTo ⟨hs.1.le, hs.2.le⟩, hsL⟩ with h | h
    · exact Or.inl (hγ.bijOn.injOn ⟨hs.1.le, hs.2.le⟩ ⟨(ht 0).1.le, (ht 0).2.le⟩ h)
    · exact Or.inr (hγ.bijOn.injOn ⟨hs.1.le, hs.2.le⟩ ⟨(ht 1).1.le, (ht 1).2.le⟩ h)
  have hsides := hγ.same_side_endpoints_of_two_crossing_charts isOpen_interior
    hA.isPolyhedron.isClosed.isOpen_compl
    (disjoint_left.mpr fun _ hi hc => hc (interior_subset hi))
    hsidecover hfrontint (frontier_compl A) t h₀ h₀₁ h₁ hparam e η hη
    (fun i p hp => hsource i ⟨hbox i hp.1, hbox i hp.2⟩) hcenter hfront
    (fun i s hs => haxis i s (hbox i hs))
  have hendsN : γ 0 ∈ frontier N ∧ γ 1 ∈ frontier N :=
    ⟨(hJends.symm.subset (by simp)).2, (hJends.symm.subset (by simp)).2⟩
  have hendsL : γ 0 ∉ L ∧ γ 1 ∉ L := by
    constructor
    · intro h
      rcases htrace.subset ⟨hγ.bijOn.mapsTo (by norm_num), h⟩ with he | he
      · exact h₀.ne' (hγ.bijOn.injOn (by norm_num) ⟨(ht 0).1.le, (ht 0).2.le⟩ he).symm
      · exact (ht 1).1.ne'
          (hγ.bijOn.injOn (by norm_num) ⟨(ht 1).1.le, (ht 1).2.le⟩ he).symm
    · intro h
      rcases htrace.subset ⟨hγ.bijOn.mapsTo (by norm_num), h⟩ with he | he
      · exact (ht 0).2.ne
          (hγ.bijOn.injOn (by norm_num) ⟨(ht 0).1.le, (ht 0).2.le⟩ he).symm
      · exact h₁.ne (hγ.bijOn.injOn (by norm_num) ⟨(ht 1).1.le, (ht 1).2.le⟩ he).symm
  have hboundary (P : Set E2) (hPN : P ⊆ N) : P ∩ frontier N ⊆ frontier P := by
    intro x hx
    exact ⟨subset_closure hx.1, fun hi => hx.2.2 (interior_mono hPN hi)⟩
  have hfinish (P : Set E2) (hP : IsPLBall 2 P) (hPN : P ⊆ N)
      (hLP : L ⊆ frontier P) (h₀P : γ 0 ∈ P) (h₁P : γ 1 ∈ P) :
      ∃ P : Set E2, IsPLBall 2 P ∧ P ⊆ N ∧
        P ∩ (L ∪ frontier N) ⊆ frontier P ∧
        γ 0 ∈ frontier P ∧ γ 1 ∈ frontier P ∧ γ 0 ∉ L ∧ γ 1 ∉ L := by
    refine ⟨P, hP, hPN, ?_, hboundary P hPN ⟨h₀P, hendsN.1⟩,
      hboundary P hPN ⟨h₁P, hendsN.2⟩, hendsL⟩
    rintro x ⟨hxP, hxL | hxN⟩
    · exact hLP hxL
    · exact hboundary P hPN ⟨hxP, hxN⟩
  rcases hsides with hsides | hsides
  · exact hfinish A hA hAN hLA (hA.closure_interior ▸ hsides.1)
      (hA.closure_interior ▸ hsides.2.1)
  · have htoB : N ∩ Aᶜ ⊆ B := fun x hx => (hAB.superset hx.1).resolve_left hx.2
    have h₀B : γ '' Ioo 0 (t 0) ⊆ B := by
      rintro x ⟨s, hs, rfl⟩
      exact htoB ⟨hJN (hγ.bijOn.mapsTo ⟨hs.1.le, by linarith [hs.2]⟩),
        hsides.2.2.1 ⟨s, hs, rfl⟩⟩
    have h₁B : γ '' Ioo (t 1) 1 ⊆ B := by
      rintro x ⟨s, hs, rfl⟩
      exact htoB ⟨hJN (hγ.bijOn.mapsTo ⟨by linarith [hs.1], hs.2.le⟩),
        hsides.2.2.2 ⟨s, hs, rfl⟩⟩
    have h₀cl : γ 0 ∈ closure (γ '' Ioo 0 (t 0)) := by
      have hsub : Ioo 0 (t 0) ⊆ Icc (0 : ℝ) 1 := by
        intro s hs
        exact ⟨hs.1.le, by linarith [hs.2]⟩
      apply ((hγ.isPiecewiseAffineOn.continuousOn 0 (by norm_num)).mono hsub).mem_closure_image
      rw [closure_Ioo h₀.ne]
      exact ⟨le_rfl, h₀.le⟩
    have h₁cl : γ 1 ∈ closure (γ '' Ioo (t 1) 1) := by
      have hsub : Ioo (t 1) 1 ⊆ Icc (0 : ℝ) 1 := by
        intro s hs
        exact ⟨by linarith [hs.1], hs.2.le⟩
      apply ((hγ.isPiecewiseAffineOn.continuousOn 1 (by norm_num)).mono hsub).mem_closure_image
      rw [closure_Ioo h₁.ne]
      exact ⟨h₁.le, le_rfl⟩
    exact hfinish B hB hBN hLB
      (closure_minimal h₀B hB.isPolyhedron.isClosed h₀cl)
      (closure_minimal h₁B hB.isPolyhedron.isClosed h₁cl)

end DifferentialGeometry.Topology.PiecewiseLinear
