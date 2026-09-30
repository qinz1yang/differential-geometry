/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallLocalSide
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskFamilyGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCircleCapSplit
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Arc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLSphere.closure_sdiff_closure_sdiff_of_Icc {S β : Set F} (hS : IsPLSphere 1 S)
    {γ : ℝ → F} (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) (hβS : β ⊆ S) :
    closure (S \ closure (S \ β)) = β := by
  obtain ⟨δ, hδ, hδ0, hδ1, hmeet, hunion⟩ := hS.exists_isPLHomeomorphOn_closure_sdiff hγ hβS
  have hβc : IsClosed β :=
    ((isPLBall_Icc (zero_lt_one' ℝ)).of_isPLHomeomorphOn hγ).isPolyhedron.isClosed
  have hSc : IsClosed S := hS.isPolyhedron.isClosed
  have hβ'S : closure (S \ β) ⊆ S := closure_minimal sdiff_subset hSc
  obtain ⟨-, -, -, -, hmeet', -⟩ := hS.exists_isPLHomeomorphOn_closure_sdiff hδ hβ'S
  apply Subset.antisymm
  · refine closure_minimal (fun x hx => ?_) hβc
    have hxS : x ∈ β ∪ closure (S \ β) := by
      rw [hunion]
      exact hx.1
    rcases hxS with h | h
    · exact h
    · exact absurd h hx.2
  · intro x hx
    by_cases hx' : x ∈ closure (S \ β)
    · have hxe : x ∈ ({δ 0, δ 1} : Set F) := by
        rw [hδ0, hδ1, ← hmeet]
        exact ⟨hx, hx'⟩
      rw [← hmeet'] at hxe
      exact hxe.2
    · exact subset_closure ⟨hβS hx, hx'⟩

theorem exists_complementary_arcs_of_or {S β A B : Set F} (hS : IsPLSphere 1 S) {γ : ℝ → F}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) (hβS : β ⊆ S)
    (h : (A = β ∧ B = closure (S \ β)) ∨ (A = closure (S \ β) ∧ B = β)) :
    ∃ a : ℝ → F, IsPLHomeomorphOn a (Icc 0 1) A ∧ A ∩ B = {a 0, a 1} ∧ A ∪ B = S ∧
      closure (S \ A) = B := by
  obtain ⟨δ, hδ, hδ0, hδ1, hmeet, hunion⟩ := hS.exists_isPLHomeomorphOn_closure_sdiff hγ hβS
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨γ, hγ, hmeet, hunion, rfl⟩
  · refine ⟨δ, hδ, ?_, ?_, hS.closure_sdiff_closure_sdiff_of_Icc hγ hβS⟩
    · rw [inter_comm, hmeet, hδ0, hδ1]
    · rw [union_comm, hunion]

end Arc

theorem IsPLBall.exists_pocket_of_inter_eq_boundary {B Z : Set E3} (hB : IsPLBall 3 B)
    {qZ : (Fin 3 → ℝ) → E3} (hqZ : IsPLHomeomorphOn qZ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Z)
    (hZB : Z ∩ B = qZ '' stdSimplexBoundary 2) (hZf : qZ '' stdSimplexBoundary 2 ⊆ frontier B) :
    ∃ (Ωp Ωq Yp : Set E3) (qp qq : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn qp (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ωp ∧
      IsPLHomeomorphOn qq (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ωq ∧
      qp '' stdSimplexBoundary 2 = qZ '' stdSimplexBoundary 2 ∧
      qq '' stdSimplexBoundary 2 = qZ '' stdSimplexBoundary 2 ∧
      Ωp ∪ Ωq = frontier B ∧ Ωp ∩ Ωq = qZ '' stdSimplexBoundary 2 ∧
      IsPLBall 3 Yp ∧ frontier Yp = Z ∪ Ωp ∧ Disjoint (interior B) Yp := by
  set J := qZ '' stdSimplexBoundary 2 with hJdef
  have hJ : IsPLSphere 1 J := hqZ.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hJZ : J ⊆ Z := by
    rw [hJdef, ← hqZ.image_eq]
    exact image_mono fun x hx => hx.1
  have hBc : IsClosed B := hB.isPolyhedron.isClosed
  have hZc : IsClosed Z := (show IsPLBall 2 Z from ⟨qZ, hqZ⟩).isPolyhedron.isClosed
  obtain ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, hq₀J, hq₁J, hunion, hinter⟩ :=
    exists_isPLBall_pair_of_isPLSphere_two hB.isPLSphere_frontier hJ hZf
  have hD₀c : IsClosed D₀ := (show IsPLBall 2 D₀ from ⟨q₀, hq₀⟩).isPolyhedron.isClosed
  have hD₁c : IsClosed D₁ := (show IsPLBall 2 D₁ from ⟨q₁, hq₁⟩).isPolyhedron.isClosed
  have hZD : ∀ D : Set E3, D ⊆ frontier B → J ⊆ D → Z ∩ D = J := by
    intro D hDB hJD
    apply Subset.antisymm
    · rw [← hZB]
      exact inter_subset_inter_right Z (hDB.trans hBc.frontier_subset)
    · exact subset_inter hJZ hJD
  have hD₀B : D₀ ⊆ frontier B := by
    rw [← hunion]
    exact subset_union_left
  have hD₁B : D₁ ⊆ frontier B := by
    rw [← hunion]
    exact subset_union_right
  have hJD₀ : J ⊆ D₀ := by
    rw [← hq₀J, ← hq₀.image_eq]
    exact image_mono fun x hx => hx.1
  have hJD₁ : J ⊆ D₁ := by
    rw [← hq₁J, ← hq₁.image_eq]
    exact image_mono fun x hx => hx.1
  have hS₀ : IsPLSphere 2 (Z ∪ D₀) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hqZ hq₀ (hZD D₀ hD₀B hJD₀) hq₀J
  have hS₁ : IsPLSphere 2 (Z ∪ D₁) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hqZ hq₁ (hZD D₁ hD₁B hJD₁) hq₁J
  obtain ⟨Y₀, hY₀, hY₀f, -⟩ := hS₀.exists_isPLBall_frontier_eq
  obtain ⟨Y₁, hY₁, hY₁f, -⟩ := hS₁.exists_isPLBall_frontier_eq
  have hne : (D₀ \ J).Nonempty := by
    refine ⟨q₀ (stdCenter 1), ?_⟩
    rw [← hq₀J, ← hq₀.image_openSimplex_stdVertices (n := 1)]
    exact mem_image_of_mem q₀ (stdCenter_mem_openSimplex 1)
  rcases union_eq_and_disjoint_or_of_theta hB hY₀ hY₁ hunion hinter hZB hY₀f hY₁f hD₀c hD₁c hZc
    hne with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨D₀, D₁, Y₀, q₀, q₁, hq₀, hq₁, hq₀J, hq₁J, hunion, hinter, hY₀, hY₀f, h⟩
  · refine ⟨D₁, D₀, Y₁, q₁, q₀, hq₁, hq₀, hq₁J, hq₀J, ?_, ?_, hY₁, hY₁f, h⟩
    · rw [union_comm]
      exact hunion
    · rw [inter_comm]
      exact hinter
theorem exists_isPLBall_frontier_eq_of_interior_subset_pocket {B₁ B₂ : Set E3}
    (hB₁ : IsPLBall 3 B₁) (hB₂ : IsPLBall 3 B₂) {ι κ : Type*} [Finite ι] [Finite κ]
    {H : ι → Set E3} {rH : ι → (Fin 3 → ℝ) → E3}
    (hrH : ∀ i, IsPLHomeomorphOn (rH i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (H i))
    (hHdisj : Pairwise fun i j => Disjoint (H i) (H j)) (h12 : B₁ ∩ B₂ = ⋃ i, H i)
    (hH₁ : ∀ i, H i ⊆ frontier B₁) (hH₂ : ∀ i, H i ⊆ frontier B₂)
    {D ρ₁ ρ₂ : κ → Set E3} {qD : κ → (Fin 3 → ℝ) → E3} {γ₂ : κ → ℝ → E3}
    (hqD : ∀ s, IsPLHomeomorphOn (qD s) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D s))
    (hDdisj : Pairwise fun s s' => Disjoint (D s) (D s'))
    (hγ₂ : ∀ s, IsPLHomeomorphOn (γ₂ s) (Icc 0 1) (ρ₂ s))
    (hDB₁ : ∀ s, D s ∩ B₁ = ρ₁ s) (hDB₂ : ∀ s, D s ∩ B₂ = ρ₂ s)
    (hρ : ∀ s, qD s '' stdSimplexBoundary 2 = ρ₁ s ∪ ρ₂ s)
    (hρ₂₁ : ∀ s, ρ₁ s ∩ ρ₂ s = {γ₂ s 0, γ₂ s 1}) (hρ₁B : ∀ s, ρ₁ s ⊆ frontier B₁)
    {X Y : Set E3} {qX qY : (Fin 3 → ℝ) → E3}
    (hqX : IsPLHomeomorphOn qX (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X)
    (hqY : IsPLHomeomorphOn qY (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Y)
    (hXY : X ∪ Y ∪ ⋃ i, H i = frontier B₁) (hXYi : X ∩ Y = ⋃ s, ρ₁ s)
    {β : ι → Set E3} {γ : ι → ℝ → E3} (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (β i))
    (hβ : ∀ i, β i ⊆ rH i '' stdSimplexBoundary 2)
    (hXH : ∀ i, (X ∩ H i = β i ∧ Y ∩ H i = closure (rH i '' stdSimplexBoundary 2 \ β i)) ∨
      (X ∩ H i = closure (rH i '' stdSimplexBoundary 2 \ β i) ∧ Y ∩ H i = β i))
    (hqXb : qX '' stdSimplexBoundary 2 = (⋃ s, ρ₁ s) ∪ ⋃ i, (X ∩ H i))
    (hqYb : qY '' stdSimplexBoundary 2 = (⋃ s, ρ₁ s) ∪ ⋃ i, (Y ∩ H i))
    {Ωp Yp : Set E3} {qp : (Fin 3 → ℝ) → E3}
    (hqp : IsPLHomeomorphOn qp (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ωp)
    (hqpb : qp '' stdSimplexBoundary 2 = (⋃ s, ρ₂ s) ∪ ⋃ i, (X ∩ H i))
    (hΩpB₂ : Ωp ⊆ frontier B₂) (hYp : IsPLBall 3 Yp) (hYpf : frontier Yp = X ∪ (⋃ s, D s) ∪ Ωp)
    (hpocket : Disjoint (interior B₂) Yp) (hne : (interior B₁ ∩ interior Yp).Nonempty) :
    ∃ (R A Ω : Set E3) (qA qΩ : (Fin 3 → ℝ) → E3), IsPLBall 3 R ∧
      frontier R = A ∪ (⋃ s, D s) ∪ Ω ∧ (A = X ∨ A = Y) ∧
      IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
      qA '' stdSimplexBoundary 2 = (⋃ s, ρ₁ s) ∪ ⋃ i, (A ∩ H i) ∧
      IsPLHomeomorphOn qΩ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ω ∧
      qΩ '' stdSimplexBoundary 2 = (⋃ s, ρ₂ s) ∪ ⋃ i, (A ∩ H i) ∧
      Ω ⊆ frontier B₂ ∧ Ω ∩ B₁ = ⋃ i, (A ∩ H i) ∧ Disjoint (interior R) (B₁ ∪ B₂) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hB₁c : IsClosed B₁ := hB₁.isPolyhedron.isClosed
  have hB₂c : IsClosed B₂ := hB₂.isPolyhedron.isClosed
  have hB₁reg : closure (interior B₁) = B₁ := hB₁.closure_interior_of_finrank hdim
  have hB₂reg : closure (interior B₂) = B₂ := hB₂.closure_interior_of_finrank hdim
  have hbd : ∀ {P : Set E3} {q : (Fin 3 → ℝ) → E3},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P → q '' stdSimplexBoundary 2 ⊆ P :=
    fun hq => by
      rw [← hq.image_eq]
      exact image_mono fun x hx => hx.1
  have hdc : ∀ {P : Set E3} {q : (Fin 3 → ℝ) → E3},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P → IsClosed P :=
    fun hq => (show IsPLBall 2 _ from ⟨_, hq⟩).isPolyhedron.isClosed
  have hopen : ∀ {U P : Set E3}, IsOpen U → closure (interior P) = P →
      Disjoint U (interior P) → Disjoint U P := by
    intro U P hU hP h
    refine Set.disjoint_left.mpr fun z hzU hzP => ?_
    rw [← hP] at hzP
    obtain ⟨w, hwU, hwP⟩ := mem_closure_iff.mp hzP U hU hzU
    exact Set.disjoint_left.mp h hwU hwP
  have hHB₁ : ∀ i, H i ⊆ B₁ := fun i => (hH₁ i).trans hB₁c.frontier_subset
  have hHB₂ : ∀ i, H i ⊆ B₂ := fun i => (hH₂ i).trans hB₂c.frontier_subset
  have hρ₁D : ∀ s, ρ₁ s ⊆ D s := fun s => by
    rw [← hDB₁ s]
    exact inter_subset_left
  have hρ₂D : ∀ s, ρ₂ s ⊆ D s := fun s => by
    rw [← hDB₂ s]
    exact inter_subset_left
  have hDH : ∀ s i, D s ∩ H i ⊆ ρ₁ s ∩ ρ₂ s := fun s i x hx => by
    rw [← hDB₁ s, ← hDB₂ s]
    exact ⟨⟨hx.1, hHB₁ i hx.2⟩, hx.1, hHB₂ i hx.2⟩
  have hρ₁X : ∀ s, ρ₁ s ⊆ X := fun s =>
    (subset_iUnion ρ₁ s).trans (subset_union_left.trans (hqXb.symm.subset.trans (hbd hqX)))
  have hρ₁Y : ∀ s, ρ₁ s ⊆ Y := fun s =>
    (subset_iUnion ρ₁ s).trans (subset_union_left.trans (hqYb.symm.subset.trans (hbd hqY)))
  have hXB₁ : X ⊆ frontier B₁ := by
    rw [← hXY]
    exact subset_union_left.trans subset_union_left
  have hYB₁ : Y ⊆ frontier B₁ := by
    rw [← hXY]
    exact subset_union_right.trans subset_union_left
  have hB₁₂ : ∀ x ∈ B₁, x ∈ B₂ → ∃ i, x ∈ H i := fun x h1 h2 =>
    mem_iUnion.mp (h12 ▸ (⟨h1, h2⟩ : x ∈ B₁ ∩ B₂))
  have hintB₁B₂ : Disjoint (interior B₁) B₂ := by
    refine Set.disjoint_left.mpr fun x hx hx2 => ?_
    obtain ⟨i, hi⟩ := hB₁₂ x (interior_subset hx) hx2
    exact (hH₁ i hi).2 hx
  have harc : ∀ i, ∃ a : ℝ → E3, IsPLHomeomorphOn a (Icc 0 1) (X ∩ H i) ∧
      (X ∩ H i) ∩ (Y ∩ H i) = {a 0, a 1} ∧
      (X ∩ H i) ∪ (Y ∩ H i) = rH i '' stdSimplexBoundary 2 ∧
      closure (rH i '' stdSimplexBoundary 2 \ (X ∩ H i)) = Y ∩ H i := fun i =>
    exists_complementary_arcs_of_or ((hrH i).isPLSphere_image_stdSimplexBoundary (n := 1))
      (hγ i) (hβ i) (hXH i)
  choose δX hδX hXYH hXYu hcY using harc
  have hXHb : ∀ i, X ∩ H i ⊆ rH i '' stdSimplexBoundary 2 := fun i => by
    rw [← hXYu i]
    exact subset_union_left
  have hYHb : ∀ i, Y ∩ H i ⊆ rH i '' stdSimplexBoundary 2 := fun i => by
    rw [← hXYu i]
    exact subset_union_right
  have hends : ∀ i, ({δX i 0, δX i 1} : Set E3) ⊆ Y ∩ H i := fun i => by
    rw [← hXYH i]
    exact inter_subset_right
  have hρ₁H : ∀ s i, ρ₁ s ∩ (X ∩ H i) ⊆ {δX i 0, δX i 1} := by
    intro s i x hx
    rw [← hXYH i]
    exact ⟨hx.2, hρ₁Y s hx.1, hx.2.2⟩
  have hUD : ⋃ s ∈ (Finset.univ : Finset κ), D s = ⋃ s, D s := by simp
  have hYpreg : closure (interior Yp) = Yp := hYp.closure_interior_of_finrank hdim
  have hYpB₂ : Disjoint (interior Yp) B₂ :=
    hopen isOpen_interior hB₂reg (Set.disjoint_left.mpr fun x hx hx2 =>
      Set.disjoint_left.mp hpocket hx2 (interior_subset hx))
  have hB₁Yp : interior B₁ ⊆ interior Yp := by
    refine subset_interior_of_isPreconnected_of_disjoint_frontier
      (hB₁.isConnected_interior_of_finrank hdim).isPreconnected ?_ hne
    refine Set.disjoint_left.mpr fun x hx hxf => ?_
    rw [hYpf] at hxf
    rcases hxf with (h | h) | h
    · exact (hXB₁ h).2 hx
    · obtain ⟨s, hs⟩ := mem_iUnion.mp h
      have hxρ : x ∈ ρ₁ s := by
        rw [← hDB₁ s]
        exact ⟨hs, interior_subset hx⟩
      exact (hρ₁B s hxρ).2 hx
    · exact Set.disjoint_left.mp hintB₁B₂ hx (hB₂c.frontier_subset (hΩpB₂ h))
  have hcaps : ∀ i, H i ⊆ Ωp := by
    intro i
    have hsub : H i \ rH i '' stdSimplexBoundary 2 ⊆ Ωp := by
      intro x hx
      by_contra hxΩ
      have hxfr : x ∉ frontier Yp := by
        rw [hYpf]
        rintro ((h | h) | h)
        · exact hx.2 (hXHb i ⟨h, hx.1⟩)
        · obtain ⟨s, hs⟩ := mem_iUnion.mp h
          exact hx.2 (hXHb i ⟨hρ₁X s (hDH s i ⟨hs, hx.1⟩).1, hx.1⟩)
        · exact hxΩ h
      have hxYp : x ∈ Yp := by
        rw [← hYpreg]
        refine closure_mono hB₁Yp ?_
        rw [hB₁reg]
        exact hHB₁ i hx.1
      have hxi : x ∈ interior Yp := by
        by_contra h
        exact hxfr ⟨subset_closure hxYp, h⟩
      have hxc : x ∈ closure (interior B₂) := by
        rw [hB₂reg]
        exact hHB₂ i hx.1
      obtain ⟨w, hwo, hw⟩ := mem_closure_iff.mp hxc _ isOpen_interior hxi
      exact Set.disjoint_left.mp hpocket hw (interior_subset hwo)
    rw [← (hrH i).closure_sdiff_image_stdSimplexBoundary (n := 1)]
    exact closure_minimal hsub (hdc hqp)
  have hHqp : ∀ i, H i ∩ qp '' stdSimplexBoundary 2 = X ∩ H i := by
    intro i
    rw [hqpb]
    apply Subset.antisymm
    · rintro x ⟨hxH, hx | hx⟩
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        exact ⟨hρ₁X s (hDH s i ⟨hρ₂D s hs, hxH⟩).1, hxH⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        by_cases hij : j = i
        · subst hij
          exact hj
        · exact absurd hxH (Set.disjoint_left.mp (hHdisj hij) hj.2)
    · intro x hx
      exact ⟨hx.2, Or.inr (mem_iUnion.mpr ⟨i, hx⟩)⟩
  have hUH : ⋃ i ∈ (Finset.univ : Finset ι), H i = ⋃ i, H i := by simp
  obtain ⟨q', hq', hq'b, hq'i, hq'u⟩ := exists_isPLHomeomorphOn_closure_sdiff_biUnion_of_caps
    hqp hrH hδX hXHb Finset.univ (fun i _ => hcaps i) (fun i _ => hHqp i)
    (fun i _ j _ h => hHdisj h)
  rw [hUH] at hq' hq'u
  simp only [Finset.mem_univ, iUnion_true] at hq'b
  set Ω' := closure (Ωp \ ⋃ i, H i)
  have hΩ'H : ∀ i, Ω' ∩ H i = Y ∩ H i := fun i => by
    have h := hq'i i (Finset.mem_univ i)
    rw [hUH, hcY i] at h
    exact h
  have hΩ'Ωp : Ω' ⊆ Ωp := by
    rw [← hq'u]
    exact subset_union_left
  have hΩ'B₂ : Ω' ⊆ B₂ := hΩ'Ωp.trans (hΩpB₂.trans hB₂c.frontier_subset)
  have hq'b' : q' '' stdSimplexBoundary 2 = (⋃ s, ρ₂ s) ∪ ⋃ i, (Y ∩ H i) := by
    rw [hq'b, hqpb]
    simp only [hcY]
    apply Subset.antisymm
    · rintro x (⟨hx | hx, hxn⟩ | hx)
      · exact Or.inl hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not] at hxn
        exact Or.inr (mem_iUnion.mpr ⟨i, hends i (hxn i hi)⟩)
      · exact Or.inr hx
    · rintro x (hx | hx)
      · refine Or.inl ⟨Or.inl hx, ?_⟩
        obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro i hi
        exact hρ₁H s i ⟨(hDH s i ⟨hρ₂D s hs, hi.2⟩).1, hi⟩
      · exact Or.inr hx
  obtain ⟨qΔ, hqΔ, hqΔb⟩ := exists_isPLHomeomorphOn_union_biUnion_of_inter_eq_arc hq' hqD hγ₂
    Finset.univ (fun s _ => by
      apply Subset.antisymm
      · intro x hx
        rw [← hDB₂ s]
        exact ⟨hx.2, hΩ'B₂ hx.1⟩
      · exact subset_inter ((subset_iUnion ρ₂ s).trans (subset_union_left.trans
          (hq'b'.symm.subset.trans (hbd hq')))) (hρ₂D s))
    (fun s _ => (subset_iUnion ρ₂ s).trans (subset_union_left.trans hq'b'.symm.subset))
    (fun s _ => by
      rw [hρ s]
      exact subset_union_right)
    (fun s _ s' _ h => hDdisj h)
  rw [hUD] at hqΔ
  simp only [Finset.mem_univ, iUnion_true] at hqΔb
  set Δ := Ω' ∪ ⋃ s, D s
  have hΔb : qΔ '' stdSimplexBoundary 2 = qY '' stdSimplexBoundary 2 := by
    rw [hqΔb, hq'b', hqYb]
    apply Subset.antisymm
    · rintro x ⟨hx, hxn⟩
      simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not] at hxn
      rcases hx with (hx | hx) | hx
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        have hxe := hxn s hs
        rw [← hρ₂₁ s] at hxe
        exact Or.inl (mem_iUnion.mpr ⟨s, hxe.1⟩)
      · exact Or.inr hx
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        rw [hρ s] at hs
        rcases hs with hs | hs
        · exact Or.inl (mem_iUnion.mpr ⟨s, hs⟩)
        · have hxe := hxn s hs
          rw [← hρ₂₁ s] at hxe
          exact Or.inl (mem_iUnion.mpr ⟨s, hxe.1⟩)
    · rintro x (hx | hx)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        refine ⟨Or.inr (mem_iUnion.mpr ⟨s, by rw [hρ s]; exact Or.inl hs⟩), ?_⟩
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro s' hs'
        by_cases hss : s' = s
        · subst hss
          rw [← hρ₂₁]
          exact ⟨hs, hs'⟩
        · exact absurd (hρ₁D s hs) (Set.disjoint_left.mp (hDdisj hss) (hρ₂D s' hs'))
      · refine ⟨Or.inl (Or.inr hx), ?_⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro s hs
        rw [← hρ₂₁ s]
        exact hDH s i ⟨hρ₂D s hs, hi.2⟩
  have hYΔ : Y ∩ Δ = qY '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro x ⟨hxY, hx | hx⟩
      · obtain ⟨i, hi⟩ := hB₁₂ x (hB₁c.frontier_subset (hYB₁ hxY)) (hΩ'B₂ hx)
        rw [hqYb]
        exact Or.inr (mem_iUnion.mpr ⟨i, hxY, hi⟩)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        rw [hqYb]
        refine Or.inl (mem_iUnion.mpr ⟨s, ?_⟩)
        rw [← hDB₁ s]
        exact ⟨hs, hB₁c.frontier_subset (hYB₁ hxY)⟩
    · refine subset_inter (hbd hqY) ?_
      rw [hqYb]
      rintro x (hx | hx)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        exact Or.inr (mem_iUnion.mpr ⟨s, hρ₁D s hs⟩)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [← hΩ'H i] at hi
        exact Or.inl hi.1
  obtain ⟨R', hR', hR'f, -⟩ :=
    (isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hqY hqΔ hYΔ
      hΔb).exists_isPLBall_frontier_eq
  obtain ⟨qXh, hqXh, hqXhb⟩ := exists_isPLHomeomorphOn_union_biUnion_of_inter_eq_arc hqX hrH
    hδX Finset.univ (fun i _ => rfl)
    (fun i _ => (subset_iUnion (fun i => X ∩ H i) i).trans
      (subset_union_right.trans hqXb.symm.subset))
    (fun i _ => hXHb i) (fun i _ j _ h => hHdisj h)
  rw [hUH] at hqXh
  simp only [Finset.mem_univ, iUnion_true] at hqXhb
  set Xh := X ∪ ⋃ i, H i
  have hXhb : qXh '' stdSimplexBoundary 2 = qY '' stdSimplexBoundary 2 := by
    rw [hqXhb, hqXb, hqYb]
    apply Subset.antisymm
    · rintro x ⟨hx, hxn⟩
      simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not] at hxn
      rcases hx with (hx | hx) | hx
      · exact Or.inl hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact Or.inr (mem_iUnion.mpr ⟨i, hends i (hxn i hi)⟩)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [← hXYu i] at hi
        rcases hi with hi | hi
        · exact Or.inr (mem_iUnion.mpr ⟨i, hends i (hxn i hi)⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
    · rintro x (hx | hx)
      · refine ⟨Or.inl (Or.inl hx), ?_⟩
        obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro i hi
        exact hρ₁H s i ⟨hs, hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        refine ⟨Or.inr (mem_iUnion.mpr ⟨i, hYHb i hi⟩), ?_⟩
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro j hj
        by_cases hij : j = i
        · subst hij
          rw [← hXYH]
          exact ⟨hj, hi⟩
        · exact absurd hi.2 (Set.disjoint_left.mp (hHdisj hij) hj.2)
  have hE : Xh ∪ Y = frontier B₁ := by
    rw [← hXY]
    change (X ∪ ⋃ i, H i) ∪ Y = X ∪ Y ∪ ⋃ i, H i
    ext x
    simp only [mem_union]
    tauto
  have hE₁₂ : Xh ∩ Y = qY '' stdSimplexBoundary 2 := by
    rw [hqYb, ← hXYi]
    change (X ∪ ⋃ i, H i) ∩ Y = _
    ext x
    simp only [mem_inter_iff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hx | ⟨i, hi⟩, hy⟩
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr ⟨i, hy, hi⟩
    · rintro (⟨hx, hy⟩ | ⟨i, hy, hi⟩)
      · exact ⟨Or.inl hx, hy⟩
      · exact ⟨Or.inr ⟨i, hi⟩, hy⟩
  have hDP : Δ ∩ B₁ = qY '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro x ⟨hx | hx, hx1⟩
      · obtain ⟨i, hi⟩ := hB₁₂ x hx1 (hΩ'B₂ hx)
        have hxY : x ∈ Y ∩ H i := by
          rw [← hΩ'H i]
          exact ⟨hx, hi⟩
        rw [hqYb]
        exact Or.inr (mem_iUnion.mpr ⟨i, hxY⟩)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        rw [hqYb]
        refine Or.inl (mem_iUnion.mpr ⟨s, ?_⟩)
        rw [← hDB₁ s]
        exact ⟨hs, hx1⟩
    · rw [hqYb]
      rintro x (hx | hx)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        exact ⟨Or.inr (mem_iUnion.mpr ⟨s, hρ₁D s hs⟩),
          hB₁c.frontier_subset (hρ₁B s hs)⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [← hΩ'H i] at hi
        exact ⟨Or.inl hi.1, hHB₁ i hi.2⟩
  have hY₁f : frontier Yp = Δ ∪ Xh := by
    rw [hYpf, ← hq'u]
    change X ∪ (⋃ s, D s) ∪ (Ω' ∪ ⋃ i, H i) = (Ω' ∪ ⋃ s, D s) ∪ (X ∪ ⋃ i, H i)
    ext x
    simp only [mem_union]
    tauto
  have hY₂f : frontier R' = Δ ∪ Y := by
    rw [hR'f, union_comm]
  have hne' : (Xh \ qY '' stdSimplexBoundary 2).Nonempty := by
    have hxX : qX (stdCenter 1) ∈ X \ qX '' stdSimplexBoundary 2 := by
      rw [← hqX.image_openSimplex_stdVertices (n := 1)]
      exact mem_image_of_mem qX (stdCenter_mem_openSimplex 1)
    refine ⟨qX (stdCenter 1), Or.inl hxX.1, fun h => ?_⟩
    have hxY : qX (stdCenter 1) ∈ X ∩ Y := ⟨hxX.1, hbd hqY h⟩
    rw [hXYi] at hxY
    exact hxX.2 (hqXb.symm.subset (Or.inl hxY))
  rcases union_eq_and_disjoint_or_of_theta hB₁ hYp hR' hE hE₁₂ hDP hY₁f hY₂f (hdc hqXh)
    (hdc hqY) (hdc hqΔ) hne' with ⟨-, h⟩ | ⟨hu, h⟩
  · obtain ⟨x, h1, h2⟩ := hne
    exact absurd (interior_subset h2) (Set.disjoint_left.mp h h1)
  · have hR'Yp : R' ⊆ Yp := by
      rw [← hu]
      exact subset_union_right
    refine ⟨R', Y, Ω', qY, q', hR', ?_, Or.inr rfl, hqY, hqYb, hq', hq'b', ?_, ?_, ?_⟩
    · rw [hR'f]
      change Y ∪ (Ω' ∪ ⋃ s, D s) = Y ∪ (⋃ s, D s) ∪ Ω'
      ext x
      simp only [mem_union]
      tauto
    · exact hΩ'Ωp.trans hΩpB₂
    · apply Subset.antisymm
      · rintro x ⟨hx, hx1⟩
        obtain ⟨i, hi⟩ := hB₁₂ x hx1 (hΩ'B₂ hx)
        have hxY : x ∈ Y ∩ H i := by
          rw [← hΩ'H i]
          exact ⟨hx, hi⟩
        exact mem_iUnion.mpr ⟨i, hxY⟩
      · intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [← hΩ'H i] at hi
        exact ⟨hi.1, hHB₁ i hi.2⟩
    · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
      · exact hopen isOpen_interior hB₁reg (Set.disjoint_left.mpr fun x hx hx1 =>
          Set.disjoint_left.mp h hx1 (interior_subset hx))
      · exact Set.disjoint_left.mpr fun x hx hx2 =>
          Set.disjoint_left.mp hYpB₂ (interior_mono hR'Yp hx) hx2

theorem exists_isPLBall_frontier_eq_of_two_balls {B₁ B₂ : Set E3} (hB₁ : IsPLBall 3 B₁)
    (hB₂ : IsPLBall 3 B₂) {ι κ : Type*} [Finite ι] [Finite κ] {H : ι → Set E3}
    {rH : ι → (Fin 3 → ℝ) → E3}
    (hrH : ∀ i, IsPLHomeomorphOn (rH i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (H i))
    (hHdisj : Pairwise fun i j => Disjoint (H i) (H j)) (h12 : B₁ ∩ B₂ = ⋃ i, H i)
    (hH₁ : ∀ i, H i ⊆ frontier B₁) (hH₂ : ∀ i, H i ⊆ frontier B₂)
    (hHint : ∀ i, H i \ rH i '' stdSimplexBoundary 2 ⊆ interior (B₁ ∪ B₂))
    {D ρ₁ ρ₂ : κ → Set E3} {qD : κ → (Fin 3 → ℝ) → E3} {γ₁ γ₂ : κ → ℝ → E3}
    (hqD : ∀ s, IsPLHomeomorphOn (qD s) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D s))
    (hDdisj : Pairwise fun s s' => Disjoint (D s) (D s'))
    (hγ₁ : ∀ s, IsPLHomeomorphOn (γ₁ s) (Icc 0 1) (ρ₁ s))
    (hγ₂ : ∀ s, IsPLHomeomorphOn (γ₂ s) (Icc 0 1) (ρ₂ s))
    (hDB₁ : ∀ s, D s ∩ B₁ = ρ₁ s) (hDB₂ : ∀ s, D s ∩ B₂ = ρ₂ s)
    (hρ : ∀ s, qD s '' stdSimplexBoundary 2 = ρ₁ s ∪ ρ₂ s)
    (hρ₁₂ : ∀ s, ρ₁ s ∩ ρ₂ s = {γ₁ s 0, γ₁ s 1}) (hρ₂₁ : ∀ s, ρ₁ s ∩ ρ₂ s = {γ₂ s 0, γ₂ s 1})
    (hρ₁B : ∀ s, ρ₁ s ⊆ frontier B₁) (hρ₂B : ∀ s, ρ₂ s ⊆ frontier B₂)
    {X Y : Set E3} {qX qY : (Fin 3 → ℝ) → E3}
    (hqX : IsPLHomeomorphOn qX (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X)
    (hqY : IsPLHomeomorphOn qY (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Y)
    (hXY : X ∪ Y ∪ ⋃ i, H i = frontier B₁) (hXYi : X ∩ Y = ⋃ s, ρ₁ s)
    {β : ι → Set E3} {γ : ι → ℝ → E3} (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (β i))
    (hβ : ∀ i, β i ⊆ rH i '' stdSimplexBoundary 2)
    (hXH : ∀ i, (X ∩ H i = β i ∧ Y ∩ H i = closure (rH i '' stdSimplexBoundary 2 \ β i)) ∨
      (X ∩ H i = closure (rH i '' stdSimplexBoundary 2 \ β i) ∧ Y ∩ H i = β i))
    (hqXb : qX '' stdSimplexBoundary 2 = (⋃ s, ρ₁ s) ∪ ⋃ i, (X ∩ H i))
    (hqYb : qY '' stdSimplexBoundary 2 = (⋃ s, ρ₁ s) ∪ ⋃ i, (Y ∩ H i)) :
    ∃ (R A Ω : Set E3) (qA qΩ : (Fin 3 → ℝ) → E3), IsPLBall 3 R ∧
      frontier R = A ∪ (⋃ s, D s) ∪ Ω ∧ (A = X ∨ A = Y) ∧
      IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
      qA '' stdSimplexBoundary 2 = (⋃ s, ρ₁ s) ∪ ⋃ i, (A ∩ H i) ∧
      IsPLHomeomorphOn qΩ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ω ∧
      qΩ '' stdSimplexBoundary 2 = (⋃ s, ρ₂ s) ∪ ⋃ i, (A ∩ H i) ∧
      Ω ⊆ frontier B₂ ∧ Ω ∩ B₁ = ⋃ i, (A ∩ H i) ∧ Disjoint (interior R) (B₁ ∪ B₂) := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hB₁c : IsClosed B₁ := hB₁.isPolyhedron.isClosed
  have hB₂c : IsClosed B₂ := hB₂.isPolyhedron.isClosed
  have hB₁reg : closure (interior B₁) = B₁ := hB₁.closure_interior_of_finrank hdim
  have hB₂reg : closure (interior B₂) = B₂ := hB₂.closure_interior_of_finrank hdim
  have hbd : ∀ {P : Set E3} {q : (Fin 3 → ℝ) → E3},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P → q '' stdSimplexBoundary 2 ⊆ P :=
    fun hq => by
      rw [← hq.image_eq]
      exact image_mono fun x hx => hx.1
  have hdc : ∀ {P : Set E3} {q : (Fin 3 → ℝ) → E3},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P → IsClosed P :=
    fun hq => (show IsPLBall 2 _ from ⟨_, hq⟩).isPolyhedron.isClosed
  have hopen : ∀ {U P : Set E3}, IsOpen U → closure (interior P) = P →
      Disjoint U (interior P) → Disjoint U P := by
    intro U P hU hP h
    refine Set.disjoint_left.mpr fun z hzU hzP => ?_
    rw [← hP] at hzP
    obtain ⟨w, hwU, hwP⟩ := mem_closure_iff.mp hzP U hU hzU
    exact Set.disjoint_left.mp h hwU hwP
  have hHB₁ : ∀ i, H i ⊆ B₁ := fun i => (hH₁ i).trans hB₁c.frontier_subset
  have hHB₂ : ∀ i, H i ⊆ B₂ := fun i => (hH₂ i).trans hB₂c.frontier_subset
  have hρ₁D : ∀ s, ρ₁ s ⊆ D s := fun s => by
    rw [← hDB₁ s]
    exact inter_subset_left
  have hρ₂D : ∀ s, ρ₂ s ⊆ D s := fun s => by
    rw [← hDB₂ s]
    exact inter_subset_left
  have hDH : ∀ s i, D s ∩ H i ⊆ ρ₁ s ∩ ρ₂ s := fun s i x hx => by
    rw [← hDB₁ s, ← hDB₂ s]
    exact ⟨⟨hx.1, hHB₁ i hx.2⟩, hx.1, hHB₂ i hx.2⟩
  have hρ₁X : ∀ s, ρ₁ s ⊆ X := fun s =>
    (subset_iUnion ρ₁ s).trans (subset_union_left.trans (hqXb.symm.subset.trans (hbd hqX)))
  have hXB₁ : X ⊆ frontier B₁ := by
    rw [← hXY]
    exact subset_union_left.trans subset_union_left
  have hB₁₂ : ∀ x ∈ B₁, x ∈ B₂ → ∃ i, x ∈ H i := fun x h1 h2 =>
    mem_iUnion.mp (h12 ▸ (⟨h1, h2⟩ : x ∈ B₁ ∩ B₂))
  have hintB₁B₂ : Disjoint (interior B₁) B₂ := by
    refine Set.disjoint_left.mpr fun x hx hx2 => ?_
    obtain ⟨i, hi⟩ := hB₁₂ x (interior_subset hx) hx2
    exact (hH₁ i hi).2 hx
  have hXYu : ∀ i, (X ∩ H i) ∪ (Y ∩ H i) = rH i '' stdSimplexBoundary 2 := fun i => by
    obtain ⟨-, -, -, h, -⟩ := exists_complementary_arcs_of_or
      ((hrH i).isPLSphere_image_stdSimplexBoundary (n := 1)) (hγ i) (hβ i) (hXH i)
    exact h
  have hUD : ⋃ s ∈ (Finset.univ : Finset κ), D s = ⋃ s, D s := by simp
  obtain ⟨qZ, hqZ, hqZb⟩ := exists_isPLHomeomorphOn_union_biUnion_of_inter_eq_arc hqX hqD hγ₁
    Finset.univ (fun s _ => by
      apply Subset.antisymm
      · intro x hx
        rw [← hDB₁ s]
        exact ⟨hx.2, hB₁c.frontier_subset (hXB₁ hx.1)⟩
      · exact subset_inter (hρ₁X s) (hρ₁D s))
    (fun s _ => (subset_iUnion ρ₁ s).trans (subset_union_left.trans hqXb.symm.subset))
    (fun s _ => by
      rw [hρ s]
      exact subset_union_left)
    (fun s _ s' _ h => hDdisj h)
  rw [hUD] at hqZ
  simp only [Finset.mem_univ, iUnion_true] at hqZb
  set Z := X ∪ ⋃ s, D s
  have hZb : qZ '' stdSimplexBoundary 2 = (⋃ s, ρ₂ s) ∪ ⋃ i, (X ∩ H i) := by
    rw [hqZb, hqXb]
    apply Subset.antisymm
    · rintro x ⟨hx, hxn⟩
      simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not] at hxn
      rcases hx with (hx | hx) | hx
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        have hxe := hxn s hs
        rw [← hρ₁₂ s] at hxe
        exact Or.inl (mem_iUnion.mpr ⟨s, hxe.2⟩)
      · exact Or.inr hx
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        rw [hρ s] at hs
        rcases hs with hs | hs
        · have hxe := hxn s hs
          rw [← hρ₁₂ s] at hxe
          exact Or.inl (mem_iUnion.mpr ⟨s, hxe.2⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨s, hs⟩)
    · rintro x (hx | hx)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        refine ⟨Or.inr (mem_iUnion.mpr ⟨s, by rw [hρ s]; exact Or.inr hs⟩), ?_⟩
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro s' hs'
        by_cases hss : s' = s
        · subst hss
          rw [← hρ₁₂]
          exact ⟨hs', hs⟩
        · exact absurd (hρ₂D s hs) (Set.disjoint_left.mp (hDdisj hss) (hρ₁D s' hs'))
      · refine ⟨Or.inl (Or.inr hx), ?_⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        simp only [mem_iUnion, mem_sdiff, not_exists, not_and, not_not]
        intro s hs
        rw [← hρ₁₂ s]
        exact hDH s i ⟨hρ₁D s hs, hi.2⟩
  have hZbB₂ : qZ '' stdSimplexBoundary 2 ⊆ frontier B₂ := by
    rw [hZb]
    rintro x (hx | hx)
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact hρ₂B s hs
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hH₂ i hi.2
  have hZB₂ : Z ∩ B₂ = qZ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro x ⟨hx | hx, hx2⟩
      · obtain ⟨i, hi⟩ := hB₁₂ x (hB₁c.frontier_subset (hXB₁ hx)) hx2
        rw [hZb]
        exact Or.inr (mem_iUnion.mpr ⟨i, hx, hi⟩)
      · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
        rw [hZb]
        refine Or.inl (mem_iUnion.mpr ⟨s, ?_⟩)
        rw [← hDB₂ s]
        exact ⟨hs, hx2⟩
    · exact subset_inter (hbd hqZ) (hZbB₂.trans hB₂c.frontier_subset)
  obtain ⟨Ωp, Ωq, Yp, qp, qq, hqp, -, hqpb, -, hΩu, -, hYp, hYpf, hpocket⟩ :=
    hB₂.exists_pocket_of_inter_eq_boundary hqZ hZB₂ hZbB₂
  have hYpc : IsClosed Yp := hYp.isPolyhedron.isClosed
  have hYpreg : closure (interior Yp) = Yp := hYp.closure_interior_of_finrank hdim
  have hΩpB₂ : Ωp ⊆ frontier B₂ := by
    rw [← hΩu]
    exact subset_union_left
  have hYpB₂ : Disjoint (interior Yp) B₂ :=
    hopen isOpen_interior hB₂reg (Set.disjoint_left.mpr fun x hx hx2 =>
      Set.disjoint_left.mp hpocket hx2 (interior_subset hx))
  by_cases hgood : Disjoint (interior Yp) (interior B₁)
  · have hYpB₁ : Disjoint (interior Yp) B₁ := hopen isOpen_interior hB₁reg hgood
    refine ⟨Yp, X, Ωp, qX, qp, hYp, hYpf, Or.inl rfl, hqX, hqXb, hqp, hqpb.trans hZb, hΩpB₂,
      ?_, Set.disjoint_union_right.mpr ⟨hYpB₁, hYpB₂⟩⟩
    apply Subset.antisymm
    · rintro x ⟨hxΩ, hx1⟩
      obtain ⟨i, hi⟩ := hB₁₂ x hx1 (hB₂c.frontier_subset (hΩpB₂ hxΩ))
      refine mem_iUnion.mpr ⟨i, ?_, hi⟩
      have hxfr : x ∈ frontier Yp := by
        rw [hYpf]
        exact Or.inr hxΩ
      have hxb : x ∈ rH i '' stdSimplexBoundary 2 := by
        by_contra hxb
        have hxi := hHint i ⟨hi, hxb⟩
        have hxc : x ∈ closure (interior Yp) := by
          rw [hYpreg]
          exact hYpc.frontier_subset hxfr
        obtain ⟨w, hwi, hw⟩ := mem_closure_iff.mp hxc _ isOpen_interior hxi
        have hwU : w ∈ B₁ ∪ B₂ := interior_subset hwi
        rcases hwU with hw1 | hw2
        · exact Set.disjoint_left.mp hYpB₁ hw hw1
        · exact Set.disjoint_left.mp hYpB₂ hw hw2
      rw [← hXYu i] at hxb
      rcases hxb with hxX | -
      · exact hxX.1
      · by_contra hxX
        have hxZ : x ∉ Z := by
          rintro (h | h)
          · exact hxX h
          · obtain ⟨s, hs⟩ := mem_iUnion.mp h
            exact hxX (hρ₁X s (hDH s i ⟨hs, hi⟩).1)
        have hO : IsOpen Zᶜ := (hdc hqZ).isOpen_compl
        obtain ⟨U, hU, -, hUout⟩ := hB₂.exists_mem_nhds_of_inter_frontier_subset hYp hO
          (fun z hz => by
            rw [hYpf] at hz
            rcases hz.2 with h | h
            · exact absurd h hz.1
            · exact hB₂c.frontier_subset (hΩpB₂ h))
          (Set.disjoint_left.mpr fun z hz hz2 =>
            Set.disjoint_left.mp hpocket hz2 (interior_subset hz))
          hxZ (hYpc.frontier_subset hxfr) (hH₂ i hi)
        have hxc : x ∈ closure (interior B₁) := by
          rw [hB₁reg]
          exact hx1
        obtain ⟨w, hwU, hwi⟩ := mem_closure_iff_nhds.mp hxc U hU
        exact Set.disjoint_left.mp hgood (hUout ⟨hwU, Set.disjoint_left.mp hintB₁B₂ hwi⟩) hwi
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine ⟨?_, hHB₁ i hi.2⟩
      have hxb : x ∈ qp '' stdSimplexBoundary 2 := by
        rw [hqpb, hZb]
        exact Or.inr hx
      exact hbd hqp hxb
  · refine exists_isPLBall_frontier_eq_of_interior_subset_pocket hB₁ hB₂ hrH hHdisj h12 hH₁ hH₂
      hqD hDdisj hγ₂ hDB₁ hDB₂ hρ hρ₂₁ hρ₁B hqX hqY hXY hXYi hγ hβ hXH hqXb hqYb hqp
      (hqpb.trans hZb) hΩpB₂ hYp hYpf hpocket ?_
    rw [Set.not_disjoint_iff] at hgood
    obtain ⟨x, h1, h2⟩ := hgood
    exact ⟨x, h2, h1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
