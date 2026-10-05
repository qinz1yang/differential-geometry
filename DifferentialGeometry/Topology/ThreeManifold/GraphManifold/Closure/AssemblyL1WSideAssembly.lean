import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NeckBox

/-!
# Chapter-14 assembly, item L1, group G3b, step T4: the cycle normal form from necks, handles, balls

`BallHandleCycle.cycleNormalForm_of_necks` (sub-statement T4 of lane ASM-L1b, frozen in
`build-logs/scratch/ASM-L1b/Targets.lean`): given necks on a neighbourhood of the closed neck box
in the standard position with respect to the OLD balls, handles and union of a `BallHandleCycle`
(sides, union, pieces, fillets, disjoint targets), reparametrized handles with the old images and
end disks that agree with the necks on the end strips, and reparametrized balls with the old images
that agree with the necks on the cap regions, the cycle has a `CycleNormalForm` with union
`range C.union.map`. Everything is set-level: the union is the balls, the handles and the fillets
(`BallHandleCycle.range_union_eq`), and every fillet lies in the neck image of the rounded box.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1bA : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance ballCharts_ASML1bA : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

namespace BallHandleCycle

variable {W : CompactCarrier.{u}}

/-- **T4 (assembly).** -/
theorem cycleNormalForm_of_necks (C : BallHandleCycle W)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (hsrc : ∀ k b, closedNeckDomain ε ⊆ (N k b).source)
    (hdisj : ∀ k b k' b', (k, b) ≠ (k', b') → Disjoint (N k b).target (N k' b').target)
    (hball : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0))
    (hhandle : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1)))
    (hunion : ∀ k b {q}, q ∈ neckDomain ε →
      (N k b q ∈ range C.union.map ↔ neckRounding ε q ≤ 0))
    (hpieces : ∀ k b, (N k b).target ∩ ((⋃ j, range (C.ball j).map) ∪
      ⋃ j, range (C.handle j).map) ⊆
        range (C.ball (rimBall C.len k b)).map ∪ range (C.handle k).map)
    (hfillet : ∀ k b, C.fillet k b ⊆ N k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0})
    (h : Fin C.len → ClosedCell 2 × Icc (0 : ℝ) 1 → W.Carrier)
    (hh : ∀ k, ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) W.model ∞ (h k) ∧
      (∀ q, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model (h k) q)) ∧ Injective (h k) ∧
      range (h k) = range (C.handle k).map ∧
      (∀ b, h k '' {q | q.2 = iccEnd b} = (C.handle k).endDisk b) ∧
      ∀ b (q : ClosedCell 2 × Icc (0 : ℝ) 1), |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε →
        h k q = N k b (handleEnd b q))
    (β : Fin C.len → ClosedCell 3 → W.Carrier)
    (hβ : ∀ j, ContMDiff (𝓡∂ 3) W.model ∞ (β j) ∧
      (∀ x, Bijective (mfderiv (𝓡∂ 3) W.model (β j) x)) ∧
      Injective (β j) ∧ range (β j) = range (C.ball j).map)
    (hcap : ∀ k b x, x ∈ neckCapRegion ε b →
      β (rimBall C.len k b) x = N k b (capMap b (x : EuclideanSpace ℝ (Fin 3)))) :
    Nonempty (CycleNormalForm W.model W.Carrier C.len ε (range C.union.map)) := by
  have hsub : ∀ k b, neckDomain ε ⊆ (N k b).source := fun k b =>
    (neckDomain_subset_closedNeckDomain ε).trans (hsrc k b)
  have hrβ : ∀ j, range (β j) = range (C.ball j).map := fun j => (hβ j).2.2.2
  have hrh : ∀ k, range (h k) = range (C.handle k).map := fun k => (hh k).2.2.2.1
  have hUβ : (⋃ j, range (β j)) = ⋃ j, range (C.ball j).map := iUnion_congr hrβ
  have hUh : (⋃ k, range (h k)) = ⋃ k, range (C.handle k).map := iUnion_congr hrh
  let M : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞ := fun k b =>
    restrictNeck (N k b) (neckDomain ε) (isOpen_neckDomain ε)
  have hM : ∀ k b q, M k b q = N k b q := fun _ _ _ => rfl
  refine ⟨{
    ε_pos := hε
    ε_le := hε'
    neck := M
    neck_source := fun k b => restrictNeck_source_of_subset (N k b) (isOpen_neckDomain ε) (hsub k b)
    neck_disjoint := fun k b k' b' hne =>
      (hdisj k b k' b' hne).mono (restrictNeck_target_subset _ _) (restrictNeck_target_subset _ _)
    ball := β
    ball_smooth := fun j => (hβ j).1
    ball_mfderiv := fun j => (hβ j).2.1
    ball_injective := fun j => (hβ j).2.2.1
    handle := h
    handle_smooth := fun k => (hh k).1
    handle_mfderiv := fun k => (hh k).2.1
    handle_injective := fun k => (hh k).2.2.1
    ball_cap := fun k b x hx => by rw [hM]; exact hcap k b x hx
    handle_end := fun k b q hq => by rw [hM]; exact (hh k).2.2.2.2.2 b q hq
    neck_ball := fun k b {q} hq => by
      rw [hM, hrβ]
      exact hball k b (hsub k b hq)
    neck_handle := fun k b {q} hq => by
      rw [hM, hrh]
      exact hhandle k b (hsub k b hq)
    neck_union := fun k b {q} hq => by
      rw [hM]
      exact hunion k b hq
    neck_pieces := fun k b => by
      rw [hUβ, hUh, hrβ, hrh]
      exact (inter_subset_inter_left _ (restrictNeck_target_subset _ _)).trans (hpieces k b)
    ball_disjoint := fun j j' hjj' => by
      change Disjoint (range (β j)) (range (β j'))
      rw [hrβ, hrβ]
      exact C.ball_disjoint hjj'
    handle_disjoint := fun k k' hkk' => by
      change Disjoint (range (h k)) (range (h k'))
      rw [hrh, hrh]
      exact C.handle_disjoint hkk'
    handle_ball_inter := fun k j => by
      rw [hrh, hrβ, (hh k).2.2.2.2.1 false, (hh k).2.2.2.2.1 true]
      exact C.handle_ball_inter k j
    union_eq := by
      rw [hUβ, hUh]
      apply Subset.antisymm
      · intro z hz
        rw [C.range_union_eq] at hz
        rcases hz with hz | hz
        · exact Or.inl hz
        · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
          obtain ⟨b, hb⟩ := mem_iUnion.mp hk
          obtain ⟨q, hq, rfl⟩ := hfillet k b hb
          exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨b, ⟨q, hq, rfl⟩⟩⟩)
      · rintro z (hz | hz)
        · rcases hz with hz | hz
          · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
            exact C.ball_subset_union j hj
          · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
            exact C.handle_subset_union k hk
        · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
          obtain ⟨b, ⟨q, ⟨hq, hψ⟩, rfl⟩⟩ := mem_iUnion.mp hk
          exact (hunion k b hq).mpr hψ }⟩

end BallHandleCycle

end GC.GraphManifold.Assembly
