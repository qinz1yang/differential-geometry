import DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Constructions

namespace DifferentialGeometry.Topology.Handle

open Set

private theorem closure_closedBall_unit (n : ℕ) :
    closure (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  exact Metric.isClosed_closedBall.closure_eq

private theorem frontier_closedBall_unit (n : ℕ) :
    frontier (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  by_cases hn : n = 0
  · subst n
    have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1 =
        (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
      ext x
      have hx0 : ‖x‖ = (0 : ℝ) := by
        have hxeq : x = 0 := Subsingleton.elim x 0
        rw [hxeq, norm_zero]
      simp [Metric.closedBall, hx0]
    have hsphere : Metric.sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 =
        (∅ : Set (EuclideanSpace ℝ (Fin 0))) := by
      ext x
      constructor
      · intro hx
        have hx1 : dist x 0 = (1 : ℝ) := by simpa [Metric.sphere] using hx
        have hx0 : dist x 0 = (0 : ℝ) := by
          have hxeq : x = 0 := Subsingleton.elim x 0
          rw [hxeq, dist_self]
        linarith
      · intro hx
        exact False.elim hx
    rw [hball, hsphere]
    exact frontier_univ
  · haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
      haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      infer_instance
    exact frontier_closedBall' (0 : EuclideanSpace ℝ (Fin n)) 1

theorem frontier_handleSet (k l : ℕ) :
    frontier (handleSet k l) = attachingSet k l ∪ beltSet k l := by
  change frontier (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1) = attachingSet k l ∪ beltSet k l
  rw [frontier_prod_eq]
  rw [closure_closedBall_unit, frontier_closedBall_unit, frontier_closedBall_unit,
    closure_closedBall_unit]
  rw [Set.union_comm]
  simp [attachingSet, beltSet]

theorem range_toAmbient (k l : ℕ) :
    Set.range (toAmbient : StandardHandle k l →
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨by simp [Metric.closedBall, dist_zero_right],
      by simp [Metric.closedBall, dist_zero_right]⟩
  · intro hp
    rcases (show p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 from by simpa [mem_prod] using hp)
      with ⟨h1, h2⟩
    have h1' : ‖p.1‖ ≤ (1 : ℝ) := by simpa [Metric.closedBall, dist_zero_right] using h1
    have h2' : ‖p.2‖ ≤ (1 : ℝ) := by simpa [Metric.closedBall, dist_zero_right] using h2
    refine ⟨(⟨p.1, h1'⟩, ⟨p.2, h2'⟩), ?_⟩
    ext <;> rfl

theorem toAmbient_attachingRegion (k l : ℕ) :
    toAmbient '' attachingRegion k l =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : ‖(q.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by simpa [attachingRegion] using hq
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨by simp [Metric.sphere, dist_zero_right, hq'],
      by simp [Metric.closedBall, dist_zero_right]⟩
  · intro hp
    rcases (show p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 from by simpa [mem_prod] using hp)
      with ⟨hp1, hp2⟩
    have hp1' : ‖p.1‖ = (1 : ℝ) := by simpa [Metric.sphere, dist_zero_right] using hp1
    have hp2' : ‖p.2‖ ≤ (1 : ℝ) := by simpa [Metric.closedBall, dist_zero_right] using hp2
    refine ⟨(⟨p.1, le_of_eq hp1'⟩, ⟨p.2, hp2'⟩), ?_, ?_⟩
    · change ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1
      exact hp1'
    · ext <;> rfl

theorem toAmbient_beltRegion (k l : ℕ) :
    toAmbient '' beltRegion k l =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : ‖(q.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by simpa [beltRegion] using hq
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨by simp [Metric.closedBall, dist_zero_right],
      by simp [Metric.sphere, dist_zero_right, hq']⟩
  · intro hp
    rcases (show p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 from by simpa [mem_prod] using hp)
      with ⟨hp1, hp2⟩
    have hp1' : ‖p.1‖ ≤ (1 : ℝ) := by simpa [Metric.closedBall, dist_zero_right] using hp1
    have hp2' : ‖p.2‖ = (1 : ℝ) := by simpa [Metric.sphere, dist_zero_right] using hp2
    refine ⟨(⟨p.1, hp1'⟩, ⟨p.2, le_of_eq hp2'⟩), ?_, ?_⟩
    · change ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1
      exact hp2'
    · ext <;> rfl

theorem toAmbient_corner (k l : ℕ) :
    toAmbient '' corner k l =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ×ˢ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : ‖(q.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ ‖(q.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
      simpa [corner] using hq
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨by simp [Metric.sphere, dist_zero_right, hq'.1],
      by simp [Metric.sphere, dist_zero_right, hq'.2]⟩
  · intro hp
    rcases (show p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 from by simpa [mem_prod] using hp)
      with ⟨hp1, hp2⟩
    have hp1' : ‖p.1‖ = (1 : ℝ) := by simpa [Metric.sphere, dist_zero_right] using hp1
    have hp2' : ‖p.2‖ = (1 : ℝ) := by simpa [Metric.sphere, dist_zero_right] using hp2
    refine ⟨(⟨p.1, le_of_eq hp1'⟩, ⟨p.2, le_of_eq hp2'⟩), ?_, ?_⟩
    · change ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1
      exact And.intro hp1' hp2'
    · ext <;> rfl

theorem attachingSet_inter_beltSet (k l : ℕ) :
    attachingSet k l ∩ beltSet k l = cornerSet k l := by
  ext p
  constructor
  · intro hp
    rcases (show p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 from
        by simpa [attachingSet, mem_prod] using hp.1)
      with ⟨hp1, _⟩
    rcases (show p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 from
        by simpa [beltSet, mem_prod] using hp.2)
      with ⟨_, hp2⟩
    simpa [cornerSet] using And.intro hp1 hp2
  · intro hp
    rcases (show p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 from
        by simpa [cornerSet, mem_prod] using hp)
      with ⟨hp1, hp2⟩
    have hp1' : ‖p.1‖ = (1 : ℝ) := by simpa [Metric.sphere, dist_zero_right] using hp1
    have hp2' : ‖p.2‖ = (1 : ℝ) := by simpa [Metric.sphere, dist_zero_right] using hp2
    constructor
    · change p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1
      exact And.intro hp1 (Metric.mem_closedBall.mpr
        (by simpa [dist_zero_right] using (le_of_eq hp2')))
    · change p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1
      exact And.intro (Metric.mem_closedBall.mpr
        (by simpa [dist_zero_right] using (le_of_eq hp1'))) hp2

theorem frontier_range_toAmbient (k l : ℕ) :
    frontier (Set.range (toAmbient : StandardHandle k l →
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) =
      toAmbient '' attachingRegion k l ∪ toAmbient '' beltRegion k l := by
  rw [range_toAmbient, toAmbient_attachingRegion, toAmbient_beltRegion]
  change frontier (handleSet k l) = attachingSet k l ∪ beltSet k l
  exact frontier_handleSet k l

@[simp]
theorem mem_handleSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ handleSet k l ↔
      p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  simp [handleSet]

@[simp]
theorem mem_attachingSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ attachingSet k l ↔
      p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  simp [attachingSet]

@[simp]
theorem mem_beltSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ beltSet k l ↔
      p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  simp [beltSet]

@[simp]
theorem mem_cornerSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ cornerSet k l ↔
      p.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ∧
        p.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin l)) 1 := by
  simp [cornerSet]

end DifferentialGeometry.Topology.Handle
