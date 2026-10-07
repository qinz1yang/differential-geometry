import DifferentialGeometry.Topology.Ends.FiniteEnds
import Mathlib.Data.ENat.Lattice

noncomputable section

namespace DifferentialGeometry.Geometry.Topology

def endCount (X : Type*) [TopologicalSpace X] : ℕ∞ :=
  ⨆ k : ℕ, ⨆ (_ : HasAtLeastEnds X k), (k : ℕ∞)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp] theorem hasAtLeastEnds_zero : HasAtLeastEnds X 0 :=
  ⟨∅, isCompact_empty, Fin.elim0, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem HasAtLeastEnds.le_endCount {k : ℕ} (h : HasAtLeastEnds X k) :
    (k : ℕ∞) ≤ endCount X :=
  le_iSup_of_le k (le_iSup_of_le h le_rfl)

theorem endCount_le_natCast_iff (k : ℕ) :
    endCount X ≤ (k : ℕ∞) ↔ ¬ HasAtLeastEnds X (k + 1) := by
  constructor
  · intro h hk
    exact Nat.not_succ_le_self k
      (ENat.natCast_le_natCast.mp (hk.le_endCount.trans h))
  · intro h
    apply iSup_le fun m => iSup_le fun hm => ?_
    apply ENat.natCast_le_natCast.mpr
    by_contra hle
    exact h (hm.mono (Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)))

theorem natCast_le_endCount_iff (k : ℕ) :
    (k : ℕ∞) ≤ endCount X ↔ HasAtLeastEnds X k := by
  constructor
  · intro h
    cases k with
    | zero => exact hasAtLeastEnds_zero
    | succ k =>
      by_contra hk
      have hle := (endCount_le_natCast_iff (X := X) k).mpr hk
      exact Nat.not_succ_le_self k (ENat.natCast_le_natCast.mp (h.trans hle))
  · exact HasAtLeastEnds.le_endCount

theorem endCount_lt_natCast_iff (k : ℕ) :
    endCount X < (k : ℕ∞) ↔ ¬ HasAtLeastEnds X k := by
  rw [← not_le, natCast_le_endCount_iff]

theorem endCount_eq_natCast_iff (k : ℕ) :
    endCount X = (k : ℕ∞) ↔ HasExactlyEnds X k := by
  constructor
  · intro h
    exact ⟨(natCast_le_endCount_iff k).mp h.ge, (endCount_le_natCast_iff k).mp h.le⟩
  · rintro ⟨hlower, hupper⟩
    exact le_antisymm ((endCount_le_natCast_iff k).mpr hupper) hlower.le_endCount

theorem endCount_eq_top_iff : endCount X = ⊤ ↔ ∀ k : ℕ, HasAtLeastEnds X k := by
  constructor
  · intro h k
    apply (natCast_le_endCount_iff k).mp
    rw [h]
    exact le_top
  · intro h
    apply top_unique
    rw [← ENat.iSup_natCast]
    exact iSup_le fun k => (h k).le_endCount

theorem endCount_lt_top_iff : endCount X < ⊤ ↔ ∃ k : ℕ, HasExactlyEnds X k := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne
    exact ⟨k, (endCount_eq_natCast_iff k).mp hk.symm⟩
  · rintro ⟨k, hk⟩
    rw [(endCount_eq_natCast_iff k).mpr hk]
    exact ENat.natCast_lt_top k

theorem endCount_homeomorph (e : X ≃ₜ Y) : endCount X = endCount Y := by
  simp only [endCount, hasAtLeastEnds_homeomorph_iff e]

@[simp] theorem endCount_eq_zero_of_compact [CompactSpace X] : endCount X = 0 := by
  apply le_antisymm _ bot_le
  exact (endCount_le_natCast_iff 0).mpr (not_hasAtLeastEnds_of_compact (by decide))

end DifferentialGeometry.Geometry.Topology
