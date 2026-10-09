import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v
variable {X : Type u} [MetricSpace X]

def HasEuclideanSplitting (p : X) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ (Y : Type v) (mY : MetricSpace Y), letI := mY
    ∃ q : Y, Nonempty (KleinerLottApprox p
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), q)) ε)

theorem hasEuclideanSplitting_zero (p : X) {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    HasEuclideanSplitting.{u, u} p 0 ε := by
  let e := (IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin 0)) X).symm
  exact ⟨X, inferInstance, p, ⟨e.toKleinerLottApprox (by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl) hε hεone⟩⟩

noncomputable def splittingRank (p : X) (β : ℕ → ℝ) (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => HasEuclideanSplitting.{u, v} p k (β k)) N

theorem splittingRank_le (p : X) (β : ℕ → ℝ) (N : ℕ) :
    splittingRank.{u, v} p β N ≤ N := by
  classical
  exact Nat.findGreatest_le N

theorem splittingRank_eq_iff (p : X) (β : ℕ → ℝ) (N k : ℕ) :
    splittingRank.{u, v} p β N = k ↔ k ≤ N ∧
      (k ≠ 0 → HasEuclideanSplitting.{u, v} p k (β k)) ∧
      ∀ j, k < j → j ≤ N → ¬ HasEuclideanSplitting.{u, v} p j (β j) := by
  classical
  exact Nat.findGreatest_eq_iff (P := fun j => HasEuclideanSplitting.{u, v} p j (β j))

theorem le_splittingRank (p : X) (β : ℕ → ℝ) {N k : ℕ} (hk : k ≤ N)
    (h : HasEuclideanSplitting.{u, v} p k (β k)) : k ≤ splittingRank.{u, v} p β N := by
  classical
  exact Nat.le_findGreatest hk h

theorem splittingRank_zero_iff (p : X) (β : ℕ → ℝ) (N : ℕ) :
    splittingRank.{u, v} p β N = 0 ↔
      ∀ j, 0 < j → j ≤ N → ¬ HasEuclideanSplitting.{u, v} p j (β j) := by
  classical
  exact Nat.findGreatest_eq_zero_iff (P := fun j => HasEuclideanSplitting.{u, v} p j (β j))

end GC.MetricGeometry
