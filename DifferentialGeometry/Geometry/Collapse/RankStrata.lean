import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

/-!
# Finite splitting strata at a positive pointwise scale

LC16 uses a finite maximum, with rank zero as a fallback and an exact product isometry.
No continuity of the scale or admission at a smaller tolerance is asserted.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace GC.MetricGeometry

universe u v

variable {M : Type u} [m : MetricSpace M]

def scaledSplittingRank (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (p : M) : ℕ :=
  @splittingRank.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p β 3

def scaledSplittingStratum (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ)
    (k : Fin 4) : Set M := {p | scaledSplittingRank.{u, v} ρ hρ β p = k.val}

def rankZeroProductIsometry (X : Type u) [MetricSpace X] :
    X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × X) :=
  (IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin 0)) X).symm

theorem scaledSplittingRank_le (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ)
    (p : M) : scaledSplittingRank.{u, v} ρ hρ β p ≤ 3 :=
  @splittingRank_le.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p β 3

theorem scaledSplittingRank_eq_iff {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
    {p : M} {k : ℕ} : scaledSplittingRank.{u, v} ρ hρ β p = k ↔ k ≤ 3 ∧
      (k ≠ 0 → @HasEuclideanSplitting.{u, v} M
        (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p k (β k)) ∧
      ∀ j, k < j → j ≤ 3 → ¬ @HasEuclideanSplitting.{u, v} M
        (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p j (β j) :=
  @splittingRank_eq_iff.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p β 3 k

theorem scaledSplittingStrata_cover (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) :
    (⋃ k : Fin 4, scaledSplittingStratum.{u, v} ρ hρ β k) = univ := by
  apply eq_univ_of_forall
  intro p
  exact mem_iUnion.mpr ⟨⟨scaledSplittingRank.{u, v} ρ hρ β p,
    Nat.lt_succ_of_le (scaledSplittingRank_le ρ hρ β p)⟩, rfl⟩

theorem scaledSplittingStrata_disjoint (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ)
    {j k : Fin 4} (hjk : j ≠ k) :
    Disjoint (scaledSplittingStratum.{u, v} ρ hρ β j)
      (scaledSplittingStratum.{u, v} ρ hρ β k) := by
  apply disjoint_left.mpr
  intro p hp hq
  exact hjk (Fin.ext (hp.symm.trans hq))

theorem splittingRank_le_two_of_no_three (p : M) (β : ℕ → ℝ)
    (h : ¬ HasEuclideanSplitting.{u, v} p 3 (β 3)) :
    splittingRank.{u, v} p β 3 ≤ 2 := by
  have hle := splittingRank_le.{u, v} p β 3
  have hne : splittingRank.{u, v} p β 3 ≠ 3 := by
    intro heq
    exact h (((splittingRank_eq_iff.{u, v} p β 3 3).mp heq).2.1 (by decide))
  omega

end GC.MetricGeometry
