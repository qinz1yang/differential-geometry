import DifferentialGeometry.Geometry.Metric.Approximation.RealAnchorAlignment

/-!
# Consumers of the one-dimensional anchor alignment (FC20, EGP03)

* The reflection `t ↦ -t` with an additive perturbation of size `δ` at one point is aligned with the
  sign `-1`.
* An exactly factorized rank-one splitting of `ℝ¹ × {pt}` (the identity), which is
  `SplittingCompatible` with itself, yields a sign alignment through
  `exists_sign_alignment_of_splittingCompatible_one_one`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

theorem neg_anchor_alignment_example :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ v : ℝ, |v| ≤ 1 → |-v - σ * v| ≤ 4 * 0 :=
  exists_sign_of_real_anchor_alignment (f := fun t => -t) (a := 1) one_pos (by simp)
    (fun v w _ _ => by rw [show -v - -w = -(v - w) by ring, abs_neg, sub_self, abs_zero])

/-- The identity splitting of `ℝ¹ × {pt}`. -/
def unitLineSplitting :
    KleinerLottApprox (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), ()))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), ())) (1 / 4) :=
  (IsometryEquiv.refl _).toKleinerLottApprox rfl (by norm_num) (by norm_num)

theorem unitLineSplitting_compatible :
    SplittingCompatible unitLineSplitting unitLineSplitting (1 / 2) := by
  let : Unique (EuclideanSpace ℝ (Fin (1 - 1))) :=
    { default := 0
      uniq := fun v => by ext i; exact absurd i.isLt (by simp) }
  apply splittingCompatible_of_exact_factorization unitLineSplitting unitLineSplitting le_rfl
    (by norm_num) (by norm_num)
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ (EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin (1 - 1)))).symm
    ((IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin (1 - 1))) Unit))
    rfl
  intro x _
  rfl

theorem unitLineSplitting_sign_alignment :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ ball (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)),
      ())) (1 / 2)⁻¹, |(unitLineSplitting.toFun x).fst 0| ≤ (1 / 2)⁻¹ / 2 →
        |(unitLineSplitting.toFun x).fst 0 - σ * (unitLineSplitting.toFun x).fst 0| ≤
          5 * (1 / 2) :=
  exists_sign_alignment_of_splittingCompatible_one_one unitLineSplitting unitLineSplitting
    unitLineSplitting_compatible

end GC.MetricGeometry
