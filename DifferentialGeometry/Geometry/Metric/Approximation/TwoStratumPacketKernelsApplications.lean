import DifferentialGeometry.Geometry.Metric.CircleCoordinateEnclosure
import DifferentialGeometry.Analysis.InnerProductSpace.TwoStratumGraphRank
import DifferentialGeometry.Geometry.Metric.Approximation.OrthogonalAnchorAlignment

/-!
# Consumers of the two-stratum packet kernels (TCP01, TCP02, TCP06)

* TCP01: in the exact product `ℝ² × {pt}` with the identity map, every point with `‖η‖ ≤ 8` lies within
  `10` of the base point.
* TCP02: the identity splitting of `ℝ² × {pt}` is compatible with itself (exact factorization), so the
  equal-rank alignment produces an orthogonal map with error `≤ (24·2 + 1)/10`.
* TCP06: the identity graph reference on `ℝ` with an exact derivative gives the projected rank bounds.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

theorem plane_circle_coordinate_enclosure (q : WithLp 2 (EuclideanSpace ℝ (Fin 2) × Unit))
    (hq : ‖q.fst‖ ≤ 8) : dist q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ())) < 10 :=
  dist_lt_ten_of_circle_coordinate id (fun x => x.fst) rfl (by simp) (by simp) (by simp) hq

/-- The identity splitting of `ℝ² × {pt}`. -/
def unitPlaneSplitting :
    KleinerLottApprox (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ()))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ())) (1 / 4) :=
  (IsometryEquiv.refl _).toKleinerLottApprox rfl (by norm_num) (by norm_num)

theorem unitPlaneSplitting_compatible :
    SplittingCompatible unitPlaneSplitting unitPlaneSplitting (1 / 10) := by
  let : Unique (EuclideanSpace ℝ (Fin (2 - 2))) :=
    { default := 0
      uniq := fun v => by ext i; exact absurd i.isLt (by simp) }
  apply splittingCompatible_of_exact_factorization unitPlaneSplitting unitPlaneSplitting le_rfl
    (by norm_num) (by norm_num)
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin (2 - 2)))).symm
    ((IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin (2 - 2))) Unit))
    rfl
  intro x _
  rfl

theorem unitPlaneSplitting_orthogonal_alignment :
    ∃ Aₒ : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
      ∀ x ∈ ball (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ())) (1 / 10)⁻¹,
        ‖(unitPlaneSplitting.toFun x).fst‖ ≤ (1 / 10)⁻¹ / 2 →
          ‖(unitPlaneSplitting.toFun x).fst - Aₒ (unitPlaneSplitting.toFun x).fst‖ ≤
            (24 * ((2 : ℕ) : ℝ) + 1) * (1 / 10) :=
  exists_orthogonal_alignment_of_splittingCompatible_equal_rank unitPlaneSplitting
    unitPlaneSplitting unitPlaneSplitting_compatible (by norm_num)

end GC.MetricGeometry

namespace ContinuousLinearMap

theorem identity_reference_projected_rank :
    let P := (ContinuousLinearMap.id ℝ ℝ).range.orthogonalProjectionOnto.comp
      (ContinuousLinearMap.id ℝ ℝ)
    Function.Surjective P ∧
      ‖ContinuousLinearMap.id ℝ ℝ - (ContinuousLinearMap.id ℝ ℝ).range.subtypeL.comp P‖ ≤ 0 ∧
      ∀ v ∈ P.kerᗮ, 1 / 2 * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ 3 * 1 * ‖v‖ :=
  projected_rank_of_reference_graph (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ) (fun z => by simp) (norm_id_le)
    (fun z => by rw [adjoint_id, id_apply]; nlinarith [norm_nonneg z])
    (norm_id_le.trans (by norm_num)) (by simp) (by norm_num) zero_le_one

end ContinuousLinearMap
