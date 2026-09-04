import DifferentialGeometry.Geometry.Exponential.LocalAddition.SecondDerivativeBlocks
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

noncomputable def traceRemainder {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) : E :=
  ∑ i, ∑ j, c i j • secondDerivativeRemainder (I := I) g p v z (e i) (e j)

noncomputable def traceSecondDerivative {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) : E :=
  ∑ i, ∑ j, c i j •
    fderiv ℝ
      (fderiv ℝ (fun x ↦ targetCoordinates (I := I) g p (x, v x))) z
      (e i) (e j)

theorem traceSecondDerivative_eq {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E)
    (hF : ContDiffAt ℝ 2 (targetCoordinates (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z) :
    traceSecondDerivative (I := I) g p v z c e =
      partialFDeriv₂ (targetCoordinates (I := I) g p) z (v z)
          (∑ i, ∑ j, c i j •
            fderiv ℝ (fderiv ℝ v) z (e i) (e j)) +
        traceRemainder (I := I) g p v z c e := by
  classical
  simp only [traceSecondDerivative, traceRemainder]
  simp_rw [secondDerivative_section_eq (I := I) g p v z _ _ hF hv]
  simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul]

theorem traceRemainder_eq_blocks {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) :
    traceRemainder (I := I) g p v z c e =
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (e i, 0) (e j, 0)) +
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (e i, 0) (0, fderiv ℝ v z (e j))) +
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z (e i)) (e j, 0)) +
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z (e i)) (0, fderiv ℝ v z (e j))) := by
  classical
  simp only [traceRemainder]
  simp_rw [secondDerivativeRemainder_eq_blocks (I := I) g p v z _ _]
  simp only [smul_add, Finset.sum_add_distrib]

theorem inverse_partialFDeriv₂_traceSecondDerivative_sub_remainder {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E)
    (hF : ContDiffAt ℝ 2 (targetCoordinates (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z)
    (hJ : (partialFDeriv₂
      (targetCoordinates (I := I) g p) z (v z)).IsInvertible) :
    (partialFDeriv₂ (targetCoordinates (I := I) g p) z (v z)).inverse
        (traceSecondDerivative (I := I) g p v z c e -
          traceRemainder (I := I) g p v z c e) =
      ∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ v) z (e i) (e j) := by
  rw [traceSecondDerivative_eq (I := I) g p v z c e hF hv,
    add_sub_cancel_right]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self hJ _

theorem exists_traceSecondDerivative_recovery_on_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r > 0,
      IsCompact (Metric.closedBall (zeroCoordinates (I := I) p) r) ∧
      ContinuousOn
        (fun w : E × E ↦
          (partialFDeriv₂
            (targetCoordinates (I := I) g p) w.1 w.2).inverse)
        (Metric.closedBall (zeroCoordinates (I := I) p) r) ∧
      ∀ (n : ℕ) (v : E → E) (z : E)
          (c : Fin n → Fin n → ℝ) (e : Fin n → E),
        (z, v z) ∈ Metric.closedBall (zeroCoordinates (I := I) p) r →
        ContDiffAt ℝ 2 (targetCoordinates (I := I) g p) (z, v z) →
        ContDiffAt ℝ 2 v z →
        (partialFDeriv₂
            (targetCoordinates (I := I) g p) z (v z)).inverse
            (traceSecondDerivative (I := I) g p v z c e -
              traceRemainder (I := I) g p v z c e) =
          ∑ i, ∑ j, c i j •
            fderiv ℝ (fderiv ℝ v) z (e i) (e j) := by
  obtain ⟨r, hr, hcompact, hinv, hcont⟩ :=
    exists_partialFDeriv₂_targetCoordinates_inverse_on_closedBall (I := I) g p
  refine ⟨r, hr, hcompact, hcont, ?_⟩
  intro n v z c e hstate hF hv
  exact inverse_partialFDeriv₂_traceSecondDerivative_sub_remainder (I := I) g p v z c e hF hv
    (hinv (z, v z) hstate)

end DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

end
