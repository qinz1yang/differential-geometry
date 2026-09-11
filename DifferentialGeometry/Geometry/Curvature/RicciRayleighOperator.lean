import DifferentialGeometry.Geometry.Curvature.RicciRayleigh
import DifferentialGeometry.Geometry.Curvature.TraceNormalizedOperator
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Curvature

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem actual_metric_traceData
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (hB : OrthonormalBasisAt g x B) :
    RiemannFromRicci3DTraceDataAt g
      (-metricRicciAt g x) (-metricScalarAt g x)
      (metricRm04At g x) B := by
  have hLower :=
    rm04LowersRm13At_of_realizes
      g (leviCivitaConnectionOfMetric g)
      (metricRm13 g) (metricRm04 g)
      (metricCurvatureSections g).rm13Realizes
      (metricCurvatureSections g).rm04Realizes x
  have hcurv :
      AlgebraicCurvatureSymmetries3
        (standardRmCompAt B (metricRm04 g x)) :=
    algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (g := g) (Rm04 := metricRm04 g)
      (hRm04 := (metricCurvatureSections g).rm04Realizes) B
  have hinv : MetricInverseInBasis g x B delta3 :=
    orthonormal_invBasis3 g B hB
  have hRicFirst :
      RicciRealizesRm04FirstTraceAt
        (metricRicci g x) (metricRm04 g x) delta3 B :=
    ricciFirstTraceAt_of_rm13 g B delta3 hinv
      (metricRicci g x) (metricRm13 g x) (metricRm04 g x)
      ((metricCurvatureSections g).ricciRealizes x) hLower
  have hScalar :
      ScalarRealizesRicciTraceAt
        (metricScalarAt g x) (metricRicci g x) delta3 B := by
    unfold ScalarRealizesRicciTraceAt
    rw [metricRicci_apply]
    exact metricTracePair0SAt_eq_sum_basis
      g B delta3 hinv (metricRicciAt g x)
  simpa only [metricRicci_apply, metricRm04_apply] using
    traceDataOfFirst hB hcurv hRicFirst hScalar

private theorem actual_operator_matrix_in_ricci_frame
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (hB : OrthonormalBasisAt g x B)
    (r1 r2 r3 : ℝ)
    (hdiag : ∀ i j : Fin 3,
      metricRicciAt g x (vec2 (I := 𝓡 3) (B i) (B j)) =
        ricciDiag3 r1 r2 r3 i j) :
    curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x) =
      Matrix.diagonal
        ![metricScalarAt g x / 2 - r3,
          metricScalarAt g x / 2 - r2,
          metricScalarAt g x / 2 - r1] := by
  have hR : metricScalarAt g x = r1 + r2 + r3 := by
    change metricTracePair0SAt g (metricRicciAt g x) = _
    rw [metricTrace_comp_orthonormal B hB]
    simp [ricciScal3, hdiag, ricciDiag3, Fin.sum_univ_three, Fin.reduceEq]
  have htrace := actual_metric_traceData g x B hB
  have hneg (i j : Fin 3) :
      ricciCompAt B (-metricRicciAt g x) i j =
        -ricciDiag3 r1 r2 r3 i j := by
    rw [ricciCompAt_apply]
    change -metricRicciAt g x
      (vec2 (I := 𝓡 3) (B i) (B j)) = _
    rw [hdiag]
  ext i j
  change metricRm04At g x
    (vec4 (I := 𝓡 3)
      (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
      (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1)) = _
  rw [← rm04CompAt_apply,
    rm04Comp_displayedRiemannFromRicci3D_at htrace]
  simp only [hneg]
  fin_cases i <;> fin_cases j <;>
    norm_num [bivectorIndex3, Matrix.diagonal, ricciDiag3, delta3, hR,
      Matrix.cons_val_two,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;>
    ring

theorem curvatureOperatorLowerBoundAt_iff_neg_leastUpperRicciAt_le
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) (K : ℝ) :
    curvatureOperatorLowerBoundAt g x
        (metricAlgebraicCurvatureTensorAt g x) K ↔
      -leastUpperRicciAt g x ≤ K := by
  obtain ⟨B, r1, r2, r3, hB, h21, h32, hdiag,
    hmin, _hunit, _hvalue, _hleft, _hright⟩ :=
    exists_ordered_ricci_frame_leastUpperRicciAt g x
  have hmat := actual_operator_matrix_in_ricci_frame
    g x B hB r1 r2 r3 hdiag
  have hslot :
      metricRm04StandardAt g x (B 1) (B 2) (B 2) (B 1) =
        leastUpperRicciAt g x := by
    have hh := congrArg
      (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 2 2) hmat
    simpa [curvatureOperatorMatrixAt, bivectorIndex3,
      Matrix.diagonal, hmin, metricRm04StandardAt] using hh
  have hbase (n : ℕ) (c : Fin n → ℝ)
      (v w : Fin n → TangentSpace (𝓡 3) x) :
      leastUpperRicciAt g x *
          algebraicCurvatureIdentityQuadraticEval g c v w ≤
        algebraicCurvatureOperatorQuadraticEval
          (metricAlgebraicCurvatureTensorAt g x) c v w := by
    let a : Fin 3 → ℝ := fun i =>
      ∑ k : Fin n, c k *
        (B.repr (v k) (bivectorIndex3 i).1 *
            B.repr (w k) (bivectorIndex3 i).2 -
          B.repr (v k) (bivectorIndex3 i).2 *
            B.repr (w k) (bivectorIndex3 i).1)
    have hid :
        algebraicCurvatureIdentityQuadraticEval g c v w =
          ∑ i : Fin 3, a i ^ 2 :=
      algebraicCurvatureIdentityQuadraticEval_eq_bivectorNormSq
        g x c v w B hB
    have hquad :
        algebraicCurvatureOperatorQuadraticEval
            (metricAlgebraicCurvatureTensorAt g x) c v w =
          ∑ i : Fin 3, ∑ j : Fin 3, a i * a j *
            curvatureOperatorMatrixAt x B
              (metricAlgebraicCurvatureTensorAt g x) i j :=
      algebraicCurvatureOperatorQuadraticEval_eq_bivectorQuad
        x B (metricAlgebraicCurvatureTensorAt g x) c v w
    rw [hid, hquad, hmat, hmin]
    have h0 := mul_nonneg
      (sub_nonneg.mpr (h32.trans h21)) (sq_nonneg (a 0))
    have h1 := mul_nonneg
      (sub_nonneg.mpr h21) (sq_nonneg (a 1))
    norm_num [Fin.sum_univ_three, Matrix.diagonal, Matrix.cons_val_two, Fin.reduceEq]
    nlinarith only [h0, h1]
  constructor
  · intro hK
    have hh := hK 1 (fun _ => 1) (fun _ => B 1) (fun _ => B 2)
    simp only [algebraicCurvatureOperatorQuadraticEval,
      algebraicCurvatureIdentityQuadraticEval,
      Fin.sum_univ_one, one_mul] at hh
    change 0 ≤ metricRm04StandardAt g x (B 1) (B 2) (B 2) (B 1) +
      K * (g.inner x (B 1) (B 1) * g.inner x (B 2) (B 2) -
        g.inner x (B 1) (B 2) * g.inner x (B 2) (B 1)) at hh
    rw [hslot] at hh
    have h11 : g.inner x (B 1) (B 1) = 1 := by simpa [delta3] using hB 1 1
    have h22 : g.inner x (B 2) (B 2) = 1 := by simpa [delta3] using hB 2 2
    have h12 : g.inner x (B 1) (B 2) = 0 := by simpa [delta3, Fin.reduceEq] using hB 1 2
    have h21 : g.inner x (B 2) (B 1) = 0 := by simpa [delta3, Fin.reduceEq] using hB 2 1
    rw [h11, h22, h12, h21] at hh
    norm_num only [mul_one, zero_mul, sub_zero] at hh
    linarith only [hh]
  · intro hK n c v w
    have hb := hbase n c v w
    have hid :=
      algebraicCurvatureIdentityQuadraticEval_nonneg g x c v w B hB
    have hcoeff : 0 ≤ leastUpperRicciAt g x + K := by
      linarith only [hK]
    have hm := mul_nonneg hcoeff hid
    change 0 ≤
      algebraicCurvatureOperatorQuadraticEval
          (metricAlgebraicCurvatureTensorAt g x) c v w +
        K * algebraicCurvatureIdentityQuadraticEval g c v w
    nlinarith only [hb, hm]

theorem leastCurvatureOperatorEigenvalueAt_eq_leastUpperRicciAt
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) :
    leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x) =
      leastUpperRicciAt g x := by
  have hset :
      {K : ℝ | curvatureOperatorLowerBoundAt g x
        (metricAlgebraicCurvatureTensorAt g x) K} =
        Ici (-leastUpperRicciAt g x) := by
    ext K
    exact curvatureOperatorLowerBoundAt_iff_neg_leastUpperRicciAt_le g x K
  unfold leastCurvatureOperatorEigenvalueAt
  rw [hset, csInf_Ici, neg_neg]

theorem algebraicCurvatureOperatorQuadraticEval_pos_of_leastUpperRicciAt_pos
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (hpos : 0 < leastUpperRicciAt g x)
    (n : ℕ) (c : Fin n → ℝ)
    (v w : Fin n → TangentSpace (𝓡 3) x)
    (hvw : 0 < algebraicCurvatureIdentityQuadraticEval g c v w) :
    0 < algebraicCurvatureOperatorQuadraticEval
      (metricAlgebraicCurvatureTensorAt g x) c v w := by
  have hbound :=
    (curvatureOperatorLowerBoundAt_iff_neg_leastUpperRicciAt_le
      g x (-leastUpperRicciAt g x)).mpr le_rfl
  have hh := hbound n c v w
  have hp := mul_pos hpos hvw
  nlinarith only [hh, hp]

theorem iInf_rayleigh_traceNormalizedCurvatureOperatorAt_eq_two_mul_leastUpperRicciAt
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (hB : OrthonormalBasisAt g x B) :
    (⨅ v : {v : E3 // v ≠ 0},
      (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient v) =
        2 * leastUpperRicciAt g x := by
  rw [iInf_rayleigh_traceNormalizedCurvatureOperatorAt g x B hB,
    leastCurvatureOperatorEigenvalueAt_eq_leastUpperRicciAt]

end DifferentialGeometry.Geometry.Curvature
