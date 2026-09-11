import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem scalar_gradient_abs_le_nabla_rm
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    |g.inner x (gradientFun (I := I) g (metricScalarAt (I := I) g) x) v| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 5
          (totalNabla0SFun (I := I) 4 (metricCov (I := I) g)
            (metricRm04 (I := I) g) x)) * Real.sqrt (g.inner x v v) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  let delta := identityInvMetric
    (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))
  have hinv : MetricInverseInBasis (I := I) g x basis delta :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let nRic := totalNabla0SFun (I := I) 2 (metricCov (I := I) g)
    (metricRicci (I := I) g) x
  let nRm := totalNabla0SFun (I := I) 4 (metricCov (I := I) g)
    (metricRm04 (I := I) g) x
  have hRic : ∀ A B C, nRic (vec3 A B C) =
      ∑ i, nRm (vec5 A (basis i) B C (basis i)) := by
    intro A B C
    have h := levi_civita_covariant_ricci_eq_riemann_trace (I := I)
      g basis delta hinv A B C
    simpa [delta, identityInvMetric, diagonalInvMetric, nRic, nRm,
      metricCov, metricRicci, metricRm04] using h
  have hscalarFn :
      (fun y ↦ metricTracePair0SAt (I := I) g (metricRicci (I := I) g y)) =
        metricScalarAt (I := I) g := by
    funext y
    rw [metricScalarAt_def, metricRicci_apply]
  have hd := scalar_curvature_differential_eq_ricci_trace (I := I)
    g basis delta hinv v
  change differential1FormFun (I := I)
    (fun y ↦ metricTracePair0SAt (I := I) g (metricRicci (I := I) g y))
      x (fun _ ↦ v) = ∑ i, ∑ j, delta i j * nRic (vec3 v (basis i) (basis j)) at hd
  rw [hscalarFn, differential1FormFun_apply_eq_mvfderiv,
    ← inner_gradientFun g (metricScalarAt (I := I) g) x v] at hd
  have hd' : g.inner x (gradientFun (I := I) g (metricScalarAt (I := I) g) x) v =
      ∑ i, ∑ j, nRm (vec5 v (basis j) (basis i) (basis i) (basis j)) := by
    simpa [delta, identityInvMetric, diagonalInvMetric, hRic] using hd
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      |nRm (vec5 v (basis j) (basis i) (basis i) (basis j))| ≤
        Real.sqrt (normSq0S (I := I) g x 5 nRm) * Real.sqrt (g.inner x v v) := by
    have h := abs_apply_le_norm0S (I := I) g x 5 nRm
      (vec5 v (basis j) (basis i) (basis i) (basis j))
    simpa [vec5, Fin.prod_univ_succ, hON] using h
  rw [hd']
  calc
    |∑ i, ∑ j, nRm (vec5 v (basis j) (basis i) (basis i) (basis j))| ≤
        ∑ i, ∑ j, |nRm (vec5 v (basis j) (basis i) (basis i) (basis j))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace I x)),
          Real.sqrt (normSq0S (I := I) g x 5 nRm) * Real.sqrt (g.inner x v v) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * _) = _
      ring

end DifferentialGeometry.Geometry.Curvature
