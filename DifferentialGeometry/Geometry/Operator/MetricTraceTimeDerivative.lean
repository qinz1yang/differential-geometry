import DifferentialGeometry.Geometry.Metric.InverseTimeDerivative
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature (vec2)
open scoped Manifold ContDiff BigOperators

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem hasDerivWithinAt_metricTracePair0SAt
    {x : M} {t : ℝ} {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (gdot : Tensor0SSpace (I := I) 2 x)
    (T : ℝ → Tensor0SSpace (I := I) 2 x)
    (Tdot : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w) (gdot (vec2 (I := I) v w)) J t)
    (hT : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    HasDerivWithinAt (fun r => metricTracePair0SAt (I := I) (g r) (T r))
      (-(inner0S (I := I) (g t) x 2 gdot (T t)) +
        metricTracePair0SAt (I := I) (g t) Tdot) J t := by
  classical
  let basis := Module.finBasis ℝ (TangentSpace I x)
  let B := fun r => basisInvMetric (I := I) (g r) x basis
  let D := fun i j => gdot (vec2 (I := I) (basis i) (basis j))
  have hB (i j) := Metric.basisInvMetric_hasDerivWithinAt g x basis D J t
    (fun i j => hg (basis i) (basis j)) i j
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hB i j).mul (hT (vec2 (I := I) (basis i) (basis j)))))
  have he (r : ℝ) : metricTracePair0SAt (I := I) (g r) (T r) =
      ∑ i, ∑ j, B r i j * T r (vec2 (I := I) (basis i) (basis j)) :=
    metricTracePair0SAt_eq_sum_basis (g r) basis _ (basisInvMetric_isInverse (g r) x basis) (T r)
  change HasDerivWithinAt
    (fun r => ∑ i, ∑ j, B r i j * T r (vec2 (I := I) (basis i) (basis j))) _ J t at h
  rw [show (fun r => ∑ i, ∑ j, B r i j * T r (vec2 (I := I) (basis i) (basis j))) =
    (fun r => metricTracePair0SAt (I := I) (g r) (T r)) from funext fun r => (he r).symm] at h
  apply h.congr_deriv
  rw [inner0S_symm (g t) x gdot (T t),
    inner0S_two_eq_coord_direct (g t) x basis _ (basisInvMetric_isInverse (g t) x basis),
    metricTracePair0SAt_eq_sum_basis (g t) basis _ (basisInvMetric_isInverse (g t) x basis)]
  simp only [Finset.sum_add_distrib]
  congr 1
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [basisInvMetric_symm (g t) x basis b j]
  have hv (u v : TangentSpace I x) :
      vec2 (I := I) u v = fun a : Fin 2 => if a = 0 then u else v := by
    funext k
    fin_cases k <;> rfl
  simp only [D, hv]
  ring

theorem hasDerivAt_metricTracePair0SAt
    {x : M} {t : ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (gdot : Tensor0SSpace (I := I) 2 x)
    (T : ℝ → Tensor0SSpace (I := I) 2 x)
    (Tdot : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivAt (fun r => (g r).inner x v w) (gdot (vec2 (I := I) v w)) t)
    (hT : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => T r v) (Tdot v) t) :
    HasDerivAt (fun r => metricTracePair0SAt (I := I) (g r) (T r))
      (-(inner0S (I := I) (g t) x 2 gdot (T t)) +
        metricTracePair0SAt (I := I) (g t) Tdot) t :=
  (hasDerivWithinAt_metricTracePair0SAt (J := Set.univ) g gdot T Tdot
    (fun v w => (hg v w).hasDerivWithinAt) (fun v => (hT v).hasDerivWithinAt)).hasDerivAt
      (by simp)

theorem hasDerivWithinAt_metricTracePair0SAt_const
    {x : M} {t : ℝ} {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (gdot T : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w) (gdot (vec2 (I := I) v w)) J t) :
    HasDerivWithinAt (fun r => metricTracePair0SAt (I := I) (g r) T)
      (-(inner0S (I := I) (g t) x 2 gdot T)) J t := by
  have h := hasDerivWithinAt_metricTracePair0SAt g gdot (fun _ => T) 0 hg
    (fun v => hasDerivWithinAt_const t J (T v))
  simpa only [metricTracePair0SAt, inner0S, MetricFiberData.inner, map_zero, add_zero] using h

theorem hasDerivAt_metricTracePair0SAt_const
    {x : M} {t : ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (gdot T : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivAt (fun r => (g r).inner x v w) (gdot (vec2 (I := I) v w)) t) :
    HasDerivAt (fun r => metricTracePair0SAt (I := I) (g r) T)
      (-(inner0S (I := I) (g t) x 2 gdot T)) t :=
  (hasDerivWithinAt_metricTracePair0SAt_const (J := Set.univ) g gdot T
    (fun v w => (hg v w).hasDerivWithinAt)).hasDerivAt (by simp)

end DifferentialGeometry.Geometry.Operator

end
