import DifferentialGeometry.Geometry.Curvature.ConstantSectional
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import DifferentialGeometry.Geometry.Metric.Evaluation
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

set_option autoImplicit false
noncomputable section

open Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g : SmoothRiemannianMetric I M) (κ : ℝ)
  (hsec : ∀ (x : M) (u v : TangentSpace I x),
    metricRm04StandardAt g x u v v u =
      κ * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2))

include hsec

private theorem metricRm04_eval_of_constant_sectional (x : M)
    (v : Fin 4 → TangentSpace I x) :
    metricRm04 g x v =
      κ * (g.inner x (v 0) (v 3) * g.inner x (v 1) (v 2) -
        g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3)) := by
  have hv : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> rfl
  have h := metricRm04StandardAt_eq_of_constant_sectional_numerator
    g x κ (hsec x) (v 0) (v 1) (v 2) (v 3)
  rw [metricRm04StandardAt_apply, hv] at h
  simpa only [metricRm04_apply] using h

set_option backward.isDefEq.respectTransparency false in
private theorem covStep_metricRm04_eval_eq_zero_of_constant_sectional
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (V : Fin 4 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covStep g 4 (metricRm04 g) x (Fin.cons (X x) (fun i => V i x)) = 0 := by
  classical
  let b (i j : Fin 4) : M → ℝ := fun y => g.inner y (V i y) (V j y)
  let d (i : Fin 4) : TangentSpace I x :=
    (leviCivitaConnectionOfMetric g) (V i) x (X x)
  have hb (i j : Fin 4) : MDifferentiableAt I 𝓘(ℝ, ℝ) (b i j) x :=
    (contMDiff_metric_inner g (V i) (V j)).mdifferentiableAt (by simp)
  have hdb (i j : Fin 4) : mvfderiv I (b i j) x (X x) =
      g.inner x (d i) (V j x) + g.inner x (V i x) (d j) := by
    exact (leviCivitaConnectionOfMetric_isMetricCompatible g).apply
      (V i).mdifferentiableAt (V j).mdifferentiableAt (X x)
  have hD : mvfderiv I
      (fun y => κ * (b 0 3 y * b 1 2 y - b 0 2 y * b 1 3 y)) x (X x) =
      κ * ((g.inner x (d 0) (V 3 x) + g.inner x (V 0 x) (d 3)) * b 1 2 x +
        b 0 3 x * (g.inner x (d 1) (V 2 x) + g.inner x (V 1 x) (d 2)) -
        (g.inner x (d 0) (V 2 x) + g.inner x (V 0 x) (d 2)) * b 1 3 x -
        b 0 2 x * (g.inner x (d 1) (V 3 x) + g.inner x (V 1 x) (d 3))) := by
    have hs := (hb 0 3).mul (hb 1 2)
    have ht := (hb 0 2).mul (hb 1 3)
    change (mvfderiv I
      (fun y => κ * (((b 0 3 * b 1 2) - (b 0 2 * b 1 3)) y)) x) (X x) = _
    rw [DifferentialGeometry.mvfderiv_const_mul I κ (hs.sub ht)]
    change κ * mvfderiv I
      ((b 0 3 * b 1 2) - (b 0 2 * b 1 3)) x (X x) = _
    rw [mvfderiv_sub hs ht, mvfderiv_mul (hb 0 3) (hb 1 2),
      mvfderiv_mul (hb 0 2) (hb 1 3)]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, hdb]
    ring
  rw [covStep_eval_smooth_slots]
  simp_rw [metricRm04_eval_of_constant_sectional g κ hsec]
  change mvfderiv I (fun y => κ * (b 0 3 y * b 1 2 y - b 0 2 y * b 1 3 y))
      x (X x) - _ = 0
  rw [hD]
  simp [Fin.sum_univ_four, Function.update, b, d]
  ring

/-- A metric with one constant sectional numerator coefficient has parallel
curvature. The statement remains valid for manifolds with boundary. -/
theorem covStep_metricRm04_eq_zero_of_constant_sectional :
    covStep g 4 (metricRm04 g) = 0 := by
  classical
  refine DFunLike.ext _ _ (fun x => ?_)
  refine tensor0SSpace_ext 5 x (fun slots => ?_)
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
  choose V hV using fun i : Fin 4 =>
    ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots i.succ)
  have hslots : Fin.cons (X x) (fun i : Fin 4 => V i x) = slots := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hX
    · exact hV j
  have hz := covStep_metricRm04_eval_eq_zero_of_constant_sectional g κ hsec X V x
  rw [hslots] at hz
  exact hz

/-- Every positive-order actual covariant curvature tensor vanishes for a
metric with constant sectional curvature. -/
theorem curvCovDeriv_succ_eq_zero_of_constant_sectional (k : ℕ) :
    curvCovDeriv g (k + 1) = 0 := by
  induction k with
  | zero =>
      rw [curvCovDeriv_succ, curvStep_eq_covStep]
      exact covStep_metricRm04_eq_zero_of_constant_sectional g κ hsec
  | succ k ih =>
      rw [curvCovDeriv_succ, ih, curvStep_eq_covStep, covStep_zero]

theorem curvDerivNormSq_succ_eq_zero_of_constant_sectional (k : ℕ) (x : M) :
    curvDerivNormSq (k + 1) g x = 0 := by
  rw [curvDerivNormSq]
  have hz : curvCovDeriv g (k + 1) x = 0 := by
    rw [curvCovDeriv_succ_eq_zero_of_constant_sectional g κ hsec k]
    rfl
  rw [hz]
  exact (normSq0S_eq_zero_iff g x ((k + 1) + 4) 0).mpr rfl

theorem curvDerivNorm_succ_eq_zero_of_constant_sectional (k : ℕ) (x : M) :
    curvDerivNorm (k + 1) g x = 0 := by
  rw [curvDerivNorm, curvDerivNormSq_succ_eq_zero_of_constant_sectional g κ hsec,
    Real.sqrt_zero]

end DifferentialGeometry.CheegerGromovCompactness
