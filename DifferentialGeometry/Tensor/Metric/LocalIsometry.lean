import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.OpenRestriction
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private theorem cov_step_pullback_sections (h : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J⟯ N) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := J) (M := N) ∞ r)
    (hAB : ∀ (y : M) (v : Fin r → TangentSpace I y),
      A y v = B (Φ y) (fun i => mfderiv I J (Φ : M → N) y (v i)))
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (V : Fin r → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    covStep (Diffeomorph.pullbackMetricCross h Φ) r A x (Fin.cons (X x) (fun i => V i x)) =
      covStep h r B (Φ x) (Fin.cons (pushFwdSectionCross Φ X (Φ x))
        (fun i => pushFwdSectionCross Φ (V i) (Φ x))) := by
  classical
  rw [covStep_eval_smooth_slots, covStep_eval_smooth_slots]
  apply congrArg₂ (· - ·)
  · have heval : (fun y : M => A y (fun i => V i y)) =
        (fun z : N => B z (fun i => pushFwdSectionCross Φ (V i) z)) ∘ Φ := by
      funext y
      simpa only [Function.comp_apply, pushFwdSectionCross_apply_at_image] using
        hAB y (fun i => V i y)
    rw [heval]
    have hsmooth := tensor0SField_eval_smooth_slots_contMDiffAt B
      (fun i => pushFwdSectionCross Φ (V i)) (Φ x)
    rw [pushFwdSectionCross_apply_at_image]
    rw [mvfderiv_real_eq_mfderiv, mvfderiv_real_eq_mfderiv]
    exact congrArg (NormedSpace.fromTangentSpace _)
      (mfderiv_comp_apply x (hsmooth.mdifferentiableAt (by simp))
        (Φ.mdifferentiable (by decide) x) (X x))
  · apply Finset.sum_congr rfl
    intro i _
    rw [hAB]
    apply congrArg (B (Φ x))
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      simpa only [metricCov, pushFwdSectionCross_apply_at_image] using
        metricCov_pullbackCross h Φ (V i) x (X x)
    · simp only [Function.update_of_ne hji, pushFwdSectionCross_apply_at_image]

theorem cov_step_pullback (h : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J⟯ N) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := J) (M := N) ∞ r)
    (hAB : ∀ (y : M) (v : Fin r → TangentSpace I y),
      A y v = B (Φ y) (fun i => mfderiv I J (Φ : M → N) y (v i)))
    (x : M) (v : Fin (r + 1) → TangentSpace I x) :
    covStep (Diffeomorph.pullbackMetricCross h Φ) r A x v =
      covStep h r B (Φ x) (fun i => mfderiv I J (Φ : M → N) x (v i)) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
  choose V hV using fun i : Fin r => ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v i.succ)
  have hv : Fin.cons (X x) (fun i => V i x) = v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hX
    · exact hV j
  have hpush : Fin.cons (pushFwdSectionCross Φ X (Φ x))
      (fun i => pushFwdSectionCross Φ (V i) (Φ x)) =
        (fun i => mfderiv I J (Φ : M → N) x (v i)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero, pushFwdSectionCross_apply_at_image] using
        congrArg (mfderiv I J (Φ : M → N) x) hX
    · simpa only [Fin.cons_succ, pushFwdSectionCross_apply_at_image] using
        congrArg (mfderiv I J (Φ : M → N) x) (hV j)
  simpa only [hv, hpush] using cov_step_pullback_sections h Φ A B hAB X V x

theorem iter_cov_pullback (h : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J⟯ N) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := J) (M := N) ∞ r)
    (hAB : ∀ (y : M) (v : Fin r → TangentSpace I y),
      A y v = B (Φ y) (fun i => mfderiv I J (Φ : M → N) y (v i))) (k : ℕ) :
    ∀ (x : M) (v : Fin (r + k) → TangentSpace I x),
      iterCov (Diffeomorph.pullbackMetricCross h Φ) r A k x v =
        iterCov h r B k (Φ x) (fun i => mfderiv I J (Φ : M → N) x (v i)) := by
  induction k with
  | zero => exact hAB
  | succ k ih =>
    exact cov_step_pullback h Φ (iterCov (Diffeomorph.pullbackMetricCross h Φ) r A k)
      (iterCov h r B k) ih

theorem iter_cov_of_metric_isometry (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = h.inner (Φ y) (mfderiv I J (Φ : M → N) y v)
        (mfderiv I J (Φ : M → N) y w)) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := J) (M := N) ∞ r)
    (hAB : ∀ (y : M) (v : Fin r → TangentSpace I y),
      A y v = B (Φ y) (fun i => mfderiv I J (Φ : M → N) y (v i)))
    (k : ℕ) (x : M) (v : Fin (r + k) → TangentSpace I x) :
    iterCov g r A k x v =
      iterCov h r B k (Φ x) (fun i => mfderiv I J (Φ : M → N) x (v i)) := by
  have hg : g = Diffeomorph.pullbackMetricCross h Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  rw [hg]
  exact iter_cov_pullback h Φ A B hAB k x v

omit [CompleteSpace E] [T2Space M] in
private theorem restrict_open_apply {r : ℕ} (U : TopologicalSpace.Opens M)
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (x : U) (v : Fin r → TangentSpace I x) :
    restrictOpen0S r (V := U) A x v = A (x : M) v := rfl

theorem cov_step_restrict_open (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r) :
    covStep (g.restrictOpen U) r (restrictOpen0S r (V := U) A) =
      restrictOpen0S (r + 1) (V := U) (covStep g r A) := by
  classical
  apply DFunLike.ext
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  change covStep (g.restrictOpen U) r (restrictOpen0S r (V := U) A) x v =
    covStep g r A (x : M) v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (v 0)
  choose V hV using fun i : Fin r => ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (v i.succ)
  have hv : Fin.cons (X (x : M)) (fun i => V i (x : M)) = v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hX
    · exact hV j
  have hs : covStep (g.restrictOpen U) r (restrictOpen0S r (V := U) A) x
      (Fin.cons (restrictOpenTangentSection U X x)
        (fun i => restrictOpenTangentSection U (V i) x)) =
      covStep g r A (x : M) (Fin.cons (X (x : M)) (fun i => V i (x : M))) := by
    rw [covStep_eval_smooth_slots, covStep_eval_smooth_slots]
    apply congrArg₂ (· - ·)
    · simp only [restrictOpenTangentSection_apply]
      change mvfderiv (I := I) (fun y : U => A (y : M) (fun i => V i (y : M)))
        x (X (x : M)) = _
      exact mvfderiv_restrictOpen U (fun y : M => A y (fun i => V i y)) x (X (x : M))
        ((tensor0SField_eval_smooth_slots_contMDiffAt A V (x : M)).mdifferentiableAt
          (by simp))
    · apply Finset.sum_congr rfl
      intro i _
      rw [restrict_open_apply]
      apply congrArg (A (x : M))
      simp only [restrictOpenTangentSection_apply]
      have hcov := metricCov_restrictOpen_globalSection g U (V i) x (X (x : M))
      have hfield : restrictOpenTangentField U (fun y : M => V i y) =
          (fun y : U => V i (y : M)) := by
        funext y
        exact restrictOpenTangentField_apply U (fun z : M => V i z) y
      rw [hfield] at hcov
      simp only [metricCov] at hcov
      exact congrArg (fun z => Function.update (fun b => V b (x : M)) i z) hcov
  have hleft : Fin.cons (restrictOpenTangentSection U X x)
      (fun i => restrictOpenTangentSection U (V i) x) = v := by
    simpa only [restrictOpenTangentSection_apply] using hv
  rw [hleft] at hs
  exact hs.trans (congrArg (covStep g r A (x : M)) hv)

theorem iter_cov_restrict_open (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ) :
    iterCov (g.restrictOpen U) r (restrictOpen0S r (V := U) A) k =
      restrictOpen0S (r + k) (V := U) (iterCov g r A k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterCov_succ, ih, cov_step_restrict_open]
    rfl

theorem iter_cov_of_metric_isometry_on_opens (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (Φ : U ≃ₘ⟮I, J⟯ V)
    (hmetric : ∀ (y : U) (v w : TangentSpace I y),
      g.inner (y : M) v w = h.inner (Φ y : N) (mfderiv I J (Φ : U → V) y v)
        (mfderiv I J (Φ : U → V) y w)) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r)
    (B : Tensor0SField (I := J) (M := N) ∞ r)
    (hAB : ∀ (y : U) (v : Fin r → TangentSpace I y),
      A (y : M) v = B (Φ y : N) (fun i => mfderiv I J (Φ : U → V) y (v i)))
    (k : ℕ) (x : U) (v : Fin (r + k) → TangentSpace I x) :
    iterCov g r A k (x : M) v =
      iterCov h r B k (Φ x : N) (fun i => mfderiv I J (Φ : U → V) x (v i)) := by
  have hlocal := iter_cov_of_metric_isometry (g.restrictOpen U) (h.restrictOpen V) Φ
    hmetric (restrictOpen0S r (V := U) A) (restrictOpen0S r (V := V) B) hAB k x v
  rw [iter_cov_restrict_open, iter_cov_restrict_open] at hlocal
  exact hlocal

end DifferentialGeometry.Geometry.Tensor
