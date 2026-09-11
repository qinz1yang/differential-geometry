import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Pullback.CovariantDerivative


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

section Slots

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance tensorJetSlotsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance tensorJetSlotsC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem tensorJet_succ_smooth_slots
    (g : SmoothRiemannianMetric I M) (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (a : ℕ) (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (V : Fin (a + 2) → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    covDerivOfField g A (a + 1) x (Fin.cons (X x) (fun q => V q x)) =
      mvfderiv (I := I) (fun y => covDerivOfField g A a y (fun q => V q y)) x (X x) -
        ∑ p : Fin (a + 2), covDerivOfField g A a x
          (Function.update (fun q => V q x) p
            ((leviCivitaConnectionOfMetric g) (fun y => V p y) x (X x))) := by
  rw [covDerivOfField_succ, metricCovDerivStep_apply, totalNabla0SFun_apply_section]
  exact nabla0SFun_eval_smooth_slots (leviCivitaConnectionOfMetric g) X V
    (covDerivOfField g A a) x

end Slots

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private local instance tensorJetSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance tensorJetSourceC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance tensorJetTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance tensorJetTargetC2 : IsManifold J 2 N :=
  IsManifold.of_le (n := ∞) (by decide)


theorem covDerivOfField_pullbackCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (B : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (hAB : ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      A x v = B (Phi x) (fun q => mfderiv I J Phi x (v q))) :
    ∀ a : ℕ, ∀ x : M, ∀ v : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (DifferentialGeometry.Diffeomorph.pullbackMetricCross g Phi) A a x v =
        covDerivOfField g B a (Phi x) (fun q => mfderiv I J Phi x (v q)) := by
  classical
  intro a
  induction a with
  | zero => exact hAB
  | succ a ih =>
    intro x slots
    obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
    let V : Fin (a + 2) → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
      fun q => (ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots q.succ)).choose
    have hV (q : Fin (a + 2)) : V q x = slots q.succ :=
      (ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots q.succ)).choose_spec
    let gp := DifferentialGeometry.Diffeomorph.pullbackMetricCross g Phi
    have hsmooth : covDerivOfField gp A (a + 1) x (Fin.cons (X x) (fun q => V q x)) =
        covDerivOfField g B (a + 1) (Phi x)
          (Fin.cons (pushFwdSectionCross Phi X (Phi x))
            (fun q => pushFwdSectionCross Phi (V q) (Phi x))) := by
      rw [tensorJet_succ_smooth_slots, tensorJet_succ_smooth_slots]
      apply congrArg₂ (fun r s : ℝ => r - s)
      · have heq : (fun y : M => covDerivOfField gp A a y (fun q => V q y)) =
            fun y => covDerivOfField g B a (Phi y)
              (fun q => pushFwdSectionCross Phi (V q) (Phi y)) := by
          funext y
          simpa only [gp, pushFwdSectionCross_apply_at_image] using ih y (fun q => V q y)
        have hf : MDifferentiableAt J 𝓘(ℝ, ℝ)
            (fun y : N => covDerivOfField g B a y
              (fun q => pushFwdSectionCross Phi (V q) y)) (Phi x) :=
          (tensor0SField_eval_smooth_slots_contMDiffAt (covDerivOfField g B a)
            (fun q => pushFwdSectionCross Phi (V q)) (Phi x)).mdifferentiableAt (by simp)
        rw [heq, mvfderiv_real_eq_mfderiv, mvfderiv_real_eq_mfderiv]
        have hchain := mfderiv_comp_apply (I := I) (I' := J) (I'' := 𝓘(ℝ, ℝ)) x hf
          (Phi.mdifferentiable (by decide) x) (X x)
        simpa only [Function.comp_def, pushFwdSectionCross_apply_at_image] using
          congrArg (NormedSpace.fromTangentSpace _) hchain
      · apply Finset.sum_congr rfl
        intro p _
        let covL := (leviCivitaConnectionOfMetric gp) (fun y => V p y) x (X x)
        let covR := (leviCivitaConnectionOfMetric g)
          (fun y => pushFwdSectionCross Phi (V p) y) (Phi x)
            (pushFwdSectionCross Phi X (Phi x))
        have hcov : mfderiv I J Phi x covL = covR := by
          have h := metricCov_pullbackCross g Phi (V p) x (X x)
          simpa only [covL, covR, gp, metricCov, pushFwdSectionCross_apply_at_image] using h
        have hslots : (fun q : Fin (a + 2) => mfderiv I J Phi x
            (Function.update (fun q => V q x) p covL q)) =
            Function.update (fun q => pushFwdSectionCross Phi (V q) (Phi x)) p covR := by
          funext q
          by_cases hqp : q = p
          · subst q
            simpa [Function.update] using hcov
          · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
            exact (pushFwdSectionCross_apply_at_image Phi (V q) x).symm
        have h := ih x (Function.update (fun q => V q x) p covL)
        rw [hslots] at h
        exact h
    have hslots : slots = Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) := by
      funext q
      refine Fin.cases ?_ (fun p => ?_) q
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ]
    have hpush : (fun q : Fin ((a + 1) + 2) => mfderiv I J Phi x (slots q)) =
        Fin.cons (mfderiv I J Phi x (slots 0))
          (fun q : Fin (a + 2) => mfderiv I J Phi x (slots q.succ)) := by
      funext q
      refine Fin.cases ?_ (fun p => ?_) q
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ]
    rw [hpush, hslots]
    simpa only [hX, hV, pushFwdSectionCross_apply_at_image, gp,
      Fin.cons_zero, Fin.cons_succ] using hsmooth


theorem tensor02CovDerivNormWith_pullbackCross [SigmaCompactSpace M]
    (gcov gnorm : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (B : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (hAB : ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      A x v = B (Phi x) (fun q => mfderiv I J Phi x (v q))) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith a A
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross gcov Phi)
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross gnorm Phi) x =
      tensor02CovDerivNormWith a B gcov gnorm (Phi x) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    (DifferentialGeometry.Diffeomorph.pullbackMetricCross gnorm Phi) x
  unfold tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field]
  congr 1
  exact normSq0S_pullbackCross_eval_of_orthonormal gnorm Phi x (a + 2) basis hON
    _ _ (covDerivOfField_pullbackCross gcov Phi A B hAB a x)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
