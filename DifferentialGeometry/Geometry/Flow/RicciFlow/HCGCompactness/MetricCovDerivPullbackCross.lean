import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ScalarGradient

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Cross-model pullback naturality for metric covariant-derivative towers

This file is the cross-model companion of `MetricCovDerivPullback`.  It keeps
the base field metric-valued: simultaneous pullback of the metric being
differentiated and the reference metric transports the complete covariant
derivative tower and its pointwise norm.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Connection.CovariantDerivative
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F] [CompleteSpace F] [NeZero (Module.finrank Real F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private lemma infty_ne_zeroC : (∞ : WithTop ℕ∞) ≠ 0 := by decide

private theorem extDerivFun_comp_diffeomorphCross
    (f : N → Real) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M)
    (v : TangentSpace I x)
    (hf : MDifferentiableAt J 𝓘(Real, Real) f (Phi x)) :
    extDerivFun (I := I) (fun y : M => f (Phi y)) x v =
      extDerivFun (I := J) f (Phi x)
        (mfderiv I J (Phi : M → N) x v) := by
  have hPhi : MDifferentiableAt I J (Phi : M → N) x :=
    Phi.mdifferentiable infty_ne_zeroC x
  rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
  simpa [Function.comp_def] using
    mfderiv_comp_apply (I := I) (I' := J) (I'' := 𝓘(Real, Real)) x hf hPhi v

private theorem metricCovDeriv_succ_eval_smooth_slotsC
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace Real E']
    [FiniteDimensional Real E'] [CompleteSpace E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners Real E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [SigmaCompactSpace M'] [T2Space M'] [IsManifold I' 1 M'] [IsManifold I' 2 M']
    [IsManifold I' ((∞ : WithTop ℕ∞) + 1) M'] [BoundarylessManifold I' M']
    (h gRef : SmoothRiemannianMetric I' M') (a : Nat)
    (X : ContMDiffSection I' E' (∞ : WithTop ℕ∞)
      (TangentSpace I' : M' → Type _))
    (V : Fin (a + 2) → ContMDiffSection I' E' (∞ : WithTop ℕ∞)
      (TangentSpace I' : M' → Type _))
    (x : M') :
    metricCovDeriv (I := I') h gRef (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I')
          (fun y : M' => metricCovDeriv (I := I') h gRef a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          metricCovDeriv (I := I') h gRef a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I') gRef)
                  (fun y : M' => V p y) x) (X x))) := by
  rw [metricCovDeriv_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E') (H := H') (I := I') (M := M')
    (leviCivitaConnectionOfMetric (I := I') gRef) X V
    (metricCovDeriv (I := I') h gRef a) x

/-- Cross-model naturality of the full background metric-covariant derivative
tower under simultaneous pullback of both metrics. -/
theorem metricCovDeriv_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J 2 N]
    [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (h gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) :
    ∀ a : Nat, ∀ x : M, ∀ slots : Fin (a + 2) → TangentSpace I x,
      metricCovDeriv (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) h Phi)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) a x slots =
        metricCovDeriv (I := J) h gRef a (Phi x)
          (fun q : Fin (a + 2) => mfderiv I J (Phi : M → N) x (slots q)) := by
  classical
  intro a
  induction a with
  | zero =>
      intro x slots
      change
        Tensor0SBundle.metricTensorField (I := I) (M := M)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) h Phi) x slots =
          Tensor0SBundle.metricTensorField (I := J) (M := N) h (Phi x)
            (fun q : Fin (0 + 2) => mfderiv I J (Phi : M → N) x (slots q))
      rw [Tensor0SBundle.metricTensorField_apply, Tensor0SBundle.metricTensorField_apply,
        Diffeomorph.pullbackMetricCross_inner]
  | succ a ih =>
      intro x slots
      obtain ⟨X, hX⟩ :=
        ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
          (n := (⊤ : ℕ∞)) x (slots 0)
      let V : Fin (a + 2) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
        fun q =>
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) x (slots q.succ)).choose
      have hV : ∀ q : Fin (a + 2), V q x = slots q.succ := by
        intro q
        exact
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) x (slots q.succ)).choose_spec
      have hsmooth :
          metricCovDeriv (I := I)
              (Diffeomorph.pullbackMetricCross (I := I) (J := J) h Phi)
              (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) (a + 1) x
              (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
            metricCovDeriv (I := J) h gRef (a + 1) (Phi x)
              (Fin.cons
                ((pushFwdSectionCross (I := I) (J := J) Phi X) (Phi x))
                (fun q : Fin (a + 2) =>
                  (pushFwdSectionCross (I := I) (J := J) Phi (V q)) (Phi x))) := by
        let hPb : SmoothRiemannianMetric I M :=
          Diffeomorph.pullbackMetricCross (I := I) (J := J) h Phi
        let refPb : SmoothRiemannianMetric I M :=
          Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi
        have hleft :=
          metricCovDeriv_succ_eval_smooth_slotsC (I' := I) hPb refPb a X V x
        have hright :=
          metricCovDeriv_succ_eval_smooth_slotsC (I' := J) h gRef a
            (pushFwdSectionCross (I := I) (J := J) Phi X)
            (fun q : Fin (a + 2) =>
              pushFwdSectionCross (I := I) (J := J) Phi (V q)) (Phi x)
        rw [hleft, hright]
        have hderiv :
            extDerivFun (I := I)
                (fun y : M => metricCovDeriv (I := I) hPb refPb a y
                  (fun q : Fin (a + 2) => V q y)) x (X x) =
              extDerivFun (I := J)
                (fun z : N => metricCovDeriv (I := J) h gRef a z
                  (fun q : Fin (a + 2) =>
                    pushFwdSectionCross (I := I) (J := J) Phi (V q) z)) (Phi x)
                ((pushFwdSectionCross (I := I) (J := J) Phi X) (Phi x)) := by
          have hscalar :
              (fun y : M => metricCovDeriv (I := I) hPb refPb a y
                (fun q : Fin (a + 2) => V q y)) =
                fun y : M => metricCovDeriv (I := J) h gRef a (Phi y)
                  (fun q : Fin (a + 2) =>
                    pushFwdSectionCross (I := I) (J := J) Phi (V q) (Phi y)) := by
            funext y
            simpa [hPb, refPb, pushFwdSectionCross_apply_at_image] using
              ih y (fun q : Fin (a + 2) => V q y)
          have hf : MDifferentiableAt J 𝓘(Real, Real)
              (fun z : N => metricCovDeriv (I := J) h gRef a z
                (fun q : Fin (a + 2) =>
                  pushFwdSectionCross (I := I) (J := J) Phi (V q) z))
              (Phi x) :=
            (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
              (I := J) (metricCovDeriv (I := J) h gRef a)
              (fun q : Fin (a + 2) =>
                pushFwdSectionCross (I := I) (J := J) Phi (V q))
              (Phi x)).mdifferentiableAt (by simp)
          rw [hscalar]
          simpa [pushFwdSectionCross_apply_at_image] using
            extDerivFun_comp_diffeomorphCross (I := I) (J := J)
              (f := fun z : N => metricCovDeriv (I := J) h gRef a z
                (fun q : Fin (a + 2) =>
                  pushFwdSectionCross (I := I) (J := J) Phi (V q) z))
              Phi x (X x) hf
        have hsum :
            (∑ p : Fin (a + 2),
              metricCovDeriv (I := I) hPb refPb a x
                (Function.update (fun q : Fin (a + 2) => V q x) p
                  (((leviCivitaConnectionOfMetric (I := I) refPb)
                      (fun y : M => V p y) x) (X x)))) =
              ∑ p : Fin (a + 2),
                metricCovDeriv (I := J) h gRef a (Phi x)
                  (Function.update
                    (fun q : Fin (a + 2) =>
                      pushFwdSectionCross (I := I) (J := J) Phi (V q) (Phi x)) p
                    (((leviCivitaConnectionOfMetric (I := J) gRef)
                        (fun z : N =>
                          pushFwdSectionCross (I := I) (J := J) Phi (V p) z)
                        (Phi x))
                      (pushFwdSectionCross (I := I) (J := J) Phi X (Phi x)))) := by
          apply Finset.sum_congr rfl
          intro p _
          let covL : TangentSpace I x :=
            ((leviCivitaConnectionOfMetric (I := I) refPb)
              (fun y : M => V p y) x) (X x)
          let covR : TangentSpace J (Phi x) :=
            ((leviCivitaConnectionOfMetric (I := J) gRef)
              (fun z : N => pushFwdSectionCross (I := I) (J := J) Phi (V p) z) (Phi x))
              (pushFwdSectionCross (I := I) (J := J) Phi X (Phi x))
          have hcov : mfderiv I J (Phi : M → N) x covL = covR := by
            have hcov' := metricCov_pullbackCross (I := I) (J := J) gRef Phi (V p) x (X x)
            simpa [covL, covR, refPb, metricCov, pushFwdSectionCross_apply_at_image] using hcov'
          have hslots : (fun q : Fin (a + 2) =>
              mfderiv I J (Phi : M → N) x
                (Function.update (fun q : Fin (a + 2) => V q x) p covL q)) =
              Function.update
                (fun q : Fin (a + 2) =>
                  pushFwdSectionCross (I := I) (J := J) Phi (V q) (Phi x))
                p covR := by
            funext q
            by_cases hqp : q = p
            · subst q
              simpa [Function.update] using hcov
            · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
              simp [pushFwdSectionCross_apply_at_image]
          have hih := ih x (Function.update (fun q : Fin (a + 2) => V q x) p covL)
          calc
            metricCovDeriv (I := I) hPb refPb a x
                (Function.update (fun q : Fin (a + 2) => V q x) p covL) =
              metricCovDeriv (I := J) h gRef a (Phi x)
                (fun q : Fin (a + 2) =>
                  mfderiv I J (Phi : M → N) x
                    (Function.update (fun q : Fin (a + 2) => V q x) p covL q)) := by
                simpa [hPb, refPb, covL] using hih
            _ =
              metricCovDeriv (I := J) h gRef a (Phi x)
                (Function.update
                  (fun q : Fin (a + 2) =>
                    pushFwdSectionCross (I := I) (J := J) Phi (V q) (Phi x))
                  p covR) := by
                congr 1
        rw [hderiv, hsum]
      have hslots :
          slots = Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      have hpushSlots :
          (fun q : Fin ((a + 1) + 2) =>
              mfderiv I J (Phi : M → N) x (slots q)) =
            Fin.cons (mfderiv I J (Phi : M → N) x (slots 0))
              (fun q : Fin (a + 2) =>
                mfderiv I J (Phi : M → N) x (slots q.succ)) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      rw [hpushSlots, hslots]
      simpa [hX, hV, pushFwdSectionCross_apply_at_image] using hsmooth

/-- Cross-model transport of the metric-covariant difference tower, evaluated
on arbitrary source slots. -/
theorem metricDiffCovDerivAt_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J 2 N]
    [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (gk gInf gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (a : Nat) (x : M) (slots : Fin (a + 2) → TangentSpace I x) :
    metricDiffCovDerivAt (I := I) a
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) gk Phi)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) gInf Phi)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) x slots =
      metricDiffCovDerivAt (I := J) a gk gInf gRef (Phi x)
        (fun q : Fin (a + 2) => mfderiv I J (Phi : M → N) x (slots q)) := by
  unfold metricDiffCovDerivAt
  calc
    (metricCovDeriv (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) gk Phi)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) a x -
        metricCovDeriv (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) gInf Phi)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) a x) slots =
        metricCovDeriv (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) gk Phi)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) a x slots -
          metricCovDeriv (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) gInf Phi)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) a x slots :=
      Tensor0SBundle.Tensor0SSpace.sub_apply (a + 2) x _ _ slots
    _ = metricCovDeriv (I := J) gk gRef a (Phi x)
          (fun q : Fin (a + 2) => mfderiv I J (Phi : M → N) x (slots q)) -
        metricCovDeriv (I := J) gInf gRef a (Phi x)
          (fun q : Fin (a + 2) => mfderiv I J (Phi : M → N) x (slots q)) := by
      rw [metricCovDeriv_pullbackCross, metricCovDeriv_pullbackCross]
    _ = (metricCovDeriv (I := J) gk gRef a (Phi x) -
          metricCovDeriv (I := J) gInf gRef a (Phi x))
        (fun q : Fin (a + 2) => mfderiv I J (Phi : M → N) x (slots q)) :=
      (Tensor0SBundle.Tensor0SSpace.sub_apply (a + 2) (Phi x) _ _ _).symm

/-- The Ricci tensor of a cross-model pullback metric is the evaluated
pullback of the target Ricci tensor. -/
theorem ricciTensor_cross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x v w =
      ricciTensor (I := J) g (Phi x)
        (mfderiv I J (Phi : M → N) x v)
        (mfderiv I J (Phi : M → N) x w) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x
  let dPhi : TangentSpace I x ≃L[Real] TangentSpace J (Phi x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zeroC x
  let idxEquiv :
      Fin (Module.finrank Real (TangentSpace I x)) ≃
        Fin (Module.finrank Real (TangentSpace J (Phi x))) :=
    finCongr dPhi.toLinearEquiv.finrank_eq
  let basis' :
      Module.Basis (Fin (Module.finrank Real (TangentSpace J (Phi x))))
        Real (TangentSpace J (Phi x)) :=
    (basis.map dPhi.toLinearEquiv).reindex idxEquiv
  have hdPhi_apply : ∀ u : TangentSpace I x,
      dPhi u = mfderiv I J (Phi : M → N) x u := by
    intro u
    have hco :=
      Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi) (x := x) infty_ne_zeroC
    exact congrArg
      (fun f : TangentSpace I x →L[Real] TangentSpace J (Phi x) => f u) hco
  have hbasis'_apply : ∀ j,
      basis' j =
        mfderiv I J (Phi : M → N) x (basis (idxEquiv.symm j)) := by
    intro j
    change ((basis.map dPhi.toLinearEquiv).reindex idxEquiv) j = _
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
    change dPhi (basis (idxEquiv.symm j)) =
      mfderiv I J (Phi : M → N) x (basis (idxEquiv.symm j))
    exact hdPhi_apply _
  have hON' : ∀ i j,
      g.inner (Phi x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hbasis'_apply i, hbasis'_apply j,
      ← Diffeomorph.pullbackMetricCross_inner
        (I := I) (J := J) g Phi x
        (basis (idxEquiv.symm i)) (basis (idxEquiv.symm j))]
    simpa using hON (idxEquiv.symm i) (idxEquiv.symm j)
  rw [ricciTensor_eq_orthonormal_trace
        (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        x v w (fun i => basis i) hON,
      ricciTensor_eq_orthonormal_trace
        (I := J) g (Phi x)
        (mfderiv I J (Phi : M → N) x v)
        (mfderiv I J (Phi : M → N) x w)
        (fun i => basis' i) hON']
  refine Fintype.sum_equiv idxEquiv _ _ ?_
  intro i
  have hbasis'_comp :
      basis' (idxEquiv i) =
        mfderiv I J (Phi : M → N) x (basis i) := by
    simpa using hbasis'_apply (idxEquiv i)
  rw [hbasis'_comp]
  rw [(Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi).symm x
        (riemannOp
          (cov := LeviCivita (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
          x (basis i) v w) (basis i),
      ← metricRm04StdAt_eq_inner_riemannOp
        (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        x (basis i) v w (basis i),
      metricRm04Std_pullbackCross
        (I := I) (J := J) g Phi x (basis i) v w (basis i),
      metricRm04StdAt_eq_inner_riemannOp
        (I := J) g (Phi x)
        (mfderiv I J (Phi : M → N) x (basis i))
        (mfderiv I J (Phi : M → N) x v)
        (mfderiv I J (Phi : M → N) x w)
        (mfderiv I J (Phi : M → N) x (basis i)),
      g.symm (Phi x)
        (mfderiv I J (Phi : M → N) x (basis i))
        (riemannOp (cov := LeviCivita (I := J) g) (Phi x)
          (mfderiv I J (Phi : M → N) x (basis i))
          (mfderiv I J (Phi : M → N) x v)
          (mfderiv I J (Phi : M → N) x w))]

/-- The canonical Ricci `(0,2)` tensor of a cross-model pullback metric
evaluates as the pullback of the target Ricci tensor. -/
theorem metricRicci_cross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x slots =
      metricRicci (I := J) g (Phi x)
        (fun q : Fin 2 => mfderiv I J (Phi : M → N) x (slots q)) := by
  have hleft :
      metricRicci (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x
          (vec2 (slots 0) (slots 1)) =
        ricciTensor (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          x (slots 0) (slots 1) := by
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  have hright :
      metricRicci (I := J) g (Phi x)
          (vec2
            (mfderiv I J (Phi : M → N) x (slots 0))
            (mfderiv I J (Phi : M → N) x (slots 1))) =
        ricciTensor (I := J) g (Phi x)
          (mfderiv I J (Phi : M → N) x (slots 0))
          (mfderiv I J (Phi : M → N) x (slots 1)) := by
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  rw [show vec2 (slots 0) (slots 1) = slots from by
    funext i
    fin_cases i <;> rfl] at hleft
  rw [show
      vec2
          (mfderiv I J (Phi : M → N) x (slots 0))
          (mfderiv I J (Phi : M → N) x (slots 1)) =
        (fun q : Fin 2 => mfderiv I J (Phi : M → N) x (slots q)) from by
    funext i
    fin_cases i <;> rfl] at hright
  rw [hleft, ricciTensor_cross (I := I) (J := J) g Phi x (slots 0) (slots 1),
    ← hright]

/-- Squared norms of covariant tensors are preserved by a cross-model
pullback metric when the source tensor is supplied by its evaluated pullback
relation. -/
theorem normSq0S_pullbackCross_eval_of_orthonormal
    [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx,
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi).inner x
          (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (Tpb : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x)
    (T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := F) (H := G)
      (I := J) (M := N) s (Phi x))
    (hT : ∀ slots : Fin s → TangentSpace I x,
      Tpb slots = T (fun q : Fin s => mfderiv I J (Phi : M → N) x (slots q))) :
    Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x s Tpb =
      Tensor0SBundle.normSq0S (I := J) g (Phi x) s T := by
  classical
  letI : Fintype Idx := Fintype.ofFinite Idx
  let dPhi : TangentSpace I x ≃L[Real] TangentSpace J (Phi x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zeroC x
  let basis' : Module.Basis Idx Real (TangentSpace J (Phi x)) :=
    basis.map dPhi.toLinearEquiv
  have hdPhi_apply : ∀ v : TangentSpace I x,
      dPhi v = mfderiv I J (Phi : M → N) x v := by
    intro v
    have h :=
      Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi) (x := x) infty_ne_zeroC
    exact congrArg (fun f : TangentSpace I x →L[Real] TangentSpace J (Phi x) => f v) h
  have hbasis'_apply : ∀ i : Idx,
      basis' i = mfderiv I J (Phi : M → N) x (basis i) := by
    intro i
    have hmap : basis' i = dPhi (basis i) := by
      change (basis.map dPhi.toLinearEquiv) i = dPhi (basis i)
      rw [Module.Basis.map_apply]
      rfl
    rw [hmap, hdPhi_apply (basis i)]
  have hON' : ∀ i j : Idx,
      g.inner (Phi x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    have hsrc := hON i j
    rw [Diffeomorph.pullbackMetricCross_inner] at hsrc
    simpa [hbasis'_apply i, hbasis'_apply j] using hsrc
  have hinv :
      MetricInverseInBasis_gen (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x basis
        (identityInvMetric (Idx := Idx)) := by
    have h := metricInverseInBasis_of_orthonormal
      (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) basis hON
    simpa [identityInvMetric, diagonalInvMetric] using h
  have hinv' :
      MetricInverseInBasis_gen (I := J) g (Phi x) basis'
        (identityInvMetric (Idx := Idx)) := by
    have h := metricInverseInBasis_of_orthonormal (I := J) g basis' hON'
    simpa [identityInvMetric, diagonalInvMetric] using h
  rw [normSq0S_identity_eq_sum_sq (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x s basis hinv Tpb,
    normSq0S_identity_eq_sum_sq (I := J) g (Phi x) s basis' hinv' T]
  apply Finset.sum_congr rfl
  intro slots _
  congr 1
  rw [component0S_apply, component0S_apply, hT]
  exact congrArg T (funext fun q => (hbasis'_apply (slots q)).symm)

/-- Scalar curvature is preserved by a cross-model pullback metric. -/
theorem metricScalar_cross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    metricScalarAt (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x =
      metricScalarAt (I := J) g (Phi x) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x
  let dPhi : TangentSpace I x ≃L[Real] TangentSpace J (Phi x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zeroC x
  let basis' : Module.Basis _ Real (TangentSpace J (Phi x)) :=
    basis.map dPhi.toLinearEquiv
  have hbasis'_apply : ∀ i,
      basis' i = mfderiv I J (Phi : M → N) x (basis i) := by
    intro i
    have hco :=
      Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi) (x := x) infty_ne_zeroC
    change (basis.map dPhi.toLinearEquiv) i = _
    rw [Module.Basis.map_apply]
    exact congrArg
      (fun f : TangentSpace I x →L[Real] TangentSpace J (Phi x) => f (basis i)) hco
  have hON' : ∀ i j,
      g.inner (Phi x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    have hsrc := hON i j
    rw [Diffeomorph.pullbackMetricCross_inner] at hsrc
    simpa [hbasis'_apply i, hbasis'_apply j] using hsrc
  have hinv :
      MetricInverseInBasis_gen (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        x basis identityInvMetric := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal
        (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        basis hON
  have hinv' :
      MetricInverseInBasis_gen (I := J) g (Phi x) basis'
        identityInvMetric := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := J) g basis' hON'
  rw [metricScalarAt_def, metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis
      (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
      basis identityInvMetric hinv
      (metricRicciAt (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x),
    metricTracePair0SAt_eq_sum_basis
      (I := J) g basis' identityInvMetric hinv'
      (metricRicciAt (I := J) g (Phi x))]
  refine Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun j _ => ?_))
  have hric :
      metricRicciAt (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x
          (vec2 (basis i) (basis j)) =
        metricRicciAt (I := J) g (Phi x)
          (vec2 (basis' i) (basis' j)) := by
    rw [metricRicciAt_apply_eq_ricciTensor,
      metricRicciAt_apply_eq_ricciTensor,
      hbasis'_apply i, hbasis'_apply j]
    exact ricciTensor_cross (I := I) (J := J) g Phi x (basis i) (basis j)
  rw [hric]

/-- The squared norm of the canonical Ricci tensor is preserved by a
cross-model pullback metric. -/
theorem ricciNormSq_cross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    normSq0S (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        x 2
        (metricRicci (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x) =
      normSq0S (I := J) g (Phi x) 2
        (metricRicci (I := J) g (Phi x)) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x
  exact normSq0S_pullbackCross_eval_of_orthonormal
    (I := I) (J := J) g Phi x 2 basis hON
    (metricRicci (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x)
    (metricRicci (I := J) g (Phi x))
    (metricRicci_cross (I := I) (J := J) g Phi x)

/-- The canonical pointwise trace-free Ricci norm square is preserved by a
cross-model pullback metric. -/
theorem tfRicNormSq_cross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    DifferentialGeometry.PDE.RicciFlow.tracefreeRicciNormSqAtOf
        (metricScalarAt (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x)
        (normSq0S (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          x 2
          (metricRicci (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x)) =
      DifferentialGeometry.PDE.RicciFlow.tracefreeRicciNormSqAtOf
        (metricScalarAt (I := J) g (Phi x))
        (normSq0S (I := J) g (Phi x) 2
          (metricRicci (I := J) g (Phi x))) := by
  rw [metricScalar_cross (I := I) (J := J),
    ricciNormSq_cross (I := I) (J := J)]

/-- Pointwise metric-difference seminorms are invariant under simultaneous
cross-model pullback of the compared metrics and the reference metric. -/
theorem metricDerivNorm_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J 2 N]
    [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (gk gInf gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (a : Nat) (x : M) :
    metricDerivNorm (I := I) a
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) gk Phi)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) gInf Phi)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) x =
      metricDerivNorm (I := J) a gk gInf gRef (Phi x) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis
      (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) x
  unfold metricDerivNorm
  rw [normSq0S_pullbackCross_eval_of_orthonormal (I := I) (J := J)
    (g := gRef) (Phi := Phi) (x := x) (s := a + 2)
    (basis := basis) hON
    (Tpb := metricDiffCovDerivAt (I := I) a
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) gk Phi)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) gInf Phi)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) gRef Phi) x)
    (T := metricDiffCovDerivAt (I := J) a gk gInf gRef (Phi x)) ?_]
  intro slots
  exact metricDiffCovDerivAt_pullbackCross
    (I := I) (J := J) gk gInf gRef Phi a x slots

end HCGCompactness
end DifferentialGeometry
