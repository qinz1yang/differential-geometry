import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomials
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.RmJetEvolutionPolynomial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CoefficientEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField
import DifferentialGeometry.Geometry.Metric.Variation.TimeDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff _root_.Topology BigOperators

universe u uE uH

theorem hasDerivWithinAt_eval_rename_pderiv {σ τ : Type*} [Fintype σ]
    (ι : σ → τ) (A : σ → MvPolynomial τ ℝ) (P : MvPolynomial σ ℝ)
    {w : ℝ → τ → ℝ} {J : Set ℝ} {t : ℝ}
    (hd : ∀ i, HasDerivWithinAt (fun s => w s (ι i))
      (MvPolynomial.eval (w t) (A i)) J t) :
    HasDerivWithinAt
      (fun s => MvPolynomial.eval (w s) (MvPolynomial.rename ι P))
      (MvPolynomial.eval (w t)
        (∑ i : σ, A i * MvPolynomial.rename ι (MvPolynomial.pderiv i P))) J t := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hfun : (fun s => MvPolynomial.eval (w s) (MvPolynomial.rename ι (MvPolynomial.C c))) =
        fun _ : ℝ => c := by
      funext s
      simp
    have hder : MvPolynomial.eval (w t)
        (∑ i : σ, A i * MvPolynomial.rename ι (MvPolynomial.pderiv i (MvPolynomial.C c))) = 0 := by
      simp
    rw [hfun, hder]
    exact hasDerivWithinAt_const t J c
  | add P Q hP hQ =>
    have hfun : (fun s => MvPolynomial.eval (w s) (MvPolynomial.rename ι (P + Q))) =
        fun s => MvPolynomial.eval (w s) (MvPolynomial.rename ι P) +
          MvPolynomial.eval (w s) (MvPolynomial.rename ι Q) := by
      funext s
      simp
    rw [hfun]
    have hsum : (∑ i : σ, A i * MvPolynomial.rename ι (MvPolynomial.pderiv i (P + Q))) =
        (∑ i : σ, A i * MvPolynomial.rename ι (MvPolynomial.pderiv i P)) +
          ∑ i : σ, A i * MvPolynomial.rename ι (MvPolynomial.pderiv i Q) := by
      simp only [map_add, mul_add, Finset.sum_add_distrib]
    rw [hsum, map_add]
    exact hP.fun_add hQ
  | mul_X P i hP =>
    have hfun : (fun s => MvPolynomial.eval (w s) (MvPolynomial.rename ι (P * MvPolynomial.X i))) =
        fun s => MvPolynomial.eval (w s) (MvPolynomial.rename ι P) * w s (ι i) := by
      funext s
      simp
    rw [hfun]
    have hthis : ∀ j : σ, MvPolynomial.eval (w t)
          (A j * MvPolynomial.rename ι (MvPolynomial.pderiv j (P * MvPolynomial.X i))) =
        MvPolynomial.eval (w t) (A j) *
            MvPolynomial.eval (w t) (MvPolynomial.rename ι (MvPolynomial.pderiv j P))
            * w t (ι i) +
          (if j = i then MvPolynomial.eval (w t) (A j) *
            MvPolynomial.eval (w t) (MvPolynomial.rename ι P) else 0) := by
      intro j
      by_cases hji : j = i
      · rw [if_pos hji, MvPolynomial.pderiv_mul, hji, MvPolynomial.pderiv_X_self, mul_one]
        simp only [map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.eval_X]
        ring
      · rw [if_neg hji, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (Ne.symm hji),
          mul_zero, add_zero]
        simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.eval_X]
        ring
    have hsum : MvPolynomial.eval (w t)
          (∑ j : σ, A j * MvPolynomial.rename ι (MvPolynomial.pderiv j (P * MvPolynomial.X i))) =
        MvPolynomial.eval (w t) (∑ j : σ, A j * MvPolynomial.rename ι (MvPolynomial.pderiv j P))
            * w t (ι i) +
          MvPolynomial.eval (w t) (A i) * MvPolynomial.eval (w t) (MvPolynomial.rename ι P) := by
      rw [map_sum, Finset.sum_congr rfl (fun j _ => hthis j), Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_mul, map_sum]
        exact congrArg (· * w t (ι i)) (Finset.sum_congr rfl fun j _ =>
          (MvPolynomial.eval_mul (f := w t) (p := A j)
            (q := MvPolynomial.rename ι (MvPolynomial.pderiv j P))).symm)
      · rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          rw [if_neg hj]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
    rw [hsum]
    simpa only [mul_comm] using hP.fun_mul (hd i)

def curvatureJetVariableDerivative (n N K : ℕ) (h : N + 2 ≤ K) :
    CurvatureJetPolynomialVariable n N → MvPolynomial (CurvatureJetPolynomialVariable n K) ℝ
  | Sum.inl ij => MvPolynomial.C 2 * ∑ a : Fin n, ∑ c : Fin n,
      MvPolynomial.X (Sum.inl (ij.1, a)) * MvPolynomial.X (Sum.inl (ij.2, c)) *
        curvatureJetRicciPoly (n := n) K a c
  | Sum.inr ks => MvPolynomial.rename
      (curvatureJetVariableCastLe (ks.1.val + 2) K (by have := ks.1.isLt; omega))
      (curvatureJetTimeDerivativePoly (n := n) ks.1.val ks.2)

def curvatureJetSharpPoly (n N : ℕ) (i j : Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ :=
  ∑ f : Fin n, MvPolynomial.X (Sum.inl (j, f)) * curvatureJetRicciPoly (n := n) N i f

noncomputable def mixedJetDerivativePolynomialAux (n p : ℕ) :
    (q : ℕ) → ((Fin (4 + p) → Fin n) →
        MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ) →
      (Fin (4 + p) → Fin n) →
        MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q + 2)) ℝ
  | 0, _, slots => curvatureJetTimeDerivativePoly (n := n) p slots
  | q + 1, P, slots =>
      ∑ i : CurvatureJetPolynomialVariable n (p + 2 * (q + 1)),
        curvatureJetVariableDerivative n (p + 2 * (q + 1)) (p + 2 * (q + 1) + 2) (by omega) i *
          MvPolynomial.rename
            (curvatureJetVariableCastLe (p + 2 * (q + 1)) (p + 2 * (q + 1) + 2) (by omega))
            (MvPolynomial.pderiv i (P slots))

noncomputable def mixedJetPolynomial (n p : ℕ) :
    (q : ℕ) → (Fin (4 + p) → Fin n) →
      MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ
  | 0 => fun slots => MvPolynomial.X (Sum.inr ⟨⟨p, Nat.lt_succ_self p⟩, slots⟩)
  | q + 1 => fun slots =>
      mixedJetDerivativePolynomialAux n p q (mixedJetPolynomial n p q) slots +
      ∑ k : Fin (4 + p), ∑ e : Fin n,
        curvatureJetSharpPoly (n := n) (p + 2 * q + 2) (slots k) e *
          MvPolynomial.rename
            (curvatureJetVariableCastLe (p + 2 * q) (p + 2 * q + 2) (by omega))
            (mixedJetPolynomial n p q (Function.update slots k e))

noncomputable def mixedJetDerivativePolynomial (n p q : ℕ) (slots : Fin (4 + p) → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q + 2)) ℝ :=
  mixedJetDerivativePolynomialAux n p q (mixedJetPolynomial n p q) slots

noncomputable def mixedJetRicciCorrection (n p q : ℕ) (slots : Fin (4 + p) → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q + 2)) ℝ :=
  ∑ k : Fin (4 + p), ∑ e : Fin n,
    curvatureJetSharpPoly (n := n) (p + 2 * q + 2) (slots k) e *
      MvPolynomial.rename
        (curvatureJetVariableCastLe (p + 2 * q) (p + 2 * q + 2) (by omega))
        (mixedJetPolynomial n p q (Function.update slots k e))

theorem mixedJetPolynomial_succ (n p q : ℕ) (slots : Fin (4 + p) → Fin n) :
    mixedJetPolynomial n p (q + 1) slots =
      mixedJetDerivativePolynomial n p q slots + mixedJetRicciCorrection n p q slots := rfl

section Helper

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem eval_curvatureJetRicciPolyAtLevel (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    {N n : ℕ} {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (i j : Fin n) :
    MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S N t basis)
        (curvatureJetRicciPoly (n := n) N i j) =
      metricRicciAt (S.base.metric t) x (vec2 (basis i) (basis j)) := by
  classical
  have hrm04 : (S.base.rm04 t) x =
      metricRm04At (I := I) (M := M) (S.base.metric t) x :=
    metricRm04_apply (I := I) (M := M) (S.base.metric t) x
  have hbridge : ∀ a c : Fin n,
      component0S (I := I) basis (nablaKRm04Field (I := I) S t 0 x) (slots4 a i j c) =
        component0S (I := I) basis
          (metricRm04At (I := I) (M := M) (S.base.metric t) x) (slots4 a i j c) := by
    intro a c
    rw [nablaKRm04Field_zero, hrm04]
  let K := metricCurvatureSections (I := I) (M := M) (S.base.metric t)
  have hLower := rm04LowersRm13At_of_realizes (I := I) (S.base.metric t)
    (metricCov (S.base.metric t))
    (metricRm13 (S.base.metric t)) (metricRm04 (S.base.metric t))
    K.rm13Realizes K.rm04Realizes x
  have hTrace := ricciFirstTraceAt_of_rm13_section (I := I) (S.base.metric t) basis
    (basisInvMetric (I := I) (S.base.metric t) x basis)
    (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis)
    (metricRicci (S.base.metric t)) (metricRm13 (S.base.metric t))
    (metricRm04 (S.base.metric t)) K.ricciRealizes hLower i j
  simpa only [curvatureJetRicciPoly, curvatureJetRmVar, map_sum, map_mul,
    MvPolynomial.eval_X, curvatureJetPolynomialValues, hbridge,
    ← rm04CompAt_apply, rm04CompAt,
    metricRicci_apply, metricRm04_apply] using hTrace.symm

end Helper
section NablaDerivative

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem curvatureJetTimeDerivativePoly_hasDerivWithinAt (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {n k : ℕ} (t : ℝ) (ht : t ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + k) → Fin n) :
    HasDerivWithinAt
      (fun s => component0S (I := I) basis (nablaKRm04Field S s k x) slots)
      (MvPolynomial.eval (curvatureJetPolynomialValues S (k + 2) t basis)
        (curvatureJetTimeDerivativePoly (n := n) k slots)) D.carrier t := by
  have hmain := hasDerivWithinAt_curvature_canonical_residual (I := I) (M := M) S hS k
    ⟨t, ht⟩ x
  have hcomp := (tensor0SEvalCLM (I := I) (M := M)
      (fun a : Fin (4 + k) => basis (slots a))).hasFDerivAt.comp_hasDerivWithinAt t hmain
  have hev : (⇑(tensor0SEvalCLM (I := I) (M := M) (fun a : Fin (4 + k) => basis (slots a))) ∘
        fun r : ℝ => nablaKRm04Field S r k x) =
      fun s : ℝ => component0S (I := I) basis (nablaKRm04Field S s k x) slots := by
    funext s
    simp only [Function.comp_apply, tensor0SEvalCLM_apply, component0S_apply]
  rw [hev] at hcomp
  have hsplit : (tensor0SEvalCLM (I := I) (M := M) (fun a : Fin (4 + k) => basis (slots a)))
        (metricTraceFirstTwo0STensor (I := I) (S.base.metric t)
            (nablaKRm04Field S t (k + 2) x) + rmResidualField S ⟨t, ht⟩ k x) =
      component0S (I := I) basis
          (metricTraceFirstTwo0STensor (I := I) (S.base.metric t)
            (nablaKRm04Field S t (k + 2) x)) slots +
        component0S (I := I) basis (rmResidualField S ⟨t, ht⟩ k x) slots := by
    rw [ContinuousLinearMap.map_add, tensor0SEvalCLM_apply, tensor0SEvalCLM_apply]
    rfl
  refine hcomp.congr_deriv ?_
  refine hsplit.trans ?_
  rw [eval_curvatureJetTracePoly (I := I) (M := M) S t basis slots,
    eval_curvatureExpressionPoly_residual (I := I) (M := M) S ht basis slots]
  simp only [curvatureJetTimeDerivativePoly, MvPolynomial.eval_add]

end NablaDerivative
section VariableDerivative

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem hasDerivWithinAt_curvatureJetPolynomialValues_variableDerivative
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (t : D.RegularTime) {x : M}
    {n N : ℕ} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
    ∀ i : CurvatureJetPolynomialVariable n N,
      HasDerivWithinAt
        (fun s => curvatureJetPolynomialValues (I := I) (M := M) S (N + 2) s basis
          (curvatureJetVariableCastLe N (N + 2) (Nat.le_add_right N 2) i))
        (MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S (N + 2) (t : ℝ) basis)
          (curvatureJetVariableDerivative n N (N + 2) le_rfl i)) D.carrier (t : ℝ) := by
  intro i
  cases i with
  | inl ij =>
    have hd := basisInvMetric_hasDerivWithinAt_of_pairings (I := I) (S.base.metric) basis
      (fun a c => metricRicciAt (S.base.metric (t : ℝ)) x (vec2 (basis a) (basis c)))
      (fun a c => (metricDerivAt S hS t x (basis a) (basis c)).hasDerivWithinAt) (J := D.carrier)
      ij.1 ij.2
    refine hd.congr_deriv ?_
    simp only [curvatureJetVariableDerivative, curvatureJetPolynomialValues, map_mul, map_sum,
      MvPolynomial.eval_X, MvPolynomial.eval_C,
      eval_curvatureJetRicciPolyAtLevel (N := N + 2) S (t : ℝ) basis]
  | inr ks =>
    have hd := curvatureJetTimeDerivativePoly_hasDerivWithinAt S hS (t : ℝ) t.2 x basis ks.2
    refine hd.congr_deriv ?_
    have hcast : (curvatureJetPolynomialValues (I := I) (M := M) S (N + 2) (t : ℝ) basis) ∘
        (curvatureJetVariableCastLe (ks.1.val + 2) (N + 2) (by have := ks.1.isLt; omega)) =
        curvatureJetPolynomialValues (I := I) (M := M) S (ks.1.val + 2) (t : ℝ) basis := by
      funext v
      exact curvatureJetPolynomialValues_castLe S (by omega) (t : ℝ) basis v
    simp only [curvatureJetVariableDerivative, MvPolynomial.eval_rename, hcast]

end VariableDerivative
section Sharp

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem eval_curvatureJetSharpPoly (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    {N n : ℕ} {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (i j : Fin n) :
    MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S N t basis)
        (curvatureJetSharpPoly (n := n) N i j) =
      basis.repr (ricciSharp (I := I) (S.base.metric t) x (basis i)) j := by
  simp only [curvatureJetSharpPoly, map_sum, map_mul, MvPolynomial.eval_X,
    curvatureJetPolynomialValues, eval_curvatureJetRicciPolyAtLevel (N := N) S t basis]
  symm
  simpa only [inner_ricciSharp, metricRicciAt_apply_eq_ricciTensor] using
    (basis_repr_eq_sum_inv_inner (I := I) (S.base.metric t) x basis
      (basisInvMetric (I := I) (S.base.metric t) x basis)
      (basisInvMetric_isInverse (I := I) (S.base.metric t) x basis)
      (ricciSharp (I := I) (S.base.metric t) x (basis i)) j)

omit [SigmaCompactSpace M] in
theorem component0S_covariantEndomorphismAction0S_correction
    {p N n : ℕ} {x : M} {A : Tensor0SSpace (4 + p) I x}
    {P : (Fin (4 + p) → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hA : ∀ slots, component0S (I := I) basis A slots =
      MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S N t basis) (P slots))
    (slots : Fin (4 + p) → Fin n) :
    component0S (I := I) basis
        (covariantEndomorphismAction0S (I := I) A
          (ricciSharp (I := I) (S.base.metric t) x)) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues (I := I) (M := M) S (N + 2) t basis)
        (∑ k : Fin (4 + p), ∑ e : Fin n,
          curvatureJetSharpPoly (n := n) (N + 2) (slots k) e *
            MvPolynomial.rename
              (curvatureJetVariableCastLe N (N + 2) (Nat.le_add_right N 2))
              (P (Function.update slots k e))) := by
  have haction : component0S (I := I) basis
      (covariantEndomorphismAction0S (I := I) A
        (ricciSharp (I := I) (S.base.metric t) x)) slots =
      ∑ k : Fin (4 + p), ∑ e : Fin n,
        basis.repr (ricciSharp (I := I) (S.base.metric t) x (basis (slots k))) e *
          component0S (I := I) basis A (Function.update slots k e) :=
    tensor0SComponent_covariantEndomorphismAction0S (I := I) basis A
      (ricciSharp (I := I) (S.base.metric t) x) slots
  have hcast : (curvatureJetPolynomialValues (I := I) (M := M) S (N + 2) t basis) ∘
      (curvatureJetVariableCastLe N (N + 2) (Nat.le_add_right N 2)) =
      curvatureJetPolynomialValues (I := I) (M := M) S N t basis := by
    funext v
    exact curvatureJetPolynomialValues_castLe S (Nat.le_add_right N 2) t basis v
  rw [haction, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, eval_curvatureJetSharpPoly (N := N + 2) S t basis (slots k) e,
    MvPolynomial.eval_rename, hcast, hA (Function.update slots k e)]

end Sharp


section Main

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M] in
theorem tensor0SSpace_eq_zero_of_finrank_zero {s : ℕ} {x : M} (hs : 0 < s)
    (h0 : Module.finrank ℝ E = 0) (T : Tensor0SSpace s I x) : T = 0 := by
  let : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp h0
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel T = Tensor0SSpace.toModel (0 : Tensor0SSpace s I x)
  rw [Tensor0SSpace.toModel_zero]
  ext v
  exact (Tensor0SSpace.toModel T).map_coord_zero (⟨0, hs⟩ : Fin s) (Subsingleton.elim _ _)

omit [SigmaCompactSpace M] in
theorem mixedJetPolynomial_hasDerivWithinAt (n p : ℕ) (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) :
    ∀ q : ℕ, ∀ t ∈ D.regular, ∀ x : M,
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
      HasDerivWithinAt
        (fun s => iteratedMetricTimeDerivWithin S.base.metric D.carrier
          (fun s => nablaKRm04Field S s p x) q s)
        (tensorOfPolynomialComponents (I := I) basis (mixedJetDerivativePolynomial n p q)
          (curvatureJetPolynomialValues S (p + 2 * q + 2) t basis)) D.carrier t ∧
      ∀ slots : Fin (4 + p) → Fin n,
        component0S (I := I) basis
          (iteratedMetricTimeDerivWithin S.base.metric D.carrier
            (fun s => nablaKRm04Field S s p x) q t) slots =
          MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis)
            (mixedJetPolynomial n p q slots) := by
  intro q
  induction q with
  | zero =>
    intro t ht x basis
    constructor
    · refine tensor0S_hasDerivWithinAt_of_components (I := I) basis ?_
      intro slots
      have hd := curvatureJetTimeDerivativePoly_hasDerivWithinAt S hS t ht x basis slots
      simpa only [iteratedMetricTimeDerivWithin_zero, component0S_tensorOfPolynomialComponents,
        mixedJetDerivativePolynomial, mixedJetDerivativePolynomialAux] using hd
    · intro slots
      simp only [iteratedMetricTimeDerivWithin_zero, mixedJetPolynomial,
        curvatureJetPolynomialValues, MvPolynomial.eval_X]
  | succ q ih =>
    intro t ht x basis
    have hnext : ∀ s ∈ D.regular, ∀ slots : Fin (4 + p) → Fin n,
        component0S (I := I) basis
          (iteratedMetricTimeDerivWithin S.base.metric D.carrier
            (fun s => nablaKRm04Field S s p x) (q + 1) s) slots =
          MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * (q + 1)) s basis)
            (mixedJetPolynomial n p (q + 1) slots) := by
      intro s hs slots
      have huniqS : UniqueDiffWithinAt ℝ D.carrier s :=
        uniqueDiffWithinAt_of_mem_nhds (D.regular_mem_nhds hs)
      have hval : iteratedMetricTimeDerivWithin S.base.metric D.carrier
          (fun s => nablaKRm04Field S s p x) (q + 1) s =
          tensorOfPolynomialComponents (I := I) basis (mixedJetDerivativePolynomial n p q)
              (curvatureJetPolynomialValues S (p + 2 * q + 2) s basis) +
            covariantEndomorphismAction0S (I := I)
              (iteratedMetricTimeDerivWithin S.base.metric D.carrier
                (fun s => nablaKRm04Field S s p x) q s)
              (ricciSharp (I := I) (S.base.metric s) x) := by
        have hder := (ih s hs x basis).1.derivWithin huniqS
        have hder' : derivWithin (iteratedMetricTimeDerivWithin S.base.metric D.carrier
            (fun s => nablaKRm04Field S s p x) q) D.carrier s =
            tensorOfPolynomialComponents (I := I) basis (mixedJetDerivativePolynomial n p q)
              (curvatureJetPolynomialValues S (p + 2 * q + 2) s basis) := hder
        rw [iteratedMetricTimeDerivWithin_succ, metricTimeDerivWithin, hder']
      rw [hval, component0S_add_field (I := I), component0S_tensorOfPolynomialComponents,
        component0S_covariantEndomorphismAction0S_correction (p := p) (N := p + 2 * q)
          (A := iteratedMetricTimeDerivWithin S.base.metric D.carrier
            (fun s => nablaKRm04Field S s p x) q s)
          (P := mixedJetPolynomial n p q) S s basis
          (fun slots' => (ih s hs x basis).2 slots') slots,
        mixedJetPolynomial_succ, map_add]
      rfl
    constructor
    · refine tensor0S_hasDerivWithinAt_of_components (I := I) basis ?_
      intro slots
      rw [component0S_tensorOfPolynomialComponents]
      have hpt : ∀ u : ℝ,
          MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * (q + 1)) u basis)
              (mixedJetPolynomial n p (q + 1) slots) =
            MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * (q + 1) + 2) u basis)
              (MvPolynomial.rename
                (curvatureJetVariableCastLe (p + 2 * (q + 1)) (p + 2 * (q + 1) + 2) (by omega))
                (mixedJetPolynomial n p (q + 1) slots)) := fun u => by
        symm
        rw [MvPolynomial.eval_rename]
        exact congrArg
          (fun f => MvPolynomial.eval f (mixedJetPolynomial n p (q + 1) slots))
          (funext fun i => curvatureJetPolynomialValues_castLe S (by omega) u basis i)
      have hchain : HasDerivWithinAt
          (fun s => MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * (q + 1)) s basis)
            (mixedJetPolynomial n p (q + 1) slots))
          (MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * (q + 1) + 2) t basis)
            (mixedJetDerivativePolynomial n p (q + 1) slots)) D.carrier t := by
        have hd := hasDerivWithinAt_eval_rename_pderiv
          (curvatureJetVariableCastLe (p + 2 * (q + 1)) (p + 2 * (q + 1) + 2) (by omega))
          (curvatureJetVariableDerivative n (p + 2 * (q + 1)) (p + 2 * (q + 1) + 2) (by omega))
          (mixedJetPolynomial n p (q + 1) slots)
          (w := fun s j => curvatureJetPolynomialValues S (p + 2 * (q + 1) + 2) s basis j)
          (J := D.carrier) (t := t)
          (fun i => hasDerivWithinAt_curvatureJetPolynomialValues_variableDerivative
            S hS ⟨t, ht⟩ basis i)
        refine ((Filter.EventuallyEq.hasDerivWithinAt_iff (Filter.Eventually.of_forall hpt)
          (hpt t)).mpr hd).congr_deriv ?_
        simp only [mixedJetDerivativePolynomial, mixedJetDerivativePolynomialAux]
      have hev : (fun s => component0S (I := I) basis
            (iteratedMetricTimeDerivWithin S.base.metric D.carrier
              (fun s => nablaKRm04Field S s p x) (q + 1) s) slots) =ᶠ[𝓝[D.carrier] t]
          (fun s => MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * (q + 1)) s basis)
            (mixedJetPolynomial n p (q + 1) slots)) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (D.regular_isOpen.mem_nhds ht)] with s hs
        exact hnext s hs slots
      exact (Filter.EventuallyEq.hasDerivWithinAt_iff hev (hnext t ht slots)).mpr hchain
    · exact fun slots => hnext t ht slots

end Main

theorem exists_mixed_curvature_jet_polynomials (n p q : ℕ) :
    ∃ P : (Fin (4 + p) → Fin n) →
        MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ,
      ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [CompleteSpace E]
        {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        [I.Boundaryless]
        {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
        [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn S → ∀ t ∈ D.regular, ∀ x : M,
        ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
          DifferentiableAt ℝ
            (iteratedMetricTimeDerivWithin S.base.metric D.carrier
              (fun s => nablaKRm04Field S s p x) q) t ∧
          ∀ slots : Fin (4 + p) → Fin n,
            component0S (I := I) basis
              (iteratedMetricTimeDerivWithin S.base.metric D.carrier
                (fun s => nablaKRm04Field S s p x) q t) slots =
              MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis)
                (P slots) := by
  classical
  refine ⟨mixedJetPolynomial n p q, ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ D S hS t ht x basis
  by_cases hn : n = 0
  · subst hn
    have h0 : Module.finrank ℝ E = 0 := by
      change Module.finrank ℝ (TangentSpace I x) = 0
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis basis
    refine ⟨?_, ?_⟩
    · refine (Filter.EventuallyEq.differentiableAt_iff
        (f₀ := iteratedMetricTimeDerivWithin S.base.metric D.carrier
          (fun s => nablaKRm04Field S s p x) q)
        (f₁ := fun _ : ℝ => (0 : Tensor0SSpace (4 + p) I x))
        (Filter.Eventually.of_forall fun s =>
          tensor0SSpace_eq_zero_of_finrank_zero (by omega) h0 _)).mpr
        (differentiableAt_const (0 : Tensor0SSpace (4 + p) I x))
    · intro slots
      exact Fin.elim0 (slots ⟨0, by omega⟩)
  · let : NeZero (Module.finrank ℝ E) := ⟨fun hzero => hn (by
      have hcard : Module.finrank ℝ E = n := by
        change Module.finrank ℝ (TangentSpace I x) = n
        simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis basis
      exact hcard ▸ hzero)⟩
    obtain ⟨hd, hcomp⟩ := mixedJetPolynomial_hasDerivWithinAt n p S hS q t ht x basis
    exact ⟨(hd.hasDerivAt (D.regular_mem_nhds ht)).differentiableAt, hcomp⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
