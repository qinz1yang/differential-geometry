import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ResidualExpression
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeRegularity
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor Bundle.continuousMultilinearMap
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

def ricciSlotPermutation (s : ℕ) (q : Fin s) : Fin (2 + s) ≃ Fin (s + 2) :=
  (finCongr (Nat.add_comm 2 s)).trans (Equiv.swap 0 q.succ.succ)

private theorem slot_cast_zero (s : ℕ) (q : Fin s) :
    ricciSlotPermutation s q (Fin.castAdd s (0 : Fin 2)) = q.succ.succ := by
  have hc : finCongr (Nat.add_comm 2 s) (Fin.castAdd s (0 : Fin 2)) = 0 := by
    apply Fin.ext
    rfl
  simp only [ricciSlotPermutation, Equiv.trans_apply, hc, Equiv.swap_apply_left]

private theorem slot_cast_one (s : ℕ) (q : Fin s) :
    ricciSlotPermutation s q (Fin.castAdd s (1 : Fin 2)) = 1 := by
  have hc : finCongr (Nat.add_comm 2 s) (Fin.castAdd s (1 : Fin 2)) = 1 := by
    apply Fin.ext
    rfl
  have h10 : (1 : Fin (s + 2)) ≠ 0 := by
    intro h
    have he := Fin.val_eq_of_eq h
    simp only [Fin.val_one, Fin.val_zero] at he
    omega
  have h1q : (1 : Fin (s + 2)) ≠ q.succ.succ := by
    intro h
    have he := Fin.val_eq_of_eq h
    simp only [Fin.val_one, Fin.val_succ] at he
    omega
  simp only [ricciSlotPermutation, Equiv.trans_apply, hc,
    Equiv.swap_apply_of_ne_of_ne h10 h1q]

private theorem cast_nat_slot (s : ℕ) (a : Fin s) :
    finCongr (Nat.add_comm 2 s) (Fin.natAdd 2 a) = a.succ.succ := by
  apply Fin.ext
  simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
  omega

private theorem slot_nat_self (s : ℕ) (q : Fin s) :
    ricciSlotPermutation s q (Fin.natAdd 2 q) = 0 := by
  simp only [ricciSlotPermutation, Equiv.trans_apply, cast_nat_slot, Equiv.swap_apply_right]

private theorem slot_nat_ne (s : ℕ) (q a : Fin s) (ha : a ≠ q) :
    ricciSlotPermutation s q (Fin.natAdd 2 a) = a.succ.succ := by
  have ha0 : a.succ.succ ≠ (0 : Fin (s + 2)) := by
    intro h
    have he := Fin.val_eq_of_eq h
    simp only [Fin.val_zero, Fin.val_succ] at he
    omega
  have haq : a.succ.succ ≠ q.succ.succ := by
    intro h
    apply ha
    apply Fin.ext
    have he := Fin.val_eq_of_eq h
    simp only [Fin.val_succ] at he
    omega
  simp only [ricciSlotPermutation, Equiv.trans_apply, cast_nat_slot,
    Equiv.swap_apply_of_ne_of_ne ha0 haq]

private theorem slot_left {V : Type*} (s : ℕ) (q : Fin s) (u w : V) (v : Fin s → V) :
    ((Fin.cons u (Fin.cons w v)) ∘ ricciSlotPermutation s q) ∘ Fin.castAdd s = ![v q, w] := by
  let f : Fin (s + 2) → V := Fin.cons u (Fin.cons w v)
  funext a
  fin_cases a
  · change f (ricciSlotPermutation s q (Fin.castAdd s (0 : Fin 2))) = v q
    rw [slot_cast_zero]
    rfl
  · change f (ricciSlotPermutation s q (Fin.castAdd s (1 : Fin 2))) = w
    rw [slot_cast_one]
    rfl

private theorem slot_right {V : Type*} (s : ℕ) (q : Fin s) (u w : V) (v : Fin s → V) :
    ((Fin.cons u (Fin.cons w v)) ∘ ricciSlotPermutation s q) ∘ Fin.natAdd 2 = Function.update v q u := by
  funext a
  by_cases ha : a = q
  · subst a
    simp only [Function.comp_apply, slot_nat_self, Fin.cons_zero, Function.update_self]
  · simp only [Function.comp_apply, slot_nat_ne s q a ha, Fin.cons_succ, Function.update_of_ne ha]

def CurvatureExpression.ricci : CurvatureExpression 2 :=
  .trace (.perm covariantFourTracePerm (.curvature 0))

def CurvatureExpression.ricciAction {s : ℕ} (A : CurvatureExpression s) : CurvatureExpression s :=
  sumFin s (fun q => .trace (.perm (ricciSlotPermutation s q) (.product ricci A)))

def CurvatureExpression.timeLeaf (k : ℕ) : CurvatureExpression (4 + k) :=
  .add (.add (.trace (.curvature (k + 2))) (residual k)) (.ricciAction (.curvature k))

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompleteSpace E]

theorem CurvatureExpression.eval_ricci {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    ricci.eval S t x = metricRicciAt (S.base.metric t) x := by
  have h := levi_civita_ricci_section_eq_riemann_trace (S.base.metric t)
  have hp := congrArg (fun F : Tensor02Section (I := I) (M := M) => F x) h
  exact hp.symm

variable [BoundarylessManifold I M]

private theorem trace_slot_component {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M) (T : Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ι → ι → ℝ)
    (hB : MetricInverseInBasis g x basis B) (q : Fin s) (m : Fin s → ι) :
    component0S basis (metricTraceFirstTwo0STensor g
      ((productFun (F := E) (E := TangentSpace I) (metricRicciAt g x) T :
        Tensor0SSpace (2 + s) I x).domDomCongr (ricciSlotPermutation s q))) m =
      ∑ i : ι, ∑ j : ι, B i j * ricciTensor g x (basis (m q)) (basis j) *
        component0S basis T (Function.update m q i) := by
  let R : Tensor0SSpace 2 I x := metricRicciAt g x
  let P : Tensor0SSpace (2 + s) I x := productFun (F := E) (E := TangentSpace I) R T
  let Q : Tensor0SSpace (s + 2) I x := P.domDomCongr (ricciSlotPermutation s q)
  have hQ (v : Fin (s + 2) → TangentSpace I x) : Q v = P (v ∘ ricciSlotPermutation s q) :=
    Tensor0SSpace.domDomCongr_apply (ricciSlotPermutation s q) P v
  have hP (v : Fin (2 + s) → TangentSpace I x) :
      P v = R (v ∘ Fin.castAdd s) * T (v ∘ Fin.natAdd 2) := product_fun_apply R T v
  have hR (u w : TangentSpace I x) : R ![u, w] = ricciTensor g x u w := by
    have hv : ![u, w] = vec2 u w := by
      funext a
      fin_cases a <;> rfl
    exact (congrArg R hv).trans (metricRicciAt_apply_eq_ricciTensor g x u w)
  change component0S basis (metricTraceFirstTwo0STensor g Q) m = _
  rw [component0S_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis g basis B hB]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change B i j * Q (Fin.cons (basis i) (Fin.cons (basis j) (fun a => basis (m a)))) = _
  rw [hQ, hP, slot_left, slot_right, hR]
  have hu : Function.update (fun a => basis (m a)) q (basis i) =
      (fun a => basis (Function.update m q i a)) := by
    funext a
    by_cases ha : a = q
    · subst a
      simp only [Function.update_self]
    · simp only [Function.update_of_ne ha]
  rw [hu, component0S_apply]
  ring

theorem CurvatureExpression.eval_ricciAction {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) {s : ℕ} (A : CurvatureExpression s) (x : M) :
    A.ricciAction.eval S t x = ricciTimeCorrection (S.base.metric t) (A.eval S t x) := by
  classical
  let g := S.base.metric t
  let T := A.eval S t x
  let basis := Module.finBasis ℝ (TangentSpace I x)
  let B := basisInvMetric g x basis
  have hB : MetricInverseInBasis g x basis B := basisInvMetric_isInverse g x basis
  let F (q : Fin s) : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s :=
    (CurvatureExpression.trace (.perm (ricciSlotPermutation s q) (.product ricci A))).eval S t
  let ev : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s →+
      Tensor0SSpace s I x :=
    { toFun := fun U => U x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsum : A.ricciAction.eval S t x = ∑ q : Fin s, F q x := by
    have hh := congrArg (fun U : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) s => U x) (eval_sumFin S t s (fun q =>
        CurvatureExpression.trace (.perm (ricciSlotPermutation s q) (.product ricci A))))
    exact hh.trans (map_sum ev F Finset.univ)
  have hF (q : Fin s) : F q x = metricTraceFirstTwo0STensor g
      ((productFun (F := E) (E := TangentSpace I) (metricRicciAt g x) T :
        Tensor0SSpace (2 + s) I x).domDomCongr (ricciSlotPermutation s q)) := by
    exact congrArg (fun U : Tensor0SSpace 2 I x => metricTraceFirstTwo0STensor g
      ((productFun (F := E) (E := TangentSpace I) U T : Tensor0SSpace (2 + s) I x).domDomCongr
        (ricciSlotPermutation s q))) (eval_ricci S t x)
  apply ext0S_basis basis
  intro m
  have hcomp (q : Fin s) : component0S basis (F q x) m =
      ∑ i, ∑ j, B i j * ricciTensor g x (basis (m q)) (basis j) *
        component0S basis T (Function.update m q i) :=
    (congrArg (fun U : Tensor0SSpace s I x => component0S basis U m) (hF q)).trans
      (trace_slot_component g T basis B hB q m)
  calc component0S basis (A.ricciAction.eval S t x) m
      = ∑ q : Fin s, component0S basis (F q x) m := by
        rw [hsum, component0S_apply, tensor0S_sum_apply]
        rfl
    _ = ∑ q : Fin s, ∑ i, ∑ j, B i j * ricciTensor g x (basis (m q)) (basis j) *
        component0S basis T (Function.update m q i) := Finset.sum_congr rfl fun q _ => hcomp q
    _ = component0S basis (ricciTimeCorrection g T) m := by
      rw [ricciTimeCorrection_component_in_basis g T basis B hB]
      simp only [Finset.sum_mul]

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

theorem covariantTimeDerivWithin_curvature_timeLeaf {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) :
    covariantTimeDerivWithin S.base.metric (fun r => nablaKRm04Field S r k x) D.carrier (t : ℝ) =
      (CurvatureExpression.timeLeaf k).eval S (t : ℝ) x := by
  have he : (CurvatureExpression.timeLeaf k).eval S (t : ℝ) x =
      metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + (CurvatureExpression.residual k).eval S (t : ℝ) x +
      ricciTimeCorrection (S.base.metric (t : ℝ)) (nablaKRm04Field S (t : ℝ) k x) := by
    change metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + (CurvatureExpression.residual k).eval S (t : ℝ) x +
      (CurvatureExpression.curvature k).ricciAction.eval S (t : ℝ) x = _
    exact congrArg (fun U : Tensor0SSpace (4 + k) I x =>
      metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + (CurvatureExpression.residual k).eval S (t : ℝ) x + U)
      (CurvatureExpression.eval_ricciAction S (t : ℝ) (CurvatureExpression.curvature k) x)
  exact (covariantTimeDerivWithin_curvature_fixed_expression S hS k t x).trans he.symm
end DifferentialGeometry.PDE.RicciFlow
