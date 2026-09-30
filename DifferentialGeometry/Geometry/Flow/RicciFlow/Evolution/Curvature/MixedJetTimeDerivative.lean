import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CurvatureExpression
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Intrinsic
import DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ResidualExpression
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

set_option autoImplicit false

universe u uE uH
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff _root_.Topology BigOperators

section Helper

variable {E1 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
  {H1 : Type*} [TopologicalSpace H1] {I1 : ModelWithCorners ℝ E1 H1}
  {M1 : Type*} [TopologicalSpace M1] [ChartedSpace H1 M1] [IsManifold I1 ∞ M1]

theorem christoffel_coeff_eq_basis_repr
    {Idx : Type*} {frame : Idx → (y : M1) → TangentSpace I1 y} {u : Set M1}
    (hframe : IsLocalFrameOn I1 E1 (1 : WithTop ℕ∞) frame u)
    (basisOf : (p : M1) → Module.Basis Idx ℝ (TangentSpace I1 p))
    {x : M1} (hbasis : ∀ᶠ p in 𝓝 x, ∀ a, basisOf p a = frame a p)
    (hx : x ∈ u) (w : TangentSpace I1 x) (p : Idx) :
    hframe.coeff p x w = (basisOf x).repr w p := by
  have hb : hframe.toBasisAt hx = basisOf x := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe]
    exact (hbasis.self_of_nhds k).symm
  rw [IsLocalFrameOn.coeff_apply_of_mem hframe hx (fun _ : M1 => w) p]
  rw [hb]

end Helper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance mixedJetPolyC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance mixedJetPolyC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem christoffelSymbolInFrame_hasDerivAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (t : D.RegularTime) {x : M}
    {Idx : Type*} [Fintype Idx]
    {frame : Idx → (y : M) → TangentSpace I y} {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (basisOf : (p : M) → Module.Basis Idx ℝ (TangentSpace I p))
    (hbasis : ∀ᶠ p in 𝓝 x, ∀ a, basisOf p a = frame a p)
    (hx : x ∈ u) (i a p : Idx) :
    HasDerivAt
      (fun s => christoffelSymbolInFrame (S.family.connection s) frame hframe x i a p)
      (- ∑ l, basisInvMetric (I := I) (S.family.metric t) x (basisOf x) p l *
        (totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (basisOf x i) (vec2 (basisOf x a) (basisOf x l))) +
          totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (basisOf x a) (vec2 (basisOf x i) (basisOf x l))) -
          totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (basisOf x l) (vec2 (basisOf x i) (basisOf x a))))) (t : ℝ) := by
  have hfun : (fun s : ℝ =>
      christoffelSymbolInFrame (S.family.connection s) frame hframe x i a p) =
      fun s : ℝ => (basisOf x).repr
        ((LeviCivita (S.family.metric s)) (frame a) x (basisOf x i)) p := by
    funext s
    rw [christoffelSymbolInFrame_eval]
    have h2 : ((S.family.connection s (frame a) x) (frame i x))
        = ((LeviCivita (S.family.metric s)) (frame a) x) (basisOf x i) := by
      rw [show S.family.connection s = LeviCivita (S.family.metric s) from rfl]
      rw [hbasis.self_of_nhds i]
    rw [h2]
    exact christoffel_coeff_eq_basis_repr hframe basisOf hbasis hx _ p
  rw [hfun]
  have hmd : ∀ j : Idx, MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (frame j)) x := by
    intro j
    exact (hframe.contMDiffAt hu hx j).mdifferentiableAt (by simp)
  have hYx : ∀ j : Idx, frame j x = basisOf x j := fun j => (hbasis.self_of_nhds j).symm
  exact leviCivita_coeff_hasDerivAt_of_solution S hS t x (basisOf x) frame hmd hYx i a p


section CastLe

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [CompleteSpace E'] [T2Space M'] [SigmaCompactSpace M']

def curvatureJetVariableCastLe {n : ℕ} (N K : ℕ) (h : N ≤ K) :
    CurvatureJetPolynomialVariable n N → CurvatureJetPolynomialVariable n K
  | Sum.inl ij => Sum.inl ij
  | Sum.inr js => Sum.inr ⟨⟨js.1.val, by omega⟩, js.2⟩

omit [SigmaCompactSpace M'] in
theorem curvatureJetPolynomialValues_castLe {D : RealTimeInterval}
    (S : SolutionOn (I := I') (M := M') D) {n N K : ℕ} (h : N ≤ K) (t : ℝ) {x : M'}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I' x)) (v : CurvatureJetPolynomialVariable n N) :
    curvatureJetPolynomialValues S K t basis (curvatureJetVariableCastLe N K h v) =
      curvatureJetPolynomialValues S N t basis v := by
  cases v with
  | inl ij => rfl
  | inr js => rfl

end CastLe

def curvatureExpressionJetOrder : {s : ℕ} → CurvatureExpression s → ℕ
  | _, .curvature k => k
  | _, .zero _ => 0
  | _, .add A B => max (curvatureExpressionJetOrder A) (curvatureExpressionJetOrder B)
  | _, .smul _ A => curvatureExpressionJetOrder A
  | _, .product A B =>
      max (curvatureExpressionJetOrder A) (curvatureExpressionJetOrder B)
  | _, .perm _ A => curvatureExpressionJetOrder A
  | _, .trace A => curvatureExpressionJetOrder A

def curvatureExpressionPoly {n : ℕ} : {s : ℕ} → (A : CurvatureExpression s) →
    (N : ℕ) → curvatureExpressionJetOrder A ≤ N →
    (Fin s → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ
  | _, .curvature k, N, h, slots =>
      MvPolynomial.X (Sum.inr ⟨⟨k, by
        have hk : k ≤ N := by
          simpa only [curvatureExpressionJetOrder] using h
        omega⟩, slots⟩)
  | _, .zero _, _, _, _ => 0
  | _, .add A B, N, h, slots =>
      curvatureExpressionPoly A N (le_trans (le_max_left _ _) h) slots +
        curvatureExpressionPoly B N (le_trans (le_max_right _ _) h) slots
  | _, .smul c A, N, h, slots =>
      MvPolynomial.C c * curvatureExpressionPoly A N h slots
  | _, .product (s := s) (q := q) A B, N, h, slots =>
      curvatureExpressionPoly A N (le_trans (le_max_left _ _) h)
          (fun a => slots (Fin.castAdd q a)) *
        curvatureExpressionPoly B N (le_trans (le_max_right _ _) h)
          (fun a => slots (Fin.natAdd s a))
  | _, .perm (s := s) e A, N, h, slots =>
      curvatureExpressionPoly A N h (fun i => slots (e i))
  | _, .trace A, N, h, slots =>
      ∑ i : Fin n, ∑ j : Fin n,
        MvPolynomial.X (Sum.inl (i, j)) *
          curvatureExpressionPoly A N h (Fin.cons i (Fin.cons j slots))

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem component0S_tensor0SFieldProduct {s q : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q)
    {n : ℕ} {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (slots : Fin (s + q) → Fin n) :
    component0S (I := I) basis (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x) slots =
      component0S (I := I) basis (A x) (fun a => slots (Fin.castAdd q a)) *
        component0S (I := I) basis (B x) (fun a => slots (Fin.natAdd s a)) := by
  rw [component0S_apply, tensor0SField_product_apply]
  simp only [Function.comp_def]
  rw [← component0S_apply (I := I) (A := A x) basis (fun a => slots (Fin.castAdd q a)),
    ← component0S_apply (I := I) (A := B x) basis (fun a => slots (Fin.natAdd s a))]

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem component0S_metricTraceFirstTwoField {s : ℕ}
    (g : SmoothRiemannianMetric I M) {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (slots : Fin s → Fin n) :
    component0S (I := I) basis (metricTraceFirstTwoField (I := I) (M := M) g A x) slots =
      ∑ i : Fin n, ∑ j : Fin n,
        basisInvMetric (I := I) g x basis i j *
          component0S (I := I) basis (A x) (Fin.cons i (Fin.cons j slots)) := by
  rw [component0S_apply, metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
    (basisInvMetric (I := I) g x basis) (basisInvMetric_isInverse (I := I) g x basis) _
    (fun q => basis (slots q))]
  simp only [metricTrace0S2InBasis]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have harg : metricTraceInput (I := I) (basis i) (basis j) (fun q => basis (slots q))
      = (fun a : Fin (s + 2) =>
          basis ((Fin.cons i (Fin.cons j slots) : Fin (s + 2) → Fin n) a)) := by
    funext a
    cases a using Fin.cases with
    | zero => rfl
    | succ a =>
        cases a using Fin.cases with
        | zero => rfl
        | succ a => rfl
  rw [harg, ← component0S_apply]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem component0S_curvatureExpressionPoly {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) :
    ∀ {s : ℕ} (A : CurvatureExpression s) (N : ℕ)
      (h : curvatureExpressionJetOrder A ≤ N) {n : ℕ} {x : M}
      (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin s → Fin n),
      component0S (I := I) basis (A.eval S t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S N t basis)
          (curvatureExpressionPoly A N h slots) := by
  intro s A
  induction A with
  | curvature k =>
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly, MvPolynomial.eval_X,
        curvatureJetPolynomialValues, component0S_apply]
  | zero s =>
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly, ContMDiffSection.coe_zero,
        Pi.zero_apply, component0S_apply, zero_apply]
      simp
  | add A B ihA ihB =>
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly, ContMDiffSection.coe_add,
        Pi.add_apply, component0S_add_field,
        ihA N (le_trans (le_max_left _ _) h) basis slots,
        ihB N (le_trans (le_max_right _ _) h) basis slots,
        MvPolynomial.eval_add]
  | smul c A ih =>
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly, ContMDiffSection.coe_smul,
        Pi.smul_apply, component0S_smul_field,
        ih N h basis slots, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  | product A B ihA ihB =>
      rename_i s' q'
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly]
      rw [component0S_tensor0SFieldProduct (s := s') (q := q')
        (A := CurvatureExpression.eval S t A) (B := CurvatureExpression.eval S t B) basis slots]
      rw [ihA N (le_trans (le_max_left _ _) h) basis (fun a => slots (Fin.castAdd q' a)),
        ihB N (le_trans (le_max_right _ _) h) basis (fun a => slots (Fin.natAdd s' a)),
        MvPolynomial.eval_mul]
  | perm e A ih =>
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly, Tensor0SField.domDomCongr_apply]
      rw [component0S_apply, Tensor0SSpace.domDomCongr_apply]
      rw [← component0S_apply, ih N h basis (fun i => slots (e i))]
  | trace A ih =>
      rename_i s'
      intro N h n x basis slots
      simp only [CurvatureExpression.eval, curvatureExpressionPoly, MvPolynomial.eval_sum]
      rw [component0S_metricTraceFirstTwoField (s := s') (S.family.metric t) basis]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, curvatureJetPolynomialValues,
        ih N h basis (Fin.cons i (Fin.cons j slots))]
      simp only [SolutionOn.family_metric]


theorem curvatureExpressionJetOrder_spatialDerivative :
    ∀ {s : ℕ} (A : CurvatureExpression s),
      curvatureExpressionJetOrder A.spatialDerivative ≤ curvatureExpressionJetOrder A + 1 := by
  intro s A
  induction A with
  | curvature k =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder]
      omega
  | zero s =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder]
      omega
  | add A B ihA ihB =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder] at *
      omega
  | smul c A ih =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder] at *
      omega
  | product A B ihA ihB =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder] at *
      omega
  | perm e A ih =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder] at *
      omega
  | trace A ih =>
      simp only [CurvatureExpression.spatialDerivative, curvatureExpressionJetOrder] at *
      omega

theorem curvatureExpressionJetOrder_sumFin {s : ℕ} (n : ℕ)
    (A : Fin n → CurvatureExpression s) (B : ℕ)
    (h : ∀ q, curvatureExpressionJetOrder (A q) ≤ B) :
    curvatureExpressionJetOrder (CurvatureExpression.sumFin n A) ≤ B := by
  induction n with
  | zero =>
      simp only [CurvatureExpression.sumFin, curvatureExpressionJetOrder]
      exact Nat.zero_le B
  | succ n ih =>
      simp only [CurvatureExpression.sumFin, curvatureExpressionJetOrder]
      exact max_le (h 0) (ih (fun q => A q.succ) fun q => h q.succ)

theorem curvatureExpressionJetOrder_binaryContraction (k a b : ℕ)
    (e : Fin ((4 + a) + (4 + b)) ≃ Fin ((4 + k) + 4)) :
    curvatureExpressionJetOrder (CurvatureExpression.binaryContraction k a b e) ≤ max a b := by
  simp only [CurvatureExpression.binaryContraction, curvatureExpressionJetOrder]
  omega

theorem curvatureExpressionJetOrder_gamma (k : ℕ) :
    curvatureExpressionJetOrder (CurvatureExpression.gamma k) ≤ k + 1 := by
  have h₁ := curvatureExpressionJetOrder_sumFin (s := 4 + (k + 1)) (4 + k)
    (fun q => CurvatureExpression.binaryContraction (k + 1) 1 k (sigmaRic1 k q)) (k + 1)
    (fun q => le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp))
  have h₂ := curvatureExpressionJetOrder_sumFin (s := 4 + (k + 1)) (4 + k)
    (fun q => CurvatureExpression.binaryContraction (k + 1) 1 k (sigmaRic2 k q)) (k + 1)
    (fun q => le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp))
  have h₃ := curvatureExpressionJetOrder_sumFin (s := 4 + (k + 1)) (4 + k)
    (fun q => CurvatureExpression.binaryContraction (k + 1) 1 k (sigmaRic3 k q)) (k + 1)
    (fun q => le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp))
  simp only [CurvatureExpression.gamma, curvatureExpressionJetOrder]
  omega

theorem curvatureExpressionJetOrder_comm (k : ℕ) :
    curvatureExpressionJetOrder (CurvatureExpression.comm k) ≤ k + 1 := by
  have h₁ := curvatureExpressionJetOrder_sumFin (s := 4 + (k + 1)) (4 + k)
    (fun q => CurvatureExpression.binaryContraction (k + 1) 1 k (sigmaDiffA k q)) (k + 1)
    (fun q => le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp))
  have h₂ := curvatureExpressionJetOrder_sumFin (s := 4 + (k + 1)) (4 + k)
    (fun q => CurvatureExpression.binaryContraction (k + 1) 0 (k + 1) (sigmaDiffB k q)) (k + 1)
    (fun q => le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp))
  have h₃ := curvatureExpressionJetOrder_sumFin (s := 4 + (k + 1)) (4 + (k + 1))
    (fun q => if hq : q.val = 0 then
        CurvatureExpression.binaryContraction (k + 1) (k + 1) 0 (sigmaCurv0 k)
      else CurvatureExpression.binaryContraction (k + 1) (k + 1) 0 (sigmaCurvPos k q hq))
    (k + 1) (fun q => by
      by_cases hq : q.val = 0
      · simp only [dite_eq_left hq]
        exact le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp)
      · simp only [dite_eq_right hq]
        exact le_trans (curvatureExpressionJetOrder_binaryContraction _ _ _ _) (by simp))
  simp only [CurvatureExpression.comm, curvatureExpressionJetOrder]
  omega

theorem curvatureExpressionJetOrder_residual (k : ℕ) :
    curvatureExpressionJetOrder (CurvatureExpression.residual k) ≤ k + 1 := by
  induction k with
  | zero =>
      simp only [CurvatureExpression.residual]
      decide
  | succ k ih =>
      have h₁ := curvatureExpressionJetOrder_spatialDerivative (CurvatureExpression.residual k)
      have h₂ := curvatureExpressionJetOrder_comm k
      have h₃ := curvatureExpressionJetOrder_gamma k
      simp only [CurvatureExpression.residual, curvatureExpressionJetOrder]
      omega

def curvatureJetTracePoly {n : ℕ} (k : ℕ) (slots : Fin (4 + k) → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n (k + 2)) ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    MvPolynomial.X (Sum.inl (i, j)) *
      MvPolynomial.X (Sum.inr ⟨⟨k + 2, by omega⟩, Fin.cons i (Fin.cons j slots)⟩)

def curvatureJetTimeDerivativePoly {n : ℕ} (k : ℕ) (slots : Fin (4 + k) → Fin n) :
    MvPolynomial (CurvatureJetPolynomialVariable n (k + 2)) ℝ :=
  curvatureJetTracePoly k slots +
    curvatureExpressionPoly (CurvatureExpression.residual k) (k + 2)
      (le_trans (curvatureExpressionJetOrder_residual k) (by omega)) slots

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem eval_curvatureJetTracePoly {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) {k : ℕ} {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + k) → Fin n) :
    component0S (I := I) basis
        (metricTraceFirstTwo0STensor (I := I) (S.base.metric t)
          (nablaKRm04Field S t (k + 2) x)) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (k + 2) t basis)
        (curvatureJetTracePoly k slots) := by
  rw [← metricTraceFirstTwoField_apply]
  rw [component0S_metricTraceFirstTwoField (s := 4 + k) (S.base.metric t) basis
    (nablaKRm04Field S t (k + 2))]
  simp only [curvatureJetTracePoly, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, curvatureJetPolynomialValues]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem eval_curvatureExpressionPoly_residual {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {t : ℝ} (ht : t ∈ D.regular) {k : ℕ} {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + k) → Fin n) :
    component0S (I := I) basis (rmResidualField S ⟨t, ht⟩ k x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (k + 2) t basis)
        (curvatureExpressionPoly (CurvatureExpression.residual k) (k + 2)
          (le_trans (curvatureExpressionJetOrder_residual k) (by omega)) slots) := by
  have hres : CurvatureExpression.eval S t (CurvatureExpression.residual k) =
      rmResidualField S ⟨t, ht⟩ k :=
    CurvatureExpression.eval_residual S ⟨t, ht⟩ k
  rw [← hres]
  exact component0S_curvatureExpressionPoly S t (CurvatureExpression.residual k) (k + 2)
    (le_trans (curvatureExpressionJetOrder_residual k) (by omega)) basis slots

theorem exists_nablaKRm04Field_time_derivative_polynomial (n k : ℕ) :
    ∃ Y : (Fin (4 + k) → Fin n) →
        MvPolynomial (CurvatureJetPolynomialVariable n (k + 2)) ℝ,
      ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
        {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
        [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn S → ∀ t ∈ D.regular, ∀ x : M,
        ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
        ∀ slots : Fin (4 + k) → Fin n,
          HasDerivWithinAt
            (fun s => component0S (I := I) basis (nablaKRm04Field S s k x) slots)
            (MvPolynomial.eval (curvatureJetPolynomialValues S (k + 2) t basis)
              (Y slots)) D.carrier t := by
  refine ⟨fun slots => curvatureJetTimeDerivativePoly k slots, ?_⟩
  intro E _ _ _ _ _ H _ I _ M _ _ _ _ _ _ _ D S hS t ht x basis slots
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

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end
