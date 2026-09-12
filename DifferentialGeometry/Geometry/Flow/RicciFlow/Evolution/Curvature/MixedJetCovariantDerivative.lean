import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.ParallelFrameJetDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.ParallelFrameMetricInverse
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance mixedJetCovariantC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

private local instance mixedJetCovariantC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

def curvatureJetVariableCast (n N : ℕ) :
    CurvatureJetPolynomialVariable n N → CurvatureJetPolynomialVariable n (N + 1)
  | Sum.inl ij => Sum.inl ij
  | Sum.inr js => Sum.inr ⟨⟨js.1.val, by omega⟩, js.2⟩

def curvatureJetSuccessorVariable (n N : ℕ) (d : Fin n) (k : Fin (N + 1))
    (t : Fin (4 + k.val) → Fin n) : CurvatureJetPolynomialVariable n (N + 1) :=
  Sum.inr ⟨⟨k.val + 1, by omega⟩, Fin.cons d t⟩

def covariantDerivativePolynomial {n N r : ℕ}
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ) :
    (Fin (r + 1) → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n (N + 1)) ℝ :=
  fun slots =>
    ∑ k : Fin (N + 1), ∑ t : Fin (4 + k.val) → Fin n,
      MvPolynomial.rename (curvatureJetVariableCast n N)
          (MvPolynomial.pderiv (Sum.inr ⟨k, t⟩) (P (Fin.tail slots))) *
        MvPolynomial.X (curvatureJetSuccessorVariable n N (slots 0) k t)

private theorem sum_derivation_apply {σ : Type*} [Fintype σ]
    (f : σ → Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (Q : MvPolynomial σ ℝ) :
    (∑ i : σ, f i) Q = ∑ i : σ, f i Q := by
  have h := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := ℝ)
    (A := MvPolynomial σ ℝ) (M := MvPolynomial σ ℝ)) f Finset.univ) Q
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using h

private theorem mkDerivation_C_eq_sum_pderiv {σ : Type*} [Fintype σ]
    (c : σ → ℝ) :
    MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (c i))
      = ∑ i : σ, c i • MvPolynomial.pderiv i (R := ℝ) := by
  classical
  refine MvPolynomial.derivation_ext fun j => ?_
  rw [MvPolynomial.mkDerivation_X]
  rw [sum_derivation_apply]
  have hsingle : ∀ x : σ, (c x • MvPolynomial.pderiv x (R := ℝ)) (MvPolynomial.X j)
      = (if x = j then MvPolynomial.C (c x) else 0) := by
    intro x
    rw [Derivation.coe_smul, Pi.smul_apply]
    by_cases hxj : x = j
    · subst hxj
      rw [MvPolynomial.pderiv_X_self]
      rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hxj), smul_zero, if_neg hxj]
  simp only [hsingle]
  simp

private theorem eval_mkDerivation_C_eq_sum_pderiv {σ : Type*} [Fintype σ]
    (c u : σ → ℝ) (Q : MvPolynomial σ ℝ) :
    MvPolynomial.eval u (MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (c i)) Q)
      = ∑ i : σ, c i * MvPolynomial.eval u (MvPolynomial.pderiv i Q) := by
  classical
  rw [mkDerivation_C_eq_sum_pderiv (σ := σ) c]
  simp only [sum_derivation_apply]
  rw [MvPolynomial.eval_sum]
  simp [MvPolynomial.smul_eval]

omit [I.Boundaryless] in
private theorem curvatureJetPolynomialValues_cast {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (N : ℕ) (t : ℝ) {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (v : CurvatureJetPolynomialVariable n N) :
    curvatureJetPolynomialValues S (N + 1) t basis (curvatureJetVariableCast n N v) =
      curvatureJetPolynomialValues S N t basis v := by
  cases v with
  | inl ij => rfl
  | inr js => rfl

private theorem eval_covariantDerivativePolynomial {n N r : ℕ}
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ)
    (slots : Fin (r + 1) → Fin n)
    (u : CurvatureJetPolynomialVariable n N → ℝ)
    (α : CurvatureJetPolynomialVariable n (N + 1) → ℝ)
    (hu : ∀ i, α (curvatureJetVariableCast n N i) = u i)
    (d : CurvatureJetPolynomialVariable n N → ℝ)
    (hd0 : ∀ a : Fin n × Fin n, d (Sum.inl a) = 0)
    (hd : ∀ (k : Fin (N + 1)) (t : Fin (4 + k.val) → Fin n),
        d (Sum.inr ⟨k, t⟩) = α (curvatureJetSuccessorVariable n N (slots 0) k t)) :
    MvPolynomial.eval u
        (MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (d i)) (P (Fin.tail slots)))
      = MvPolynomial.eval α (covariantDerivativePolynomial P slots) := by
  classical
  have hstep : ∀ (k : Fin (N + 1)) (t : Fin (4 + k.val) → Fin n),
      MvPolynomial.eval u
          (MvPolynomial.pderiv (Sum.inr ⟨k, t⟩) (P (Fin.tail slots)))
        = MvPolynomial.eval α
          (MvPolynomial.rename (curvatureJetVariableCast n N)
            (MvPolynomial.pderiv (Sum.inr ⟨k, t⟩) (P (Fin.tail slots)))) := by
    intro k t
    rw [MvPolynomial.eval_rename]
    rw [show (α ∘ curvatureJetVariableCast n N) = u from funext hu]
  rw [eval_mkDerivation_C_eq_sum_pderiv (σ := CurvatureJetPolynomialVariable n N)]
  rw [Fintype.sum_sum_type]
  rw [Finset.sum_eq_zero (fun a _ => by rw [hd0 a, zero_mul])]
  rw [zero_add]
  rw [Fintype.sum_sigma]
  rw [covariantDerivativePolynomial]
  rw [MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hd k t, hstep k t, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  ring


section MatrixSmoothness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem contMDiffAt_matrix_det {G : M → Matrix ι ι ℝ} {x : M}
    (hG : ∀ i j, ContMDiffAt I 𝓘(ℝ) ∞ (fun p => G p i j) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun p => (G p).det) x := by
  classical
  have hfun : (fun p => (G p).det) =
      fun p => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ k, G p (σ k) k := by
    funext p
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hfun]
  exact ContMDiffAt.sum fun σ _ =>
    contMDiffAt_const.mul (ContMDiffAt.prod fun k _ => hG (σ k) k)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem contMDiffAt_matrix_adjugate {G : M → Matrix ι ι ℝ} {x : M}
    (hG : ∀ i j, ContMDiffAt I 𝓘(ℝ) ∞ (fun p => G p i j) x) (k l : ι) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun p => (G p).adjugate k l) x := by
  classical
  have hfun : (fun p => (G p).adjugate k l) =
      fun p => ((G p).updateRow l (Pi.single k 1)).det := by
    funext p
    rw [Matrix.adjugate_apply]
  rw [hfun]
  have hrow (a b : ι) : (fun p => ((G p).updateRow l (Pi.single k 1)) a b) =
      fun p => if a = l then (Pi.single k (1 : ℝ) : ι → ℝ) b else G p a b := by
    funext p
    by_cases h : a = l
    · subst h
      simp [Matrix.updateRow_self]
    · simp [h]
  refine contMDiffAt_matrix_det (G := fun p => (G p).updateRow l (Pi.single k 1)) fun a b => ?_
  rw [hrow a b]
  by_cases h : a = l
  · rw [show (fun p => if a = l then (Pi.single k (1 : ℝ) : ι → ℝ) b else G p a b) =
        fun _ : M => (Pi.single k (1 : ℝ) : ι → ℝ) b from by
      funext p
      rw [if_pos h]]
    exact contMDiffAt_const
  · rw [show (fun p => if a = l then (Pi.single k (1 : ℝ) : ι → ℝ) b else G p a b) =
        fun p => G p a b from by
      funext p
      rw [if_neg h]]
    exact hG a b

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem contMDiffAt_matrix_inv_entry {G : M → Matrix ι ι ℝ} {x : M}
    (hG : ∀ i j, ContMDiffAt I 𝓘(ℝ) ∞ (fun p => G p i j) x) (hdet : (G x).det ≠ 0)
    (i j : ι) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun p => (G p)⁻¹ i j) x := by
  classical
  have hfun : (fun p => (G p)⁻¹ i j) =
      fun p => ((G p).det)⁻¹ * (G p).adjugate i j := by
    funext p
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [hfun]
  exact ((contMDiffAt_matrix_det hG).inv₀ hdet).mul (contMDiffAt_matrix_adjugate hG i j)

end MatrixSmoothness

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_congr_of_eventuallyEq {f₁ f : M → ℝ} {x : M}
    (h : f₁ =ᶠ[𝓝 x] f) : mvfderiv I f₁ x = mvfderiv I f x := by
  have hx : f₁ x = f x := h.eq_of_nhds
  simp only [mvfderiv]
  rw [Filter.EventuallyEq.mfderiv_eq h, hx]

omit [I.Boundaryless] in
theorem component0S_totalNabla_curvatureJetPolynomial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) {t : ℝ}
    (ht : t ∈ D.regular) {n N r : ℕ}
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r)
    (nablaA : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      r (S.family.connection t) A nablaA)
    (hA : ∀ (y : M) (b : Module.Basis (Fin n) ℝ (TangentSpace I y)) (s : Fin r → Fin n),
      component0S (I := I) b (A y) s =
        MvPolynomial.eval (curvatureJetPolynomialValues S N t b) (P s))
    {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (slots : Fin (r + 1) → Fin n) :
    component0S (I := I) basis (nablaA x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (N + 1) t basis)
        (covariantDerivativePolynomial P slots) := by
  classical
  set w : TangentSpace I x := basis (slots 0) with hw
  obtain ⟨V, hVx, hVpar, hVsm⟩ :=
    exists_tangentField_parallel_direction (I := I) n x basis w (S.family.connection t)
  obtain ⟨basisOf, hbasisOf⟩ := exists_basis_apply_eq_of_frame (I := I) n x basis V hVx
    (fun a => (hVsm a).contMDiffAt.of_le (by simp))
  have hbasisOfx : basisOf x = basis := by
    ext a
    rw [hbasisOf.self_of_nhds a, hVx a]
  have hVs : ∀ a : Fin n,
      MDiffAt (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x :=
    fun a => (hVsm a).contMDiffAt.mdifferentiableAt (by simp)
  have hVmet : ∀ a b : Fin n,
      MDiffAt (fun p => (S.base.metric t).inner p (V a p) (V b p)) x := by
    intro a b
    have h := DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) (S.base.metric t) (n := 1) (x := x)
      (X := fun y => V a y) (Y := fun y => V b y)
      ((hVsm a).contMDiffAt.of_le (by simp)) ((hVsm b).contMDiffAt.of_le (by simp)) (by simp)
    exact h.mdifferentiableAt (by simp)
  let Gram : M → Matrix (Fin n) (Fin n) ℝ :=
    fun p => Matrix.of (fun a b => (S.base.metric t).inner p (V a p) (V b p))
  have hGram : ∀ a b : Fin n, ContMDiffAt I 𝓘(ℝ) ∞ (fun p => Gram p a b) x := by
    intro a b
    have h := DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) (S.base.metric t) (n := ∞) (x := x)
      (X := fun y => V a y) (Y := fun y => V b y)
      (hVsm a).contMDiffAt (hVsm b).contMDiffAt (by simp)
    simpa only [Gram, Matrix.of_apply] using h
  have hprod : Matrix.of (basisInvMetric (I := I) (S.base.metric t) x (basisOf x)) * Gram x = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [Gram, Matrix.of_apply, hbasisOfx, hVx] using
      (basisInvMetric_isInverse (I := I) (S.base.metric t) x (basisOf x) a b).1
  have hdetGram : (Gram x).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hprod
  have hv : ∀ i : CurvatureJetPolynomialVariable n N,
      MDiffAt (fun y => curvatureJetPolynomialValues S N t (basisOf y) i) x := by
    intro i
    cases i with
    | inl a =>
      have heq : (fun y => curvatureJetPolynomialValues S N t (basisOf y) (Sum.inl a))
          =ᶠ[𝓝 x] fun y => (Gram y)⁻¹ a.1 a.2 := by
        filter_upwards [hbasisOf] with p hp
        simp only [curvatureJetPolynomialValues]
        have hmat : Matrix.of (fun i j => (S.base.metric t).inner p (basisOf p i)
            (basisOf p j)) = Gram p := by
          ext i j
          simp only [Matrix.of_apply, Gram]
          rw [hp i, hp j]
        rw [basisInvMetric_eq_matrix_inv, hmat]
      exact ((contMDiffAt_matrix_inv_entry (I := I) (G := Gram) hGram hdetGram a.1 a.2
        ).mdifferentiableAt (by simp)).congr_of_eventuallyEq heq
    | inr b =>
      have heq : (fun y => curvatureJetPolynomialValues S N t (basisOf y) (Sum.inr b))
          =ᶠ[𝓝 x]
          fun y => nablaKRm04Field (I := I) S t b.1.val y
            (fun a : Fin (4 + b.1.val) => V (b.2 a) y) := by
        filter_upwards [hbasisOf] with p hp
        simp only [curvatureJetPolynomialValues, component0S_apply]
        congr 1
        funext a
        exact hp (b.2 a)
      have hcont : ContMDiffAt I 𝓘(ℝ) ∞
          (fun y => nablaKRm04Field (I := I) S t b.1.val y
            (fun a : Fin (4 + b.1.val) => V (b.2 a) y)) x :=
        DifferentialGeometry.TensorMultilinear.contMDiffAt_section_apply
          (𝕜 := ℝ) (I := I)
          (T := fun y => nablaKRm04Field (I := I) S t b.1.val y)
          (v := fun a y => V (b.2 a) y)
          ((nablaKRm04Field (I := I) S t b.1.val).contMDiff x)
          (fun a => (hVsm (b.2 a)).contMDiffAt)
      exact (hcont.mdifferentiableAt (by simp)).congr_of_eventuallyEq heq
  have hmetricCompatible : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I)
      (S.family.connection t) (S.base.metric t) := by
    simpa only [SolutionOn.family_connection, RealTimeInterval.regularToFlow_val] using
      S.metricCompatible (D.regularToFlow ⟨t, ht⟩)
  have hd0 : ∀ a : Fin n × Fin n,
      mvfderiv I (fun p => curvatureJetPolynomialValues S N t (basisOf p) (Sum.inl a)) x w = 0 :=
    fun a => mvfderiv_basisInvMetric_eq_zero_of_metricCompatible_parallel_frame (I := I)
      hmetricCompatible V basisOf hbasisOf hVmet hVs hVpar a.1 a.2
  have hd : ∀ (k : Fin (N + 1)) (ts : Fin (4 + k.val) → Fin n),
      mvfderiv I (fun p => curvatureJetPolynomialValues S N t (basisOf p) (Sum.inr ⟨k, ts⟩)) x w
        = curvatureJetPolynomialValues S (N + 1) t basis
          (curvatureJetSuccessorVariable n N (slots 0) k ts) := by
    intro k ts
    have heq : (fun p => curvatureJetPolynomialValues S N t (basisOf p) (Sum.inr ⟨k, ts⟩))
        =ᶠ[𝓝 x]
        fun p => nablaKRm04Field (I := I) S t k.val p (fun a : Fin (4 + k.val) => V (ts a) p) := by
      filter_upwards [hbasisOf] with p hp
      simp only [curvatureJetPolynomialValues, component0S_apply]
      congr 1
      funext a
      exact hp (ts a)
    rw [mvfderiv_congr_of_eventuallyEq heq]
    rw [mvfderiv_nablaKRm04Field_frameComp (I := I) S t k.val x w V ts hVpar
      (fun a => (hVsm a).contMDiffAt.of_le (by simp))]
    rw [curvatureJetSuccessorVariable, hw]
    simp only [curvatureJetPolynomialValues, component0S_apply]
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ a => simp [hVx]
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞)) (F := E)
    (V := TangentSpace I) x w
  have hstep := TotalNabla0SRealizes.eval_C1_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (cov := S.family.connection t) (α := A) (nablaAlpha := nablaA) hreal X
    (fun a : Fin r => V (slots a.succ)) x
    (fun a => (hVsm (slots a.succ)).contMDiffAt.of_le (by simp))
  rw [hX] at hstep
  have hcorr : ∀ a : Fin r, A x (Function.update (fun b : Fin r => V (slots b.succ) x) a
      (((S.family.connection t) (V (slots a.succ)) x) w)) = 0 := by
    intro a
    rw [hVpar (slots a.succ)]
    exact MultilinearMap.map_update_zero (A x).toMultilinearMap _ a
  rw [Finset.sum_eq_zero (fun a _ => hcorr a), sub_zero] at hstep
  have hslots : Fin.cons w (fun a : Fin r => V (slots a.succ) x) =
      fun i : Fin (r + 1) => basis (slots i) := by
    funext i
    cases i using Fin.cases with
    | zero => simpa using hw
    | succ a => simpa using (hVx (slots a.succ))
  have hevent : (fun p => A p (fun a : Fin r => V (slots a.succ) p)) =ᶠ[𝓝 x]
      fun p => MvPolynomial.eval (curvatureJetPolynomialValues S N t (basisOf p))
        (P (Fin.tail slots)) := by
    filter_upwards [hbasisOf] with p hp
    have h1 : (fun a : Fin r => V (slots a.succ) p) =
        fun a : Fin r => basisOf p ((Fin.tail slots) a) := by
      funext a
      exact (hp (slots a.succ)).symm
    rw [h1]
    exact hA p (basisOf p) (Fin.tail slots)
  have hvals : ∀ i : CurvatureJetPolynomialVariable n N,
      curvatureJetPolynomialValues S (N + 1) t basis (curvatureJetVariableCast n N i)
        = curvatureJetPolynomialValues S N t basis i :=
    fun i => curvatureJetPolynomialValues_cast (I := I) S N t basis i
  calc
    component0S (I := I) basis (nablaA x) slots
        = nablaA x (Fin.cons w (fun a : Fin r => V (slots a.succ) x)) := by
          rw [component0S_apply, hslots]
    _ = mvfderiv I (fun p => A p (fun a : Fin r => V (slots a.succ) p)) x w := hstep
    _ = mvfderiv I (fun p => MvPolynomial.eval
          (curvatureJetPolynomialValues S N t (basisOf p)) (P (Fin.tail slots))) x w := by
          rw [mvfderiv_congr_of_eventuallyEq hevent]
    _ = MvPolynomial.eval (curvatureJetPolynomialValues S N t (basisOf x))
          (MvPolynomial.mkDerivation ℝ
            (fun i => MvPolynomial.C
              (mvfderiv I (fun p => curvatureJetPolynomialValues S N t (basisOf p) i) x w))
            (P (Fin.tail slots))) :=
          mvfderiv_mvPolynomial_eval (I := I) _ _ hv
    _ = MvPolynomial.eval (curvatureJetPolynomialValues S N t basis)
          (MvPolynomial.mkDerivation ℝ
            (fun i => MvPolynomial.C
              (mvfderiv I (fun p => curvatureJetPolynomialValues S N t (basisOf p) i) x w))
            (P (Fin.tail slots))) := by
          rw [hbasisOfx]
    _ = MvPolynomial.eval (curvatureJetPolynomialValues S (N + 1) t basis)
          (covariantDerivativePolynomial P slots) :=
          eval_covariantDerivativePolynomial P slots _ _ hvals _
            (fun a => hd0 a)
            (fun k ts => hd k ts)


omit [I.Boundaryless] in
theorem exists_covariantDerivativePolynomial (n N r : ℕ)
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ) :
    ∃ P' : (Fin (r + 1) → Fin n) →
        MvPolynomial (CurvatureJetPolynomialVariable n (N + 1)) ℝ,
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) {t : ℝ}
        (_ht : t ∈ D.regular)
        (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r)
        (nablaA : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
          (n := ∞) (r + 1))
        (_hreal : TotalNabla0SRealizes (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
          r (S.family.connection t) A nablaA),
        (∀ (y : M) (b : Module.Basis (Fin n) ℝ (TangentSpace I y)) (s : Fin r → Fin n),
          component0S (I := I) b (A y) s =
            MvPolynomial.eval (curvatureJetPolynomialValues S N t b) (P s)) →
        ∀ {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
          (slots : Fin (r + 1) → Fin n),
          component0S (I := I) basis (nablaA x) slots =
            MvPolynomial.eval (curvatureJetPolynomialValues S (N + 1) t basis)
              (P' slots) := by
  refine ⟨covariantDerivativePolynomial P, ?_⟩
  intro D S t ht A nablaA hreal hA x basis slots
  exact component0S_totalNabla_curvatureJetPolynomial S ht P A nablaA hreal hA basis slots

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
