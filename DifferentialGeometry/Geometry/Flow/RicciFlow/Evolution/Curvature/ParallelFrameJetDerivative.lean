import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.PolynomialField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import DifferentialGeometry.Topology.Manifold.PrescribedDifferential

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology BigOperators Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

omit [IsManifold I 2 M] in
theorem exists_tangentField_parallel_direction (n : ℕ) (x : M)
    (v : Module.Basis (Fin n) ℝ (TangentSpace I x)) (w : TangentSpace I x)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    ∃ V : Fin n → (y : M) → TangentSpace I y,
      (∀ a, V a x = v a) ∧ (∀ a, (cov (V a) x) w = 0) ∧
        (∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _)))) := by
  classical
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    choose W hW using fun a => ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := TangentSpace I) x (v a)
    refine ⟨fun a => ⇑(W a), fun a => hW a, fun a => ?_, fun a => (W a).contMDiff⟩
    rw [map_zero]
  · obtain ⟨α, hαw⟩ : ∃ α : TangentSpace I x →L[ℝ] ℝ, α w = 1 := by
      have hrepr : v.repr w ≠ 0 := by
        intro h
        exact hw (v.repr.injective (by simpa using h))
      obtain ⟨j, hj⟩ : ∃ j : Fin n, v.repr w j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hrepr (by ext j; exact hc j)
      have hcoord : v.coord j w = v.repr w j := by simp [Module.Basis.coord]
      refine ⟨(v.repr w j)⁻¹ • (LinearMap.toContinuousLinearMap (v.coord j)), ?_⟩
      rw [smul_apply, LinearMap.coe_toContinuousLinearMap', smul_eq_mul, hcoord,
        inv_mul_cancel₀ hj]
    obtain ⟨φ, hφd, hφx, hφder, -, -⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_smooth_function_with_differential
        (I := I) x 0 α (U := Set.univ) Filter.univ_mem
    choose W hW using fun a => ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := TangentSpace I) x (v a)
    choose Z hZ using fun a => ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := TangentSpace I) x ((cov (⇑(W a)) x) w)
    refine ⟨fun a => (⇑(W a) : (y : M) → TangentSpace I y) +
        (-φ) • (⇑(Z a)), fun a => ?_, fun a => ?_, fun a => ?_⟩
    · simp only [Pi.add_apply]
      simp [hW a, hφx]
    · have hmdW : MDiffAt (T% (⇑(W a) : (y : M) → TangentSpace I y)) x :=
        (W a).contMDiff.mdifferentiableAt (by simp)
      have hmdZ : MDiffAt (T% (⇑(Z a) : (y : M) → TangentSpace I y)) x :=
        (Z a).contMDiff.mdifferentiableAt (by simp)
      have hmdφ : MDiffAt (-φ) x := (hφd.mdifferentiableAt (by simp)).neg
      have hmdZsm : MDiffAt
          (T% ((-φ) • (⇑(Z a) : (y : M) → TangentSpace I y))) x :=
        hmdφ.smul_section hmdZ
      have hadd := (cov.isCovariantDerivativeOn (s := Set.univ)).add hmdW hmdZsm (Set.mem_univ x)
      have hlei := (cov.isCovariantDerivativeOn (s := Set.univ)).leibniz hmdZ hmdφ (Set.mem_univ x)
      rw [hadd, hlei, add_apply, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [hZ a, Pi.neg_apply, hφx, neg_zero, zero_smul, zero_add]
      rw [mvfderiv_neg, neg_apply, hφder, hαw]
      simp
    · have h1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (⇑(W a) : (y : M) → TangentSpace I y)) := (W a).contMDiff
      have h2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (⇑(Z a) : (y : M) → TangentSpace I y)) := (Z a).contMDiff
      have h3 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% ((-φ) • (⇑(Z a) : (y : M) → TangentSpace I y))) :=
        hφd.neg.smul_section h2
      have h4 := h1.add_section h3
      simpa only [Pi.add_apply, Pi.smul_apply] using h4

theorem mvfderiv_nablaKRm04Field_frameComp {D : RealTimeInterval} {n : ℕ}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (k : ℕ) (x : M) (w : TangentSpace I x)
    (V : Fin n → (y : M) → TangentSpace I y) (τ : Fin (4 + k) → Fin n)
    (hVpar : ∀ a, ((S.family.connection t) (V a) x) w = 0)
    (hVs : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x) :
    mvfderiv I (fun p => nablaKRm04Field (I := I) S t k p (fun a => V (τ a) p)) x w =
      nablaKRm04Field (I := I) S t (k + 1) x (Fin.cons w (fun a => V (τ a) x)) := by
  classical
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := TangentSpace I) x w
  have hstep := TotalNabla0SRealizes.eval_C1_slots
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (cov := S.family.connection t) (α := nablaKRm04Field (I := I) S t k)
    (nablaAlpha := nablaKRm04Field (I := I) S t (k + 1))
    (nablaKRm04Field_realizes (I := I) S t k) X
    (fun a : Fin (4 + k) => V (τ a)) x
    (fun a => hVs (τ a))
  rw [hX] at hstep
  have hzero : ∀ a : Fin (4 + k),
      (nablaKRm04Field (I := I) S t k x)
        (Function.update (fun b : Fin (4 + k) => V (τ b) x) a
          (((S.family.connection t) (V (τ a)) x) w)) = 0 := by
    intro a
    rw [hVpar (τ a)]
    exact MultilinearMap.map_update_zero
      ((nablaKRm04Field (I := I) S t k x).toMultilinearMap) _ a
  rw [Finset.sum_eq_zero (fun a _ => hzero a), sub_zero] at hstep
  exact hstep.symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] in
theorem mvfderiv_mvPolynomial_eval {σ : Type*} (v : M → σ → ℝ) (P : MvPolynomial σ ℝ)
    {x : M} {w : TangentSpace I x} (hv : ∀ i, MDiffAt (fun y => v y i) x) :
    mvfderiv I (fun y => MvPolynomial.eval (v y) P) x w =
      MvPolynomial.eval (v x)
        (MvPolynomial.mkDerivation ℝ
          (fun i => MvPolynomial.C (mvfderiv I (fun y => v y i) x w)) P) := by
  classical
  let c : σ → MvPolynomial σ ℝ :=
    fun i => MvPolynomial.C (mvfderiv I (fun y => v y i) x w)
  have key : ∀ P : MvPolynomial σ ℝ,
      MDiffAt (fun y => MvPolynomial.eval (v y) P) x ∧
        mvfderiv I (fun y => MvPolynomial.eval (v y) P) x w =
          MvPolynomial.eval (v x) (MvPolynomial.mkDerivation ℝ c P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      have hfun : (fun y : M => MvPolynomial.eval (v y) (MvPolynomial.C a)) =
          (fun _ : M => a) := by funext y; exact MvPolynomial.eval_C a
      constructor
      · rw [hfun]
        exact mdifferentiableAt_const (I := I) (M := M) (I' := 𝓘(ℝ)) (M' := ℝ) (c := a)
      · rw [hfun, mvfderiv_const, MvPolynomial.derivation_C]
        simp only [zero_apply, map_zero]
    | add P Q hP hQ =>
      have hfun : (fun y : M => MvPolynomial.eval (v y) (P + Q)) =
          (fun y : M => MvPolynomial.eval (v y) P) +
            (fun y : M => MvPolynomial.eval (v y) Q) := by
        funext y; exact MvPolynomial.eval_add
      constructor
      · rw [hfun]; exact hP.1.add hQ.1
      · rw [hfun, mvfderiv_add hP.1 hQ.1, add_apply, hP.2, hQ.2, map_add, MvPolynomial.eval_add]
    | mul_X P i hP =>
      have hfun : (fun y : M => MvPolynomial.eval (v y) (P * MvPolynomial.X i)) =
          (fun y : M => MvPolynomial.eval (v y) P) * (fun y : M => v y i) := by
        funext y; rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]; rfl
      constructor
      · rw [hfun]; exact hP.1.mul (hv i)
      · rw [hfun, mvfderiv_mul hP.1 (hv i), add_apply, smul_apply, smul_apply, hP.2,
          Derivation.leibniz, MvPolynomial.mkDerivation_X]
        simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
          Algebra.smul_def, Algebra.algebraMap_self_apply]
        have hci : MvPolynomial.eval (v x) (c i) = (mvfderiv I (fun y => v y i) x) w :=
          MvPolynomial.eval_C _
        rw [hci]
  exact (key P).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
