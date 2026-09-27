import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open scoped Topology ContDiff Manifold

variable {σ : Type*}


theorem polynomial_hasDerivWithinAt
    (evolve : σ → MvPolynomial σ ℝ) (v : ℝ → σ → ℝ) {J : Set ℝ} {t : ℝ}
    (hv : ∀ i, HasDerivWithinAt (fun s => v s i)
      (MvPolynomial.eval (v t) (evolve i)) J t) (P : MvPolynomial σ ℝ) :
    HasDerivWithinAt (fun s => MvPolynomial.eval (v s) P)
      (MvPolynomial.eval (v t) (MvPolynomial.mkDerivation ℝ evolve P)) J t := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C, MvPolynomial.derivation_C, map_zero] using
      (hasDerivWithinAt_const t J c)
  | add P Q hP hQ =>
    simpa only [map_add] using hP.fun_add hQ
  | mul_X P i hP =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Derivation.leibniz,
      MvPolynomial.mkDerivation_X, smul_eq_mul, map_add, map_mul,
      add_comm, mul_comm]
      using hP.fun_mul (hv i)


theorem iteratedDerivWithin_polynomial_eval
    (evolve : σ → MvPolynomial σ ℝ) (v : ℝ → σ → ℝ) {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J)
    (hv : ∀ t ∈ J, ∀ i, HasDerivWithinAt (fun s => v s i)
      (MvPolynomial.eval (v t) (evolve i)) J t)
    (P : MvPolynomial σ ℝ) (q : ℕ) :
    ∀ t ∈ J, iteratedDerivWithin q (fun s => MvPolynomial.eval (v s) P) J t =
      MvPolynomial.eval (v t) ((MvPolynomial.mkDerivation ℝ evolve)^[q] P) := by
  induction q with
  | zero => intro t _ht; rfl
  | succ q ih =>
    intro t ht
    rw [iteratedDerivWithin_succ, Function.iterate_succ_apply']
    have hd := polynomial_hasDerivWithinAt evolve v (hv t ht)
      ((MvPolynomial.mkDerivation ℝ evolve)^[q] P)
    have hd' := hd.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => ih s hs)
      (ih t ht)
    exact hd'.derivWithin (hJ t ht)


theorem polynomial_eval_contMDiffAt_of_variables
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {v : M → σ → ℝ} {x : M}
    (hv : ∀ i, ContMDiffAt I 𝓘(ℝ) ∞ (fun y => v y i) x)
    (P : MvPolynomial σ ℝ) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => MvPolynomial.eval (v y) P) x := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contMDiffAt_const (c := c))
  | add P Q hP hQ =>
    apply (hP.add hQ).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => by
      simp only [map_add, Pi.add_apply]
  | mul_X P i hP =>
    apply (hP.mul (hv i)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => by
      simp only [map_mul, MvPolynomial.eval_X, Pi.mul_apply]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
