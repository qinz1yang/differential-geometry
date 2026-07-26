import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTower

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Compact-open convergence of component covariant-derivative towers

This file records the metric-free continuity of \`iterCovComp\`: compact-open
\`C∞\` convergence of the base component arrays and Christoffel arrays is
preserved by every finite level of the component covariant-derivative tower.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.HCGCompactness
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {Idx : Type*} [Fintype Idx]

private def constFrame (e : Idx → E) :
    Idx → (x : E) → TangentSpace 𝓘(Real, E) x :=
  fun i _ ↦ e i

private def covCompStep (e : Idx → E) {r : Nat} :
    ((E →L[Real] ((Fin r → Idx) → Real)) ×
      (Idx → Idx → Idx → Real) × ((Fin r → Idx) → Real)) →
        ((Fin (r + 1) → Idx) → Real) :=
  fun q n ↦
    q.1 (e (n 0)) (Fin.tail n) -
      ∑ s : Fin r, ∑ p : Idx,
        q.2.1 (n 0) (Fin.tail n s) p *
          q.2.2 (Function.update (Fin.tail n) s p)

omit [FiniteDimensional Real E] [CompleteSpace E] in
private theorem covCompStep_contDiff (e : Idx → E) {r : Nat} :
    ContDiff Real (∞ : WithTop ℕ∞) (covCompStep e (r := r)) := by
  unfold covCompStep
  fun_prop

private theorem iterCovComp_succ_eq_step
    {U : Set E} (hU : IsOpen U) (e : Idx → E) {r : Nat}
    (chr : E → Idx → Idx → Idx → Real)
    (base : E → (Fin r → Idx) → Real) (a : Nat)
    (hbase : ContDiffOn Real (∞ : WithTop ℕ∞)
      (iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base a) U) :
    Set.EqOn
      (iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base (a + 1))
      (fun x ↦ covCompStep e
        (fderiv Real
            (iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base a) x,
          chr x,
          iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base a x))
      U := by
  classical
  intro x hx
  funext n
  rw [iterCovComp_succ]
  unfold covCompStep covDerivStepComp frameExtData
  congr 1
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv, mfderiv_eq_fderiv]
  have hdiff : DifferentiableAt Real
      (iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base a) x :=
    (hbase.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hdiffm : ∀ m : Fin (r + a) → Idx, DifferentiableAt Real
      (fun y ↦ iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base a y m) x := by
    intro m
    simpa only [Function.comp_apply] using
      (differentiable_apply (𝕜 := Real) m).differentiableAt.comp x hdiff
  have hpi := fderiv_pi (𝕜 := Real) (x := x)
    (φ := fun m y ↦ iterCovComp (I := 𝓘(Real, E)) (constFrame e) chr base a y m)
    hdiffm
  have happ := congrArg
    (fun L : E →L[Real] ((Fin (r + a) → Idx) → Real) ↦
      L (e (n 0)) (Fin.tail n)) hpi
  simpa only [constFrame, ContinuousLinearMap.pi_apply] using happ.symm

/-- Compact-open \`C∞\` convergence of both the base component array and the
Christoffel array is preserved by every finite level of \`iterCovComp\` in a
fixed model-space frame. -/
theorem iter_comp_conv
    {U : Set E} (hU : IsOpen U) (e : Idx → E) {r : Nat}
    (chr : Nat → E → Idx → Idx → Idx → Real)
    (chrInf : E → Idx → Idx → Idx → Real)
    (base : Nat → E → (Fin r → Idx) → Real)
    (baseInf : E → (Fin r → Idx) → Real)
    (hchr : MapCInfConvOnCompacts U chr chrInf)
    (hbase : MapCInfConvOnCompacts U base baseInf)
    (hchr_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (chr n) U)
    (hchrInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) chrInf U)
    (hbase_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (base n) U)
    (hbaseInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) baseInf U)
    (a : Nat) :
    MapCInfConvOnCompacts U
      (fun n ↦ iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i) (chr n) (base n) a)
      (iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i) chrInf baseInf a) := by
  have hall : ∀ q : Nat,
      MapCInfConvOnCompacts U
          (fun n ↦ iterCovComp (I := 𝓘(Real, E))
            (constFrame e) (chr n) (base n) q)
          (iterCovComp (I := 𝓘(Real, E)) (constFrame e) chrInf baseInf q) ∧
        (∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
          (iterCovComp (I := 𝓘(Real, E)) (constFrame e) (chr n) (base n) q) U) ∧
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (iterCovComp (I := 𝓘(Real, E)) (constFrame e) chrInf baseInf q) U := by
    intro q
    induction q with
    | zero =>
        simpa only [iterCovComp_zero] using
          (And.intro hbase (And.intro hbase_cd hbaseInf_cd))
    | succ q ih =>
        rcases ih with ⟨hT, hT_cd, hTInf_cd⟩
        have hfd : MapCInfConvOnCompacts U
            (fun n x ↦ fderiv Real
              (iterCovComp (I := 𝓘(Real, E))
                (constFrame e) (chr n) (base n) q) x)
            (fun x ↦ fderiv Real
              (iterCovComp (I := 𝓘(Real, E))
                (constFrame e) chrInf baseInf q) x) :=
          hT.fderivOn hU hT_cd hTInf_cd
        have hfd_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦ fderiv Real
              (iterCovComp (I := 𝓘(Real, E))
                (constFrame e) (chr n) (base n) q) x) U :=
          fun n ↦ ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 (hT_cd n)).2
        have hfdInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦ fderiv Real
              (iterCovComp (I := 𝓘(Real, E))
                (constFrame e) chrInf baseInf q) x) U :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hTInf_cd).2
        have hchrT : MapCInfConvOnCompacts U
            (fun n x ↦ (chr n x,
              iterCovComp (I := 𝓘(Real, E))
                (constFrame e) (chr n) (base n) q x))
            (fun x ↦ (chrInf x,
              iterCovComp (I := 𝓘(Real, E))
                (constFrame e) chrInf baseInf q x)) :=
          mapCInfConv_prodMk hU hchr hT hchr_cd hchrInf_cd hT_cd hTInf_cd
        have hchrT_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦ (chr n x,
              iterCovComp (I := 𝓘(Real, E))
                (constFrame e) (chr n) (base n) q x)) U :=
          fun n ↦ (hchr_cd n).prodMk (hT_cd n)
        have hchrTInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦ (chrInf x,
              iterCovComp (I := 𝓘(Real, E))
                (constFrame e) chrInf baseInf q x)) U :=
          hchrInf_cd.prodMk hTInf_cd
        have htriple : MapCInfConvOnCompacts U
            (fun n x ↦
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) (chr n) (base n) q) x,
                chr n x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) (chr n) (base n) q x))
            (fun x ↦
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) chrInf baseInf q) x,
                chrInf x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) chrInf baseInf q x)) :=
          mapCInfConv_prodMk hU hfd hchrT hfd_cd hfdInf_cd
            hchrT_cd hchrTInf_cd
        have htriple_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) (chr n) (base n) q) x,
                chr n x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) (chr n) (base n) q x)) U :=
          fun n ↦ (hfd_cd n).prodMk (hchrT_cd n)
        have htripleInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) chrInf baseInf q) x,
                chrInf x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) chrInf baseInf q x)) U :=
          hfdInf_cd.prodMk hchrTInf_cd
        have hstep : MapCInfConvOnCompacts U
            (fun n x ↦ covCompStep e
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) (chr n) (base n) q) x,
                chr n x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) (chr n) (base n) q x))
            (fun x ↦ covCompStep e
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) chrInf baseInf q) x,
                chrInf x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) chrInf baseInf q x)) :=
          MapCInfConvOnCompacts.comp hU isOpen_univ htriple
            (mapCInfConv_const (covCompStep e))
            htriple_cd htripleInf_cd
            (fun _ ↦ (covCompStep_contDiff e).contDiffOn)
            (covCompStep_contDiff e).contDiffOn
            (Set.mapsTo_univ _ _) (fun _ ↦ Set.mapsTo_univ _ _)
        have hnext := hstep.congr hU
          (fun n ↦ iterCovComp_succ_eq_step hU e (chr n) (base n) q (hT_cd n))
          (iterCovComp_succ_eq_step hU e chrInf baseInf q hTInf_cd)
        have hstep_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦ covCompStep e
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) (chr n) (base n) q) x,
                chr n x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) (chr n) (base n) q x)) U :=
          fun n ↦ (covCompStep_contDiff e).contDiffOn.comp
            (htriple_cd n) (Set.mapsTo_univ _ _)
        have hstepInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun x ↦ covCompStep e
              (fderiv Real
                  (iterCovComp (I := 𝓘(Real, E))
                    (constFrame e) chrInf baseInf q) x,
                chrInf x,
                iterCovComp (I := 𝓘(Real, E))
                  (constFrame e) chrInf baseInf q x)) U :=
          (covCompStep_contDiff e).contDiffOn.comp
            htripleInf_cd (Set.mapsTo_univ _ _)
        exact ⟨hnext,
          fun n ↦ (hstep_cd n).congr
            (iterCovComp_succ_eq_step hU e (chr n) (base n) q (hT_cd n)),
          hstepInf_cd.congr
            (iterCovComp_succ_eq_step hU e chrInf baseInf q hTInf_cd)⟩
  exact (hall a).1

private theorem iterCovComp_zero_base
    (e : Idx → E) {r : Nat}
    (chr : E → Idx → Idx → Idx → Real) (a : Nat) :
    iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i) chr
        (fun (_ : E) (_ : Fin r → Idx) ↦ (0 : Real)) a =
      fun (_ : E) (_ : Fin (r + a) → Idx) ↦ (0 : Real) := by
  classical
  induction a with
  | zero => rfl
  | succ a ih =>
      funext x n
      rw [iterCovComp_succ, ih]
      simp only [covDerivStepComp, frameExtData,
        DifferentialGeometry.extDerivFun_real_eq_mfderiv, mfderiv_const,
        ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
      rfl

/-- If the base arrays converge to zero, every finite component
covariant-derivative tower converges to zero as well. -/
theorem iter_comp_zero
    {U : Set E} (hU : IsOpen U) (e : Idx → E) {r : Nat}
    (chr : Nat → E → Idx → Idx → Idx → Real)
    (chrInf : E → Idx → Idx → Idx → Real)
    (base : Nat → E → (Fin r → Idx) → Real)
    (hchr : MapCInfConvOnCompacts U chr chrInf)
    (hbase : MapCInfConvOnCompacts U base
      (fun (_ : E) (_ : Fin r → Idx) ↦ (0 : Real)))
    (hchr_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (chr n) U)
    (hchrInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) chrInf U)
    (hbase_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (base n) U)
    (a : Nat) :
    MapCInfConvOnCompacts U
      (fun n ↦ iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i) (chr n) (base n) a)
      (fun (_ : E) (_ : Fin (r + a) → Idx) ↦ (0 : Real)) := by
  simpa only [iterCovComp_zero_base] using
    iter_comp_conv hU e chr chrInf base
      (fun (_ : E) (_ : Fin r → Idx) ↦ (0 : Real))
      hchr hbase hchr_cd hchrInf_cd hbase_cd contDiffOn_const a

end DifferentialGeometry.PDE.RicciFlow
