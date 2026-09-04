import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeAlgebra
import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalNabla0STimeDeriv
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Tangent
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_hasDerivWithinAt
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T R : Set Real) (N : ℕ)
    (hbase : ∀ t ∈ R, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) T R ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ R, ∀ x : M,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivWithinAt
          (fun r : Real => (covDerivOfField (I := I) gRef (A r) p) x v)
          ((covDerivOfField (I := I) gRef (B t) p) x v) T t := by
  intro p
  induction p with
  | zero =>
      intro _ t ht x v
      exact hbase t ht x v
  | succ p ih =>
      intro hpN t ht x v
      have hext : ∀ a : Fin (p + 3),
          ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
            σ x = v a :=
        fun a => ContMDiffSection.exists_eq_at x (v a)
      choose σ hσ using hext
      have hcl := Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt (I := I)
        (leviCivitaConnectionOfMetric (I := I) gRef)
        (σ 0) (fun a : Fin (p + 2) => σ a.succ)
        (fun r => covDerivOfField (I := I) gRef (A r) p)
        (fun t' => covDerivOfField (I := I) gRef (B t') p)
        T x t
        ((hswap p (by omega) (fun a : Fin (p + 2) => σ a.succ) x) t ht x
          (Set.mem_singleton x) (σ 0 x))
        (fun a => ih (by omega) t ht x
          (Function.update (fun b : Fin (p + 2) => σ b.succ x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun q : M => σ a.succ q) x) (σ 0 x))))
      have hv : (Fin.cons (σ 0 x) (fun a : Fin (p + 2) => σ a.succ x) :
          Fin (p + 3) → TangentSpace I x) = v := by
        funext b
        refine Fin.cases ?_ ?_ b
        · simpa using hσ 0
        · intro a
          simpa using hσ a.succ
      rw [hv] at hcl
      exact hcl

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_swapReg
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T R : Set Real) (hRT : R ⊆ T)
    (hRnhds : ∀ {t : Real}, t ∈ R → T ∈ 𝓝 t)
    (N : ℕ)
    (hbase : ∀ t ∈ R, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ R, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M => (covDerivOfField (I := I) gRef (A q.1) p) q.2
          (fun a : Fin (p + 2) => V a q.2)) (t, x))
    (hFdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ s ∈ T, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (covDerivOfField (I := I) gRef (A s) p) y
          (fun a : Fin (p + 2) => V a y)) x)
    (hFtdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ R, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (covDerivOfField (I := I) gRef (B t) p) y
          (fun a : Fin (p + 2) => V a y)) x) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) T R ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p')) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ihp =>
    intro hpN V x₀
    refine fixedBaseOnReg_of_timeDerivWithin (I := I) hRT
      (fun {t} ht => hRnhds ht)
      (fun t ht x _ => hSmooth p hpN V t ht x)
      (fun s hs x _ => hFdiff p hpN V s hs x)
      (fun t ht x _ => hFtdiff p hpN V t ht x) ?_
    intro t ht x'
    exact covDerivOfField_eval_hasDerivWithinAt (I := I) gRef A B T R p hbase
      (fun q hq => ihp q hq (lt_trans hq hpN))
      p le_rfl t ht x' (fun a : Fin (p + 2) => V a x')

omit [I.Boundaryless] [IsManifold I 2 M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_contMDiffAt
    (gRef : SmoothRiemannianMetric I M)
    (A : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {t : Real} {x : M}
    (hbase : ∀ V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => (A q.1) q.2 (fun a : Fin 2 => V a q.2)) (t, x)) :
    ∀ p : ℕ, ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x) := by
  intro p
  induction p with
  | zero => intro V; exact hbase V
  | succ p ih =>
      intro V
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩
      have hWsec : ∀ a : Fin (p + 2),
          ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
            (fun y : M =>
              (⟨y, ((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a.succ q) y) ((V 0) y)⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
        intro a
        simpa [TensorLieDeriv.covariantDerivVectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (V 0) (V a.succ)
      let W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun a =>
        ⟨fun y : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef)
            (fun q : M => V a.succ q) y) ((V 0) y), hWsec a⟩
      have hdec : ∀ q : Real × M,
          (covDerivOfField (I := I) gRef (A q.1) (p + 1)) q.2
              (fun a : Fin (p + 3) => V a q.2)
            = mvfderiv (I := I)
                (fun y : M => (covDerivOfField (I := I) gRef (A q.1) p) y
                  (fun a : Fin (p + 2) => V a.succ y)) q.2 ((V 0) q.2)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef (A q.1) p) q.2
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b q.2) := by
        intro q
        have hv : (fun a : Fin (p + 3) => V a q.2)
            = Fin.cons ((V 0) q.2) (fun a : Fin (p + 2) => V a.succ q.2) := by
          funext b
          refine Fin.cases ?_ ?_ b
          · simp
          · intro a
            simp
        have hupd : ∀ a : Fin (p + 2),
            (fun b : Fin (p + 2) =>
              (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a)) b q.2)
              = Function.update (fun b : Fin (p + 2) => V b.succ q.2) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun z : M => V a.succ z) q.2) ((V 0) q.2)) := by
          intro a
          funext b
          by_cases hba : b = a
          · subst hba
            simp [W]
          · simp [Function.update_of_ne hba]
        rw [covDerivOfField_succ, metricCovDerivStep_apply, hv,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hupd a]
      have h1 := prodExtDerivAt_smooth (I := I)
        (F := fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) p) q.2
            (fun a : Fin (p + 2) => V a.succ q.2))
        (X := fun y : M => (V 0) y) (t := t) (x := x)
        (ih (fun a : Fin (p + 2) => V a.succ))
        ((V 0).contMDiff.contMDiffAt)
      have h2 : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun q : Real × M =>
            ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef (A q.1) p) q.2
                (fun b : Fin (p + 2) =>
                  (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                    b q.2)) (t, x) :=
        ContMDiffAt.sum fun a _ =>
          ih (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
      have hfun : (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) (p + 1)) q.2
            (fun a : Fin (p + 3) => V a q.2))
          = fun q : Real × M =>
              mvfderiv (I := I)
                (fun y : M => (covDerivOfField (I := I) gRef (A q.1) p) y
                  (fun a : Fin (p + 2) => V a.succ y)) q.2 ((V 0) q.2)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef (A q.1) p) q.2
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b q.2) :=
        funext hdec
      rw [hfun]
      exact h1.sub h2

omit [I.Boundaryless] [IsManifold I 2 M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_smoothAt
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {x : M}
    (hbase : ∀ V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => A0 y (fun a : Fin 2 => V a y)) x) :
    ∀ p : ℕ, ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (covDerivOfField (I := I) gRef A0 p) y
            (fun a : Fin (p + 2) => V a y)) x := by
  intro p
  induction p with
  | zero => intro V; exact hbase V
  | succ p ih =>
      intro V
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩
      have hWsec : ∀ a : Fin (p + 2),
          ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
            (fun y : M =>
              (⟨y, ((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a.succ q) y) ((V 0) y)⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
        intro a
        simpa [TensorLieDeriv.covariantDerivVectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (V 0) (V a.succ)
      let W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun a =>
        ⟨fun y : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef)
            (fun q : M => V a.succ q) y) ((V 0) y), hWsec a⟩
      have hdec : ∀ y : M,
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (fun a : Fin (p + 3) => V a y)
            = mvfderiv (I := I)
                (fun z : M => (covDerivOfField (I := I) gRef A0 p) z
                  (fun a : Fin (p + 2) => V a.succ z)) y ((V 0) y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b y) := by
        intro y
        have hv : (fun a : Fin (p + 3) => V a y)
            = Fin.cons ((V 0) y) (fun a : Fin (p + 2) => V a.succ y) := by
          funext b
          refine Fin.cases ?_ ?_ b
          · simp
          · intro a
            simp
        have hupd : ∀ a : Fin (p + 2),
            (fun b : Fin (p + 2) =>
              (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a)) b y)
              = Function.update (fun b : Fin (p + 2) => V b.succ y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun z : M => V a.succ z) y) ((V 0) y)) := by
          intro a
          funext b
          by_cases hba : b = a
          · subst hba
            simp [W]
          · simp [Function.update_of_ne hba]
        rw [covDerivOfField_succ, metricCovDerivStep_apply, hv,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hupd a]
      have h1 := mvfderiv_apply_contMDiffAt I
        (f := fun z : M => (covDerivOfField (I := I) gRef A0 p) z
          (fun a : Fin (p + 2) => V a.succ z))
        (x₀ := x)
        (ih (fun a : Fin (p + 2) => V a.succ))
        (V 0)
      have h2 : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef A0 p) y
                (fun b : Fin (p + 2) =>
                  (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                    b y)) x :=
        ContMDiffAt.sum fun a _ =>
          ih (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
      have hfun : (fun y : M =>
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
            (fun a : Fin (p + 3) => V a y))
          = fun y : M =>
              mvfderiv (I := I)
                (fun z : M => (covDerivOfField (I := I) gRef A0 p) z
                  (fun a : Fin (p + 2) => V a.succ z)) y ((V 0) y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b y) :=
        funext hdec
      rw [hfun]
      exact h1.sub h2

omit [I.Boundaryless] [IsManifold I 2 M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_mdiffAt
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        (covDerivOfField (I := I) gRef A0 p) y
          (fun a : Fin (p + 2) => V a y)) x :=
  (covDerivOfField_eval_smoothAt (I := I) gRef A0
    (fun W => Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
      (I := I) A0 W x)
    p V).mdifferentiableAt (by simp)

end HCGCompactness
end DifferentialGeometry
