import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.MetricDerivative
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

open Bundle DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem mvfderiv_hasDerivAt_of_joint
    [I.Boundaryless]
    {f : Real → M → Real} {ft : M → Real} {t : Real}
    (hfs : ∀ r, MDifferentiable I 𝓘(Real, Real) (f r))
    (hft : MDifferentiable I 𝓘(Real, Real) ft)
    (hf : ∀ y, ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
      (fun p : Real × M => f p.1 p.2) (t, y))
    (ht : ∀ y, HasDerivAt (fun r => f r y) (ft y) t)
    (x : M) (v : TangentSpace I x) :
    HasDerivAt (fun r => mvfderiv (I := I) (f r) x v)
      (mvfderiv (I := I) ft x v) t := by
  have h := fixedBaseOnRegularity_of_timeDerivWithin
    (I := I) (timeSet := Set.univ) (regularSet := {t}) (u := Set.univ)
    (F := f) (Ft := fun _ => ft)
    (by simp) (by intro r hr; exact Filter.univ_mem)
    (by intro r hr y hy; rcases Set.mem_singleton_iff.mp hr with rfl; exact hf y)
    (by intro r hr y hy; exact hfs r y)
    (by intro r hr y hy; exact hft y)
    (by intro r hr y; rcases Set.mem_singleton_iff.mp hr with rfl
        exact (ht y).hasDerivWithinAt)
  exact (h t (Set.mem_singleton t) x (Set.mem_univ x) v).hasDerivAt Filter.univ_mem

variable [FiniteDimensional Real E] [IsManifold I ∞ M] [T2Space M]

private theorem hessianSec_eval_sections
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    hessianSec (I := I) cov hcov f hf x (vec2 (I := I) (X x) (Y x)) =
      mvfderiv (I := I) (fun y => mvfderiv (I := I) f y (Y y)) x (X x) -
        mvfderiv (I := I) f x (cov (fun y => Y y) x (X x)) := by
  rw [(hessianSec_nabla (I := I) cov hcov f hf) x X (Y x)]
  have heval := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_one_eval_smooth_slots (I := I) cov X Y
    (duSec (I := I) f hf) x
  simpa only [nablaDuAt, duSec_apply, differential1FormFun_apply_eq_mvfderiv] using heval

theorem hessianSec_hasDerivAt
    [I.Boundaryless]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (f : Real → M → Real) (hfs : ∀ r, ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (f r))
    (ft : M → Real) (hft : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) ft)
    {t : Real}
    (hf : ∀ y, ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : Real × M => f p.1 p.2) (t, y))
    (ht : ∀ y, HasDerivAt (fun r => f r y) (ft y) t)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun r => hessianSec (I := I) cov hcov (f r) (hfs r) x (vec2 (I := I) v w))
      (hessianSec (I := I) cov hcov ft hft x (vec2 (I := I) v w)) t := by
  classical
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x w
  have hfirst (y : M) (z : TangentSpace I y) :
      HasDerivAt (fun r => mvfderiv (I := I) (f r) y z)
        (mvfderiv (I := I) ft y z) t :=
    mvfderiv_hasDerivAt_of_joint
      (fun r => (hfs r).mdifferentiable (by simp))
      (hft.mdifferentiable (by simp))
      (fun y => (hf y).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) ht y z
  have hsecond := mvfderiv_hasDerivAt_of_joint
    (I := I) (f := fun r y => mvfderiv (I := I) (f r) y (Y y))
    (ft := fun y => mvfderiv (I := I) ft y (Y y))
    (fun r => (dphi_apply_smooth (I := I) (f r) (hfs r) Y).mdifferentiable (by simp))
    ((dphi_apply_smooth (I := I) ft hft Y).mdifferentiable (by simp))
    (fun y => (prodExtDerivAt_smooth (I := I) (hf y) Y.contMDiff.contMDiffAt).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (fun y => hfirst y (Y y)) x (X x)
  have hsub := hsecond.sub (hfirst x (cov (fun y => Y y) x (X x)))
  have hvalue (u : M → Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
      hessianSec (I := I) cov hcov u hu x (vec2 (I := I) v w) =
        mvfderiv (I := I) (fun y => mvfderiv (I := I) u y (Y y)) x (X x) -
          mvfderiv (I := I) u x (cov (fun y => Y y) x (X x)) := by
    rw [← hX, ← hY]
    exact hessianSec_eval_sections cov hcov u hu X Y x
  rw [← hvalue ft hft] at hsub
  exact hsub.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => hvalue (f r) (hfs r))

end DifferentialGeometry.Geometry.Operator

end

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

open Bundle DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

theorem hessianSec_leviCivita_hasDerivAt
    (g : Real → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (t : Real)
    (hg : ∀ x v w, HasDerivAt (fun r => (g r).inner x v w) (h x (vec2 v w)) t)
    (hgs : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (f : Real → M → Real) (hfs : ∀ r, ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (f r))
    (ft : M → Real) (hft : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) ft)
    (hf : ∀ y, ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : Real × M => f p.1 p.2) (t, y))
    (ht : ∀ y, HasDerivAt (fun r => f r y) (ft y) t)
    (x : M) (slots : Fin 2 → TangentSpace I x) :
    HasDerivAt
      (fun r => hessianSec (I := I) (LeviCivita (g r))
        (leviCivita_contMDiffCovariantDerivativeLocally (g r)) (f r) (hfs r) x slots)
      ((hessianSec (I := I) (LeviCivita (g t))
          (leviCivita_contMDiffCovariantDerivativeLocally (g t)) ft hft x -
        connectionDifferenceOutput (I := I) (leviCivitaVariation g t x)
          (duSec (I := I) (f t) (hfs t) x)) slots) t := by
  let cov := fun r => LeviCivita (I := I) (g r)
  let hcov := fun r => leviCivita_contMDiffCovariantDerivativeLocally (I := I) (g r)
  let A := fun r => CovariantDerivative.difference (cov r) (cov t) x
  have hdf : HasDerivAt (fun r => mvfderiv (I := I) (f r) x)
      (mvfderiv (I := I) ft x) t := by
    apply hasDerivAt_clm_apply.mpr
    intro v
    have hd := fixedBaseOnRegularity_of_timeDerivWithin
      (I := I) (timeSet := Set.univ) (regularSet := {t}) (u := Set.univ)
      (F := f) (Ft := fun _ => ft)
      (by simp) (by intro r hr; exact Filter.univ_mem)
      (by intro r hr y hy; rcases Set.mem_singleton_iff.mp hr with rfl
          exact (hf y).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
      (by intro r hr y hy; exact (hfs r).mdifferentiable (by simp) y)
      (by intro r hr y hy; exact hft.mdifferentiable (by simp) y)
      (by intro r hr y; rcases Set.mem_singleton_iff.mp hr with rfl
          exact (ht y).hasDerivWithinAt)
    exact (hd t (Set.mem_singleton t) x (Set.mem_univ x) v).hasDerivAt Filter.univ_mem
  have hA : HasDerivAt A (leviCivitaVariation g t x) t :=
    leviCivita_difference_hasDerivAt g h t hg hgs x
  have hA0 : A t (slots 1) (slots 0) = 0 := by
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 1)
    rw [← hY]
    change (IsCovariantDerivativeOn.difference _ _ x) (Y x) (slots 0) = 0
    rw [IsCovariantDerivativeOn.difference_apply _ _ (Set.mem_univ x) Y.mdifferentiableAt]
    simp
  have hAeval := (hA.clm_apply (hasDerivAt_const t (slots 1))).clm_apply
    (hasDerivAt_const t (slots 0))
  simp only [ContinuousLinearMap.map_zero, add_zero] at hAeval
  have hcorrection := hdf.clm_apply hAeval
  simp only [hA0, ContinuousLinearMap.map_zero, zero_add] at hcorrection
  have hslots : slots = vec2 (I := I) (slots 0) (slots 1) := by
    funext a
    fin_cases a <;> rfl
  have hfixed := hessianSec_hasDerivAt (I := I) (cov t) (hcov t) f hfs ft hft
    hf ht x (slots 0) (slots 1)
  rw [← hslots] at hfixed
  have hresult := hfixed.sub hcorrection
  have hvalue (r : Real) :
      hessianSec (I := I) (cov r) (hcov r) (f r) (hfs r) x slots =
        hessianSec (I := I) (cov t) (hcov t) (f r) (hfs r) x slots -
          mvfderiv (I := I) (f r) x (A r (slots 1) (slots 0)) := by
    have heq := congrArg (fun T => T slots)
      (hess_sub_conn (I := I) (cov r) (cov t) (hcov r) (hcov t) (f r) (hfs r) x)
    change hessianSec (I := I) (cov r) (hcov r) (f r) (hfs r) x slots -
        hessianSec (I := I) (cov t) (hcov t) (f r) (hfs r) x slots =
      -(connectionDifferenceOutput (I := I) (A r) (duSec (I := I) (f r) (hfs r) x) slots)
      at heq
    have hout :
        connectionDifferenceOutput (I := I) (A r) (duSec (I := I) (f r) (hfs r) x) slots =
          mvfderiv (I := I) (f r) x (A r (slots 1) (slots 0)) := by
      rw [← Tensor0SSpace.eval_eq, connectionDifferenceOutput_apply]
      exact differential1FormFun_apply_eq_mvfderiv (I := I) (f r) x _
    rw [hout] at heq
    linarith
  have hout :
      (connectionDifferenceOutput (I := I) (leviCivitaVariation g t x)
        (duSec (I := I) (f t) (hfs t) x)) slots =
      mvfderiv (I := I) (f t) x (leviCivitaVariation g t x (slots 1) (slots 0)) := by
    rw [← Tensor0SSpace.eval_eq, connectionDifferenceOutput_apply]
    exact differential1FormFun_apply_eq_mvfderiv (I := I) (f t) x _
  change HasDerivAt _
    (hessianSec (I := I) (cov t) (hcov t) ft hft x slots -
      connectionDifferenceOutput (I := I) (leviCivitaVariation g t x)
        (duSec (I := I) (f t) (hfs t) x) slots) t
  rw [hout]
  exact hresult.congr_of_eventuallyEq (Filter.Eventually.of_forall hvalue)

end DifferentialGeometry.Geometry.Operator

end
