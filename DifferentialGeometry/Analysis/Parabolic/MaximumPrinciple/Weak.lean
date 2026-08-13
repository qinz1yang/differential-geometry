import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section


def spacetimeSlab (T : Real) : Set (Real × M) :=
  Set.Icc 0 T ×ˢ Set.univ


def parabolicOperatorWithDrift
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M) : Real :=
  derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
    heatOperatorWithDrift (I := I) G t (X t) (u t) x

@[simp] theorem parabolicOperatorWithDrift_eq
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X u t x =
      derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
        heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
  rfl


theorem parabolic_const_sub
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => C - u s y) t x =
      - parabolicOperatorWithDrift (I := I) G T X u t x := by
  unfold parabolicOperatorWithDrift
  have htime :
      derivWithin (fun s : Real => C - u s x) (Set.Icc 0 T) t =
        - derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t := by
    have hconst : DifferentiableWithinAt Real
        (fun _s : Real => C) (Set.Icc 0 T) t :=
      differentiableWithinAt_const C
    rw [derivWithin_fun_sub hconst hu_time]
    have hconst_deriv :
        derivWithin (fun _s : Real => C) (Set.Icc 0 T) t = 0 := by
      exact (hasDerivWithinAt_const
        (x := t) (s := Set.Icc 0 T) (c := C)).derivWithin huniq
    rw [hconst_deriv]
    ring
  have hsub_space : forall y : M,
      MDifferentiableAt I 𝓘(Real, Real) (fun z : M => u t z - C) y := by
    intro y
    exact (hu_space y).sub mdifferentiableAt_const
  have hsub_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y) x := by
    have hplain :
        (fun y : M =>
          gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y) =
        (fun y : M => gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      calc
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y =
          gradientFun (I := I) (G.metric t) (u t) y -
            gradientFun (I := I) (G.metric t) (fun _ : M => C) y := by
            exact gradientFun_sub (I := I) (G.metric t)
              (hu_space y) mdifferentiableAt_const
        _ = gradientFun (I := I) (G.metric t) (u t) y := by
            rw [gradientFun_const]
            simp
    have hsection :
        (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y) =
        (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      simpa using congrFun hplain y
    rw [hsection]
    exact hu_grad
  have hheat_sub :
      heatOperatorWithDrift (I := I) G t (X t) (fun y : M => u t y - C) x =
        heatOperatorWithDrift (I := I) G t (X t) (u t) x :=
    heatOperatorWithDrift_sub_const (I := I) G t (X t) C hu_space x
  have hheat_scale :
      heatOperatorWithDrift (I := I) G t (X t)
          ((-1 : Real) • fun y : M => u t y - C) x =
        (-1 : Real) *
          heatOperatorWithDrift (I := I) G t (X t) (fun y : M => u t y - C) x :=
    heatOperatorWithDrift_const_smul (I := I) G t (X t) (-1)
      (f := fun y : M => u t y - C) hsub_space hsub_grad
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => C - u t y) x =
        - heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
    have hfun :
        (fun y : M => C - u t y) =
          ((-1 : Real) • fun y : M => u t y - C) := by
      funext y
      simp
    rw [hfun, hheat_scale, hheat_sub]
    ring
  rw [htime, hheat]
  ring

theorem parabolic_add
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u v : Real -> M -> Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y + v s y) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x +
        parabolicOperatorWithDrift (I := I) G T X v t x := by
  unfold parabolicOperatorWithDrift
  rw [derivWithin_fun_add hu_time hv_time]
  rw [heatDrift_add (I := I) G t (X t)
    hu_space hv_space hu_grad hv_grad]
  ring

theorem parabolic_smul
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (a : Real) (u : Real -> M -> Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => a * u s y) t x =
      a * parabolicOperatorWithDrift (I := I) G T X u t x := by
  unfold parabolicOperatorWithDrift
  rw [derivWithin_const_mul a hu_time]
  have hheat := heatOperatorWithDrift_const_smul
    (I := I) G t (X t) a hu_space hu_grad
  have hheat' :
      heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => a * u t y) x =
        a * heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
    simpa [smul_eq_mul] using hheat
  rw [hheat']
  ring

theorem parabolic_neg
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => -u s y) t x =
      -parabolicOperatorWithDrift (I := I) G T X u t x := by
  have hfun : (fun s y => -u s y) =
      (fun s y => (-1 : Real) * u s y) := by
    funext s y
    ring
  rw [hfun, parabolic_smul (I := I) G T X (-1) u t x
    hu_time hu_space hu_grad]
  ring

theorem parabolic_sub
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u v : Real -> M -> Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y - v s y) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x -
        parabolicOperatorWithDrift (I := I) G T X v t x := by
  let nv : Real -> M -> Real := fun s y => (-1 : Real) * v s y
  have hnv_time : DifferentiableWithinAt Real (fun s => nv s x)
      (Set.Icc 0 T) t := hv_time.const_mul (-1)
  have hnv_space : forall y : M,
      MDifferentiableAt I 𝓘(Real, Real) (nv t) y := by
    intro y
    exact (hv_space y).const_smul (-1)
  have hnv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (nv t) y) x := by
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (nv t) y) =
          (T% fun y : M => -gradientFun (I := I) (G.metric t) (v t) y) := by
      funext y
      apply congrArg (fun z =>
        (⟨y, z⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
      change gradientFun (I := I) (G.metric t) ((-1 : Real) • v t) y = _
      rw [gradientFun_const_smul (I := I) (G.metric t) (-1) (hv_space y)]
      simp
    rw [heq]
    exact mdifferentiableAt_neg_section hv_grad
  have hscale := parabolic_smul (I := I) G T X (-1) v t x
    hv_time hv_space hv_grad
  have hadd := parabolic_add (I := I) G T X u nv t x
    hu_time hnv_time hu_space hnv_space hu_grad hnv_grad
  have hsum : (fun s y => u s y + nv s y) =
      (fun s y => u s y - v s y) := by
    funext s y
    dsimp [nv]
    ring
  rw [hsum] at hadd
  change parabolicOperatorWithDrift (I := I) G T X nv t x =
    (-1 : Real) * parabolicOperatorWithDrift (I := I) G T X v t x at hscale
  rw [hscale] at hadd
  simpa only [neg_one_mul, sub_eq_add_neg] using hadd

theorem parabolic_sum
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {κ : Type} (s : Finset κ)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : κ -> Real -> M -> Real) (t : Real) (x : M)
    (htime : ∀ i ∈ s, DifferentiableWithinAt Real
      (fun a : Real => u i a x) (Set.Icc 0 T) t)
    (hspace : ∀ i ∈ s, ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (u i t) y)
    (hgrad : ∀ i ∈ s, ∀ y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) (u i t) z) y) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun a y => ∑ i ∈ s, u i a y) t x =
      ∑ i ∈ s, parabolicOperatorWithDrift (I := I) G T X (u i) t x := by
  classical
  have hgrad_sum : ∀ (r : Finset κ),
      (∀ i ∈ r, ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (u i t) y) ->
      (∀ i ∈ r, ∀ y : M, MDiffAt (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (u i t) z) y) ->
      ∀ y : M, MDiffAt (T% fun z : M =>
        gradientFun (I := I) (G.metric t)
          (fun w : M => ∑ i ∈ r, u i t w) z) y := by
    intro r hr_space hr_grad y
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t)
          (fun w : M => ∑ i ∈ r, u i t w) z) =
        (fun z : M => ∑ i ∈ r,
          gradientFun (I := I) (G.metric t) (u i t) z) := by
      funext z
      have hfunc :
          (fun w : M => ∑ i ∈ r, u i t w) = ∑ i ∈ r, u i t := by
        funext w
        simp only [Finset.sum_apply]
      rw [hfunc]
      exact gradientFun_sum (I := I) (G.metric t) r
        (f := fun i => u i t) (x := z)
        (fun i hi => by simpa only using hr_space i hi z)
    have hsection :
        (T% fun z : M => gradientFun (I := I) (G.metric t)
          (fun w : M => ∑ i ∈ r, u i t w) z) =
        (T% fun z : M => ∑ i ∈ r,
          gradientFun (I := I) (G.metric t) (u i t) z) := by
      funext z
      exact congrArg (fun v =>
        (⟨z, v⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        (congrFun hplain z)
    rw [hsection]
    clear hplain hsection
    induction r using Finset.induction_on with
    | empty =>
        simpa using mdifferentiableAt_zeroSection
          (𝕜 := Real) (F := E) (E := (TangentSpace I : M -> Type _)) (x := y)
    | @insert a r ha ih =>
        have ha_grad := hr_grad a (Finset.mem_insert_self a r) y
        have htail := ih
          (fun i hi => hr_space i (Finset.mem_insert_of_mem hi))
          (fun i hi => hr_grad i (Finset.mem_insert_of_mem hi))
        simpa [Finset.sum_insert ha] using
          mdifferentiableAt_add_section ha_grad htail
  induction s using Finset.induction_on with
  | empty =>
      have hheat_zero :
          heatOperatorWithDrift (I := I) G t (X t)
              (fun _ : M => (0 : Real)) x = 0 := by
        unfold heatOperatorWithDrift laplacianAt laplacian driftTerm gradientAt
        have hzero :
            gradientFun (I := I) (G.metric t) (fun _ : M => (0 : Real)) = 0 := by
          funext y
          exact gradientFun_const (I := I) (G.metric t) 0 y
        rw [hzero]
        simp
      change parabolicOperatorWithDrift (I := I) G T X
        (fun _ _ => (0 : Real)) t x = 0
      unfold parabolicOperatorWithDrift
      rw [hheat_zero]
      simp
  | @insert a s ha ih =>
      have ha_time := htime a (Finset.mem_insert_self a s)
      have hs_time : DifferentiableWithinAt Real
          (fun b : Real => ∑ i ∈ s, u i b x) (Set.Icc 0 T) t :=
        DifferentiableWithinAt.fun_sum fun i hi =>
          htime i (Finset.mem_insert_of_mem hi)
      have ha_space : ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real) (u a t) y :=
        hspace a (Finset.mem_insert_self a s)
      have hs_space : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
          (fun z : M => ∑ i ∈ s, u i t z) y := by
        intro y
        have hfunc :
            (fun z : M => ∑ i ∈ s, u i t z) = ∑ i ∈ s, u i t := by
          funext z
          simp only [Finset.sum_apply]
        rw [hfunc]
        exact MDifferentiableAt.sum (𝕜 := Real) (I := I) (E' := Real)
          (t := s) (f := fun i => u i t) (z := y)
          (fun i hi => by
            simpa only using hspace i (Finset.mem_insert_of_mem hi) y)
      have ha_grad := hgrad a (Finset.mem_insert_self a s) x
      have hs_grad := hgrad_sum s
        (fun i hi => hspace i (Finset.mem_insert_of_mem hi))
        (fun i hi => hgrad i (Finset.mem_insert_of_mem hi)) x
      calc
        parabolicOperatorWithDrift (I := I) G T X
            (fun b y => ∑ i ∈ insert a s, u i b y) t x =
          parabolicOperatorWithDrift (I := I) G T X
            (fun b y => u a b y + ∑ i ∈ s, u i b y) t x := by
              congr 1
              funext b y
              rw [Finset.sum_insert ha]
        _ = parabolicOperatorWithDrift (I := I) G T X (u a) t x +
              parabolicOperatorWithDrift (I := I) G T X
                (fun b y => ∑ i ∈ s, u i b y) t x :=
          parabolic_add (I := I) G T X (u a)
            (fun b y => ∑ i ∈ s, u i b y) t x
            ha_time hs_time ha_space hs_space ha_grad hs_grad
        _ = parabolicOperatorWithDrift (I := I) G T X (u a) t x +
              ∑ i ∈ s,
                parabolicOperatorWithDrift (I := I) G T X (u i) t x := by
          rw [ih
            (fun i hi => htime i (Finset.mem_insert_of_mem hi))
            (fun i hi => hspace i (Finset.mem_insert_of_mem hi))
            (fun i hi => hgrad i (Finset.mem_insert_of_mem hi))]
        _ = ∑ i ∈ insert a s,
              parabolicOperatorWithDrift (I := I) G T X (u i) t x := by
          rw [Finset.sum_insert ha]

theorem parabolic_mul
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u v : Real -> M -> Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hu_grad : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) (u t) z) y)
    (hv_grad : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) (v t) z) y) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y * v s y) t x =
      u t x * parabolicOperatorWithDrift (I := I) G T X v t x +
        v t x * parabolicOperatorWithDrift (I := I) G T X u t x -
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t (u t) x)
            (gradientAt (I := I) G t (v t) x) := by
  unfold parabolicOperatorWithDrift
  rw [derivWithin_fun_mul hu_time hv_time]
  rw [heatDrift_mul (I := I) G t (X t) hu_space hv_space hu_grad hv_grad]
  ring

private theorem lap_comp_nhds
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {φ : Real → Real} {f : M → Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => φ (f y)) x =
      deriv φ (f x) * laplacian (I := I) cov g f x +
        deriv (deriv φ) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  let c : M → Real := fun y => deriv φ (f y)
  have hc : MDifferentiableAt I 𝓘(Real, Real) c x :=
    hφ'.mdifferentiableAt.comp x hf.self_of_nhds
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z => φ (f z)) y)
        =ᶠ[𝓝 x]
      (fun y : M => c y • gradientFun (I := I) g f y) := by
    filter_upwards [hf] with y hy
    exact gradientFun_comp (I := I) g (hφ (f y)) hy
  have hscaled :
      MDiffAt
        (T% fun y : M => c y • gradientFun (I := I) g f y) x :=
    hc.smul_section hgrad
  have hgrad_total :
      (T% fun y : M =>
        gradientFun (I := I) g (fun z => φ (f z)) y) =ᶠ[𝓝 x]
      (T% fun y : M => c y • gradientFun (I := I) g f y) := by
    filter_upwards [hgrad_eq] with y hy
    change TotalSpace.mk' E y
        (gradientFun (I := I) g (fun z => φ (f z)) y) =
      TotalSpace.mk' E y (c y • gradientFun (I := I) g f y)
    rw [hy]
  have hgrad_comp :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g (fun z => φ (f z)) y) x :=
    hscaled.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov.toFun
          (fun y : M =>
            gradientFun (I := I) g (fun z => φ (f z)) y) x =
        cov.toFun
          (fun y : M => c y • gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_comp hscaled Filter.univ_mem hgrad_eq
  calc
    laplacian (I := I) cov g (fun y : M => φ (f y)) x =
        divergence (I := I) cov
          (c • fun y : M => gradientFun (I := I) g f y) x := by
      unfold laplacian divergence
      rw [hcov]
      rfl
    _ = c x * laplacian (I := I) cov g f x +
          g.inner x (gradientFun (I := I) g c x)
            (gradientFun (I := I) g f x) :=
      divergence_smul_gradientFun_pair (I := I) cov g hc hgrad
    _ = deriv φ (f x) * laplacian (I := I) cov g f x +
          deriv (deriv φ) (f x) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
      rw [gradientFun_comp
        (I := I) g hφ' hf.self_of_nhds]
      simp [c]

theorem parabolic_comp_nhds
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    {φ : Real → Real} (u : Real → M → Real) (t : Real) (x : M)
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (u t x))
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => φ (u s y)) t x =
      deriv φ (u t x) *
          parabolicOperatorWithDrift (I := I) G T X u t x -
        deriv (deriv φ) (u t x) *
          (G.metric t).inner x
            (gradientAt (I := I) G t (u t) x)
            (gradientAt (I := I) G t (u t) x) := by
  have htime :
      derivWithin (fun s : Real => φ (u s x)) (Set.Icc 0 T) t =
        deriv φ (u t x) *
          derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t := by
    simpa only [Function.comp_apply, derivWithin_univ] using
      (derivWithin_comp (x := t)
        (h := fun s : Real => u s x) (h₂ := φ)
        (s := Set.Icc 0 T) (s' := Set.univ)
        (hφ (u t x)).differentiableWithinAt hu_time
        (Set.mapsTo_univ _ _))
  have hlap :=
    lap_comp_nhds (I := I) (G.connection t) (G.metric t)
      hφ hφ' hu_space hu_grad
  have hgrad :=
    gradientFun_comp
      (I := I) (G.metric t) (hφ (u t x)) hu_space.self_of_nhds
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
    laplacianAt driftTerm gradientAt
  rw [htime, hlap, hgrad]
  simp only [map_smul, smul_eq_mul]
  ring

theorem parabolic_comp
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    {φ : Real -> Real} (u : Real -> M -> Real) (t : Real) (x : M)
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (u t x))
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => φ (u s y)) t x =
      deriv φ (u t x) *
          parabolicOperatorWithDrift (I := I) G T X u t x -
        deriv (deriv φ) (u t x) *
          (G.metric t).inner x
            (gradientAt (I := I) G t (u t) x)
            (gradientAt (I := I) G t (u t) x) := by
  have htime :
      derivWithin (fun s : Real => φ (u s x)) (Set.Icc 0 T) t =
        deriv φ (u t x) *
          derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t := by
    simpa only [Function.comp_apply, derivWithin_univ] using
      (derivWithin_comp (x := t)
        (h := fun s : Real => u s x) (h₂ := φ)
        (s := Set.Icc 0 T) (s' := Set.univ)
        (hφ (u t x)).differentiableWithinAt hu_time
        (Set.mapsTo_univ _ _))
  unfold parabolicOperatorWithDrift
  rw [htime]
  rw [heatDrift_comp (I := I) G t (X t)
    hφ hφ' hu_space hu_grad]
  ring

theorem reaction_difference_lower_bound_on_negative_region
    {uval cval Fu Fc L : Real}
    (hlip : |Fu - Fc| <= L * |uval - cval|)
    (hneg : uval - cval < 0) :
    L * (uval - cval) <= Fu - Fc := by
  have hlow_abs : -(L * |uval - cval|) <= Fu - Fc := by
    exact le_trans (neg_le_neg hlip) (neg_abs_le (Fu - Fc))
  have hvabs : |uval - cval| = -(uval - cval) := abs_of_neg hneg
  calc
    L * (uval - cval) = -(L * |uval - cval|) := by
      rw [hvabs]
      ring
    _ <= Fu - Fc := hlow_abs

theorem negative_region_parabolic_lower_bound
    {uval cval Pu Pv cderiv Fu Fc L : Real}
    (hsuper : Fu <= Pu)
    (hode : cderiv = Fc)
    (hsub : Pv = Pu - cderiv)
    (hlip : |Fu - Fc| <= L * |uval - cval|)
    (hneg : uval - cval < 0) :
    L * (uval - cval) <= Pv := by
  have hlow : L * (uval - cval) <= Fu - Fc :=
    reaction_difference_lower_bound_on_negative_region hlip hneg
  have hupper : Fu - Fc <= Pv := by
    calc
      Fu - Fc <= Pu - cderiv := by
        rw [hode]
        exact sub_le_sub_right hsuper Fc
      _ = Pv := hsub.symm
  exact le_trans hlow hupper

theorem parabolic_sub_time_curve_identity
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (t : Real)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (x : M)
    (hu : DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc : DifferentiableWithinAt Real c (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => u s y - c s) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x -
        derivWithin c (Set.Icc 0 T) t := by
  unfold parabolicOperatorWithDrift
  have htime :
      derivWithin (fun s : Real => u s x - c s) (Set.Icc 0 T) t =
        derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
          derivWithin c (Set.Icc 0 T) t := by
    exact derivWithin_fun_sub hu hc
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t) (fun y : M => u t y - c t) x =
        heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
    exact heatOperatorWithDrift_sub_const (I := I) G t (X t) (c t) hu_space x
  rw [htime, hheat]
  ring

theorem parabolic_exp_rescale_identity
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T L : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (v : Real -> M -> Real)
    (t : Real)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (x : M)
    (hv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x)
    (hv : DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hscale : DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
      (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => Real.exp (-L * s) * v s y) t x =
      Real.exp (-L * t) *
        (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
  unfold parabolicOperatorWithDrift
  have hlinear_diff :
      DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
  have hlinear_deriv :
      derivWithin (fun s : Real => -L * s) (Set.Icc 0 T) t = -L := by
    have hid :
        derivWithin (fun s : Real => s) (Set.Icc 0 T) t = 1 := by
      exact derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t) huniq
    rw [derivWithin_const_mul (-L)
      (d := fun s : Real => s) (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [hid]
    ring
  have hscale_deriv :
      derivWithin (fun s : Real => Real.exp (-L * s)) (Set.Icc 0 T) t =
        -L * Real.exp (-L * t) := by
    rw [derivWithin_exp hlinear_diff huniq]
    rw [hlinear_deriv]
    ring
  have htime :
      derivWithin (fun s : Real => Real.exp (-L * s) * v s x) (Set.Icc 0 T) t =
        (-L * Real.exp (-L * t)) * v t x +
          Real.exp (-L * t) * derivWithin (fun s : Real => v s x) (Set.Icc 0 T) t := by
    rw [derivWithin_fun_mul hscale hv]
    rw [hscale_deriv]
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => Real.exp (-L * t) * v t y) x =
        Real.exp (-L * t) * heatOperatorWithDrift (I := I) G t (X t) (v t) x := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      heatOperatorWithDrift_const_smul (I := I) G t (X t) (Real.exp (-L * t))
        (f := v t) hv_space hv_grad
  rw [htime, hheat]
  ring

theorem parabolic_exp_rescale_nonneg_of_potential
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 < T) (L : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (V v : Real -> M -> Real)
    (t : Real) (ht : t ∈ Set.Icc 0 T)
    (hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (x : M)
    (hv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x)
    (hv : DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hv_nonneg : 0 <= v t x) (hV : L <= V t x)
    (hsuper : 0 <=
      parabolicOperatorWithDrift (I := I) G T X v t x - V t x * v t x) :
    0 <= parabolicOperatorWithDrift (I := I) G T X
      (fun s y => Real.exp (-L * s) * v s y) t x := by
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hscale : DifferentiableWithinAt Real
      (fun s : Real => Real.exp (-L * s)) (Set.Icc 0 T) t :=
    (((differentiableAt_const (-L)).mul differentiableAt_id).exp
      (x := t)).differentiableWithinAt
  rw [parabolic_exp_rescale_identity (I := I) G T L X v t huniq
    hv_space x hv_grad hv hscale]
  apply mul_nonneg (Real.exp_pos _).le
  have hreaction : 0 <= (V t x - L) * v t x :=
    mul_nonneg (sub_nonneg.mpr hV) hv_nonneg
  linarith


structure ParabolicUpperSupportAt
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (t : Real) (x : M) where
  v : Real -> M -> Real
  eq_at : v t x = w t x
  upper_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      w p.1 p.2 <= v p.1 p.2
  time_diff :
    DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (v t) y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) x
  operator_nonneg :
    0 <= parabolicOperatorWithDrift (I := I) G T X v t x

private theorem spacetimeSlab_isCompact
    [CompactSpace M] (T : Real) :
    IsCompact (spacetimeSlab (M := M) T) := by
  unfold spacetimeSlab
  exact isCompact_Icc.prod isCompact_univ

private theorem derivWithin_nonpos_at_Icc_min_of_pos
    {φ : Real -> Real} {T t : Real}
    (hmin : IsLocalMinOn φ (Set.Icc 0 T) t)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) :
    derivWithin φ (Set.Icc 0 T) t <= 0 := by
  have hdir : (0 : Real) - t ∈ posTangentConeAt (Set.Icc 0 T) t := by
    have hseg : segment Real t 0 ⊆ Set.Icc 0 T := by
      rw [segment_symm, segment_eq_Icc ht.1]
      intro y hy
      exact ⟨hy.1, hy.2.trans ht.2⟩
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg :
      (0 : Real) <=
        (fderivWithin Real φ (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) :=
    hmin.fderivWithin_nonneg hdir
  have hlin :
      (fderivWithin Real φ (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) =
        (0 - t) * derivWithin φ (Set.Icc 0 T) t := by
    rw [← fderivWithin_derivWithin (𝕜 := Real) (f := φ) (s := Set.Icc 0 T) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real φ (Set.Icc 0 T) t : Real →L[Real] Real).map_smul
        (0 - t) (1 : Real))
  have htneg : (0 : Real) - t < 0 := sub_neg.mpr htpos
  rw [hlin] at hnonneg
  exact nonpos_of_mul_nonneg_right hnonneg htneg


omit [TopologicalSpace M] in
private theorem derivWithin_add_eps_mul_time
    {w : Real -> M -> Real} {T t ε : Real} {x : M}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hw : DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t) :
    derivWithin (fun s : Real => w s x + ε * s) (Set.Icc 0 T) t =
      derivWithin (fun s : Real => w s x) (Set.Icc 0 T) t + ε := by
  have hlinear :
      DifferentiableWithinAt Real (fun s : Real => ε * s) (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul ε
  have hderiv_linear :
      derivWithin (fun s : Real => ε * s) (Set.Icc 0 T) t = ε := by
    rw [derivWithin_const_mul ε
      (d := fun s : Real => s) (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t) huniq]
    ring
  rw [derivWithin_fun_add hw hlinear]
  rw [hderiv_linear]


theorem strict_barrier_nonnegative_of_positive_time
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  classical
  have hbarrier_nonneg :
      forall ε : Real, 0 < ε ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          0 <= w t x + ε * t := by
    intro ε hε
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    let Φ : Real × M -> Real := fun p => w p.1 p.2 + ε * p.1
    have hΦ_cont : ContinuousOn Φ (spacetimeSlab (M := M) T) := by
      have hlinear :
          ContinuousOn (fun p : Real × M => ε * p.1) (spacetimeSlab (M := M) T) :=
        (continuous_const.mul continuous_fst).continuousOn
      exact hw_cont.add hlinear
    have hslab_compact : IsCompact (spacetimeSlab (M := M) T) :=
      spacetimeSlab_isCompact (M := M) T
    have hslab_nonempty : (spacetimeSlab (M := M) T).Nonempty :=
      ⟨(tb, xb), ⟨htb, trivial⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hΦ_cont
    rcases p0 with ⟨t0, x0⟩
    have hp0_time : t0 ∈ Set.Icc 0 T := hp0.1
    have hΦ_min_bad : Φ (t0, x0) <= Φ (tb, xb) :=
      hp0min (show (tb, xb) ∈ spacetimeSlab (M := M) T from ⟨htb, trivial⟩)
    have hΦ0_neg : Φ (t0, x0) < 0 := lt_of_le_of_lt hΦ_min_bad hbneg
    have ht0_ne_zero : t0 ≠ 0 := by
      intro ht0
      have hnonneg0 : 0 <= Φ (t0, x0) := by
        simp [Φ, ht0, hw0 x0]
      exact not_lt_of_ge hnonneg0 hΦ0_neg
    have ht0_pos : 0 < t0 := lt_of_le_of_ne hp0_time.1 (Ne.symm ht0_ne_zero)
    have hT_pos : 0 < T := lt_of_lt_of_le ht0_pos hp0_time.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hT_pos).uniqueDiffWithinAt hp0_time
    have htime_min : IsMinOn (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min (show (s, x0) ∈ spacetimeSlab (M := M) T from ⟨hs, trivial⟩)
    have htime_diff :
        DifferentiableWithinAt Real (fun s : Real => w s x0 + ε * s)
          (Set.Icc 0 T) t0 := by
      exact (hw_time t0 hp0_time ht0_pos x0).add
        ((differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t0)).const_mul ε)
    have hbarrier_deriv_nonpos :
        derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 <= 0 :=
      derivWithin_nonpos_at_Icc_min_of_pos htime_min.localize hp0_time ht0_pos
    have hderiv_eq :
      derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 =
        derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 + ε :=
      derivWithin_add_eps_mul_time (M := M) huniq (hw_time t0 hp0_time ht0_pos x0)
    have hw_deriv_le : derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 <= -ε := by
      linarith
    have hw_t0_neg : w t0 x0 < 0 := by
      have hεt_nonneg : 0 <= ε * t0 := mul_nonneg (le_of_lt hε) hp0_time.1
      nlinarith [hΦ0_neg, hεt_nonneg]
    have hspatial_min : IsLocalMin (w t0) x0 := by
      unfold IsLocalMin IsMinFilter
      exact Filter.Eventually.of_forall fun y => by
        have hymin : Φ (t0, x0) <= Φ (t0, y) :=
          hp0min (show (t0, y) ∈ spacetimeSlab (M := M) T from ⟨hp0_time, trivial⟩)
        dsimp [Φ] at hymin ⊢
        linarith
    have hheat_nonneg :
        0 <= heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg (I := I) G t0 (X t0)
        hspatial_min (hw_mdiff t0 hp0_time ht0_pos x0)
        (Filter.Eventually.of_forall fun y => hw_mdiff t0 hp0_time ht0_pos y)
        (hw_grad t0 hp0_time ht0_pos x0)
    have hP_neg :
        parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge (hnegative t0 hp0_time ht0_pos x0 hw_t0_neg) hP_neg
  intro t ht x
  by_contra hnot
  have hw_neg : w t x < 0 := lt_of_not_ge hnot
  by_cases ht_zero : t = 0
  · exact not_lt_of_ge (by simpa [ht_zero] using hw0 x) hw_neg
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    let ε : Real := -(w t x) / (2 * t)
    have hε_pos : 0 < ε := by
      exact div_pos (neg_pos.mpr hw_neg) (mul_pos two_pos ht_pos)
    have hbarrier := hbarrier_nonneg ε hε_pos t ht x
    have hε_mul : ε * t = -(w t x) / 2 := by
      dsimp [ε]
      field_simp [ht_zero]
    have hbarrier_neg : w t x + ε * t < 0 := by
      rw [hε_mul]
      linarith
    exact not_lt_of_ge hbarrier hbarrier_neg

theorem strict_barrier_positive_region
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  classical
  have hbarrier_nonneg :
      forall ε : Real, 0 < ε ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          0 <= w t x + ε * t := by
    intro ε hε
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    let Φ : Real × M -> Real := fun p => w p.1 p.2 + ε * p.1
    have hΦ_cont : ContinuousOn Φ (spacetimeSlab (M := M) T) := by
      have hlinear :
          ContinuousOn (fun p : Real × M => ε * p.1) (spacetimeSlab (M := M) T) :=
        (continuous_const.mul continuous_fst).continuousOn
      exact hw_cont.add hlinear
    have hslab_compact : IsCompact (spacetimeSlab (M := M) T) :=
      spacetimeSlab_isCompact (M := M) T
    have hslab_nonempty : (spacetimeSlab (M := M) T).Nonempty :=
      ⟨(tb, xb), ⟨htb, trivial⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hΦ_cont
    rcases p0 with ⟨t0, x0⟩
    have hp0_time : t0 ∈ Set.Icc 0 T := hp0.1
    have hΦ_min_bad : Φ (t0, x0) <= Φ (tb, xb) :=
      hp0min (show (tb, xb) ∈ spacetimeSlab (M := M) T from ⟨htb, trivial⟩)
    have hΦ0_neg : Φ (t0, x0) < 0 := lt_of_le_of_lt hΦ_min_bad hbneg
    have ht0_ne_zero : t0 ≠ 0 := by
      intro ht0
      have hnonneg0 : 0 <= Φ (t0, x0) := by
        simp [Φ, ht0, hw0 x0]
      exact not_lt_of_ge hnonneg0 hΦ0_neg
    have ht0_pos : 0 < t0 := lt_of_le_of_ne hp0_time.1 (Ne.symm ht0_ne_zero)
    have hT_pos : 0 < T := lt_of_lt_of_le ht0_pos hp0_time.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hT_pos).uniqueDiffWithinAt hp0_time
    have htime_min : IsMinOn (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min (show (s, x0) ∈ spacetimeSlab (M := M) T from ⟨hs, trivial⟩)
    have htime_diff :
        DifferentiableWithinAt Real (fun s : Real => w s x0 + ε * s)
          (Set.Icc 0 T) t0 := by
      exact (hw_time t0 hp0_time ht0_pos x0).add
        ((differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t0)).const_mul ε)
    have hbarrier_deriv_nonpos :
        derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 <= 0 :=
      derivWithin_nonpos_at_Icc_min_of_pos htime_min.localize hp0_time ht0_pos
    have hderiv_eq :
      derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 =
        derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 + ε :=
      derivWithin_add_eps_mul_time (M := M) huniq (hw_time t0 hp0_time ht0_pos x0)
    have hw_deriv_le : derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 <= -ε := by
      linarith
    have hw_t0_neg : w t0 x0 < 0 := by
      have hεt_nonneg : 0 <= ε * t0 := mul_nonneg (le_of_lt hε) hp0_time.1
      nlinarith [hΦ0_neg, hεt_nonneg]
    have hspatial_min : IsLocalMin (w t0) x0 := by
      unfold IsLocalMin IsMinFilter
      exact Filter.Eventually.of_forall fun y => by
        have hymin : Φ (t0, x0) <= Φ (t0, y) :=
          hp0min (show (t0, y) ∈ spacetimeSlab (M := M) T from ⟨hp0_time, trivial⟩)
        dsimp [Φ] at hymin ⊢
        linarith
    have hheat_nonneg :
        0 <= heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg (I := I) G t0 (X t0)
        hspatial_min (hw_mdiff t0 hp0_time ht0_pos x0)
        (Filter.Eventually.of_forall fun y => hw_mdiff t0 hp0_time ht0_pos y)
        (hw_grad t0 hp0_time ht0_pos x0)
    have hP_neg :
        parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge (hnegative t0 hp0_time ht0_pos x0 hw_t0_neg) hP_neg
  intro t ht x
  by_contra hnot
  have hw_neg : w t x < 0 := lt_of_not_ge hnot
  by_cases ht_zero : t = 0
  · exact not_lt_of_ge (by simpa [ht_zero] using hw0 x) hw_neg
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    let ε : Real := -(w t x) / (2 * t)
    have hε_pos : 0 < ε := by
      exact div_pos (neg_pos.mpr hw_neg) (mul_pos two_pos ht_pos)
    have hbarrier := hbarrier_nonneg ε hε_pos t ht x
    have hε_mul : ε * t = -(w t x) / 2 := by
      dsimp [ε]
      field_simp [ht_zero]
    have hbarrier_neg : w t x + ε * t < 0 := by
      rw [hε_mul]
      linarith
    exact not_lt_of_ge hbarrier hbarrier_neg

theorem strict_barrier_cpt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (K : Set M) (hK : IsCompact K)
    (hw_out : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, x ∉ K -> 0 <= w t x)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (Set.Icc 0 T ×ˢ K))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  classical
  have hbarrier_nonneg :
      forall ε : Real, 0 < ε ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          0 <= w t x + ε * t := by
    intro ε hε
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    have hxbK : xb ∈ K := by
      by_contra hxb
      have hwb : 0 <= w tb xb := hw_out tb htb xb hxb
      have hεtb : 0 <= ε * tb := mul_nonneg (le_of_lt hε) htb.1
      linarith
    let Φ : Real × M -> Real := fun p => w p.1 p.2 + ε * p.1
    have hΦ_cont : ContinuousOn Φ (Set.Icc 0 T ×ˢ K) := by
      have hlinear :
          ContinuousOn (fun p : Real × M => ε * p.1) (Set.Icc 0 T ×ˢ K) :=
        (continuous_const.mul continuous_fst).continuousOn
      exact hw_cont.add hlinear
    have hslab_compact : IsCompact (Set.Icc 0 T ×ˢ K) :=
      isCompact_Icc.prod hK
    have hslab_nonempty : (Set.Icc 0 T ×ˢ K).Nonempty :=
      ⟨(tb, xb), ⟨htb, hxbK⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hΦ_cont
    rcases p0 with ⟨t0, x0⟩
    have hp0_time : t0 ∈ Set.Icc 0 T := hp0.1
    have hΦ_min_bad : Φ (t0, x0) <= Φ (tb, xb) :=
      hp0min (show (tb, xb) ∈ Set.Icc 0 T ×ˢ K from ⟨htb, hxbK⟩)
    have hΦ0_neg : Φ (t0, x0) < 0 := lt_of_le_of_lt hΦ_min_bad hbneg
    have ht0_ne_zero : t0 ≠ 0 := by
      intro ht0
      have hnonneg0 : 0 <= Φ (t0, x0) := by
        simp [Φ, ht0, hw0 x0]
      exact not_lt_of_ge hnonneg0 hΦ0_neg
    have ht0_pos : 0 < t0 := lt_of_le_of_ne hp0_time.1 (Ne.symm ht0_ne_zero)
    have hT_pos : 0 < T := lt_of_lt_of_le ht0_pos hp0_time.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hT_pos).uniqueDiffWithinAt hp0_time
    have htime_min : IsMinOn (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min (show (s, x0) ∈ Set.Icc 0 T ×ˢ K from ⟨hs, hp0.2⟩)
    have htime_diff :
        DifferentiableWithinAt Real (fun s : Real => w s x0 + ε * s)
          (Set.Icc 0 T) t0 := by
      exact (hw_time t0 hp0_time ht0_pos x0).add
        ((differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t0)).const_mul ε)
    have hbarrier_deriv_nonpos :
        derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 <= 0 :=
      derivWithin_nonpos_at_Icc_min_of_pos htime_min.localize hp0_time ht0_pos
    have hderiv_eq :
        derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 =
          derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 + ε :=
      derivWithin_add_eps_mul_time (M := M) huniq (hw_time t0 hp0_time ht0_pos x0)
    have hw_deriv_le : derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 <= -ε := by
      linarith
    have hw_t0_neg : w t0 x0 < 0 := by
      have hεt_nonneg : 0 <= ε * t0 := mul_nonneg (le_of_lt hε) hp0_time.1
      nlinarith [hΦ0_neg, hεt_nonneg]
    have hspatial_min : IsLocalMin (w t0) x0 := by
      unfold IsLocalMin IsMinFilter
      exact Filter.Eventually.of_forall fun y => by
        by_cases hyK : y ∈ K
        · have hymin : Φ (t0, x0) <= Φ (t0, y) :=
            hp0min (show (t0, y) ∈ Set.Icc 0 T ×ˢ K from ⟨hp0_time, hyK⟩)
          dsimp [Φ] at hymin ⊢
          linarith
        · exact (le_of_lt hw_t0_neg).trans (hw_out t0 hp0_time y hyK)
    have hheat_nonneg :
        0 <= heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg (I := I) G t0 (X t0)
        hspatial_min (hw_mdiff t0 hp0_time ht0_pos x0)
        (Filter.Eventually.of_forall fun y => hw_mdiff t0 hp0_time ht0_pos y)
        (hw_grad t0 hp0_time ht0_pos x0)
    have hP_neg :
        parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge (hnegative t0 hp0_time ht0_pos x0 hw_t0_neg) hP_neg
  intro t ht x
  by_contra hnot
  have hw_neg : w t x < 0 := lt_of_not_ge hnot
  by_cases ht_zero : t = 0
  · exact not_lt_of_ge (by simpa [ht_zero] using hw0 x) hw_neg
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    let ε : Real := -(w t x) / (2 * t)
    have hε_pos : 0 < ε :=
      div_pos (neg_pos.mpr hw_neg) (mul_pos two_pos ht_pos)
    have hbarrier := hbarrier_nonneg ε hε_pos t ht x
    have hε_mul : ε * t = -(w t x) / 2 := by
      dsimp [ε]
      field_simp [ht_zero]
    have hbarrier_neg : w t x + ε * t < 0 := by
      rw [hε_mul]
      linarith
    exact not_lt_of_ge hbarrier hbarrier_neg

theorem strict_barrier_cpt_of_upperSupport
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (K : Set M) (hK : IsCompact K)
    (hw_out : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, x ∉ K -> 0 <= w t x)
    (hw_cont : ContinuousOn
      (fun p : Real × M => w p.1 p.2) (Set.Icc 0 T ×ˢ K))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hsupport : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        ParabolicUpperSupportAt (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  classical
  have hbarrier_nonneg :
      forall ε : Real, 0 < ε ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          0 <= w t x + ε * t := by
    intro ε hε
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    have hxbK : xb ∈ K := by
      by_contra hxb
      have hwb : 0 <= w tb xb := hw_out tb htb xb hxb
      have hεtb : 0 <= ε * tb := mul_nonneg (le_of_lt hε) htb.1
      linarith
    let Φ : Real × M -> Real := fun p => w p.1 p.2 + ε * p.1
    have hΦ_cont : ContinuousOn Φ (Set.Icc 0 T ×ˢ K) := by
      have hlinear :
          ContinuousOn (fun p : Real × M => ε * p.1) (Set.Icc 0 T ×ˢ K) :=
        (continuous_const.mul continuous_fst).continuousOn
      exact hw_cont.add hlinear
    have hslab_compact : IsCompact (Set.Icc 0 T ×ˢ K) :=
      isCompact_Icc.prod hK
    have hslab_nonempty : (Set.Icc 0 T ×ˢ K).Nonempty :=
      ⟨(tb, xb), ⟨htb, hxbK⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hΦ_cont
    rcases p0 with ⟨t0, x0⟩
    have hp0_time : t0 ∈ Set.Icc 0 T := hp0.1
    have hΦ_min_bad : Φ (t0, x0) <= Φ (tb, xb) :=
      hp0min (show (tb, xb) ∈ Set.Icc 0 T ×ˢ K from ⟨htb, hxbK⟩)
    have hΦ0_neg : Φ (t0, x0) < 0 := lt_of_le_of_lt hΦ_min_bad hbneg
    have hΦ_min_slab :
        IsMinOn Φ (spacetimeSlab (M := M) T) (t0, x0) := by
      intro p hp
      by_cases hpK : p.2 ∈ K
      · exact hp0min ⟨hp.1, hpK⟩
      · have hwp : 0 <= w p.1 p.2 := hw_out p.1 hp.1 p.2 hpK
        have hεp : 0 <= ε * p.1 := mul_nonneg (le_of_lt hε) hp.1.1
        have hΦp : 0 <= Φ p := by
          dsimp [Φ]
          linarith
        exact (le_of_lt hΦ0_neg).trans hΦp
    have ht0_ne_zero : t0 ≠ 0 := by
      intro ht0
      have hnonneg0 : 0 <= Φ (t0, x0) := by
        simp [Φ, ht0, hw0 x0]
      exact not_lt_of_ge hnonneg0 hΦ0_neg
    have ht0_pos : 0 < t0 :=
      lt_of_le_of_ne hp0_time.1 (Ne.symm ht0_ne_zero)
    have hT_pos : 0 < T := lt_of_lt_of_le ht0_pos hp0_time.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hT_pos).uniqueDiffWithinAt hp0_time
    have hw_t0_neg : w t0 x0 < 0 := by
      have hεt_nonneg : 0 <= ε * t0 :=
        mul_nonneg (le_of_lt hε) hp0_time.1
      nlinarith [hΦ0_neg, hεt_nonneg]
    let support := hsupport t0 hp0_time ht0_pos x0 hw_t0_neg
    let Ψ : Real × M -> Real :=
      fun p => support.v p.1 p.2 + ε * p.1
    have hΨ_local :
        IsLocalMinOn Ψ (spacetimeSlab (M := M) T) (t0, x0) := by
      unfold IsLocalMinOn IsMinFilter
      filter_upwards [support.upper_nhds, self_mem_nhdsWithin] with p hp_upper hp_slab
      have hmin := hΦ_min_slab hp_slab
      dsimp [Ψ, Φ] at hmin ⊢
      rw [support.eq_at]
      linarith
    have htime_min :
        IsLocalMinOn (fun s : Real => support.v s x0 + ε * s)
          (Set.Icc 0 T) t0 := by
      have hcomp := hΨ_local.comp_continuousOn
        (s := Set.Icc 0 T) (g := fun s : Real => (s, x0))
        (by
          intro s hs
          exact ⟨hs, Set.mem_univ x0⟩)
        (continuous_id.prodMk continuous_const).continuousOn hp0_time
      simpa only [Function.comp_apply, Ψ] using hcomp
    have htime_diff :
        DifferentiableWithinAt Real
          (fun s : Real => support.v s x0 + ε * s) (Set.Icc 0 T) t0 :=
      support.time_diff.add
        ((differentiableWithinAt_id'
          (𝕜 := Real) (s := Set.Icc 0 T) (x := t0)).const_mul ε)
    have hbarrier_deriv_nonpos :
        derivWithin (fun s : Real => support.v s x0 + ε * s)
          (Set.Icc 0 T) t0 <= 0 :=
      derivWithin_nonpos_at_Icc_min_of_pos
        htime_min hp0_time ht0_pos
    have hderiv_eq :
        derivWithin (fun s : Real => support.v s x0 + ε * s)
            (Set.Icc 0 T) t0 =
          derivWithin (fun s : Real => support.v s x0)
            (Set.Icc 0 T) t0 + ε :=
      derivWithin_add_eps_mul_time (M := M) huniq support.time_diff
    have hv_deriv_le :
        derivWithin (fun s : Real => support.v s x0)
          (Set.Icc 0 T) t0 <= -ε := by
      linarith
    have hspace_min_shift :
        IsLocalMin (fun y : M => support.v t0 y + ε * t0) x0 := by
      rw [← isLocalMinOn_univ_iff]
      have hcomp := hΨ_local.comp_continuousOn
        (s := Set.univ) (g := fun y : M => (t0, y))
        (by
          intro y _
          exact ⟨hp0_time, Set.mem_univ y⟩)
        (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x0)
      simpa only [Function.comp_apply, Ψ] using hcomp
    have hspatial_min : IsLocalMin (support.v t0) x0 := by
      unfold IsLocalMin IsMinFilter at hspace_min_shift ⊢
      filter_upwards [hspace_min_shift] with y hy
      linarith
    have hheat_nonneg :
        0 <= heatOperatorWithDrift
          (I := I) G t0 (X t0) (support.v t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg (I := I) G t0 (X t0)
        hspatial_min support.space_diff_nhds.self_of_nhds support.space_diff_nhds
        support.grad_diff
    have hP_neg :
        parabolicOperatorWithDrift
          (I := I) G T X support.v t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge support.operator_nonneg hP_neg
  intro t ht x
  by_contra hnot
  have hw_neg : w t x < 0 := lt_of_not_ge hnot
  by_cases ht_zero : t = 0
  · exact not_lt_of_ge (by simpa [ht_zero] using hw0 x) hw_neg
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    let ε : Real := -(w t x) / (2 * t)
    have hε_pos : 0 < ε :=
      div_pos (neg_pos.mpr hw_neg) (mul_pos two_pos ht_pos)
    have hbarrier := hbarrier_nonneg ε hε_pos t ht x
    have hε_mul : ε * t = -(w t x) / 2 := by
      dsimp [ε]
      field_simp [ht_zero]
    have hbarrier_neg : w t x + ε * t < 0 := by
      rw [hε_mul]
      linarith
    exact not_lt_of_ge hbarrier hbarrier_neg

theorem strict_barrier_nonnegative
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
  strict_barrier_nonnegative_of_positive_time (I := I) G T X w
    hw_cont hw0
    (fun t ht _htpos x => hw_time t ht x)
    (fun t ht _htpos x => hw_mdiff t ht x)
    (fun t ht _htpos x => hw_grad t ht x)
    (fun t ht _htpos x hwneg => hnegative t ht x hwneg)

theorem scalar_weak_maximum_principle_sub_const_of_parabolic_nonpos
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => C - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C - u s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C - u t y) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => C - u t z) y) x)
    (hinit : forall x : M, u 0 x <= C)
    (hsub : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M,
        parabolicOperatorWithDrift (I := I) G T X u t x <= 0)
    (hoperator_neg : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
        (fun s y => C - u s y) t x =
      - parabolicOperatorWithDrift (I := I) G T X u t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= C := by
  let w : Real -> M -> Real := fun t x => C - u t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x _hwneg
    rw [hoperator_neg t ht x]
    exact neg_nonneg.mpr (hsub t ht htpos x)
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative_of_positive_time (I := I) G T X w
      (by simpa [w] using hw_cont) hw0
      (fun t ht _htpos x => by simpa [w] using hw_time t ht x)
      (fun t ht _htpos x => by simpa [w] using hw_mdiff t ht x)
      (fun t ht _htpos x => by simpa [w] using hw_grad t ht x)
      hnegative
  intro t ht x
  exact sub_nonneg.mp (by simpa [w] using hw_nonneg t ht x)

theorem scalar_sub_const_positive_region
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => C - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C - u s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C - u t y) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => C - u t z) y) x)
    (hinit : forall x : M, u 0 x <= C)
    (hsub : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M,
        parabolicOperatorWithDrift (I := I) G T X u t x <= 0)
    (hoperator_neg : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
        (fun s y => C - u s y) t x =
      - parabolicOperatorWithDrift (I := I) G T X u t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= C := by
  let w : Real -> M -> Real := fun t x => C - u t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x _hwneg
    rw [hoperator_neg t ht htpos x]
    exact neg_nonneg.mpr (hsub t ht htpos x)
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_positive_region (I := I) G T X w
      (by simpa [w] using hw_cont) hw0
      (by simpa [w] using hw_time)
      (by simpa [w] using hw_mdiff)
      (by simpa [w] using hw_grad)
      hnegative
  intro t ht x
  exact sub_nonneg.mp (by simpa [w] using hw_nonneg t ht x)

theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-L * s) * (u s x - c s)) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hexpCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-L * s) * (u s y - c s)) t x =
        Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - L * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => Real.exp (-L * t) * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    simpa [w, v] using hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    have hexppos : 0 < Real.exp (-L * t) := Real.exp_pos _
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= Real.exp (-L * t) * v t x :=
        mul_nonneg (le_of_lt hexppos) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        L * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      exact negative_region_parabolic_lower_bound
        (hsuper t ht x)
        (hode t ht)
        (by simpa [v] using hsubCalc t ht x)
        (hlip t ht x)
        (by simpa [v] using hvneg)
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
        exact mul_nonneg (le_of_lt hexppos) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hexpCalc t ht x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T X w
      (by simpa [w, v] using hw_cont) hw0
      (by simpa [w, v] using hw_time)
      (by simpa [w, v] using hw_mdiff) (by simpa [w, v] using hw_grad)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)

theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_positive_time
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-L * s) * (u s x - c s)) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hexpCalc : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-L * s) * (u s y - c s)) t x =
        Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - L * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => Real.exp (-L * t) * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    simpa [w, v] using hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hwneg
    have hexppos : 0 < Real.exp (-L * t) := Real.exp_pos _
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= Real.exp (-L * t) * v t x :=
        mul_nonneg (le_of_lt hexppos) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        L * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      exact negative_region_parabolic_lower_bound
        (hsuper t ht htpos x)
        (hode t ht htpos)
        (by simpa [v] using hsubCalc t ht htpos x)
        (hlip t ht x)
        (by simpa [v] using hvneg)
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
        exact mul_nonneg (le_of_lt hexppos) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hexpCalc t ht htpos x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative_of_positive_time (I := I) G T X w
      (by simpa [w, v] using hw_cont) hw0
      (fun t ht htpos x => by simpa [w, v] using hw_time t ht htpos x)
      (fun t ht htpos x => by simpa [w, v] using hw_mdiff t ht htpos x)
      (fun t ht htpos x => by simpa [w, v] using hw_grad t ht htpos x)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)

theorem scalar_weak_maximum_principle_supersolution_lower_bound
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (alpha : Real)
    (hw_cont : ContinuousOn (fun p : Real × M => u p.1 p.2 - alpha)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x - alpha) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => u t y - alpha) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - alpha) y) x)
    (hinit : forall x : M, alpha <= u 0 x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      u t x < alpha ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - alpha) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, alpha <= u t x := by
  let w : Real -> M -> Real := fun t x => u t x - alpha
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hneg : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    exact hnegative t ht x (by simpa [w] using hwneg)
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T X w
      (by simpa [w] using hw_cont) hw0
      (by simpa [w] using hw_time)
      (by simpa [w] using hw_mdiff) (by simpa [w] using hw_grad)
      hneg
  intro t ht x
  exact sub_nonneg.mp (by simpa [w] using hw_nonneg t ht x)

theorem scalar_weak_maximum_principle_pointwise_bounds
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C1 C2 : Real)
    (hlower_cont : ContinuousOn (fun p : Real × M => u p.1 p.2 - C1)
      (spacetimeSlab (M := M) T))
    (hlower_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x - C1) (Set.Icc 0 T) t)
    (hlower_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => u t y - C1) x)
    (hlower_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - C1) y) x)
    (hupper_cont : ContinuousOn (fun p : Real × M => C2 - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hupper_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C2 - u s x) (Set.Icc 0 T) t)
    (hupper_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C2 - u t y) x)
    (hupper_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => C2 - u t z) y) x)
    (hinit_lower : forall x : M, C1 <= u 0 x)
    (hinit_upper : forall x : M, u 0 x <= C2)
    (hlower_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      u t x < C1 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - C1) t x)
    (hupper_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      C2 < u t x ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => C2 - u s y) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      C1 <= u t x ∧ u t x <= C2 := by
  have hlower :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, C1 <= u t x :=
    scalar_weak_maximum_principle_supersolution_lower_bound (I := I) G T X u C1
      hlower_cont hlower_time hlower_mdiff hlower_grad hinit_lower hlower_negative
  have hupper_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= C2 - u t x := by
    simpa using
      (scalar_weak_maximum_principle_supersolution_lower_bound (I := I) G T X
        (fun t x => C2 - u t x) 0
        (by simpa using hupper_cont)
        (by simpa using hupper_time)
        (by simpa using hupper_mdiff)
        (by simpa using hupper_grad)
        (fun x => sub_nonneg.mpr (hinit_upper x))
        (fun t ht x hneg => by
          simpa using hupper_negative t ht x (by linarith)))
  intro t ht x
  exact ⟨hlower t ht x, sub_nonneg.mp (hupper_nonneg t ht x)⟩

theorem scalar_weak_maximum_principle_linear_reaction_nonneg
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C : Real)
    (hJ_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-C * p.1) * u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hJ_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s) * u s x) (Set.Icc 0 T) t)
    (hJ_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-C * t) * u t y) x)
    (hJ_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-C * t) * u t z) y) x)
    (hinit : forall x : M, 0 <= u 0 x)
    (hJ_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      Real.exp (-C * t) * u t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-C * s) * u s y) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x := by
  let J : Real -> M -> Real := fun t x => Real.exp (-C * t) * u t x
  have hJ_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= J t x := by
    simpa [J] using
      (scalar_weak_maximum_principle_supersolution_lower_bound (I := I) G T X J 0
        (by simpa [J] using hJ_cont)
        (by simpa [J] using hJ_time)
        (by simpa [J] using hJ_mdiff)
        (by simpa [J] using hJ_grad)
        (fun x => by simpa [J] using hinit x)
        (by simpa [J] using hJ_negative))
  intro t ht x
  have hprod : 0 <= Real.exp (-C * t) * u t x := by
    simpa [J] using hJ_nonneg t ht x
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos (-C * t))).mp hprod

theorem linear_reaction_nonneg
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (beta : Real -> M -> Real) (C : Real)
    (hbeta : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      beta t x <= C)
    (hJ_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-C * p.1) * u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hJ_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s) * u s x) (Set.Icc 0 T) t)
    (hJ_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-C * t) * u t y) x)
    (hJ_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-C * t) * u t z) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hreaction : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x =
        beta t x * u t x)
    (hinit : forall x : M, 0 <= u 0 x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x := by
  refine scalar_weak_maximum_principle_linear_reaction_nonneg (I := I) G T X u C
    hJ_cont hJ_time hJ_mdiff hJ_grad hinit ?_
  intro t ht x hJneg
  by_cases hTpos : 0 < T
  · have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      uniqueDiffOn_Icc hTpos t ht
    have hscale :
        DifferentiableWithinAt Real (fun s : Real => Real.exp (-C * s))
          (Set.Icc 0 T) t := by
      have hlinear :
          DifferentiableWithinAt Real (fun s : Real => -C * s)
            (Set.Icc 0 T) t := by
        simpa using
          (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-C)
      exact hlinear.exp
    rw [parabolic_exp_rescale_identity (I := I) G T C X u t huniq
      (hu_space t ht) x (hu_grad t ht x) (hu_time t ht x) hscale]
    rw [hreaction t ht x]
    have hu_neg : u t x < 0 :=
      lt_of_mul_lt_mul_left (by simpa using hJneg) (Real.exp_pos (-C * t)).le
    apply mul_nonneg (Real.exp_pos (-C * t)).le
    calc
      beta t x * u t x - C * u t x = (beta t x - C) * u t x := by ring
      _ >= 0 := mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hbeta t ht x)) hu_neg.le
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hTpos) hT
    have ht0 : t = 0 := by
      apply le_antisymm
      · simpa [hT0] using ht.2
      · exact ht.1
    have hu_neg : u 0 x < 0 := by
      rw [ht0] at hJneg
      exact lt_of_mul_lt_mul_left (by simpa using hJneg)
        (Real.exp_pos (-C * 0)).le
    exact False.elim (not_lt_of_ge (hinit x) hu_neg)

theorem scalar_weak_maximum_principle_supersolutions_of_weighted_lipschitz_on_values
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c ρ A : Real -> Real)
    (F : Real -> Real -> Real)
    (hρ_pos : forall t : Real, t ∈ Set.Icc 0 T -> 0 < ρ t)
    (hw_cont : ContinuousOn
      (fun p : Real × M => ρ p.1 * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => ρ s * (u s x - c s)) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ρ t * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => ρ t * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= A t * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hweightCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => ρ s * (u s y - c s)) t x =
        ρ t *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - A t * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => ρ t * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have h0mem : (0 : Real) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    exact mul_nonneg (le_of_lt (hρ_pos 0 h0mem)) hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    have hρt : 0 < ρ t := hρ_pos t ht
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= ρ t * v t x :=
        mul_nonneg (le_of_lt hρt) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        A t * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      have hlow : A t * (u t x - c t) <= F (u t x) t - F (c t) t :=
        reaction_difference_lower_bound_on_negative_region
          (hlip t ht x) (by simpa [v] using hvneg)
      have hupper :
          F (u t x) t - F (c t) t <=
            parabolicOperatorWithDrift (I := I) G T X v t x := by
        calc
          F (u t x) t - F (c t) t <=
              parabolicOperatorWithDrift (I := I) G T X u t x -
                derivWithin c (Set.Icc 0 T) t := by
            rw [hode t ht]
            exact sub_le_sub_right (hsuper t ht x) (F (c t) t)
          _ = parabolicOperatorWithDrift (I := I) G T X v t x := by
            have hsub :
                parabolicOperatorWithDrift (I := I) G T X v t x =
                  parabolicOperatorWithDrift (I := I) G T X u t x -
                    derivWithin c (Set.Icc 0 T) t := by
              simpa [v] using hsubCalc t ht x
            exact hsub.symm
      exact le_trans hlow hupper
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - A t * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= ρ t *
          (parabolicOperatorWithDrift (I := I) G T X v t x - A t * v t x) := by
        exact mul_nonneg (le_of_lt hρt) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hweightCalc t ht x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T X w
      (by simpa [w, v] using hw_cont) hw0
      (by simpa [w, v] using hw_time)
      (by simpa [w, v] using hw_mdiff) (by simpa [w, v] using hw_grad)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (hρ_pos t ht) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)

theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_regular
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  by_cases hTpos : 0 < T
  · refine scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values
      (I := I) G T X u c F L hw_cont ?_ hw_mdiff hw_grad
      hsuper hode hinit hlip ?_ ?_
    · intro t ht x
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht x).sub (hc_time t ht)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact hscale.mul hv_time
    · intro t ht x
      exact parabolic_sub_time_curve_identity (I := I) G T X u c t
        (hu_space t ht) x (hu_time t ht x) (hc_time t ht)
    · intro t ht x
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
        uniqueDiffOn_Icc hTpos t ht
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht x).sub (hc_time t ht)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact parabolic_exp_rescale_identity (I := I) G T L X
        (fun s y => u s y - c s) t huniq (hv_space t ht) x
        (hv_grad t ht x) hv_time hscale
  · have hTle : T <= 0 := le_of_not_gt hTpos
    have hT0 : T = 0 := le_antisymm hTle hT
    intro t ht x
    have ht0 : t = 0 := by
      have htle : t <= 0 := by
        simpa [hT0] using ht.2
      exact le_antisymm htle ht.1
    simpa [ht0] using hinit x

theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_regular_positive_time
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  by_cases hTpos : 0 < T
  · refine scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_positive_time
      (I := I) G T X u c F L hw_cont ?_ hw_mdiff hw_grad
      hsuper hode hinit hlip ?_ ?_
    · intro t ht htpos x
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht htpos x).sub (hc_time t ht htpos)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact hscale.mul hv_time
    · intro t ht htpos x
      exact parabolic_sub_time_curve_identity (I := I) G T X u c t
        (hu_space t ht htpos) x (hu_time t ht htpos x) (hc_time t ht htpos)
    · intro t ht htpos x
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
        uniqueDiffOn_Icc hTpos t ht
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht htpos x).sub (hc_time t ht htpos)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact parabolic_exp_rescale_identity (I := I) G T L X
        (fun s y => u s y - c s) t huniq (hv_space t ht htpos) x
        (hv_grad t ht htpos x) hv_time hscale
  · have hTle : T <= 0 := le_of_not_gt hTpos
    have hT0 : T = 0 := le_antisymm hTle hT
    intro t ht x
    have ht0 : t = 0 := by
      have htle : t <= 0 := by
        simpa [hT0] using ht.2
      exact le_antisymm htle ht.1
    simpa [ht0] using hinit x

def scalarValueSet (u : Real -> M -> Real) (c : Real -> Real) (t : Real) : Set Real :=
  Set.range (fun x : M => u t x) ∪ {c t}


theorem scalarValueSet_isCompact_of_continuous
    [CompactSpace M]
    (u : Real -> M -> Real) (c : Real -> Real) (t : Real)
    (hu : Continuous (fun x : M => u t x)) :
    IsCompact (scalarValueSet (M := M) u c t) := by
  have hrange : IsCompact (Set.range (fun x : M => u t x)) := by
    simpa using (isCompact_univ.image hu)
  exact hrange.union isCompact_singleton

theorem exists_abs_lipschitzOnWith_of_locallyLipschitzOn_isCompact
    {f : Real -> Real} {s : Set Real}
    (hs : IsCompact s)
    (hf : LocallyLipschitzOn s f) :
    ∃ K : NNReal, ∀ a ∈ s, ∀ b ∈ s,
      |f a - f b| <= (K : Real) * |a - b| := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs hf
  refine ⟨K, ?_⟩
  intro a ha b hb
  simpa [Real.dist_eq] using hK.dist_le_mul a ha b hb

omit [TopologicalSpace M] in
theorem exists_time_dependent_lipschitz_bound_on_values
    (F : Real -> Real -> Real)
    (u : Real -> M -> Real) (c : Real -> Real) (T : Real)
    (hF : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LocallyLipschitzOn (scalarValueSet (M := M) u c t)
        (fun a : Real => F a t))
    (hcompact : ∀ t : Real, t ∈ Set.Icc 0 T ->
      IsCompact (scalarValueSet (M := M) u c t)) :
    ∃ A : Real -> Real,
      (∀ t : Real, t ∈ Set.Icc 0 T -> 0 <= A t) ∧
      (∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        |F (u t x) t - F (c t) t| <= A t * |u t x - c t|) := by
  classical
  have hExists : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∃ K : NNReal, ∀ a ∈ scalarValueSet (M := M) u c t,
        ∀ b ∈ scalarValueSet (M := M) u c t,
          |(fun a : Real => F a t) a - (fun a : Real => F a t) b| <=
            (K : Real) * |a - b| := by
    intro t ht
    exact exists_abs_lipschitzOnWith_of_locallyLipschitzOn_isCompact
      (hcompact t ht) (hF t ht)
  let A : Real -> Real := fun t =>
    if ht : t ∈ Set.Icc 0 T then
      ((Classical.choose (hExists t ht) : NNReal) : Real)
    else
      0
  refine ⟨A, ?_, ?_⟩
  · intro t ht
    dsimp [A]
    rw [dif_pos ht]
    exact NNReal.coe_nonneg _
  · intro t ht x
    dsimp [A]
    rw [dif_pos ht]
    have hu_mem : u t x ∈ scalarValueSet (M := M) u c t := by
      left
      exact ⟨x, rfl⟩
    have hc_mem : c t ∈ scalarValueSet (M := M) u c t := by
      right
      rfl
    exact Classical.choose_spec (hExists t ht) (u t x) hu_mem (c t) hc_mem


omit [TopologicalSpace M] in
theorem exists_time_dependent_lipschitz_bound_on_values_of_locallyLipschitz
    (F : Real -> Real -> Real)
    (u : Real -> M -> Real) (c : Real -> Real) (T : Real)
    (hF : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LocallyLipschitz (fun a : Real => F a t))
    (hcompact : ∀ t : Real, t ∈ Set.Icc 0 T ->
      IsCompact (scalarValueSet (M := M) u c t)) :
    ∃ A : Real -> Real,
      (∀ t : Real, t ∈ Set.Icc 0 T -> 0 <= A t) ∧
      (∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        |F (u t x) t - F (c t) t| <= A t * |u t x - c t|) := by
  exact exists_time_dependent_lipschitz_bound_on_values (M := M) F u c T
    (fun t ht => (hF t ht).locallyLipschitzOn) hcompact


def scalarWeakMaximumPrincipleValueSet (T : Real) (u : Real -> M -> Real)
    (c : Real -> Real) : Set Real :=
  (fun p : Real × M => u p.1 p.2) '' spacetimeSlab (M := M) T ∪ c '' Set.Icc 0 T


omit [TopologicalSpace M] in
theorem scalarWeakMaximumPrincipleValueSet_u_mem
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (x : M) :
    u t x ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c := by
  left
  refine ⟨(t, x), ?_, rfl⟩
  exact ⟨ht, trivial⟩


omit [TopologicalSpace M] in
theorem scalarWeakMaximumPrincipleValueSet_c_mem
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    {t : Real} (ht : t ∈ Set.Icc 0 T) :
    c t ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c := by
  right
  exact ⟨t, ht, rfl⟩

theorem scalarWeakMaximumPrincipleValueSet_isCompact
    [CompactSpace M]
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hc_cont : ContinuousOn c (Set.Icc 0 T)) :
    IsCompact (scalarWeakMaximumPrincipleValueSet (M := M) T u c) := by
  have hslab : IsCompact (spacetimeSlab (M := M) T) := by
    simpa [spacetimeSlab] using (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set M)))
  exact (hslab.image_of_continuousOn hu_cont).union (isCompact_Icc.image_of_continuousOn hc_cont)

omit [TopologicalSpace M] in
theorem scalarWeakMaximumPrincipleValueSet_mono
    {T T' : Real} (hTT' : T' <= T)
    (u : Real -> M -> Real) (c : Real -> Real) :
    scalarWeakMaximumPrincipleValueSet (M := M) T' u c ⊆
      scalarWeakMaximumPrincipleValueSet (M := M) T u c := by
  intro a ha
  rcases ha with ⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩
  · left
    refine ⟨p, ?_, rfl⟩
    exact ⟨⟨hp.1.1, hp.1.2.trans hTT'⟩, hp.2⟩
  · right
    exact ⟨t, ⟨ht.1, ht.2.trans hTT'⟩, rfl⟩

omit [TopologicalSpace M] in
theorem scalarWeakMaximumPrincipleValueSet_neg_mem
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    {a : Real} (ha : a ∈ scalarWeakMaximumPrincipleValueSet (M := M) T
      (fun t x => -u t x) (fun t => -c t)) :
    -a ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c := by
  rcases ha with ⟨p, hp, hpa⟩ | ⟨t, ht, hta⟩
  · left
    refine ⟨p, hp, ?_⟩
    have hneg : -(u p.1 p.2) = a := hpa
    rw [← hneg]
    ring
  · right
    refine ⟨t, ht, ?_⟩
    have hneg : -(c t) = a := hta
    rw [← hneg]
    ring

omit [TopologicalSpace M] in
theorem scalarWeakMaximumPrincipleLipschitzOnValueSetBound
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= (K : Real) * |u t x - c t| := by
  intro t ht x
  have hu_mem : u t x ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c :=
    scalarWeakMaximumPrincipleValueSet_u_mem (M := M) T u c ht x
  have hc_mem : c t ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c :=
    scalarWeakMaximumPrincipleValueSet_c_mem (M := M) T u c ht
  simpa [Real.dist_eq] using (hF_lip t ht).dist_le_mul (u t x) hu_mem (c t) hc_mem

theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_value_set_of_regular
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  exact scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_regular
    (I := I) G T hT X u c F (K : Real)
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    hsuper hode hinit
    (scalarWeakMaximumPrincipleLipschitzOnValueSetBound (M := M) T u c F K hF_lip)

theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_value_set_of_regular_positive_time
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  exact scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_regular_positive_time
    (I := I) G T hT X u c F (K : Real)
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    hsuper hode hinit
    (scalarWeakMaximumPrincipleLipschitzOnValueSetBound (M := M) T u c F K hF_lip)

end

theorem scalar_weak_maximum_principle_ode_compare_supersolution
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x :=
  scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_value_set_of_regular_positive_time
    (I := I) G T hT X u c F K hw_cont hw_mdiff hw_grad hu_time hc_time
    hu_space hv_space hv_grad hsuper hode hinit hF_lip

theorem scalar_weak_maximum_principle_ode_compare_subsolution
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) *
        ((-u p.1 p.2) - (-c p.1)))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) *
          ((-u t y) - (-c t))) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) *
            ((-u t z) - (-c t))) y) x)
    (hneg_u_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => -u s x) (Set.Icc 0 T) t)
    (hneg_c_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real (fun s : Real => -c s) (Set.Icc 0 T) t)
    (hneg_u_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => -u t z) y)
    (hneg_v_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => (-u t z) - (-c t)) y)
    (hneg_v_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => (-u t z) - (-c t)) y) x)
    (hsub_as_super : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      (fun a : Real => -F (-a) t) (-u t x) <=
        parabolicOperatorWithDrift (I := I) G T X
          (fun s y => -u s y) t x)
    (hode_neg : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin (fun s : Real => -c s) (Set.Icc 0 T) t =
        (fun a : Real => -F (-a) t) (-c t))
    (hinit : forall x : M, u 0 x <= c 0)
    (hF_lip_neg : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => -F (-a) t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T
          (fun t x => -u t x) (fun t => -c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= c t := by
  have hneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, -c t <= -u t x :=
    scalar_weak_maximum_principle_ode_compare_supersolution
      (I := I) G T hT X (fun t x => -u t x) (fun t => -c t)
      (fun a t => -F (-a) t) K
      hw_cont hw_mdiff hw_grad hneg_u_time hneg_c_time
      hneg_u_space hneg_v_space hneg_v_grad hsub_as_super hode_neg
      (fun x => by linarith [hinit x]) hF_lip_neg
  intro t ht x
  linarith [hneg t ht x]

theorem scalar_weak_maximum_principle_ode_compare_supersolution_autonomous
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t))
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x :=
  scalar_weak_maximum_principle_ode_compare_supersolution
    (I := I) G T hT X u c (fun a _ => F a) K
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    hsuper hode hinit (fun t ht => by simpa using hF_lip t ht)

private theorem
    scalar_weak_maximum_principle_ode_compare_supersolution_of_heat_pot_on_strict_subinterval
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hTpos : 0 < T)
    (V u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hu : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T (le_of_lt hTpos)) G V u)
    (hc_cont : ContinuousOn c (Set.Icc 0 T))
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hF_le : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= V t x * u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c))
    {T' : Real} (hT'pos : 0 < T') (hT'lt : T' < T) :
    forall t : Real, t ∈ Set.Icc 0 T' -> forall x : M, c t <= u t x := by
  let X : Real -> (x : M) -> TangentSpace I x := fun _ x => 0
  have hT'le : 0 <= T' := le_of_lt hT'pos
  have hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T') := by
    have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
        (spacetimeSlab (M := M) T') := by
      apply (by
        simpa only [RealTimeInterval.closed]
          using hu.jointCont : ContinuousOn (fun p : Real × M => u p.1 p.2)
            (Set.Icc (0 : Real) T ×ˢ Set.univ)).mono
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans hT'lt.le⟩, hp.2⟩
    have hc_cont_slab : ContinuousOn (fun p : Real × M => c p.1)
        (spacetimeSlab (M := M) T') := by
      refine hc_cont.comp continuousOn_fst ?_
      intro p hp
      exact ⟨hp.1.1, hp.1.2.trans hT'lt.le⟩
    have hexp_cont : ContinuousOn (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1)) (spacetimeSlab (M := M) T') := by
      exact (by fun_prop : Continuous (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1))).continuousOn
    exact hexp_cont.mul (hu_cont.sub hc_cont_slab)
  have hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x := by
    intro t ht htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    have hslice : ContMDiff I 𝓘(Real, Real) ∞
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) := by
      exact contMDiff_const.mul ((hu.sliceSmooth t htcarrier).sub contMDiff_const)
    exact hslice.mdifferentiable (by simp) x
  have hw_grad : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x := by
    intro t ht htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    have hslice : ContMDiff I 𝓘(Real, Real) ∞
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) := by
      exact contMDiff_const.mul ((hu.sliceSmooth t htcarrier).sub contMDiff_const)
    exact gradientFun_mdiffAt (I := I) (G.metric t) hslice x
  have hu_time : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T') t := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
    exact (hu.timeDiff t htreg x).differentiableWithinAt
  have hc_time' : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T') t := by
    intro t ht htpos
    have htT : t ∈ Set.Icc 0 T := ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    exact (hc_time t htT htpos).mono (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hT'lt.le⟩)
  have hu_space : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y := by
    intro t ht htpos y
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    exact (hu.sliceSmooth t htcarrier).mdifferentiable (by simp) y
  have hv_space : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y := by
    intro t ht htpos y
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    have hslice : ContMDiff I 𝓘(Real, Real) ∞ (fun z : M => u t z - c t) :=
      (hu.sliceSmooth t htcarrier).sub contMDiff_const
    exact hslice.mdifferentiable (by simp) y
  have hv_grad : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x := by
    intro t ht htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    have hslice : ContMDiff I 𝓘(Real, Real) ∞ (fun z : M => u t z - c t) :=
      (hu.sliceSmooth t htcarrier).sub contMDiff_const
    exact gradientFun_mdiffAt (I := I) (G.metric t) hslice x
  have hsuper : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T' X u t x := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T (le_of_lt hTpos)).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T') t :=
      (uniqueDiffOn_Icc hT'pos).uniqueDiffWithinAt ht
    have hderiv : derivWithin (fun s : Real => u s x) (Set.Icc 0 T') t =
        deriv (fun s : Real => u s x) t :=
      (hu.timeDiff t htreg x).derivWithin huniq
    have hlap : heatOperatorWithDrift (I := I) G t (X t) (u t) x =
        laplacianAt (I := I) G t (u t) x := by
      rw [show X t = (fun y : M => (0 : TangentSpace I y)) from rfl]
      rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt]
    have hV : V t x * u t x <=
        deriv (fun s : Real => u s x) t - laplacianAt (I := I) G t (u t) x := by
      linarith [hu.equation_ge t htreg x]
    rw [parabolicOperatorWithDrift_eq, hderiv]
    rw [hlap]
    exact le_trans (hF_le t htcarrier x) hV
  have hode' : forall t : Real, t ∈ Set.Icc 0 T' -> 0 < t ->
      derivWithin c (Set.Icc 0 T') t = F (c t) t := by
    intro t ht htpos
    have htT : t ∈ Set.Icc 0 T := ⟨ht.1, le_trans ht.2 hT'lt.le⟩
    have huniq' : UniqueDiffWithinAt Real (Set.Icc 0 T') t :=
      (uniqueDiffOn_Icc hT'pos).uniqueDiffWithinAt ht
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt htT
    have hwithin : DifferentiableWithinAt Real c (Set.Icc 0 T') t :=
      (hc_time t htT htpos).mono (by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 hT'lt.le⟩)
    have hdiff : DifferentiableAt Real c t := by
      have hIoo : Set.Ioo 0 T ∈ 𝓝 t :=
        isOpen_Ioo.mem_nhds ⟨htpos, lt_of_le_of_lt ht.2 hT'lt⟩
      have hIcc_mem : Set.Icc 0 T ∈ 𝓝 t :=
        mem_of_superset hIoo Set.Ioo_subset_Icc_self
      exact (hc_time t htT htpos).differentiableAt hIcc_mem
    have h1 : derivWithin c (Set.Icc 0 T') t = deriv c t :=
      hdiff.derivWithin huniq'
    have h2 : derivWithin c (Set.Icc 0 T) t = deriv c t :=
      hdiff.derivWithin huniq
    calc
      derivWithin c (Set.Icc 0 T') t = deriv c t := h1
      _ = derivWithin c (Set.Icc 0 T) t := h2.symm
      _ = F (c t) t := hode t htT htpos
  have hF_lip' : forall t : Real, t ∈ Set.Icc 0 T' ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T' u c) := by
    intro t ht
    exact (hF_lip t ⟨ht.1, le_trans ht.2 hT'lt.le⟩).mono
      (scalarWeakMaximumPrincipleValueSet_mono (M := M) hT'lt.le u c)
  exact scalar_weak_maximum_principle_ode_compare_supersolution
    (I := I) G T' hT'le X u c F K hw_cont hw_mdiff hw_grad
    hu_time hc_time' hu_space hv_space hv_grad hsuper hode' hinit hF_lip'

theorem scalar_weak_maximum_principle_ode_compare_supersolution_of_heat_pot
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (V : Real -> M -> Real)
    (hu : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V u)
    (hc_cont : ContinuousOn c (Set.Icc 0 T))
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hF_le : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= V t x * u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  by_cases hTzero : T = 0
  · intro t ht x
    have htzero : t = 0 := le_antisymm (by simpa [hTzero] using ht.2) ht.1
    simpa [htzero] using hinit x
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
  have hshort : forall T' : Real, 0 < T' -> T' < T ->
      forall t : Real, t ∈ Set.Icc 0 T' -> forall x : M, c t <= u t x := by
    intro T' hT'pos hT'lt
    exact scalar_weak_maximum_principle_ode_compare_supersolution_of_heat_pot_on_strict_subinterval
      (I := I) G hTpos V u c F K hu hc_cont hc_time hF_le hode hinit hF_lip
      (T' := T') hT'pos hT'lt
  have hIco : forall t : Real, t ∈ Set.Ico 0 T -> forall x : M, c t <= u t x := by
    intro t ht x
    let T' : Real := (t + T) / 2
    have hT'pos : 0 < T' := by
      dsimp [T']
      linarith [ht.1, hTpos]
    have hT'lt : T' < T := by
      dsimp [T']
      linarith [ht.2]
    have htT' : t <= T' := by
      dsimp [T']
      linarith [ht.2]
    exact hshort T' hT'pos hT'lt t ⟨ht.1, htT'⟩ x
  have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc (0 : Real) T ×ˢ Set.univ) := by
    simpa only [RealTimeInterval.closed] using hu.jointCont
  intro t ht x
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · have ht_eq : t = T := htT
    rw [ht_eq]
    have hT_in : (T, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) :=
      ⟨right_mem_Icc.mpr hT, Set.mem_univ x⟩
    have h_cont_at := hu_cont (T, x) hT_in
    have h_tend : Filter.Tendsto (fun s : Real => u s x)
        (𝓝[<] T) (𝓝 (u T x)) := by
      have h_pair : Filter.Tendsto (fun s : Real => (s, x))
          (𝓝[<] T) (𝓝 (T, x)) := by
        refine Filter.Tendsto.prodMk_nhds ?_ tendsto_const_nhds
        exact nhdsWithin_le_nhds
      have h_evt : ∀ᶠ s in 𝓝[<] T,
          (s, x) ∈ Set.Icc (0 : Real) T ×ˢ (Set.univ : Set M) := by
        have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
        have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
        filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
        exact ⟨⟨le_of_lt hs, le_of_lt hslt⟩, Set.mem_univ x⟩
      have h_pair_within : Filter.Tendsto (fun s : Real => (s, x))
          (𝓝[<] T) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (T, x)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨h_pair, h_evt⟩
      exact h_cont_at.tendsto.comp h_pair_within
    have hc_tend : Filter.Tendsto (fun s : Real => c s) (𝓝[<] T) (𝓝 (c T)) := by
      have h_pair_id : Filter.Tendsto (fun s : Real => s) (𝓝[<] T) (𝓝 T) :=
        nhdsWithin_le_nhds
      have h_evt : ∀ᶠ s in 𝓝[<] T, s ∈ Set.Icc 0 T := by
        have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
        have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
        filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
        exact ⟨le_of_lt hs, le_of_lt hslt⟩
      have h_id_within : Filter.Tendsto (fun s : Real => s)
          (𝓝[<] T) (𝓝[Set.Icc 0 T] T) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨h_pair_id, h_evt⟩
      exact (hc_cont.continuousWithinAt (right_mem_Icc.mpr hT)).tendsto.comp h_id_within
    have hdiff_tend : Filter.Tendsto (fun s : Real => u s x - c s)
        (𝓝[<] T) (𝓝 (u T x - c T)) := h_tend.sub hc_tend
    have hneg_tend : Filter.Tendsto (fun s : Real => -(u s x - c s))
        (𝓝[<] T) (𝓝 (-(u T x - c T))) := hdiff_tend.neg
    have h_evt_nonpos : ∀ᶠ s in 𝓝[<] T, -(u s x - c s) <= 0 := by
      have h0 : Set.Ioi (0 : Real) ∈ 𝓝 T := Ioi_mem_nhds hTpos
      have h0' : Set.Ioi (0 : Real) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
      filter_upwards [h0', self_mem_nhdsWithin] with s hs hslt
      exact neg_nonpos.mpr (sub_nonneg.mpr (hIco s ⟨le_of_lt hs, hslt⟩ x))
    have h_nonneg : 0 <= u T x - c T :=
      neg_nonpos.mp (le_of_tendsto hneg_tend h_evt_nonpos)
    exact sub_nonneg.mp h_nonneg
  · exact hIco t ⟨ht.1, htT⟩ x

theorem scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (V : Real -> M -> Real)
    (hu : IsHeatPotSubsolutionOn (RealTimeInterval.closed 0 T hT) G V u)
    (hc_cont : ContinuousOn c (Set.Icc 0 T))
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hF_ge : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      V t x * u t x <= F (u t x) t)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, u 0 x <= c 0)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= c t := by
  let uneg : Real -> M -> Real := fun t x => -u t x
  let cneg : Real -> Real := fun t => -c t
  let Fneg : Real -> Real -> Real := fun a t => -F (-a) t
  have huneg : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V uneg :=
    hu.neg
  have hcneg_cont : ContinuousOn cneg (Set.Icc 0 T) := by
    simpa only [cneg] using hc_cont.neg
  have hcneg_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real cneg (Set.Icc 0 T) t := by
    intro t ht htpos
    simpa only [cneg] using (hc_time t ht htpos).neg
  have hFneg_le : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      Fneg (uneg t x) t <= V t x * uneg t x := by
    intro t ht x
    dsimp [uneg, Fneg]
    have h1 : -F (u t x) t <= -(V t x * u t x) := neg_le_neg (hF_ge t ht x)
    simpa [uneg, Fneg, mul_neg] using h1
  have hode_neg : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin cneg (Set.Icc 0 T) t = Fneg (cneg t) t := by
    intro t ht htpos
    dsimp [cneg, Fneg]
    have hd : derivWithin (fun s : Real => -c s) (Set.Icc 0 T) t =
        -derivWithin c (Set.Icc 0 T) t := by
      have hder : HasDerivWithinAt (fun s : Real => -c s)
          (-derivWithin c (Set.Icc 0 T) t) (Set.Icc 0 T) t := by
        simpa using ((hc_time t ht htpos).hasDerivWithinAt).neg
      have hTpos' : 0 < T := lt_of_lt_of_le htpos ht.2
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
        (uniqueDiffOn_Icc hTpos').uniqueDiffWithinAt ht
      exact hder.derivWithin huniq
    rw [hd, hode t ht htpos]
    ring_nf
  have hinit_neg : forall x : M, cneg 0 <= uneg 0 x := by
    intro x
    dsimp [uneg, cneg]
    linarith [hinit x]
  have hFneg_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => Fneg a t)
        (scalarWeakMaximumPrincipleValueSet (M := M) T uneg cneg) := by
    intro t ht
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    have ha' : -a ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c :=
      scalarWeakMaximumPrincipleValueSet_neg_mem (M := M) T u c ha
    have hb' : -b ∈ scalarWeakMaximumPrincipleValueSet (M := M) T u c :=
      scalarWeakMaximumPrincipleValueSet_neg_mem (M := M) T u c hb
    have hbound := (hF_lip t ht).dist_le_mul (-a) ha' (-b) hb'
    simpa [Fneg, dist_neg_neg] using hbound
  have hcmp := scalar_weak_maximum_principle_ode_compare_supersolution_of_heat_pot
    (I := I) G T hT uneg cneg Fneg K V huneg hcneg_cont hcneg_time
    hFneg_le hode_neg hinit_neg hFneg_lip
  intro t ht x
  have hle : cneg t <= uneg t x := hcmp t ht x
  dsimp [uneg, cneg] at hle
  linarith

theorem scalar_weak_maximum_principle_ode_compare_supersolution_autonomous_of_heat_pot
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real) (K : NNReal)
    (V : Real -> M -> Real)
    (hu : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V u)
    (hc_cont : ContinuousOn c (Set.Icc 0 T))
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hF_le : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) <= V t x * u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      derivWithin c (Set.Icc 0 T) t = F (c t))
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a)
        (scalarWeakMaximumPrincipleValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x :=
  scalar_weak_maximum_principle_ode_compare_supersolution_of_heat_pot
    (I := I) G T hT u c (fun a _ => F a) K V hu hc_cont hc_time
    (fun t ht x => hF_le t ht x)
    (fun t ht htpos => by simpa using hode t ht htpos)
    hinit
    (fun t ht => by simpa using hF_lip t ht)

end DifferentialGeometry.Analysis.Parabolic
