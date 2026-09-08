import DifferentialGeometry.Geometry.Operator.Family.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators Bundle Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

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

theorem parabolic_mul_nhds
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (u v : Real → M → Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y * v s y) t x =
      u t x * parabolicOperatorWithDrift (I := I) G T X v t x +
        v t x * parabolicOperatorWithDrift (I := I) G T X u t x -
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t (u t) x)
            (gradientAt (I := I) G t (v t) x) := by
  have hlap := laplacian_mul_at (G.connection t) (G.metric t)
    hu_space hv_space hu_grad hv_grad
  have hdrift := driftTerm_mul (I := I) G t (X t)
    hu_space.self_of_nhds hv_space.self_of_nhds
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt gradientAt
  rw [derivWithin_fun_mul hu_time hv_time, hlap, hdrift]
  ring

theorem parabolic_add_nhds
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (u v : Real → M → Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y + v s y) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x +
        parabolicOperatorWithDrift (I := I) G T X v t x := by
  have hlap := laplacian_add_at (G.connection t) (G.metric t)
    hu_space hv_space hu_grad hv_grad
  have hdrift := driftTerm_add (I := I) G t (X t)
    hu_space.self_of_nhds hv_space.self_of_nhds
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
  rw [derivWithin_fun_add hu_time hv_time, hlap, hdrift]
  ring

private theorem sum_regularity_nhds
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {κ : Type*} (s : Finset κ)
    (u : κ → Real → M → Real) (T t : Real) (x : M)
    (htime : ∀ i ∈ s, DifferentiableWithinAt Real
      (fun a : Real => u i a x) (Set.Icc 0 T) t)
    (hspace : ∀ i ∈ s, ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u i t) y)
    (hgrad : ∀ i ∈ s,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u i t) y) x) :
    DifferentiableWithinAt Real
        (fun a : Real => ∑ i ∈ s, u i a x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => ∑ i ∈ s, u i t z) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => ∑ i ∈ s, u i t z) y) x := by
  classical
  refine ⟨DifferentiableWithinAt.fun_sum htime, ?_,
    mdifferentiableAt_gradientFun_finset_sum (G.metric t) s
      (fun i => u i t) x hspace hgrad⟩
  filter_upwards [(Filter.eventually_all_finset s).mpr hspace] with y hy
  clear htime hgrad hspace
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using mdifferentiableAt_const
  | @insert i s hi ih =>
      have hhead := hy i (Finset.mem_insert_self i s)
      have htail := ih (fun j hj => hy j (Finset.mem_insert_of_mem hj))
      rw [show (fun z => ∑ j ∈ insert i s, u j t z) =
          u i t + (fun z => ∑ j ∈ s, u j t z) by
        funext z
        simp only [Finset.sum_insert hi, Pi.add_apply]]
      exact hhead.add htail

theorem parabolic_const
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (a t : Real) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun _ _ => a) t x = 0 := by
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
    laplacian divergence driftTerm gradientAt
  rw [derivWithin_fun_const]
  rw [show gradientFun (I := I) (G.metric t) ((fun _ _ => a) t) =
      (fun y : M => (0 : TangentSpace I y)) by
    funext y
    simp only [gradientFun_const]]
  rw [show (fun y : M => (0 : TangentSpace I y)) = 0 by rfl]
  rw [(G.connection t).isCovariantDerivativeOnUniv.zero (x := x)]
  rw [show (↑(0 : TangentSpace I x →L[Real] TangentSpace I x) :
      TangentSpace I x →ₗ[Real] TangentSpace I x) = 0 by rfl]
  simp only [map_zero, Pi.zero_apply, sub_zero, zero_add]

theorem parabolic_sum_nhds
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {κ : Type*} (s : Finset κ)
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (u : κ → Real → M → Real) (t : Real) (x : M)
    (htime : ∀ i ∈ s, DifferentiableWithinAt Real
      (fun a : Real => u i a x) (Set.Icc 0 T) t)
    (hspace : ∀ i ∈ s, ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u i t) y)
    (hgrad : ∀ i ∈ s,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u i t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun a y => ∑ i ∈ s, u i a y) t x =
      ∑ i ∈ s, parabolicOperatorWithDrift (I := I) G T X (u i) t x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact parabolic_const T X 0 t x
  | @insert a s ha ih =>
      have hatime := htime a (Finset.mem_insert_self a s)
      have haspace := hspace a (Finset.mem_insert_self a s)
      have hagrad := hgrad a (Finset.mem_insert_self a s)
      have hsreg := sum_regularity_nhds (I := I) (G := G) s u T t x
        (fun i hi => htime i (Finset.mem_insert_of_mem hi))
        (fun i hi => hspace i (Finset.mem_insert_of_mem hi))
        (fun i hi => hgrad i (Finset.mem_insert_of_mem hi))
      rw [show (fun r y => ∑ i ∈ insert a s, u i r y) =
          (fun r y => u a r y + ∑ i ∈ s, u i r y) by
        funext r y
        rw [Finset.sum_insert ha]]
      rw [Finset.sum_insert ha]
      rw [parabolic_add_nhds (I := I) T X (u a)
        (fun r y => ∑ i ∈ s, u i r y) t x
        hatime hsreg.1 haspace hsreg.2.1 hagrad hsreg.2.2]
      rw [ih (fun i hi => htime i (Finset.mem_insert_of_mem hi))
        (fun i hi => hspace i (Finset.mem_insert_of_mem hi))
        (fun i hi => hgrad i (Finset.mem_insert_of_mem hi))]

theorem parabolic_smul_nhds
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (u : Real → M → Real) (t : Real) (x : M)
    (hu_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => a * u s y) t x =
      a * parabolicOperatorWithDrift (I := I) G T X u t x := by
  have hlap := laplacian_smul_at (G.connection t) (G.metric t) a hu_space hu_grad
  have hdrift := driftTerm_const_smul (I := I) G t (X t) a hu_space.self_of_nhds
  change laplacian (G.connection t) (G.metric t) (fun y => a * u t y) x =
    a * laplacian (G.connection t) (G.metric t) (u t) x at hlap
  change driftTerm G t (X t) (fun y => a * u t y) x =
    a * driftTerm G t (X t) (u t) x at hdrift
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
  rw [derivWithin_const_mul_field, hlap, hdrift]
  ring

theorem parabolic_affine_sub_nhds
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (F : Real → M → Real) (a b t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hFtime : DifferentiableWithinAt Real
      (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hFspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (F t) y)
    (hFgrad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (F t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => (a + b * s) - F s y) t x =
      b - parabolicOperatorWithDrift (I := I) G T X F t x := by
  let A : Real → M → Real := fun s _ => a + b * s
  have hAtime : DifferentiableWithinAt Real
      (fun s : Real => A s x) (Set.Icc 0 T) t :=
    (differentiableWithinAt_const a).add
      ((differentiableWithinAt_fun_id
        (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul b)
  have hAspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (A t) y :=
    Filter.Eventually.of_forall fun _ => mdifferentiableAt_const
  have hAgrad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (A t) y) x := by
    rw [show (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (A t) y) =
        (T% fun y : M => (0 : TangentSpace I y)) by
      funext y
      simp only [A, gradientFun_const]]
    exact mdifferentiableAt_zeroSection
      (𝕜 := Real) (F := E) (E := (TangentSpace I : M → Type _)) (x := x)
  have hnegtime : DifferentiableWithinAt Real
      (fun s : Real => (-1 : Real) * F s x) (Set.Icc 0 T) t :=
    hFtime.const_mul (-1)
  have hnegspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z => (-1 : Real) * F t z) y := by
    filter_upwards [hFspace] with y hy
    exact hy.const_smul (-1)
  have hneggrad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z => (-1 : Real) * F t z) y) x := by
    refine (hFgrad.smul_const_section (a := (-1 : Real))).congr_of_eventuallyEq ?_
    filter_upwards [hFspace] with y hy
    exact congrArg (fun b =>
      (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (by
        rw [show (fun z => (-1 : Real) * F t z) = (-1 : Real) • F t by
          funext z
          rw [Pi.smul_apply, smul_eq_mul]]
        exact gradientFun_const_smul (I := I) (G.metric t) (-1) hy)
  have hadd := parabolic_add_nhds (I := I) T X A
    (fun s y => (-1 : Real) * F s y) t x
    hAtime hnegtime hAspace hnegspace hAgrad hneggrad
  have hneg := parabolic_smul_nhds (I := I) T X (-1) F t x
    hFspace hFgrad
  have hA :
      parabolicOperatorWithDrift (I := I) G T X A t x = b := by
    unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
      laplacian divergence driftTerm gradientAt
    dsimp only [A]
    have hda :
        derivWithin (fun _ : Real => a) (Set.Icc 0 T) t = 0 :=
      (hasDerivWithinAt_const
        (x := t) (s := Set.Icc 0 T) (c := a)).derivWithin huniq
    have hdb :
        derivWithin (fun s : Real => b * s) (Set.Icc 0 T) t = b := by
      have hdb' :=
        ((hasDerivWithinAt_id t (Set.Icc 0 T)).const_mul b).derivWithin huniq
      rw [show (fun y : Real => b * id y) = (fun s : Real => b * s) by
        funext y
        rw [id_eq]] at hdb'
      simpa only [mul_one] using hdb'
    rw [derivWithin_fun_add (differentiableWithinAt_const a)
      ((differentiableWithinAt_fun_id
        (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul b),
      hda, hdb]
    rw [show gradientFun (I := I) (G.metric t) (fun _ : M => a + b * t) =
        (fun y : M => (0 : TangentSpace I y)) by
      funext y
      simp only [gradientFun_const]]
    rw [show (fun y : M => (0 : TangentSpace I y)) = 0 by rfl]
    rw [(G.connection t).isCovariantDerivativeOnUniv.zero (x := x)]
    rw [show (↑(0 : TangentSpace I x →L[Real] TangentSpace I x) :
        TangentSpace I x →ₗ[Real] TangentSpace I x) = 0 by rfl]
    rw [map_zero, Pi.zero_apply, map_zero]
    ring
  rw [show (fun s y => (a + b * s) - F s y) =
      (fun s y => A s y + (-1 : Real) * F s y) by
    funext s y
    ring]
  rw [hadd, hA, hneg]
  ring

theorem parabolic_pow_le_nhds
    {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (u : ℝ → M → ℝ) (t : ℝ) (x : M) (b : ℝ)
    (hu_nonneg : 0 ≤ u t x)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x)
    (hop : parabolicOperatorWithDrift (I := I) G T X u t x ≤ b) (p : ℕ) :
    parabolicOperatorWithDrift (I := I) G T X
      (fun s y => u s y ^ (p + 1)) t x ≤
        ((p + 1 : ℕ) : ℝ) * b * u t x ^ p := by
  induction p with
  | zero => simpa using hop
  | succ p ih =>
      let qpow : Real → M → Real := fun s y => u s y ^ (p + 1)
      have hqtime := hu_time.pow (p + 1)
      have hqspace : ∀ᶠ y in 𝓝 x,
          MDifferentiableAt I 𝓘(Real, Real) (qpow t) y := by
        filter_upwards [hu_space] with y hy
        exact hy.pow (p + 1)
      have hqgrad :
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (qpow t) y) x := by
        have hrhs :
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
              (((p + 1 : Nat) : Real) * u t y ^ p) •
                gradientFun (I := I) (G.metric t) (u t) y) x :=
          (((hu_space.self_of_nhds.pow p).const_smul
            (((p + 1 : Nat) : Real))).smul_section hu_grad)
        refine hrhs.congr_of_eventuallyEq ?_
        filter_upwards [hu_space] with y hy
        exact congrArg (fun b =>
          (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
          (gradientFun_pow (I := I) (G.metric t) p hy)
      have hmul := parabolic_mul_nhds (I := I) T
        X qpow u t x
        hqtime hu_time hqspace hu_space
        hqgrad hu_grad
      have hgrad := gradientFun_pow (I := I) (G.metric t) p
        hu_space.self_of_nhds
      have hinner : 0 ≤ (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (u t) x) := by
        dsimp only [qpow]
        simp only [gradientAt_eq, hgrad, map_smul,
          smul_apply, smul_eq_mul]
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu_nonneg p))
          (DifferentialGeometry.metric_inner_self_nonneg
            (I := I) (M := M) (G.metric t) x
              (gradientFun (I := I) (G.metric t) (u t) x))
      have hu_mul := mul_le_mul_of_nonneg_left ih hu_nonneg
      have hbound_mul := mul_le_mul_of_nonneg_left hop
        (pow_nonneg hu_nonneg (p + 1))
      calc
        parabolicOperatorWithDrift (I := I) G T
            X
            (fun s y => u s y ^ (Nat.succ p + 1)) t x =
            parabolicOperatorWithDrift (I := I) G T
              X
              (fun s y => qpow s y * u s y) t x := by
                congr 1
        _ ≤ u t x ^ (p + 1) * b +
            u t x *
              ((((p + 1 : Nat) : Real) * b) * u t x ^ p) := by
              rw [hmul]
              linarith
        _ = (((Nat.succ p + 1 : Nat) : Real) * b) *
            u t x ^ Nat.succ p := by
              simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ]
              ring

theorem parabolic_time_mul_nhds
    {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (a : ℝ → ℝ) (u : ℝ → M → ℝ) (t : ℝ) (x : M)
    (hat : DifferentiableWithinAt ℝ a (Icc 0 T) t)
    (hut : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hug : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift G T X (fun s y => a s * u s y) t x =
      derivWithin a (Icc 0 T) t * u t x + a t * parabolicOperatorWithDrift G T X u t x := by
  have hlap := laplacian_smul_at (G.connection t) (G.metric t) (a t) hus hug
  have hdrift := driftTerm_const_smul G t (X t) (a t) hus.self_of_nhds
  change laplacian (G.connection t) (G.metric t) (fun y => a t * u t y) x =
    a t * laplacian (G.connection t) (G.metric t) (u t) x at hlap
  change driftTerm G t (X t) (fun y => a t * u t y) x =
    a t * driftTerm G t (X t) (u t) x at hdrift
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
  rw [derivWithin_fun_mul hat hut, hlap, hdrift]
  ring

end DifferentialGeometry.Analysis.Parabolic
