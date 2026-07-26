import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiHigher
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ShiCutoffData
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

/-!
# Complete noncompact Bernstein estimates

This file owns the noncompact localization interfaces for the Bernstein
curvature tower.  A valid complete-manifold proof must consume quantitative
parabolic cutoffs and the curvature-tower Kato estimate before discarding the
negative next-level terms.

The legacy `estimate_complete` statement below predates that audit and has
insufficient hypotheses.  It remains temporarily for its current caller, but
must not be treated as the canonical target.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Bundle Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- Local scalar product rule for the parabolic operator.  Unlike
`parabolic_mul`, scalar differentiability is required only near the evaluation
point. -/
private theorem parabolic_mul_nhds
    {G : RealizedMetricFamily (I := I) (M := M) Real}
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
  have hgrad_eq :
      (fun y : M =>
          gradientFun (I := I) (G.metric t) (fun z => u t z * v t z) y) =ᶠ[𝓝 x]
        (fun y : M =>
          u t y • gradientFun (I := I) (G.metric t) (v t) y +
            v t y • gradientFun (I := I) (G.metric t) (u t) y) := by
    filter_upwards [hu_space, hv_space] with y huy hvy
    exact gradientFun_mul (I := I) (G.metric t) huy hvy
  have hsum_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        u t y • gradientFun (I := I) (G.metric t) (v t) y +
          v t y • gradientFun (I := I) (G.metric t) (u t) y) x :=
    mdifferentiableAt_add_section
      (hu_space.self_of_nhds.smul_section hv_grad)
      (hv_space.self_of_nhds.smul_section hu_grad)
  have hprod_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z => u t z * v t z) y) x :=
    hsum_grad.congr_of_eventuallyEq (by
      filter_upwards [hgrad_eq] with y hy
      exact congrArg (fun a =>
        (⟨y, a⟩ : TotalSpace E (TangentSpace I : M → Type _))) hy)
  have hcov :
      (G.connection t)
          (fun y : M =>
            gradientFun (I := I) (G.metric t) (fun z => u t z * v t z) y) x =
        (G.connection t)
          (fun y : M =>
            u t y • gradientFun (I := I) (G.metric t) (v t) y +
              v t y • gradientFun (I := I) (G.metric t) (u t) y) x :=
    (G.connection t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hprod_grad hsum_grad Filter.univ_mem hgrad_eq
  have hlap :
      laplacianAt (I := I) G t (fun y : M => u t y * v t y) x =
        u t x * laplacianAt (I := I) G t (v t) x +
          v t x * laplacianAt (I := I) G t (u t) x +
            2 * (G.metric t).inner x
              (gradientAt (I := I) G t (u t) x)
              (gradientAt (I := I) G t (v t) x) := by
    unfold laplacianAt laplacian divergence
    rw [hcov]
    rw [show (fun y : M =>
        u t y • gradientFun (I := I) (G.metric t) (v t) y +
          v t y • gradientFun (I := I) (G.metric t) (u t) y) =
        u t • gradientFun (I := I) (G.metric t) (v t) +
          v t • gradientFun (I := I) (G.metric t) (u t) by
      rfl]
    rw [(G.connection t).isCovariantDerivativeOnUniv.add
      (hu_space.self_of_nhds.smul_section hv_grad)
      (hv_space.self_of_nhds.smul_section hu_grad)]
    rw [(G.connection t).isCovariantDerivativeOnUniv.leibniz
      hv_grad hu_space.self_of_nhds]
    rw [(G.connection t).isCovariantDerivativeOnUniv.leibniz
      hu_grad hv_space.self_of_nhds]
    simp only [ContinuousLinearMap.coe_add, map_add,
      ContinuousLinearMap.coe_smul]
    rw [map_smul, map_smul]
    have htrace_u :
        LinearMap.trace Real (TangentSpace I x)
            ((extDerivFun (I := I) (u t) x).toLinearMap.smulRight
              (gradientFun (I := I) (G.metric t) (v t) x)) =
          extDerivFun (I := I) (u t) x
            (gradientFun (I := I) (G.metric t) (v t) x) :=
      LinearMap.trace_smulRight _ _
    have htrace_v :
        LinearMap.trace Real (TangentSpace I x)
            ((extDerivFun (I := I) (v t) x).toLinearMap.smulRight
              (gradientFun (I := I) (G.metric t) (u t) x)) =
          extDerivFun (I := I) (v t) x
            (gradientFun (I := I) (G.metric t) (u t) x) :=
      LinearMap.trace_smulRight _ _
    change
      u t x • LinearMap.trace Real (TangentSpace I x)
          (G.connection t (gradientFun (I := I) (G.metric t) (v t)) x).toLinearMap +
          LinearMap.trace Real (TangentSpace I x)
            ((extDerivFun (I := I) (u t) x).toLinearMap.smulRight
              (gradientFun (I := I) (G.metric t) (v t) x)) +
        (v t x • LinearMap.trace Real (TangentSpace I x)
            (G.connection t (gradientFun (I := I) (G.metric t) (u t)) x).toLinearMap +
          LinearMap.trace Real (TangentSpace I x)
            ((extDerivFun (I := I) (v t) x).toLinearMap.smulRight
              (gradientFun (I := I) (G.metric t) (u t) x))) = _
    rw [htrace_u, htrace_v]
    simp only [gradientAt, extDerivFun]
    have huv :
        extDerivFun (I := I) (u t) x
            (gradientFun (I := I) (G.metric t) (v t) x) =
          (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) (u t) x)
            (gradientFun (I := I) (G.metric t) (v t) x) := by
      simpa [extDerivFun] using
        (inner_gradientFun (I := I) (G.metric t) (u t) x
          (gradientFun (I := I) (G.metric t) (v t) x)).symm
    have hvu :
        extDerivFun (I := I) (v t) x
            (gradientFun (I := I) (G.metric t) (u t) x) =
          (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) (v t) x)
            (gradientFun (I := I) (G.metric t) (u t) x) := by
      simpa [extDerivFun] using
        (inner_gradientFun (I := I) (G.metric t) (v t) x
          (gradientFun (I := I) (G.metric t) (u t) x)).symm
    rw [huv, hvu]
    rw [(G.metric t).symm x
      (gradientFun (I := I) (G.metric t) (v t) x)
      (gradientFun (I := I) (G.metric t) (u t) x)]
    simp only [smul_eq_mul]
    ring
  have hdrift := driftTerm_mul (I := I) G t (X t)
    hu_space.self_of_nhds hv_space.self_of_nhds
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [derivWithin_fun_mul hu_time hv_time, hlap, hdrift]
  ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- Local additivity of the scalar parabolic operator. -/
private theorem parabolic_add_nhds
    {G : RealizedMetricFamily (I := I) (M := M) Real}
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
  have hgrad_eq :
      (fun y : M =>
          gradientFun (I := I) (G.metric t) (fun z => u t z + v t z) y) =ᶠ[𝓝 x]
        (fun y : M =>
          gradientFun (I := I) (G.metric t) (u t) y +
            gradientFun (I := I) (G.metric t) (v t) y) := by
    filter_upwards [hu_space, hv_space] with y huy hvy
    exact gradientFun_add (I := I) (G.metric t) huy hvy
  have hsum_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y +
          gradientFun (I := I) (G.metric t) (v t) y) x :=
    mdifferentiableAt_add_section hu_grad hv_grad
  have hleft_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z => u t z + v t z) y) x :=
    hsum_grad.congr_of_eventuallyEq (by
      filter_upwards [hgrad_eq] with y hy
      exact congrArg (fun a =>
        (⟨y, a⟩ : TotalSpace E (TangentSpace I : M → Type _))) hy)
  have hcov :
      (G.connection t)
          (fun y : M =>
            gradientFun (I := I) (G.metric t) (fun z => u t z + v t z) y) x =
        (G.connection t)
          (fun y : M =>
            gradientFun (I := I) (G.metric t) (u t) y +
              gradientFun (I := I) (G.metric t) (v t) y) x :=
    (G.connection t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hleft_grad hsum_grad Filter.univ_mem hgrad_eq
  have hlap :
      laplacianAt (I := I) G t (fun y : M => u t y + v t y) x =
        laplacianAt (I := I) G t (u t) x +
          laplacianAt (I := I) G t (v t) x := by
    unfold laplacianAt laplacian divergence
    rw [hcov]
    rw [show (fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y +
          gradientFun (I := I) (G.metric t) (v t) y) =
        gradientFun (I := I) (G.metric t) (u t) +
          gradientFun (I := I) (G.metric t) (v t) by rfl]
    rw [(G.connection t).isCovariantDerivativeOnUniv.add hu_grad hv_grad]
    exact LinearMap.map_add
      (LinearMap.trace Real (TangentSpace I x)) _ _
  have hdrift := driftTerm_add (I := I) G t (X t)
    hu_space.self_of_nhds hv_space.self_of_nhds
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [derivWithin_fun_add hu_time hv_time, hlap, hdrift]
  ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
/-- Local regularity of a finite scalar sum and of its spatial gradient. -/
private theorem sum_reg_nhds
    {G : RealizedMetricFamily (I := I) (M := M) Real}
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
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using
          (differentiableWithinAt_const (c := (0 : Real))
            (x := t) (s := Set.Icc 0 T))
      · exact Filter.Eventually.of_forall fun _ => by
          simpa using (mdifferentiableAt_const :
            MDifferentiableAt I 𝓘(Real, Real) (fun _ : M => (0 : Real)) _)
      · rw [show (T% fun y : M =>
            gradientFun (I := I) (G.metric t)
              (fun z : M => ∑ i ∈ (∅ : Finset κ), u i t z) y) =
            (T% fun y : M => (0 : TangentSpace I y)) by
          funext y
          simp only [Finset.sum_empty, gradientFun_const]]
        exact mdifferentiableAt_zeroSection
          (𝕜 := Real) (F := E) (E := (TangentSpace I : M → Type _)) (x := x)
  | @insert a s ha ih =>
      have ih' := ih
        (fun i hi => htime i (Finset.mem_insert_of_mem hi))
        (fun i hi => hspace i (Finset.mem_insert_of_mem hi))
        (fun i hi => hgrad i (Finset.mem_insert_of_mem hi))
      have hatime := htime a (Finset.mem_insert_self a s)
      have haspace := hspace a (Finset.mem_insert_self a s)
      have hagrad := hgrad a (Finset.mem_insert_self a s)
      refine ⟨?_, ?_, ?_⟩
      · rw [show (fun r : Real => ∑ i ∈ insert a s, u i r x) =
            (fun r : Real => u a r x + ∑ i ∈ s, u i r x) by
          funext r
          rw [Finset.sum_insert ha]]
        exact hatime.add ih'.1
      · filter_upwards [haspace, ih'.2.1] with y hay hsy
        rw [show (fun z : M => ∑ i ∈ insert a s, u i t z) =
            (fun z : M => u a t z + ∑ i ∈ s, u i t z) by
          funext z
          rw [Finset.sum_insert ha]]
        exact hay.add hsy
      · have hgrad_eq :
            (fun y : M => gradientFun (I := I) (G.metric t)
                (fun z : M => ∑ i ∈ insert a s, u i t z) y) =ᶠ[𝓝 x]
              (fun y : M =>
                gradientFun (I := I) (G.metric t) (u a t) y +
                  gradientFun (I := I) (G.metric t)
                    (fun z : M => ∑ i ∈ s, u i t z) y) := by
          filter_upwards [haspace, ih'.2.1] with y hay hsy
          rw [show (fun z : M => ∑ i ∈ insert a s, u i t z) =
              (fun z : M => u a t z + ∑ i ∈ s, u i t z) by
            funext z
            rw [Finset.sum_insert ha]]
          exact gradientFun_add (I := I) (G.metric t) hay hsy
        have hsum_grad :
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
              gradientFun (I := I) (G.metric t) (u a t) y +
                gradientFun (I := I) (G.metric t)
                  (fun z : M => ∑ i ∈ s, u i t z) y) x :=
          mdifferentiableAt_add_section hagrad ih'.2.2
        exact hsum_grad.congr_of_eventuallyEq (by
          filter_upwards [hgrad_eq] with y hy
          exact congrArg (fun b =>
            (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) hy)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
/-- Local finite-sum rule for the scalar parabolic operator. -/
private theorem parabolic_sum_nhds
    {G : RealizedMetricFamily (I := I) (M := M) Real}
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
      have hzero_time : DifferentiableWithinAt Real
          (fun _ : Real => (0 : Real)) (Set.Icc 0 T) t :=
        differentiableWithinAt_const 0
      have hzero_space : ∀ᶠ y in 𝓝 x,
          MDifferentiableAt I 𝓘(Real, Real) (fun _ : M => (0 : Real)) y :=
        Filter.Eventually.of_forall fun _ => mdifferentiableAt_const
      have hzero_grad :
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (fun _ : M => (0 : Real)) y) x := by
        rw [show (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (fun _ : M => (0 : Real)) y) =
            (T% fun y : M => (0 : TangentSpace I y)) by
          funext y
          simp only [gradientFun_const]]
        exact mdifferentiableAt_zeroSection
          (𝕜 := Real) (F := E) (E := (TangentSpace I : M → Type _)) (x := x)
      have hadd := parabolic_add_nhds (I := I) T X
        (fun _ _ => (0 : Real)) (fun _ _ => (0 : Real)) t x
        hzero_time hzero_time hzero_space hzero_space hzero_grad hzero_grad
      change parabolicOperatorWithDrift (I := I) G T X
          (fun _ _ => (0 : Real)) t x = 0
      have hadd' :
          parabolicOperatorWithDrift (I := I) G T X
              (fun _ _ => (0 : Real)) t x =
            parabolicOperatorWithDrift (I := I) G T X
                (fun _ _ => (0 : Real)) t x +
              parabolicOperatorWithDrift (I := I) G T X
                (fun _ _ => (0 : Real)) t x := by
        simpa only [zero_add] using hadd
      linarith
  | @insert a s ha ih =>
      have hatime := htime a (Finset.mem_insert_self a s)
      have haspace := hspace a (Finset.mem_insert_self a s)
      have hagrad := hgrad a (Finset.mem_insert_self a s)
      have hsreg := sum_reg_nhds (I := I) (G := G) s u T t x
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

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
/-- The scalar parabolic operator vanishes on a spacetime constant. -/
private theorem parabolic_const_zero
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (a t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun _ _ => a) t x = 0 := by
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
    laplacian divergence driftTerm gradientAt
  rw [(hasDerivWithinAt_const
    (x := t) (s := Set.Icc 0 T) (c := a)).derivWithin huniq]
  rw [show gradientFun (I := I) (G.metric t) ((fun _ _ => a) t) =
      (fun y : M => (0 : TangentSpace I y)) by
    funext y
    simp only [gradientFun_const]]
  rw [show (fun y : M => (0 : TangentSpace I y)) = 0 by rfl]
  rw [(G.connection t).isCovariantDerivativeOnUniv.zero (x := x)]
  rw [show (↑(0 : TangentSpace I x →L[Real] TangentSpace I x) :
      TangentSpace I x →ₗ[Real] TangentSpace I x) = 0 by rfl]
  rw [map_zero, Pi.zero_apply, map_zero]
  ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- Local fixed-scalar rule for the scalar parabolic operator. -/
private theorem parabolic_smul_nhds
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (u : Real → M → Real) (t : Real) (x : M)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => a * u s y) t x =
      a * parabolicOperatorWithDrift (I := I) G T X u t x := by
  have ha_time : DifferentiableWithinAt Real
      (fun _ : Real => a) (Set.Icc 0 T) t :=
    differentiableWithinAt_const a
  have ha_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (fun _ : M => a) y :=
    Filter.Eventually.of_forall fun _ => mdifferentiableAt_const
  have ha_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun _ : M => a) y) x := by
    rw [show (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun _ : M => a) y) =
        (T% fun y : M => (0 : TangentSpace I y)) by
      funext y
      simp only [gradientFun_const]]
    exact mdifferentiableAt_zeroSection
      (𝕜 := Real) (F := E) (E := (TangentSpace I : M → Type _)) (x := x)
  have hmul := parabolic_mul_nhds (I := I) T X
    (fun _ _ => a) u t x
    ha_time hu_time ha_space hu_space ha_grad hu_grad
  rw [parabolic_const_zero (I := I) T X a t x huniq] at hmul
  have hzero :
      gradientAt (I := I) G t (fun _ : M => a) x = 0 := by
    unfold gradientAt
    rw [gradientFun_const]
  rw [hzero] at hmul
  simpa using hmul

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- Local affine-minus-function rule for the scalar parabolic operator. -/
private theorem parabolic_aff_nhds
    {G : RealizedMetricFamily (I := I) (M := M) Real}
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
      ((differentiableWithinAt_id'
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
        simpa only [Pi.smul_apply, smul_eq_mul] using
          gradientFun_const_smul (I := I) (G.metric t) (-1) hy)
  have hadd := parabolic_add_nhds (I := I) T X A
    (fun s y => (-1 : Real) * F s y) t x
    hAtime hnegtime hAspace hnegspace hAgrad hneggrad
  have hneg := parabolic_smul_nhds (I := I) T X (-1) F t x
    hFtime hFspace hFgrad huniq
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
      simpa only [mul_one] using
        ((hasDerivWithinAt_id t (Set.Icc 0 T)).const_mul b).derivWithin huniq
    rw [derivWithin_fun_add (differentiableWithinAt_const a)
      ((differentiableWithinAt_id'
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

/-- Pointwise Kato control for the gradients of a Bernstein tower.  For the
curvature tower this is supplied by `towerNorm_grad_le`; it is generated from
the solution and is not an HCG input. -/
def TowerNormGradUpTo
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G) (m : Nat) : Prop :=
  ∀ k : Nat, k ≤ m → ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (B.w k t) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      4 * B.w k t x * B.w (k + 1) t x

/-- Pointwise Kato control at every level of a Bernstein tower. -/
def TowerNormGradOn
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G) : Prop :=
  ∀ m : Nat, TowerNormGradUpTo (I := I) B m

namespace TowerNormGradOn

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- Restrict all-level Kato control to the levels used by a localized
Bernstein polynomial. -/
theorem upTo
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    {B : BernsteinTower (I := I) G}
    (h : TowerNormGradOn (I := I) B) (m : Nat) :
    TowerNormGradUpTo (I := I) B m :=
  h m

end TowerNormGradOn

namespace ShiCutoffData

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The cutoff-gradient cross term is absorbed by half of the next tower
level, up to the cutoff error times the current level. -/
theorem cross_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n k : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hk : k ≤ m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M) :
    -2 * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (cut.chi n t) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      cut.chi n t x * B.w (k + 1) t x +
        4 * cut.err n * B.w k t x := by
  let a := gradientFun (I := I) (G.metric t) (cut.chi n t) x
  let b := gradientFun (I := I) (G.metric t) (B.w k t) x
  let c := (G.metric t).inner x a b
  let p := cut.chi n t x * B.w (k + 1) t x
  let q := 4 * cut.err n * B.w k t x
  have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
  have herr : 0 ≤ cut.err n := cut.err_nonneg n
  have hw : 0 ≤ B.w k t x := B.hw_nonneg k t ht x
  have hnext : 0 ≤ B.w (k + 1) t x := B.hw_nonneg (k + 1) t ht x
  have ha : (G.metric t).inner x a a ≤ cut.err n * cut.chi n t x := by
    simpa [a] using cut.grad_sq_le n t ht htpos x
  have hb : (G.metric t).inner x b b ≤ 4 * B.w k t x * B.w (k + 1) t x := by
    simpa [b] using hgrad k hk t ht htpos x
  have haa : 0 ≤ (G.metric t).inner x a a :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x a
  have hbb : 0 ≤ (G.metric t).inner x b b :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x b
  have hsq : c ^ 2 ≤ p * q := by
    calc
      c ^ 2 ≤
          (G.metric t).inner x a a * (G.metric t).inner x b b := by
        exact DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          (I := I) (M := M) (G.metric t) x a b
      _ ≤ (cut.err n * cut.chi n t x) *
          (4 * B.w k t x * B.w (k + 1) t x) :=
        mul_le_mul ha hb hbb (mul_nonneg herr hchi)
      _ = p * q := by simp only [p, q]; ring
  have hp : 0 ≤ p := mul_nonneg hchi hnext
  have hq : 0 ≤ q := mul_nonneg (mul_nonneg (by norm_num) herr) hw
  have hhalf : p * q ≤ ((p + q) / 2) ^ 2 := by
    nlinarith [sq_nonneg (p - q)]
  have habs : |c| ≤ (p + q) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (p + q) / 2 := (neg_le_abs c).trans habs
  dsimp [c, p, q] at hneg ⊢
  linarith

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
/-- The parabolic cutoff error of a positive natural power is controlled by
the same power with one factor removed. -/
theorem pow_parabolic_le
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (n p : Nat)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M) :
    parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => (cut.chi n s y) ^ (p + 1)) t x ≤
      (((p + 1 : Nat) : Real) * cut.err n) * (cut.chi n t x) ^ p := by
  induction p with
  | zero =>
      simpa using cut.parabolic_le n t ht htpos x
  | succ p ih =>
      have hu_time : DifferentiableWithinAt Real
          (fun s : Real => (cut.chi n s x) ^ (p + 1)) (Set.Icc 0 T) t :=
        (cut.time_diff n t ht htpos x).pow (p + 1)
      have hv_time : DifferentiableWithinAt Real
          (fun s : Real => cut.chi n s x) (Set.Icc 0 T) t :=
        cut.time_diff n t ht htpos x
      have hu_space : ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun z : M => (cut.chi n t z) ^ (p + 1)) y :=
        fun y => (cut.space_diff ht y).pow (p + 1)
      have hv_space : ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real) (cut.chi n t) y :=
        fun y => cut.space_diff ht y
      have hu_grad : ∀ y : M,
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
            gradientFun (I := I) (G.metric t)
              (fun q : M => (cut.chi n t q) ^ (p + 1)) z) y :=
        fun y => gradientFun_mdiffAt (I := I) (G.metric t)
          ((cut.space_smooth n t ht).pow (p + 1)) y
      have hv_grad : ∀ y : M,
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
            gradientFun (I := I) (G.metric t) (cut.chi n t) z) y :=
        fun y => cut.grad_diff ht y
      have hmul := parabolic_mul (I := I) G T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => (cut.chi n s y) ^ (p + 1)) (cut.chi n) t x
        hu_time hv_time hu_space hv_space hu_grad hv_grad
      have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
      have hgrad := gradientFun_pow (I := I) (G.metric t)
        (f := cut.chi n t) p (cut.space_diff (n := n) ht x)
      have hinner : 0 ≤ (G.metric t).inner x
          (gradientAt (I := I) G t
            (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
          (gradientAt (I := I) G t (cut.chi n t) x) := by
        simp only [gradientAt_eq, hgrad, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hchi p))
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) (G.metric t) x
              (gradientFun (I := I) (G.metric t) (cut.chi n t) x))
      have hcross : -2 * (G.metric t).inner x
          (gradientAt (I := I) G t
            (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
          (gradientAt (I := I) G t (cut.chi n t) x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by norm_num) hinner
      have hcut := cut.parabolic_le n t ht htpos x
      have hcut_mul := mul_le_mul_of_nonneg_left hcut (pow_nonneg hchi (p + 1))
      have hih_mul := mul_le_mul_of_nonneg_left ih hchi
      calc
        parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y))
            (fun s y => (cut.chi n s y) ^ (Nat.succ p + 1)) t x =
            parabolicOperatorWithDrift (I := I) G T
              (fun _ y => (0 : TangentSpace I y))
              (fun s y => (cut.chi n s y) ^ (p + 1) * cut.chi n s y) t x := by
                apply congrArg (fun u : Real → M → Real =>
                  parabolicOperatorWithDrift (I := I) G T
                    (fun _ y => (0 : TangentSpace I y)) u t x)
                funext s y
                rw [show Nat.succ p + 1 = (p + 1) + 1 by omega, pow_succ]
        _ = (cut.chi n t x) ^ (p + 1) *
              parabolicOperatorWithDrift (I := I) G T
                (fun _ y => (0 : TangentSpace I y)) (cut.chi n) t x +
            cut.chi n t x *
              parabolicOperatorWithDrift (I := I) G T
                (fun _ y => (0 : TangentSpace I y))
                (fun s y => (cut.chi n s y) ^ (p + 1)) t x -
            2 * (G.metric t).inner x
              (gradientAt (I := I) G t
                (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
              (gradientAt (I := I) G t (cut.chi n t) x) := hmul
        _ ≤ (cut.chi n t x) ^ (p + 1) * cut.err n +
            cut.chi n t x *
              ((((p + 1 : Nat) : Real) * cut.err n) *
                (cut.chi n t x) ^ p) := by
              linarith
        _ = (((Nat.succ p + 1 : Nat) : Real) * cut.err n) *
            (cut.chi n t x) ^ Nat.succ p := by
              simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ]
              ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- A cutoff-power gradient term is absorbed by half of the next tower level,
leaving an error with one fewer cutoff factor. -/
theorem pow_cross_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n k p : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hk : k ≤ m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M) :
    -2 * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t)
          (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      (1 / 2 : Real) * (cut.chi n t x) ^ (p + 1) * B.w (k + 1) t x +
        8 * (((p + 1 : Nat) : Real) ^ 2) * cut.err n *
          (cut.chi n t x) ^ p * B.w k t x := by
  let a := gradientFun (I := I) (G.metric t) (cut.chi n t) x
  let b := gradientFun (I := I) (G.metric t) (B.w k t) x
  let c₀ := (G.metric t).inner x a b
  let c := (G.metric t).inner x
    (gradientFun (I := I) (G.metric t)
      (fun y : M => (cut.chi n t y) ^ (p + 1)) x) b
  let r : Real := ((p + 1 : Nat) : Real) * (cut.chi n t x) ^ p
  let q₁ : Real := (1 / 2 : Real) * (cut.chi n t x) ^ (p + 1) * B.w (k + 1) t x
  let q₂ : Real := 8 * (((p + 1 : Nat) : Real) ^ 2) * cut.err n *
    (cut.chi n t x) ^ p * B.w k t x
  have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
  have herr : 0 ≤ cut.err n := cut.err_nonneg n
  have hw : 0 ≤ B.w k t x := B.hw_nonneg k t ht x
  have hnext : 0 ≤ B.w (k + 1) t x := B.hw_nonneg (k + 1) t ht x
  have ha : (G.metric t).inner x a a ≤ cut.err n * cut.chi n t x := by
    simpa [a] using cut.grad_sq_le n t ht htpos x
  have hb : (G.metric t).inner x b b ≤ 4 * B.w k t x * B.w (k + 1) t x := by
    simpa [b] using hgrad k hk t ht htpos x
  have haa : 0 ≤ (G.metric t).inner x a a :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x a
  have hbb : 0 ≤ (G.metric t).inner x b b :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x b
  have hsq₀ : c₀ ^ 2 ≤
      (cut.err n * cut.chi n t x) *
        (4 * B.w k t x * B.w (k + 1) t x) := by
    calc
      c₀ ^ 2 ≤ (G.metric t).inner x a a * (G.metric t).inner x b b := by
        exact DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          (I := I) (M := M) (G.metric t) x a b
      _ ≤ (cut.err n * cut.chi n t x) *
          (4 * B.w k t x * B.w (k + 1) t x) :=
        mul_le_mul ha hb hbb (mul_nonneg herr hchi)
  have hc : c = r * c₀ := by
    dsimp [c, r, c₀, a]
    rw [gradientFun_pow (I := I) (G.metric t)
      (f := cut.chi n t) p (cut.space_diff (n := n) ht x)]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hsq : c ^ 2 ≤ q₁ * q₂ := by
    rw [hc]
    calc
      (r * c₀) ^ 2 = r ^ 2 * c₀ ^ 2 := by ring
      _ ≤ r ^ 2 * ((cut.err n * cut.chi n t x) *
          (4 * B.w k t x * B.w (k + 1) t x)) :=
        mul_le_mul_of_nonneg_left hsq₀ hr2
      _ = q₁ * q₂ := by
        dsimp [r, q₁, q₂]
        rw [pow_succ]
        ring
  have hq₁ : 0 ≤ q₁ := by
    dsimp [q₁]
    positivity
  have hq₂ : 0 ≤ q₂ := by
    dsimp [q₂]
    positivity
  have hhalf : q₁ * q₂ ≤ ((q₁ + q₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (q₁ - q₂)]
  have habs : |c| ≤ (q₁ + q₂) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (q₁ + q₂) / 2 := (neg_le_abs c).trans habs
  dsimp [c, q₁, q₂, b] at hneg ⊢
  linarith

end ShiCutoffData

/-- The scalar coefficient of the level-`i` cutoff error in the graded
Bernstein recurrence. -/
def cutErrCoeff (i : Nat) : Real :=
  8 * (i + 1 : Real) ^ 2 + (i + 1 : Real)

/-- Graded cutoff-error coefficients are nonnegative. -/
theorem cutErrCoeff_nonneg (i : Nat) : 0 ≤ cutErrCoeff i := by
  unfold cutErrCoeff
  positivity

/-- The graded cutoff-error coefficient increases with the tower level. -/
theorem cutErrCoeff_mono : Monotone cutErrCoeff := by
  intro i j hij
  have hij' : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
  have hi : 0 ≤ (i : Real) + 1 := by positivity
  have hj : 0 ≤ (j : Real) + 1 := by positivity
  have hfac :
      0 ≤ (((j : Real) + 1) - ((i : Real) + 1)) *
        (((j : Real) + 1) + ((i : Real) + 1)) :=
    mul_nonneg (by linarith) (add_nonneg hj hi)
  unfold cutErrCoeff
  nlinarith

namespace ShiCutoffData

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- For every fixed finite tower, the cutoff errors eventually satisfy the
smallness inequalities used by the graded Bernstein recurrence. -/
theorem cutErr_small
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (m : Nat) :
    ∀ᶠ n in Filter.atTop, ∀ i ∈ Finset.range (m + 1),
      cutErrCoeff i * cut.err n * T < (1 : Real) / 4 := by
  refine (Filter.eventually_all_finset (Finset.range (m + 1))).mpr ?_
  intro i hi
  have hlim : Filter.Tendsto
      (fun n ↦ cutErrCoeff i * cut.err n * T)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      (cut.err_tendsto.const_mul (cutErrCoeff i)).mul_const T
  exact hlim.eventually_lt_const (by norm_num)

end ShiCutoffData

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
private theorem support_pow_para
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T eps t : Real}
    {chi : Real → M → Real} {x : M}
    (support : ShiCutoffLowerSupportAt (I := I) G T eps chi t x)
    (ht : t ∈ Set.Icc 0 T) (p : Nat) :
    parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => (support.phi s y) ^ (p + 1)) t x ≤
      (((p + 1 : Nat) : Real) * eps) * (support.phi t x) ^ p := by
  have hphi0 : 0 ≤ support.phi t x :=
    (support.lower_nhds.self_of_nhdsWithin
      (show (t, x) ∈ spacetimeSlab (M := M) T from ⟨ht, Set.mem_univ x⟩)).1
  induction p with
  | zero => simpa using support.parabolic_le
  | succ p ih =>
      let qpow : Real → M → Real := fun s y => support.phi s y ^ (p + 1)
      have hqtime := support.time_diff.pow (p + 1)
      have hqspace : ∀ᶠ y in 𝓝 x,
          MDifferentiableAt I 𝓘(Real, Real) (qpow t) y := by
        filter_upwards [support.space_diff_nhds] with y hy
        exact hy.pow (p + 1)
      have hqgrad :
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (qpow t) y) x := by
        have hrhs :
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
              (((p + 1 : Nat) : Real) * support.phi t y ^ p) •
                gradientFun (I := I) (G.metric t) (support.phi t) y) x :=
          (((support.space_diff_nhds.self_of_nhds.pow p).const_smul
            (((p + 1 : Nat) : Real))).smul_section support.grad_diff)
        refine hrhs.congr_of_eventuallyEq ?_
        filter_upwards [support.space_diff_nhds] with y hy
        exact congrArg (fun b =>
          (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
          (gradientFun_pow (I := I) (G.metric t) p hy)
      have hmul := parabolic_mul_nhds (I := I) T
        (fun _ y => (0 : TangentSpace I y)) qpow support.phi t x
        hqtime support.time_diff hqspace support.space_diff_nhds
        hqgrad support.grad_diff
      have hgrad := gradientFun_pow (I := I) (G.metric t) p
        support.space_diff_nhds.self_of_nhds
      have hinner : 0 ≤ (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (support.phi t) x) := by
        dsimp only [qpow]
        simp only [gradientAt_eq, hgrad, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hphi0 p))
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) (G.metric t) x
              (gradientFun (I := I) (G.metric t) (support.phi t) x))
      have hphi_mul := mul_le_mul_of_nonneg_left ih hphi0
      have hcut_mul := mul_le_mul_of_nonneg_left support.parabolic_le
        (pow_nonneg hphi0 (p + 1))
      calc
        parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y))
            (fun s y => support.phi s y ^ (Nat.succ p + 1)) t x =
            parabolicOperatorWithDrift (I := I) G T
              (fun _ y => (0 : TangentSpace I y))
              (fun s y => qpow s y * support.phi s y) t x := by
                congr 1
        _ ≤ support.phi t x ^ (p + 1) * eps +
            support.phi t x *
              ((((p + 1 : Nat) : Real) * eps) * support.phi t x ^ p) := by
              rw [hmul]
              linarith
        _ = (((Nat.succ p + 1 : Nat) : Real) * eps) *
            support.phi t x ^ Nat.succ p := by
              simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ]
              ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem support_pow_cross
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    {m k p : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hk : k ≤ m)
    {eps t : Real} {chi : Real → M → Real} {x : M}
    (support : ShiCutoffLowerSupportAt (I := I) G B.T eps chi t x)
    (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (heps : 0 ≤ eps) :
    -2 * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t)
          (fun y : M => support.phi t y ^ (p + 1)) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      (1 / 2 : Real) * support.phi t x ^ (p + 1) * B.w (k + 1) t x +
        8 * (((p + 1 : Nat) : Real) ^ 2) * eps *
          support.phi t x ^ p * B.w k t x := by
  let a := gradientFun (I := I) (G.metric t) (support.phi t) x
  let b := gradientFun (I := I) (G.metric t) (B.w k t) x
  let c₀ := (G.metric t).inner x a b
  let c := (G.metric t).inner x
    (gradientFun (I := I) (G.metric t)
      (fun y : M => support.phi t y ^ (p + 1)) x) b
  let r : Real := ((p + 1 : Nat) : Real) * support.phi t x ^ p
  let q₁ : Real := (1 / 2 : Real) * support.phi t x ^ (p + 1) * B.w (k + 1) t x
  let q₂ : Real := 8 * (((p + 1 : Nat) : Real) ^ 2) * eps *
    support.phi t x ^ p * B.w k t x
  have hphi0 : 0 ≤ support.phi t x :=
    (support.lower_nhds.self_of_nhdsWithin
      (show (t, x) ∈ spacetimeSlab (M := M) B.T from ⟨ht, Set.mem_univ x⟩)).1
  have hsq₀ : c₀ ^ 2 ≤
      (eps * support.phi t x) * (4 * B.w k t x * B.w (k + 1) t x) := by
    calc
      c₀ ^ 2 ≤ (G.metric t).inner x a a * (G.metric t).inner x b b :=
        DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          (I := I) (M := M) (G.metric t) x a b
      _ ≤ (eps * support.phi t x) *
          (4 * B.w k t x * B.w (k + 1) t x) :=
        mul_le_mul support.grad_sq_le (hgrad k hk t ht htpos x)
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) (G.metric t) x b)
          (mul_nonneg heps hphi0)
  have hc : c = r * c₀ := by
    dsimp [c, r, c₀, a]
    rw [gradientFun_pow (I := I) (G.metric t) p
      support.space_diff_nhds.self_of_nhds]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsq : c ^ 2 ≤ q₁ * q₂ := by
    rw [hc]
    calc
      (r * c₀) ^ 2 = r ^ 2 * c₀ ^ 2 := by ring
      _ ≤ r ^ 2 * ((eps * support.phi t x) *
          (4 * B.w k t x * B.w (k + 1) t x)) :=
        mul_le_mul_of_nonneg_left hsq₀ (sq_nonneg r)
      _ = q₁ * q₂ := by
        dsimp [r, q₁, q₂]
        rw [pow_succ]
        ring
  have hq₁ : 0 ≤ q₁ := by
    dsimp [q₁]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hphi0 (p + 1)))
      (B.hw_nonneg (k + 1) t ht x)
  have hq₂ : 0 ≤ q₂ := by
    dsimp [q₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) heps)
      (pow_nonneg hphi0 p)) (B.hw_nonneg k t ht x)
  have hhalf : q₁ * q₂ ≤ ((q₁ + q₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (q₁ - q₂)]
  have habs : |c| ≤ (q₁ + q₂) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (q₁ + q₂) / 2 := (neg_le_abs c).trans habs
  dsimp [c, q₁, q₂, b] at hneg ⊢
  linarith

private noncomputable def GfunLocal
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (q : Real → M → Real) (m : Nat) (t : Real) (x : M) : Real :=
  ∑ i ∈ Finset.range (m + 1),
    BernsteinTower.Gcoef (I := I) B m i * t ^ i *
      (q t x) ^ (i + 1) * B.w i t x

/-- The graded localized Bernstein polynomial.  Level `i` is multiplied by
`chi^(i+1)`, so every summand has compact support while cutoff errors can be
absorbed one level lower in the tower recursion. -/
noncomputable def GfunCut
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) (t : Real) (x : M) : Real :=
  ∑ i ∈ Finset.range (m + 1),
    BernsteinTower.Gcoef (I := I) B m i * t ^ i *
      (cut.chi n t x) ^ (i + 1) * B.w i t x

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded localized Bernstein polynomial is nonnegative on the controlled
time slab. -/
theorem GfunCut_nonneg
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T) (x : M) :
    0 ≤ GfunCut (I := I) B cut m n t x := by
  rw [GfunCut]
  apply Finset.sum_nonneg
  intro i hi
  have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (BernsteinTower.Gcoef_nonneg (I := I) B m i)
        (pow_nonneg ht.1 i))
      (pow_nonneg hchi (i + 1)))
    (B.hw_nonneg i t ht x)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded polynomial vanishes wherever the cutoff vanishes. -/
@[simp] theorem GfunCut_zero
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} {t : Real} {x : M}
    (hchi : cut.chi n t x = 0) :
    GfunCut (I := I) B cut m n t x = 0 := by
  simp [GfunCut, hchi]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded polynomial vanishes outside the spatial support of its cutoff
on the controlled time slab. -/
theorem GfunCut_off
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T)
    {x : M} (hx : x ∉ cut.support n) :
    GfunCut (I := I) B cut m n t x = 0 :=
  GfunCut_zero (I := I) B cut (cut.support_zero n t ht x hx)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded localized Bernstein polynomial is jointly continuous on its
closed spacetime slab. -/
theorem GfunCut_cont
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) :
    ContinuousOn (fun p : Real × M => GfunCut (I := I) B cut m n p.1 p.2)
      (spacetimeSlab (M := M) B.T) := by
  rw [show (fun p : Real × M => GfunCut (I := I) B cut m n p.1 p.2) =
      (fun p : Real × M => ∑ i ∈ Finset.range (m + 1),
        BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i *
          (cut.chi n p.1 p.2) ^ (i + 1) * B.w i p.1 p.2) from by
    funext p
    rw [GfunCut]]
  apply continuousOn_finset_sum
  intro i hi
  exact (((continuous_const.mul (continuous_fst.pow i)).continuousOn.mul
    ((cut.joint_cont n).pow (i + 1))).mul (B.hw_cont i))

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- On the exhausted region, the graded polynomial is the ordinary Bernstein
polynomial. -/
theorem GfunCut_one
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} {t : Real} {x : M}
    (hchi : cut.chi n t x = 1) :
    GfunCut (I := I) B cut m n t x = BernsteinTower.Gfun (I := I) B m t x := by
  simp [GfunCut, BernsteinTower.Gfun, hchi]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem cutWterms_nonpos
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    {m : Nat} (hm : 1 ≤ m) {t q eps : Real}
    (ht : t ∈ Set.Icc 0 B.T) (x : M)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (he0 : 0 ≤ eps)
    (hsmall : 2 * eps * B.T * cutErrCoeff m ≤ 1) :
    let beta := towerBeta B.c B.α (towerConst B.c B.α) m
    let barTop := towerBarTop B.c (towerConst B.c B.α) m
    (∑ k ∈ Finset.Ico 1 m, (
        BernsteinTower.Gcoef (I := I) B m k *
              ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) +
            BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
              t ^ k * q ^ k * B.w k t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (k - 1) *
              t ^ (k - 1) * q ^ k * B.w k t x)) +
      (BernsteinTower.Gcoef (I := I) B m m *
              ((m : Real) * t ^ (m - 1) * q ^ (m + 1) * B.w m t x) +
            BernsteinTower.Gcoef (I := I) B m m * cutErrCoeff m * eps *
              t ^ m * q ^ m * B.w m t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (m - 1) *
              t ^ (m - 1) * q ^ m * B.w m t x +
            barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x)) ≤ 0 := by
  classical
  dsimp only
  set beta : Real := towerBeta B.c B.α (towerConst B.c B.α) m with hbeta
  set barTop : Real := towerBarTop B.c (towerConst B.c B.α) m with hbarTop
  have ht0 : 0 ≤ t := ht.1
  have hT0 : 0 ≤ B.T := le_trans ht.1 ht.2
  have hbeta0 : 0 ≤ beta := by
    simpa [beta] using towerBeta_nonneg B.hc B.hα m
  have hbarTop0 : 0 ≤ barTop := by
    simpa [barTop] using towerBarTop_nonneg B.hc B.α m
  have hKt : t * B.K ≤ B.α := by
    have htT : t ≤ B.T := ht.2
    have htle : t ≤ B.α / B.K := htT.trans B.hTK
    calc
      t * B.K ≤ (B.α / B.K) * B.K :=
        mul_le_mul_of_nonneg_right htle (le_of_lt B.hK)
      _ = B.α := div_mul_cancel₀ B.α (ne_of_gt B.hK)
  have herr_le (k : Nat) (hk : k ≤ m) :
      eps * cutErrCoeff k * t ≤ (1 / 2 : Real) := by
    have hck : cutErrCoeff k ≤ cutErrCoeff m := cutErrCoeff_mono hk
    have hprod : 2 * eps * t * cutErrCoeff k ≤
        2 * eps * B.T * cutErrCoeff m := by
      have htprod : eps * t ≤ eps * B.T :=
        mul_le_mul_of_nonneg_left ht.2 he0
      have hleft0 : 0 ≤ 2 * eps * t := by positivity
      have hmid0 : 0 ≤ 2 * eps * B.T := by positivity
      calc
        2 * eps * t * cutErrCoeff k ≤
            2 * eps * t * cutErrCoeff m :=
          mul_le_mul_of_nonneg_left hck hleft0
        _ ≤ 2 * eps * B.T * cutErrCoeff m :=
          mul_le_mul_of_nonneg_right (by linarith) (cutErrCoeff_nonneg m)
    nlinarith [hprod.trans hsmall]
  have hmid : ∀ k ∈ Finset.Ico 1 m,
      BernsteinTower.Gcoef (I := I) B m k *
            ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) +
          BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
            t ^ k * q ^ k * B.w k t x -
          (3 / 2 : Real) * beta * towerFactCoeff m (k - 1) *
            t ^ (k - 1) * q ^ k * B.w k t x ≤ 0 := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkm : k < m := hk.2
    have hkle : k ≤ m := hkm.le
    have hGk : BernsteinTower.Gcoef (I := I) B m k =
        beta * towerFactCoeff m k := by
      rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ k = m)]
    have hfac : (k : Real) * towerFactCoeff m k =
        towerFactCoeff m (k - 1) :=
      nat_mul_towerFactCoeff m hk1
    have hG0 : 0 ≤ BernsteinTower.Gcoef (I := I) B m k :=
      BernsteinTower.Gcoef_nonneg (I := I) B m k
    have hw0 : 0 ≤ B.w k t x := B.hw_nonneg k t ht x
    have hz0 : 0 ≤ t ^ (k - 1) * q ^ k * B.w k t x := by positivity
    have hqpow : q ^ (k + 1) ≤ q ^ k := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hq0 k) hq1
    have htime :
        BernsteinTower.Gcoef (I := I) B m k *
            ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) ≤
          beta * towerFactCoeff m (k - 1) *
            (t ^ (k - 1) * q ^ k * B.w k t x) := by
      rw [hGk]
      have hpowmul : t ^ (k - 1) * q ^ (k + 1) * B.w k t x ≤
          t ^ (k - 1) * q ^ k * B.w k t x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqpow (pow_nonneg ht0 (k - 1))) hw0
      calc
        beta * towerFactCoeff m k *
              ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) =
            (beta * ((k : Real) * towerFactCoeff m k)) *
              (t ^ (k - 1) * q ^ (k + 1) * B.w k t x) := by ring
        _ = (beta * towerFactCoeff m (k - 1)) *
              (t ^ (k - 1) * q ^ (k + 1) * B.w k t x) := by rw [hfac]
        _ ≤ (beta * towerFactCoeff m (k - 1)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) :=
          mul_le_mul_of_nonneg_left hpowmul
            (mul_nonneg hbeta0 (towerFactCoeff_nonneg _ _))
    have hGprev : BernsteinTower.Gcoef (I := I) B m k ≤
        beta * towerFactCoeff m (k - 1) := by
      rw [hGk, ← hfac]
      have hfact0 : 0 ≤ towerFactCoeff m k := towerFactCoeff_nonneg _ _
      apply mul_le_mul_of_nonneg_left _ hbeta0
      calc
        towerFactCoeff m k = 1 * towerFactCoeff m k := by ring
        _ ≤ (k : Real) * towerFactCoeff m k :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hfact0
    have herr :
        BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
              t ^ k * q ^ k * B.w k t x ≤
          (1 / 2 : Real) * (beta * towerFactCoeff m (k - 1)) *
            (t ^ (k - 1) * q ^ k * B.w k t x) := by
      have htk : t ^ k = t * t ^ (k - 1) := by
        calc
          t ^ k = t ^ ((k - 1) + 1) := by
            congr 1
            omega
          _ = t * t ^ (k - 1) := pow_succ' t (k - 1)
      rw [htk]
      have he : eps * cutErrCoeff k * t ≤ (1 / 2 : Real) :=
        herr_le k hkle
      calc
        BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
              (t * t ^ (k - 1)) * q ^ k * B.w k t x =
            (BernsteinTower.Gcoef (I := I) B m k *
              (eps * cutErrCoeff k * t)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by ring
        _ ≤ (BernsteinTower.Gcoef (I := I) B m k * (1 / 2 : Real)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he hG0) hz0
        _ ≤ ((beta * towerFactCoeff m (k - 1)) * (1 / 2 : Real)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGprev (by norm_num)) hz0
        _ = (1 / 2 : Real) * (beta * towerFactCoeff m (k - 1)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by ring
    linarith
  have hmidsum :
      (∑ k ∈ Finset.Ico 1 m, (
        BernsteinTower.Gcoef (I := I) B m k *
              ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) +
            BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
              t ^ k * q ^ k * B.w k t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (k - 1) *
              t ^ (k - 1) * q ^ k * B.w k t x)) ≤ 0 :=
    Finset.sum_nonpos hmid
  have hGm : BernsteinTower.Gcoef (I := I) B m m = 1 := by
    rw [BernsteinTower.Gcoef]
    simp
  have hfactm : towerFactCoeff m (m - 1) = 1 := by
    rw [towerFactCoeff]
    rw [div_self (by exact_mod_cast (Nat.factorial_pos (m - 1)).ne')]
  have hwm0 : 0 ≤ B.w m t x := B.hw_nonneg m t ht x
  have hz0 : 0 ≤ t ^ (m - 1) * q ^ m * B.w m t x := by positivity
  have hqpow : q ^ (m + 1) ≤ q ^ m := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hq0 m) hq1
  have htimeTop :
      (m : Real) * t ^ (m - 1) * q ^ (m + 1) * B.w m t x ≤
        (m : Real) * (t ^ (m - 1) * q ^ m * B.w m t x) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqpow (pow_nonneg ht0 (m - 1))) hwm0)
      (Nat.cast_nonneg m)
  have herrTop :
      cutErrCoeff m * eps * t ^ m * q ^ m * B.w m t x ≤
        (1 / 2 : Real) * (t ^ (m - 1) * q ^ m * B.w m t x) := by
    have htm : t ^ m = t * t ^ (m - 1) := by
      calc
        t ^ m = t ^ ((m - 1) + 1) := by
          congr 1
          omega
        _ = t * t ^ (m - 1) := pow_succ' t (m - 1)
    rw [htm]
    have he : eps * cutErrCoeff m * t ≤ (1 / 2 : Real) :=
      herr_le m le_rfl
    calc
      cutErrCoeff m * eps * (t * t ^ (m - 1)) * q ^ m * B.w m t x =
          (eps * cutErrCoeff m * t) *
            (t ^ (m - 1) * q ^ m * B.w m t x) := by ring
      _ ≤ (1 / 2 : Real) * (t ^ (m - 1) * q ^ m * B.w m t x) :=
        mul_le_mul_of_nonneg_right he hz0
  have hreactTop :
      barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) ≤
        (barTop * B.α) * (t ^ (m - 1) * q ^ m * B.w m t x) := by
    have htm : t ^ m = t * t ^ (m - 1) := by
      calc
        t ^ m = t ^ ((m - 1) + 1) := by
          congr 1
          omega
        _ = t * t ^ (m - 1) := pow_succ' t (m - 1)
    rw [htm]
    have hKtq : B.K * t * q ≤ B.α := by
      have hKt' : B.K * t ≤ B.α := by simpa [mul_comm] using hKt
      calc
        B.K * t * q ≤ B.K * t * 1 :=
          mul_le_mul_of_nonneg_left hq1 (mul_nonneg (le_of_lt B.hK) ht0)
        _ = B.K * t := by ring
        _ ≤ B.α := hKt'
    calc
      barTop * B.K * ((t * t ^ (m - 1)) * q ^ (m + 1) * B.w m t x) =
          (barTop * (B.K * t * q)) *
            (t ^ (m - 1) * q ^ m * B.w m t x) := by
        rw [pow_succ]
        ring
      _ ≤ (barTop * B.α) *
            (t ^ (m - 1) * q ^ m * B.w m t x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKtq hbarTop0) hz0
  have hbetaEq : beta = barTop * B.α + (m : Real) := by
    rw [hbeta, towerBeta, ← hbarTop]
  have htop :
      BernsteinTower.Gcoef (I := I) B m m *
              ((m : Real) * t ^ (m - 1) * q ^ (m + 1) * B.w m t x) +
            BernsteinTower.Gcoef (I := I) B m m * cutErrCoeff m * eps *
              t ^ m * q ^ m * B.w m t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (m - 1) *
              t ^ (m - 1) * q ^ m * B.w m t x +
            barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) ≤ 0 := by
    rw [hGm, hfactm, one_mul, one_mul]
    have hcoef :
        (m : Real) + (1 / 2 : Real) - (3 / 2 : Real) * beta +
            barTop * B.α ≤ 0 := by
      rw [hbetaEq]
      have hm1 : (1 : Real) ≤ (m : Real) := by exact_mod_cast hm
      nlinarith [hbarTop0, B.hα]
    nlinarith [htimeTop, herrTop, hreactTop, mul_nonpos_of_nonpos_of_nonneg hcoef hz0]
  linarith

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem cutWsum_nonpos
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    {m : Nat} (hm : 1 ≤ m) {t q eps : Real}
    (ht : t ∈ Set.Icc 0 B.T) (x : M)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (he0 : 0 ≤ eps)
    (hsmall : 2 * eps * B.T * cutErrCoeff m ≤ 1) :
    let beta := towerBeta B.c B.α (towerConst B.c B.α) m
    let barTop := towerBarTop B.c (towerConst B.c B.α) m
    (∑ k ∈ Finset.range (m + 1),
        BernsteinTower.Gcoef (I := I) B m k *
          ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x)) -
      (3 / 2 : Real) * beta *
        (∑ k ∈ Finset.range m,
          towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) +
      barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) +
      (∑ k ∈ Finset.range (m + 1),
        BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
          t ^ k * q ^ k * B.w k t x) ≤
        BernsteinTower.Gcoef (I := I) B m 0 * cutErrCoeff 0 * eps *
          B.w 0 t x := by
  classical
  dsimp only
  set beta : Real := towerBeta B.c B.α (towerConst B.c B.α) m with hbeta
  set barTop : Real := towerBarTop B.c (towerConst B.c B.α) m with hbarTop
  have hcore := cutWterms_nonpos (I := I) B hm ht x hq0 hq1 he0 hsmall
  dsimp only at hcore
  rw [← hbeta, ← hbarTop] at hcore
  let timeTerm : Nat → Real := fun k =>
    BernsteinTower.Gcoef (I := I) B m k *
      ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x)
  let errTerm : Nat → Real := fun k =>
    BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * eps *
      t ^ k * q ^ k * B.w k t x
  let negTerm : Nat → Real := fun k =>
    towerFactCoeff m (k - 1) * t ^ (k - 1) * q ^ k * B.w k t x
  have hcore' :
      (∑ k ∈ Finset.Ico 1 m, timeTerm k) +
          (∑ k ∈ Finset.Ico 1 m, errTerm k) -
          (3 / 2 : Real) * beta * (∑ k ∈ Finset.Ico 1 m, negTerm k) +
        (timeTerm m + errTerm m - (3 / 2 : Real) * beta * negTerm m +
          barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x)) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hcore
    simpa only [timeTerm, errTerm, negTerm, Finset.mul_sum, mul_assoc] using hcore
  have htime :
      (∑ k ∈ Finset.range (m + 1), timeTerm k) =
        (∑ k ∈ Finset.Ico 1 m, timeTerm k) + timeTerm m := by
    rw [BernsteinTower.sum_range_succ_split timeTerm hm]
    have hzero : timeTerm 0 = 0 := by simp [timeTerm]
    rw [hzero, zero_add]
  have herr :
      (∑ k ∈ Finset.range (m + 1), errTerm k) =
        errTerm 0 + (∑ k ∈ Finset.Ico 1 m, errTerm k) + errTerm m :=
    BernsteinTower.sum_range_succ_split errTerm hm
  have hnegIcc :
      (∑ k ∈ Finset.range m,
        towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) =
        ∑ k ∈ Finset.Icc 1 m, negTerm k := by
    have hIcc : Finset.Ico 1 (m + 1) = Finset.Icc 1 m := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [← hIcc, Finset.sum_Ico_eq_sum_range]
    rw [show m + 1 - 1 = m by omega]
    apply Finset.sum_congr rfl
    intro k _
    simp only [negTerm]
    rw [show 1 + k - 1 = k by omega, show 1 + k = k + 1 by omega]
  have hmIcc : m ∈ Finset.Icc 1 m := by
    simp only [Finset.mem_Icc]
    omega
  have herase : (Finset.Icc 1 m).erase m = Finset.Ico 1 m := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hneg :
      (∑ k ∈ Finset.range m,
        towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) =
        (∑ k ∈ Finset.Ico 1 m, negTerm k) + negTerm m := by
    rw [hnegIcc, ← Finset.sum_erase_add _ _ hmIcc, herase]
  have herr0 : errTerm 0 =
      BernsteinTower.Gcoef (I := I) B m 0 * cutErrCoeff 0 * eps *
        B.w 0 t x := by
    simp [errTerm]
  rw [← herr0]
  change (∑ k ∈ Finset.range (m + 1), timeTerm k) -
      (3 / 2 : Real) * beta *
        (∑ k ∈ Finset.range m,
          towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) +
      barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) +
      (∑ k ∈ Finset.range (m + 1), errTerm k) ≤ errTerm 0
  rw [htime, herr, hneg]
  convert add_le_add_right hcore' (errTerm 0) using 1 <;> ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem supportLevel_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    {m i : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hi : i ≤ m)
    {eps t : Real} {chi : Real → M → Real} {x : M}
    (support : ShiCutoffLowerSupportAt (I := I) G B.T eps chi t x)
    (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (heps : 0 ≤ eps)
    (d : Real)
    (hd : HasDerivWithinAt (fun s : Real => B.w i s x) d (Set.Icc 0 B.T) t)
    (hheat : d - B.wLap i t x ≤
      -2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x) :
    parabolicOperatorWithDrift (I := I) G B.T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => BernsteinTower.Gcoef (I := I) B m i *
          (s ^ i * (support.phi s y) ^ (i + 1) * B.w i s y)) t x ≤
      BernsteinTower.Gcoef (I := I) B m i *
        ((support.phi t x) ^ (i + 1) *
            ((i : Real) * t ^ (i - 1) * B.w i t x +
              t ^ i * (-2 * B.w (i + 1) t x +
                towerReactionSum (M := M) B.w B.c i t x)) +
          (1 / 2 : Real) * t ^ i * (support.phi t x) ^ (i + 1) *
            B.w (i + 1) t x +
          cutErrCoeff i * eps * t ^ i * (support.phi t x) ^ i *
            B.w i t x) := by
  let qpow : Real → M → Real := fun s y => (support.phi s y) ^ (i + 1)
  let v : Real → M → Real := fun s y => s ^ i * B.w i s y
  have hq_time : DifferentiableWithinAt Real
      (fun s : Real => qpow s x) (Set.Icc 0 B.T) t := by
    simpa [qpow] using support.time_diff.pow (i + 1)
  have hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 B.T) t := by
    exact (((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).mul hd).differentiableWithinAt
  have hq_space : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (qpow t) y := by
    filter_upwards [support.space_diff_nhds] with y hy
    simpa [qpow] using hy.pow (i + 1)
  have hv_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y := by
    intro y
    have h := (B.hw_space i t ht htpos y).const_smul (t ^ i)
    simpa [v, smul_eq_mul] using h
  have hq_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (qpow t) z) x := by
    have hrhs :
        MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
          (((i + 1 : Nat) : Real) * support.phi t y ^ i) •
            gradientFun (I := I) (G.metric t) (support.phi t) y) x :=
      (((support.space_diff_nhds.self_of_nhds.pow i).const_smul
        (((i + 1 : Nat) : Real))).smul_section support.grad_diff)
    refine hrhs.congr_of_eventuallyEq ?_
    filter_upwards [support.space_diff_nhds] with y hy
    exact congrArg (fun b =>
      (⟨y, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (gradientFun_pow (I := I) (G.metric t) i hy)
  have hv_grad : ∀ y : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (v t) z) y := by
    intro y
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t) (v t) z) =
          (t ^ i • fun z : M =>
            gradientFun (I := I) (G.metric t) (B.w i t) z) := by
      funext z
      rw [show v t = t ^ i • B.w i t by
        funext w
        simp [v, smul_eq_mul]]
      exact gradientFun_const_smul (I := I) (G.metric t) (t ^ i)
        (B.hw_space i t ht htpos z)
    have hsection :
        (T% fun z : M => gradientFun (I := I) (G.metric t) (v t) z) =
          (T% (t ^ i • fun z : M =>
            gradientFun (I := I) (G.metric t) (B.w i t) z)) := by
      funext z
      simpa using congrFun hplain z
    rw [hsection]
    exact (B.hw_grad i t ht htpos y).smul_const_section (a := t ^ i)
  have hprod_grad :
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t)
          (fun w : M => qpow t w * v t w) z) x := by
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t)
          (fun w : M => qpow t w * v t w) z) =ᶠ[𝓝 x]
        (fun z : M => qpow t z •
            gradientFun (I := I) (G.metric t) (v t) z +
          v t z • gradientFun (I := I) (G.metric t) (qpow t) z) := by
      filter_upwards [hq_space] with z hqz
      exact gradientFun_mul (I := I) (G.metric t) hqz (hv_space z)
    have hrhs := mdifferentiableAt_add_section
      (hq_space.self_of_nhds.smul_section (hv_grad x))
      ((hv_space x).smul_section hq_grad)
    exact hrhs.congr_of_eventuallyEq (by
      filter_upwards [hplain] with z hz
      exact congrArg (fun b =>
        (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) hz)
  have hv_parabolic :
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y => (0 : TangentSpace I y)) v t x =
        (i : Real) * t ^ (i - 1) * B.w i t x +
          t ^ i * (d - B.wLap i t x) := by
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) t :=
      (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt ht
    have htime : derivWithin (fun s : Real => v s x) (Set.Icc 0 B.T) t =
        (i : Real) * t ^ (i - 1) * B.w i t x + t ^ i * d := by
      simpa [v] using
        (((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).mul hd).derivWithin huniq
    have hheat : heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) (v t) x =
        t ^ i * B.wLap i t x := by
      have hscale := heatOperatorWithDrift_const_smul
        (I := I) G t (fun y : M => (0 : TangentSpace I y)) (t ^ i)
        (B.hw_space i t ht htpos) (B.hw_grad i t ht htpos x)
      rw [show v t = t ^ i • B.w i t by
        funext y
        simp [v, smul_eq_mul]]
      rw [hscale, B.hLap i t ht htpos x]
    rw [parabolicOperatorWithDrift_eq, htime, hheat]
    ring
  have hv_gradient : gradientAt (I := I) G t (v t) x =
      t ^ i • gradientAt (I := I) G t (B.w i t) x := by
    unfold gradientAt
    rw [show v t = t ^ i • B.w i t by
      funext y
      simp [v, smul_eq_mul]]
    exact gradientFun_const_smul (I := I) (G.metric t) (t ^ i)
      (B.hw_space i t ht htpos x)
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) t :=
    (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt ht
  have hmul := parabolic_mul_nhds (I := I) B.T
    (fun _ y => (0 : TangentSpace I y)) qpow v t x
    hq_time hv_time hq_space (Filter.Eventually.of_forall hv_space)
    hq_grad (hv_grad x)
  have hscale := parabolic_smul_nhds (I := I) B.T
    (fun _ y => (0 : TangentSpace I y))
    (BernsteinTower.Gcoef (I := I) B m i)
    (fun s y => qpow s y * v s y) t x
    (hq_time.mul hv_time)
    (by
      filter_upwards [hq_space] with y hy
      exact hy.mul (hv_space y))
    hprod_grad huniq
  have hq_bound := support_pow_para (I := I) support ht i
  have hcross := support_pow_cross (I := I) B (m := m) (k := i) (p := i)
    hgrad hi support ht htpos heps
  have hcoef0 : 0 ≤ BernsteinTower.Gcoef (I := I) B m i :=
    BernsteinTower.Gcoef_nonneg (I := I) B m i
  have hti0 : 0 ≤ t ^ i := pow_nonneg ht.1 i
  have hwi0 : 0 ≤ B.w i t x := B.hw_nonneg i t ht x
  have hq_term :
      v t x * parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y => (0 : TangentSpace I y)) qpow t x ≤
        (((i + 1 : Nat) : Real) * eps) *
          t ^ i * (support.phi t x) ^ i * B.w i t x := by
    have hmult := mul_le_mul_of_nonneg_left hq_bound
      (mul_nonneg hti0 hwi0)
    dsimp [qpow, v]
    convert hmult using 1
    ring
  have hcross_term :
      -2 * (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (v t) x) ≤
        (1 / 2 : Real) * t ^ i * (support.phi t x) ^ (i + 1) *
            B.w (i + 1) t x +
          8 * (((i + 1 : Nat) : Real) ^ 2) * eps * t ^ i *
            (support.phi t x) ^ i * B.w i t x := by
    rw [hv_gradient]
    simp only [map_smul, smul_eq_mul]
    have hmult := mul_le_mul_of_nonneg_left hcross hti0
    dsimp [qpow]
    unfold gradientAt
    convert hmult using 1 <;> ring
  rw [show (fun s y => BernsteinTower.Gcoef (I := I) B m i *
        (s ^ i * (support.phi s y) ^ (i + 1) * B.w i s y)) =
      (fun s y => BernsteinTower.Gcoef (I := I) B m i *
        (qpow s y * v s y)) by
      funext s y
      dsimp [qpow, v]
      ring]
  rw [hscale, hmul, hv_parabolic]
  have hheat_mul :
      (support.phi t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (d - B.wLap i t x)) ≤
        (support.phi t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (-2 * B.w (i + 1) t x +
              towerReactionSum (M := M) B.w B.c i t x)) := by
    apply mul_le_mul_of_nonneg_left _
      (pow_nonneg
        (support.lower_nhds.self_of_nhdsWithin
          (show (t, x) ∈ spacetimeSlab (M := M) B.T from
            ⟨ht, Set.mem_univ x⟩)).1 (i + 1))
    linarith [mul_le_mul_of_nonneg_left hheat hti0]
  apply mul_le_mul_of_nonneg_left _ hcoef0
  calc
    qpow t x *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (d - B.wLap i t x)) +
        v t x * parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y => (0 : TangentSpace I y)) qpow t x -
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (v t) x) ≤
      (support.phi t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (d - B.wLap i t x)) +
        (((i + 1 : Nat) : Real) * eps) * t ^ i *
          (support.phi t x) ^ i * B.w i t x +
        ((1 / 2 : Real) * t ^ i * (support.phi t x) ^ (i + 1) *
            B.w (i + 1) t x +
          8 * (((i + 1 : Nat) : Real) ^ 2) * eps * t ^ i *
            (support.phi t x) ^ i * B.w i t x) := by
      dsimp [qpow, v]
      linarith
    _ ≤ (support.phi t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (-2 * B.w (i + 1) t x +
              towerReactionSum (M := M) B.w B.c i t x)) +
        (1 / 2 : Real) * t ^ i * (support.phi t x) ^ (i + 1) *
          B.w (i + 1) t x +
        cutErrCoeff i * eps * t ^ i * (support.phi t x) ^ i *
          B.w i t x := by
      rw [cutErrCoeff]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [hheat_mul]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem cutLevel_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n i : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hi : i ≤ m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M)
    (d : Real)
    (hd : HasDerivWithinAt (fun s : Real => B.w i s x) d (Set.Icc 0 B.T) t)
    (hheat : d - B.wLap i t x ≤
      -2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x) :
    parabolicOperatorWithDrift (I := I) G B.T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => BernsteinTower.Gcoef (I := I) B m i *
          (s ^ i * cut.chi n s y ^ (i + 1) * B.w i s y)) t x ≤
      BernsteinTower.Gcoef (I := I) B m i *
        (cut.chi n t x ^ (i + 1) *
            ((i : Real) * t ^ (i - 1) * B.w i t x +
              t ^ i * (-2 * B.w (i + 1) t x +
                towerReactionSum (M := M) B.w B.c i t x)) +
          (1 / 2 : Real) * t ^ i * cut.chi n t x ^ (i + 1) *
            B.w (i + 1) t x +
          cutErrCoeff i * cut.err n * t ^ i * cut.chi n t x ^ i *
            B.w i t x) := by
  let support : ShiCutoffLowerSupportAt
      (I := I) G B.T (cut.err n) (cut.chi n) t x :=
    { phi := cut.chi n
      eq_at := rfl
      lower_nhds := by
        filter_upwards [self_mem_nhdsWithin] with p hp
        exact ⟨(cut.range n p.1 p.2 hp.1).1, le_rfl⟩
      time_diff := cut.time_diff n t ht htpos x
      space_diff_nhds := Filter.Eventually.of_forall fun y => cut.space_diff ht y
      grad_diff := cut.grad_diff ht x
      grad_sq_le := cut.grad_sq_le n t ht htpos x
      parabolic_le := cut.parabolic_le n t ht htpos x }
  exact supportLevel_le (I := I) B hgrad hi support ht htpos
    (cut.err_nonneg n) d hd hheat

omit [NeZero (Module.finrank Real E)] in
private theorem GfunSupport_parabolic_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    {m : Nat} (hm : 1 ≤ m)
    (hgrad : TowerNormGradUpTo (I := I) B m)
    {eps t : Real} {chi : Real → M → Real} {x : M}
    (support : ShiCutoffLowerSupportAt (I := I) G B.T eps chi t x)
    (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t)
    (hchi : chi t x ∈ Set.Icc (0 : Real) 1) (heps : 0 ≤ eps)
    (hIH : ∀ j, j < m →
      t ^ j * B.w j t x ≤ (towerConst B.c B.α j) ^ 2 * B.K ^ 2)
    (hsmall : 2 * eps * B.T * cutErrCoeff m ≤ 1) :
    let F := GfunLocal (I := I) B support.phi m
    DifferentiableWithinAt Real (fun s => F s x) (Set.Icc 0 B.T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (F t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (F t) y) x ∧
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) F t x ≤
        (towerBarTop B.c (towerConst B.c B.α) m +
          towerBeta B.c B.α (towerConst B.c B.α) m *
            ∑ i ∈ Finset.range m,
              towerFactCoeff m i *
                towerBarGood B.c (towerConst B.c B.α) i) * B.K ^ 3 +
        9 * eps * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := by
  classical
  dsimp only
  set q : Real := support.phi t x with hq
  set C : Nat → Real := towerConst B.c B.α with hC
  set beta : Real := towerBeta B.c B.α C m with hbeta
  set barTop : Real := towerBarTop B.c C m with hbarTop
  have hq0 : 0 ≤ q := by simpa only [hq, support.eq_at] using hchi.1
  have hq1 : q ≤ 1 := by simpa only [hq, support.eq_at] using hchi.2
  have hqpow_le : ∀ k : Nat, q ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        calc
          q ^ k * q ≤ q ^ k * 1 :=
            mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 k)
          _ = q ^ k := mul_one _
          _ ≤ 1 := ih
  have hbeta0 : 0 ≤ beta := by
    simpa only [hbeta, hC] using towerBeta_nonneg B.hc B.hα m
  have hbarTop0 : 0 ≤ barTop := by
    simpa only [hbarTop, hC] using towerBarTop_nonneg B.hc B.α m
  let tau : RealTimeInterval.RegularTime B.D :=
    ⟨t, B.hregular t ht htpos⟩
  set dvec : Nat → Real := fun i ↦ Classical.choose (B.hheat i tau x) with hdvec
  have hspec : ∀ i : Nat,
      HasDerivWithinAt (fun r : Real ↦ B.w i r x) (dvec i) B.D.carrier t ∧
      dvec i ≤ B.wLap i t x +
        (-2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x) := by
    intro i
    have h := Classical.choose_spec (B.hheat i tau x)
    simpa only [hdvec, tau] using h
  have hd : ∀ i : Nat,
      HasDerivWithinAt (fun r : Real ↦ B.w i r x) (dvec i) (Set.Icc 0 B.T) t :=
    fun i ↦ (hspec i).1.mono B.hslab
  let term : Nat → Real → M → Real := fun i s y ↦
    (BernsteinTower.Gcoef (I := I) B m i * s ^ i) *
      (support.phi s y ^ (i + 1) * B.w i s y)
  have htime : ∀ i ∈ Finset.range (m + 1),
      DifferentiableWithinAt Real (fun s : Real ↦ term i s x) (Set.Icc 0 B.T) t := by
    intro i _
    have hprod :=
      ((((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).differentiableWithinAt.mul
        (support.time_diff.pow (i + 1))).mul
          (hd i).differentiableWithinAt)
    simpa only [term, mul_assoc] using
      hprod.const_mul (BernsteinTower.Gcoef (I := I) B m i)
  have hspace : ∀ i ∈ Finset.range (m + 1), ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (term i t) y := by
    intro i _
    filter_upwards [support.space_diff_nhds] with y hy
    have hprod := (hy.pow (i + 1)).mul (B.hw_space i t ht htpos y)
    rw [show term i t =
        (BernsteinTower.Gcoef (I := I) B m i * t ^ i) •
          (fun z : M => support.phi t z ^ (i + 1) * B.w i t z) by
      funext z
      simp only [term, Pi.smul_apply, smul_eq_mul]]
    exact hprod.const_smul (BernsteinTower.Gcoef (I := I) B m i * t ^ i)
  have hgradTerm : ∀ i ∈ Finset.range (m + 1),
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
        gradientFun (I := I) (G.metric t) (term i t) z) x := by
    intro i _
    let qpow : M → Real := fun z ↦ support.phi t z ^ (i + 1)
    let wi : M → Real := B.w i t
    have hq_space : ∀ᶠ z in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) qpow z := by
      filter_upwards [support.space_diff_nhds] with z hz
      simpa only [qpow] using hz.pow (i + 1)
    have hw_space : ∀ z : M, MDifferentiableAt I 𝓘(Real, Real) wi z := by
      intro z
      simpa only [wi] using B.hw_space i t ht htpos z
    have hq_grad :
        MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun w : M ↦
        gradientFun (I := I) (G.metric t) qpow w) x := by
      have hrhs := (((support.space_diff_nhds.self_of_nhds.pow i).const_smul
        (((i + 1 : Nat) : Real))).smul_section support.grad_diff)
      refine hrhs.congr_of_eventuallyEq ?_
      filter_upwards [support.space_diff_nhds] with z hz
      exact congrArg (fun b =>
        (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        (gradientFun_pow (I := I) (G.metric t) i hz)
    have hw_grad :
        MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun w : M ↦
        gradientFun (I := I) (G.metric t) wi w) x := by
      simpa only [wi] using B.hw_grad i t ht htpos x
    have hprod_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
        gradientFun (I := I) (G.metric t) (fun w ↦ qpow w * wi w) z) x := by
      have hplain :
          (fun z : M ↦ gradientFun (I := I) (G.metric t)
            (fun w ↦ qpow w * wi w) z) =ᶠ[𝓝 x]
            (fun z : M ↦ qpow z • gradientFun (I := I) (G.metric t) wi z +
              wi z • gradientFun (I := I) (G.metric t) qpow z) := by
        filter_upwards [hq_space] with z hz
        exact gradientFun_mul (I := I) (G.metric t) hz (hw_space z)
      exact (mdifferentiableAt_add_section
        (hq_space.self_of_nhds.smul_section hw_grad)
        ((hw_space x).smul_section hq_grad)).congr_of_eventuallyEq (by
          filter_upwards [hplain] with z hz
          exact congrArg (fun b =>
            (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) hz)
    let hcoef : Real := BernsteinTower.Gcoef (I := I) B m i * t ^ i
    have hscaled := hprod_grad.smul_const_section (a := hcoef)
    rw [show term i t =
        hcoef • (fun z : M => qpow z * wi z) by
      funext z
      simp only [term, hcoef, qpow, wi, Pi.smul_apply, smul_eq_mul]]
    refine hscaled.congr_of_eventuallyEq ?_
    filter_upwards [hq_space] with z hz
    exact congrArg (fun b =>
      (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (by
        exact gradientFun_const_smul (I := I) (G.metric t) hcoef
          (hz.mul (hw_space z)))
  have hF :
      GfunLocal (I := I) B support.phi m =
        (fun s y ↦ ∑ i ∈ Finset.range (m + 1), term i s y) := by
    funext s y
    rw [GfunLocal]
    apply Finset.sum_congr rfl
    intro i _
    simp only [term]
    ring
  have hsum :
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y))
          (GfunLocal (I := I) B support.phi m) t x =
        ∑ i ∈ Finset.range (m + 1),
          parabolicOperatorWithDrift (I := I) G B.T
            (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x := by
    rw [hF]
    exact parabolic_sum_nhds (I := I) (Finset.range (m + 1)) B.T
      (fun _ y ↦ (0 : TangentSpace I y)) term t x htime hspace hgradTerm
  have hreg := sum_reg_nhds (I := I) (G := G)
    (Finset.range (m + 1)) term B.T t x htime hspace hgradTerm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF]
    exact hreg.1
  · rw [hF]
    exact hreg.2.1
  · rw [hF]
    exact hreg.2.2
  have hlevel : ∀ i ∈ Finset.range (m + 1),
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x ≤
        BernsteinTower.Gcoef (I := I) B m i *
          (q ^ (i + 1) *
              ((i : Real) * t ^ (i - 1) * B.w i t x +
                t ^ i * (-2 * B.w (i + 1) t x +
                  towerReactionSum (M := M) B.w B.c i t x)) +
            (1 / 2 : Real) * t ^ i * q ^ (i + 1) * B.w (i + 1) t x +
            cutErrCoeff i * eps * t ^ i * q ^ i * B.w i t x) := by
    intro i hi
    have him : i ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
    have hheat : dvec i - B.wLap i t x ≤
        -2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x := by
      linarith [(hspec i).2]
    rw [show term i =
        (fun s y => BernsteinTower.Gcoef (I := I) B m i *
          (s ^ i * support.phi s y ^ (i + 1) * B.w i s y)) by
      funext s y
      simp only [term]
      ring]
    simpa only [hq] using supportLevel_le (I := I) B hgrad him support
      ht htpos heps (dvec i) (hd i) hheat
  let timeTerm : Nat → Real := fun i ↦
    BernsteinTower.Gcoef (I := I) B m i *
      ((i : Real) * t ^ (i - 1) * q ^ (i + 1) * B.w i t x)
  let negTerm : Nat → Real := fun i ↦
    (3 / 2 : Real) * beta * towerFactCoeff m i * t ^ i * q ^ (i + 1) *
      B.w (i + 1) t x
  let errTerm : Nat → Real := fun i ↦
    BernsteinTower.Gcoef (I := I) B m i * cutErrCoeff i * eps *
      t ^ i * q ^ i * B.w i t x
  let forceTerm : Nat → Real := fun i ↦
    beta * towerFactCoeff m i * towerBarGood B.c C i * B.K ^ 3
  let lowerBound : Nat → Real := fun i ↦
    timeTerm i - negTerm i + errTerm i + forceTerm i
  let topNeg : Real := (3 / 2 : Real) * t ^ m * q ^ (m + 1) * B.w (m + 1) t x
  let topSpace : Real := barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x)
  let topBound : Real :=
    timeTerm m - topNeg + topSpace + barTop * B.K ^ 3 + errTerm m
  have hlower : ∀ i ∈ Finset.range m,
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x ≤ lowerBound i := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hGi : BernsteinTower.Gcoef (I := I) B m i =
        beta * towerFactCoeff m i := by
      rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ i = m), hbeta, hC]
    have hR := BernsteinTower.tpow_mul_reactionSum_le (I := I) B i htpos
      (fun j hj ↦ hIH j (lt_of_le_of_lt hj him))
    rw [← hC] at hR
    have hforce0 : 0 ≤ towerBarGood B.c C i * B.K ^ 3 :=
      mul_nonneg (by simpa only [hC] using towerBarGood_nonneg B.hc B.α i)
        (pow_nonneg (le_of_lt B.hK) 3)
    have hRq : q ^ (i + 1) *
        (t ^ i * towerReactionSum (M := M) B.w B.c i t x) ≤
          towerBarGood B.c C i * B.K ^ 3 := by
      calc
        q ^ (i + 1) * (t ^ i * towerReactionSum (M := M) B.w B.c i t x) ≤
            q ^ (i + 1) * (towerBarGood B.c C i * B.K ^ 3) :=
          mul_le_mul_of_nonneg_left hR (pow_nonneg hq0 (i + 1))
        _ ≤ 1 * (towerBarGood B.c C i * B.K ^ 3) :=
          mul_le_mul_of_nonneg_right (hqpow_le (i + 1)) hforce0
        _ = towerBarGood B.c C i * B.K ^ 3 := one_mul _
    have hcoef0 : 0 ≤ beta * towerFactCoeff m i :=
      mul_nonneg hbeta0 (towerFactCoeff_nonneg _ _)
    have hRqcoef := mul_le_mul_of_nonneg_left hRq hcoef0
    have hraw := hlevel i (Finset.mem_range.mpr (lt_trans him (Nat.lt_succ_self m)))
    rw [hGi] at hraw
    dsimp only [lowerBound, timeTerm, negTerm, errTerm, forceTerm]
    rw [hGi]
    nlinarith [hRqcoef]
  have htop :
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term m) t x ≤ topBound := by
    have hGm : BernsteinTower.Gcoef (I := I) B m m = 1 := by
      rw [BernsteinTower.Gcoef]
      simp
    have hreact := BernsteinTower.reactionSum_top_le (I := I) B hm htpos ht hIH
    rw [← hC, ← hbarTop] at hreact
    have htm0 : 0 ≤ t ^ m := pow_nonneg ht.1 m
    have htmne : t ^ m ≠ 0 := ne_of_gt (pow_pos htpos m)
    have htmR :
        t ^ m * towerReactionSum (M := M) B.w B.c m t x ≤
          barTop * B.K * (t ^ m * B.w m t x) + barTop * B.K ^ 3 := by
      calc
        t ^ m * towerReactionSum (M := M) B.w B.c m t x ≤
            t ^ m * (barTop * B.K * (B.w m t x + B.K ^ 2 / t ^ m)) :=
          mul_le_mul_of_nonneg_left hreact htm0
        _ = barTop * B.K * (t ^ m * B.w m t x) + barTop * B.K ^ 3 := by
          field_simp
    have htopForce0 : 0 ≤ barTop * B.K ^ 3 :=
      mul_nonneg hbarTop0 (pow_nonneg (le_of_lt B.hK) 3)
    have hRq : q ^ (m + 1) *
        (t ^ m * towerReactionSum (M := M) B.w B.c m t x) ≤
          topSpace + barTop * B.K ^ 3 := by
      calc
        q ^ (m + 1) * (t ^ m * towerReactionSum (M := M) B.w B.c m t x) ≤
            q ^ (m + 1) *
              (barTop * B.K * (t ^ m * B.w m t x) + barTop * B.K ^ 3) :=
          mul_le_mul_of_nonneg_left htmR (pow_nonneg hq0 (m + 1))
        _ = topSpace + q ^ (m + 1) * (barTop * B.K ^ 3) := by
          dsimp only [topSpace]
          ring
        _ ≤ topSpace + 1 * (barTop * B.K ^ 3) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right (hqpow_le (m + 1)) htopForce0) topSpace
        _ = topSpace + barTop * B.K ^ 3 := by ring
    have hraw := hlevel m (Finset.mem_range.mpr (Nat.lt_succ_self m))
    rw [hGm] at hraw
    dsimp only [topBound, timeTerm, topNeg, topSpace, errTerm]
    rw [hGm]
    nlinarith [hRq]
  have hsumBound :
      (∑ i ∈ Finset.range (m + 1),
        parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x) ≤
        (∑ i ∈ Finset.range m, lowerBound i) + topBound := by
    rw [Finset.sum_range_succ]
    exact add_le_add (Finset.sum_le_sum hlower) htop
  have hW := cutWsum_nonpos (I := I) B hm ht x hq0 hq1 heps hsmall
  dsimp only at hW
  rw [← hbeta, ← hbarTop] at hW
  rw [Finset.mul_sum] at hW
  have hW' : (∑ i ∈ Finset.range (m + 1), timeTerm i) -
      (∑ i ∈ Finset.range m, negTerm i) + topSpace +
      (∑ i ∈ Finset.range (m + 1), errTerm i) ≤ errTerm 0 := by
    simpa only [timeTerm, negTerm, topSpace, errTerm, Nat.cast_zero, zero_mul,
      pow_zero, one_mul, mul_assoc] using hW
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hW'
  have hforceSum :
      (∑ i ∈ Finset.range m, forceTerm i) =
        beta * (∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3 := by
    dsimp only [forceTerm]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlowerSum :
      (∑ i ∈ Finset.range m, lowerBound i) =
        (∑ i ∈ Finset.range m, timeTerm i) -
          (∑ i ∈ Finset.range m, negTerm i) +
          (∑ i ∈ Finset.range m, errTerm i) +
          (∑ i ∈ Finset.range m, forceTerm i) := by
    simp only [lowerBound, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have htopNeg0 : 0 ≤ topNeg := by
    dsimp only [topNeg]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht.1 m))
        (pow_nonneg hq0 (m + 1))) (B.hw_nonneg (m + 1) t ht x)
  have hassembled :
      (∑ i ∈ Finset.range m, lowerBound i) + topBound ≤
        errTerm 0 +
          (barTop + beta * (∑ i ∈ Finset.range m,
            towerFactCoeff m i * towerBarGood B.c C i)) * B.K ^ 3 := by
    rw [hlowerSum, hforceSum]
    dsimp only [topBound]
    nlinarith [hW', htopNeg0]
  have herr0 : errTerm 0 ≤
      9 * eps * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := by
    have hcoef0 : 0 ≤
        9 * eps * BernsteinTower.Gcoef (I := I) B m 0 := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) heps)
        (BernsteinTower.Gcoef_nonneg (I := I) B m 0)
    calc
      errTerm 0 =
          (9 * eps * BernsteinTower.Gcoef (I := I) B m 0) * B.w 0 t x := by
        simp only [errTerm, cutErrCoeff, Nat.cast_zero, zero_add, pow_zero]
        ring
      _ ≤ (9 * eps * BernsteinTower.Gcoef (I := I) B m 0) * B.K ^ 2 :=
        mul_le_mul_of_nonneg_left (B.hw0_bound t ht x) hcoef0
      _ = 9 * eps * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := rfl
  rw [hsum]
  linarith [hsumBound, hassembled, herr0]

omit [NeZero (Module.finrank Real E)] in
/-- The graded localized Bernstein polynomial satisfies the closed pointwise
parabolic recurrence.  All positive-level cutoff errors telescope into the
retained next-level dissipation; only the base curvature error remains. -/
theorem GfunCut_parabolic_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} (hm : 1 ≤ m)
    (hgrad : TowerNormGradUpTo (I := I) B m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M)
    (hIH : ∀ j, j < m →
      t ^ j * B.w j t x ≤ (towerConst B.c B.α j) ^ 2 * B.K ^ 2)
    (hsmall : 2 * cut.err n * B.T * cutErrCoeff m ≤ 1) :
    parabolicOperatorWithDrift (I := I) G B.T
        (fun _ y ↦ (0 : TangentSpace I y))
        (GfunCut (I := I) B cut m n) t x ≤
      (towerBarTop B.c (towerConst B.c B.α) m +
          towerBeta B.c B.α (towerConst B.c B.α) m *
            ∑ i ∈ Finset.range m,
              towerFactCoeff m i *
                towerBarGood B.c (towerConst B.c B.α) i) * B.K ^ 3 +
        9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := by
  let support : ShiCutoffLowerSupportAt
      (I := I) G B.T (cut.err n) (cut.chi n) t x :=
    { phi := cut.chi n
      eq_at := rfl
      lower_nhds := by
        filter_upwards [self_mem_nhdsWithin] with p hp
        exact ⟨(cut.range n p.1 p.2 hp.1).1, le_rfl⟩
      time_diff := cut.time_diff n t ht htpos x
      space_diff_nhds := Filter.Eventually.of_forall fun y => cut.space_diff ht y
      grad_diff := cut.grad_diff ht x
      grad_sq_le := cut.grad_sq_le n t ht htpos x
      parabolic_le := cut.parabolic_le n t ht htpos x }
  simpa only [GfunCut, GfunLocal] using
    (GfunSupport_parabolic_le (I := I) B hm hgrad support ht htpos
      (cut.range n t x ht) (cut.err_nonneg n) hIH hsmall).2.2.2

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem GfunCut_time_diff
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t)
    (x : M) :
    DifferentiableWithinAt Real
      (fun s : Real ↦ GfunCut (I := I) B cut m n s x)
      (Set.Icc 0 B.T) t := by
  classical
  let τ : RealTimeInterval.RegularTime B.D :=
    ⟨t, B.hregular t ht htpos⟩
  set dvec : Nat → Real := fun i ↦ Classical.choose (B.hheat i τ x) with hdvec
  have hd : ∀ i : Nat,
      HasDerivWithinAt (fun s : Real ↦ B.w i s x) (dvec i)
        (Set.Icc 0 B.T) t := by
    intro i
    have hi := (Classical.choose_spec (B.hheat i τ x)).1
    have hi' : HasDerivWithinAt (fun s : Real ↦ B.w i s x) (dvec i)
        B.D.carrier t := by
      simpa only [hdvec, τ] using hi
    exact hi'.mono B.hslab
  let term : Nat → Real → Real := fun i s ↦
    BernsteinTower.Gcoef (I := I) B m i * s ^ i *
      (cut.chi n s x) ^ (i + 1) * B.w i s x
  have hterm : ∀ i ∈ Finset.range (m + 1),
      DifferentiableWithinAt Real (term i) (Set.Icc 0 B.T) t := by
    intro i _
    have hprod :=
      ((((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).differentiableWithinAt.mul
        ((cut.time_diff n t ht htpos x).pow (i + 1))).mul
          (hd i).differentiableWithinAt)
    simpa only [term, mul_assoc] using
      hprod.const_mul (BernsteinTower.Gcoef (I := I) B m i)
  rw [show (fun s : Real ↦ GfunCut (I := I) B cut m n s x) =
      (fun s : Real ↦ ∑ i ∈ Finset.range (m + 1), term i s) by
    funext s
    rw [GfunCut]]
  exact DifferentiableWithinAt.fun_sum hterm

omit [NeZero (Module.finrank Real E)] in
private theorem GfunCut_space_diff
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (GfunCut (I := I) B cut m n t) x := by
  classical
  let f : Nat → M → Real := fun i y ↦
    (cut.chi n t y) ^ (i + 1) * B.w i t y
  let c : Nat → Real := fun i ↦
    BernsteinTower.Gcoef (I := I) B m i * t ^ i
  rw [show GfunCut (I := I) B cut m n t =
      (fun y : M ↦ ∑ i ∈ Finset.range (m + 1), c i * f i y) by
    funext y
    rw [GfunCut]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, f]
    ring]
  exact mdifferentiableAt_finset_sum_smul (I := I)
    (Finset.range (m + 1)) f c x (fun i _ ↦ by
      exact ((cut.space_diff (n := n) ht x).pow (i + 1)).mul
        (B.hw_space i t ht htpos x))

namespace BernsteinTower

omit [NeZero (Module.finrank Real E)] in
/-- **Fixed-order complete-noncompact Bernstein estimate from quantitative cutoffs.**

The cutoff family localizes the graded Bernstein polynomial to one compact
spatial set, while `TowerNormGradUpTo` through the requested order absorbs the
cutoff-gradient terms.  The cutoff index is internal: exhaustion recovers the
ordinary polynomial at the requested point and `err n → 0` removes the
remaining level-zero error. -/
theorem estimate_cutoff_at
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m : Nat)
    (hgrad : TowerNormGradUpTo (I := I) B m) :
    ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  revert hgrad
  induction m using Nat.strong_induction_on with
  | h m IH =>
    intro hgrad
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      intro t ht _ x
      simp only [pow_zero, one_mul, towerConst_zero, one_pow]
      exact B.hw0_bound t ht x
    · classical
      set C : Nat → Real := towerConst B.c B.α with hC
      set beta : Real := towerBeta B.c B.α C m with hbeta
      have hbeta0 : 0 ≤ beta := by
        simpa only [hbeta, hC] using towerBeta_nonneg B.hc B.hα m
      set barTop : Real := towerBarTop B.c C m with hbarTop
      have hbarTop0 : 0 ≤ barTop := by
        simpa only [hbarTop, hC] using towerBarTop_nonneg B.hc B.α m
      set aBar : Real := beta * (Nat.factorial (m - 1) : Real) * B.K ^ 2
        with haBar
      set bCore : Real :=
        (barTop + beta * ∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3
        with hbCore
      let bErr : Nat → Real := fun n ↦
        9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2
      let bBar : Nat → Real := fun n ↦ bCore + bErr n
      have haBar0 : 0 ≤ aBar := by
        rw [haBar]
        exact mul_nonneg
          (mul_nonneg hbeta0 (Nat.cast_nonneg (Nat.factorial (m - 1))))
          (pow_nonneg (le_of_lt B.hK) 2)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (towerFactCoeff_nonneg _ _)
          (by simpa only [hC] using towerBarGood_nonneg B.hc B.α i)
      have hbCore0 : 0 ≤ bCore := by
        rw [hbCore]
        exact mul_nonneg
          (add_nonneg hbarTop0 (mul_nonneg hbeta0 hsum0))
          (pow_nonneg (le_of_lt B.hK) 3)
      have hbErr0 : ∀ n, 0 ≤ bErr n := by
        intro n
        dsimp only [bErr]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (cut.err_nonneg n))
            (BernsteinTower.Gcoef_nonneg (I := I) B m 0))
          (pow_nonneg (le_of_lt B.hK) 2)
      have hbBar0 : ∀ n, 0 ≤ bBar n :=
        fun n ↦ add_nonneg hbCore0 (hbErr0 n)
      have htK_slab : ∀ s : Real, s ∈ Set.Icc 0 B.T → s * B.K ≤ B.α := by
        intro s hs
        have hsle : s ≤ B.α / B.K := le_trans hs.2 B.hTK
        calc
          s * B.K ≤ (B.α / B.K) * B.K :=
            mul_le_mul_of_nonneg_right hsle (le_of_lt B.hK)
          _ = B.α := div_mul_cancel₀ B.α (ne_of_gt B.hK)
      have hbound_cut : ∀ n : Nat,
          2 * cut.err n * B.T * cutErrCoeff m ≤ 1 →
          ∀ s : Real, s ∈ Set.Icc 0 B.T → ∀ y : M,
            GfunCut (I := I) B cut m n s y ≤ aBar + bBar n * s := by
        intro n hsmall
        let F : Real → M → Real := GfunCut (I := I) B cut m n
        let w : Real → M → Real := fun s y ↦ (aBar + bBar n * s) - F s y
        have hFtime : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            DifferentiableWithinAt Real (fun r : Real ↦ F r y)
              (Set.Icc 0 B.T) s := by
          intro s hs hspos y
          simpa only [F] using
            GfunCut_time_diff (I := I) B cut m n hs hspos y
        have hFspace : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I 𝓘(Real, Real) (F s) y := by
          intro s hs hspos y
          simpa only [F] using
            GfunCut_space_diff (I := I) B cut m n hs hspos y
        have hFgrad : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
              gradientFun (I := I) (G.metric s) (F s) z) y := by
          intro s hs hspos y
          let f : Nat → M → Real := fun i z ↦
            (cut.chi n s z) ^ (i + 1) * B.w i s z
          let c : Nat → Real := fun i ↦
            BernsteinTower.Gcoef (I := I) B m i * s ^ i
          have hf : ∀ i ∈ Finset.range (m + 1), ∀ z : M,
              MDifferentiableAt I 𝓘(Real, Real) (f i) z := by
            intro i _ z
            exact ((cut.space_diff (n := n) hs z).pow (i + 1)).mul
              (B.hw_space i s hs hspos z)
          have hgradf : ∀ i ∈ Finset.range (m + 1),
              MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
                gradientFun (I := I) (G.metric s) (f i) z) y := by
            intro i _
            let qpow : M → Real := fun z ↦ (cut.chi n s z) ^ (i + 1)
            let wi : M → Real := B.w i s
            have hq_space : ∀ z : M,
                MDifferentiableAt I 𝓘(Real, Real) qpow z := by
              intro z
              simpa only [qpow] using (cut.space_diff (n := n) hs z).pow (i + 1)
            have hw_space : ∀ z : M,
                MDifferentiableAt I 𝓘(Real, Real) wi z := by
              intro z
              simpa only [wi] using B.hw_space i s hs hspos z
            have hq_grad : ∀ z : M,
                MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun u : M ↦
                  gradientFun (I := I) (G.metric s) qpow u) z := by
              intro z
              exact gradientFun_mdiffAt (I := I) (G.metric s)
                ((cut.space_smooth n s hs).pow (i + 1)) z
            have hw_grad : ∀ z : M,
                MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun u : M ↦
                  gradientFun (I := I) (G.metric s) wi u) z := by
              intro z
              simpa only [wi] using B.hw_grad i s hs hspos z
            have hprod_grad :
                MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
                  gradientFun (I := I) (G.metric s)
                    (fun u ↦ qpow u * wi u) z) y := by
              have hplain :
                  (fun z : M ↦ gradientFun (I := I) (G.metric s)
                    (fun u ↦ qpow u * wi u) z) =
                    (fun z : M ↦
                      qpow z • gradientFun (I := I) (G.metric s) wi z +
                      wi z • gradientFun (I := I) (G.metric s) qpow z) := by
                funext z
                exact gradientFun_mul (I := I) (G.metric s)
                  (hq_space z) (hw_space z)
              rw [show (T% fun z : M ↦ gradientFun (I := I) (G.metric s)
                  (fun u ↦ qpow u * wi u) z) =
                  (T% fun z : M ↦
                    qpow z • gradientFun (I := I) (G.metric s) wi z +
                    wi z • gradientFun (I := I) (G.metric s) qpow z) by
                funext z
                simpa using congrFun hplain z]
              exact mdifferentiableAt_add_section
                ((hq_space y).smul_section (hw_grad y))
                ((hw_space y).smul_section (hq_grad y))
            simpa only [f, qpow, wi] using hprod_grad
          rw [show F s =
              (fun z : M ↦ ∑ i ∈ Finset.range (m + 1), c i * f i z) by
            funext z
            change GfunCut (I := I) B cut m n s z = _
            rw [GfunCut]
            apply Finset.sum_congr rfl
            intro i _
            simp only [c, f]
            ring]
          exact mdiffAt_gradientFun_finset_sum_smul (I := I)
            (Finset.range (m + 1)) G s f c y hf hgradf
        have hFcont : ContinuousOn (fun p : Real × M ↦ F p.1 p.2)
            (Set.Icc 0 B.T ×ˢ cut.support n) := by
          simpa only [F] using
            (GfunCut_cont (I := I) B cut m n).mono (fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩)
        have hinit : ∀ y : M, F 0 y ≤ aBar := by
          intro y
          have h0mem : (0 : Real) ∈ Set.Icc 0 B.T :=
            ⟨le_rfl, le_of_lt B.hT⟩
          have hF0 : F 0 y =
              BernsteinTower.Gcoef (I := I) B m 0 * cut.chi n 0 y * B.w 0 0 y := by
            change GfunCut (I := I) B cut m n 0 y = _
            rw [GfunCut]
            rw [Finset.sum_eq_single 0]
            · simp
            · intro i _ hi0
              rcases Nat.eq_zero_or_pos i with hi | hi
              · exact absurd hi hi0
              · simp [zero_pow (by omega : i ≠ 0)]
            · intro h
              simp at h
          have hGc0 : BernsteinTower.Gcoef (I := I) B m 0 =
              beta * (Nat.factorial (m - 1) : Real) := by
            rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ (0 : Nat) = m),
              towerFactCoeff]
            rw [Nat.factorial_zero, Nat.cast_one, div_one, ← hC, ← hbeta]
          have hchi := cut.range n 0 y h0mem
          have hw0 := B.hw_nonneg 0 0 h0mem y
          have hchi_w : cut.chi n 0 y * B.w 0 0 y ≤ B.K ^ 2 := by
            calc
              cut.chi n 0 y * B.w 0 0 y ≤ 1 * B.w 0 0 y :=
                mul_le_mul_of_nonneg_right hchi.2 hw0
              _ = B.w 0 0 y := one_mul _
              _ ≤ B.K ^ 2 := B.hw0_bound 0 h0mem y
          rw [hF0, hGc0, haBar]
          calc
            beta * (Nat.factorial (m - 1) : Real) * cut.chi n 0 y * B.w 0 0 y =
                (beta * (Nat.factorial (m - 1) : Real)) *
                  (cut.chi n 0 y * B.w 0 0 y) := by ring
            _ ≤ (beta * (Nat.factorial (m - 1) : Real)) * B.K ^ 2 :=
              mul_le_mul_of_nonneg_left hchi_w
                (mul_nonneg hbeta0 (Nat.cast_nonneg (Nat.factorial (m - 1))))
        have hw_out : ∀ s : Real, s ∈ Set.Icc 0 B.T →
            ∀ y : M, y ∉ cut.support n → 0 ≤ w s y := by
          intro s hs y hy
          dsimp only [w]
          rw [show F s y = 0 by
            exact GfunCut_off (I := I) B cut m n hs hy]
          simpa only [sub_zero] using
            add_nonneg haBar0 (mul_nonneg (hbBar0 n) hs.1)
        have hw_cont : ContinuousOn (fun p : Real × M ↦ w p.1 p.2)
            (Set.Icc 0 B.T ×ˢ cut.support n) := by
          have haffine : ContinuousOn
              (fun p : Real × M ↦ aBar + bBar n * p.1)
              (Set.Icc 0 B.T ×ˢ cut.support n) :=
            (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn
          simpa only [w] using haffine.sub hFcont
        have hw0 : ∀ y : M, 0 ≤ w 0 y := by
          intro y
          have hy := hinit y
          dsimp only [w]
          simpa only [mul_zero, add_zero] using sub_nonneg.mpr hy
        have hw_time : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            DifferentiableWithinAt Real (fun r : Real ↦ w r y)
              (Set.Icc 0 B.T) s := by
          intro s hs hspos y
          have haffine : DifferentiableWithinAt Real
              (fun r : Real ↦ aBar + bBar n * r) (Set.Icc 0 B.T) s :=
            (differentiableWithinAt_const aBar).add
              ((differentiableWithinAt_id' (𝕜 := Real)
                (s := Set.Icc 0 B.T) (x := s)).const_mul (bBar n))
          simpa only [w] using haffine.sub (hFtime s hs hspos y)
        have hw_mdiff : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I 𝓘(Real, Real) (w s) y := by
          intro s hs hspos y
          simpa only [w] using
            mdifferentiableAt_const.sub (hFspace s hs hspos y)
        have hw_grad : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
              gradientFun (I := I) (G.metric s) (w s) z) y := by
          intro s hs hspos y
          have hplain :
              (fun z : M ↦ gradientFun (I := I) (G.metric s) (w s) z) =
                (fun z : M ↦ -gradientFun (I := I) (G.metric s) (F s) z) := by
            funext z
            calc
              gradientFun (I := I) (G.metric s) (w s) z =
                  gradientFun (I := I) (G.metric s)
                    (fun u : M ↦ aBar + bBar n * s) z -
                    gradientFun (I := I) (G.metric s) (F s) z := by
                exact gradientFun_sub (I := I) (G.metric s)
                  mdifferentiableAt_const (hFspace s hs hspos z)
              _ = -gradientFun (I := I) (G.metric s) (F s) z := by
                rw [gradientFun_const]
                simp
          rw [show (T% fun z : M ↦
              gradientFun (I := I) (G.metric s) (w s) z) =
              (T% fun z : M ↦
                -gradientFun (I := I) (G.metric s) (F s) z) by
            funext z
            simpa using congrFun hplain z]
          rw [show (T% fun z : M ↦
              -gradientFun (I := I) (G.metric s) (F s) z) =
              (T% ((-1 : Real) • fun z : M ↦
                gradientFun (I := I) (G.metric s) (F s) z)) by
            funext z
            simp]
          exact (hFgrad s hs hspos y).smul_const_section (a := (-1 : Real))
        have hw_negative : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s →
            ∀ y : M, w s y < 0 →
              0 ≤ parabolicOperatorWithDrift (I := I) G B.T
                (fun _ z ↦ (0 : TangentSpace I z)) w s y := by
          intro s hs hspos y _
          have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) s :=
            (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt hs
          have hop :
              parabolicOperatorWithDrift (I := I) G B.T
                  (fun _ z ↦ (0 : TangentSpace I z)) w s y =
                bBar n - parabolicOperatorWithDrift (I := I) G B.T
                  (fun _ z ↦ (0 : TangentSpace I z)) F s y := by
            simpa only [w] using
              parabolicOperatorWithDrift_affine_sub (I := I) G B.T
                (fun _ z ↦ (0 : TangentSpace I z)) F aBar (bBar n) s y
                huniq (hFtime s hs hspos y)
                (fun z ↦ hFspace s hs hspos z) (hFgrad s hs hspos y)
          have hsub := GfunCut_parabolic_le (I := I) B cut hmpos
            hgrad hs hspos y
            (fun j hj ↦ by
              have hgrad_j : TowerNormGradUpTo (I := I) B j := by
                intro k hk
                exact hgrad k (hk.trans (Nat.le_of_lt hj))
              exact IH j hj hgrad_j s hs hspos y)
            hsmall
          have hsub' : parabolicOperatorWithDrift (I := I) G B.T
              (fun _ z ↦ (0 : TangentSpace I z)) F s y ≤ bBar n := by
            simpa only [F, bBar, bCore, bErr] using hsub
          rw [hop]
          linarith
        have hw_nonneg := strict_barrier_cpt (I := I) G B.T (le_of_lt B.hT)
          (fun _ z ↦ (0 : TangentSpace I z)) w (cut.support n)
          (cut.support_compact n) hw_out hw_cont hw0 hw_time hw_mdiff hw_grad
          hw_negative
        intro s hs y
        have hw := hw_nonneg s hs y
        dsimp only [w] at hw
        linarith
      intro t ht htpos x
      have hwm_le_G : t ^ m * B.w m t x ≤ BernsteinTower.Gfun (I := I) B m t x := by
        rw [BernsteinTower.Gfun]
        have hm_mem : m ∈ Finset.range (m + 1) := by simp
        rw [← Finset.sum_erase_add _ _ hm_mem]
        have htop : BernsteinTower.Gcoef (I := I) B m m * t ^ m * B.w m t x =
            t ^ m * B.w m t x := by
          rw [BernsteinTower.Gcoef]
          simp
        rw [htop]
        have hrest : 0 ≤ ∑ i ∈ (Finset.range (m + 1)).erase m,
            BernsteinTower.Gcoef (I := I) B m i * t ^ i * B.w i t x := by
          apply Finset.sum_nonneg
          intro i hi
          exact mul_nonneg
            (mul_nonneg (BernsteinTower.Gcoef_nonneg (I := I) B m i)
              (pow_nonneg ht.1 i))
            (B.hw_nonneg i t ht x)
        linarith
      have hsmall_eventually : ∀ᶠ n in Filter.atTop,
          2 * cut.err n * B.T * cutErrCoeff m ≤ 1 := by
        filter_upwards [cut.cutErr_small m] with n hn
        have hm_cut := hn m (by simp)
        ring_nf at hm_cut ⊢
        linarith
      have hexhaust : ∀ᶠ n in Filter.atTop, cut.chi n t x = 1 := by
        obtain ⟨n₀, hn₀⟩ := cut.exhausts t x ht
        exact Filter.eventually_atTop.2 ⟨n₀, hn₀⟩
      have hbound_eventually : ∀ᶠ n in Filter.atTop,
          t ^ m * B.w m t x ≤ aBar + bBar n * t := by
        filter_upwards [hsmall_eventually, hexhaust] with n hsmall hchi
        have hcut := hbound_cut n hsmall t ht x
        rw [GfunCut_one (I := I) B cut hchi] at hcut
        exact hwm_le_G.trans hcut
      have hbErr_tendsto : Filter.Tendsto bErr Filter.atTop (nhds 0) := by
        simpa only [bErr, zero_mul, mul_zero] using
          (((cut.err_tendsto.const_mul 9).mul_const
            (BernsteinTower.Gcoef (I := I) B m 0)).mul_const (B.K ^ 2))
      have hrhs_tendsto : Filter.Tendsto
          (fun n ↦ aBar + bBar n * t) Filter.atTop (nhds (aBar + bCore * t)) := by
        have hconst : Filter.Tendsto (fun _ : Nat ↦ aBar + bCore * t)
            Filter.atTop (nhds (aBar + bCore * t)) := tendsto_const_nhds
        simpa only [bBar, add_mul, add_assoc, zero_mul, add_zero] using
          (hconst.add (hbErr_tendsto.mul_const t))
      have hlimit : t ^ m * B.w m t x ≤ aBar + bCore * t :=
        ge_of_tendsto hrhs_tendsto hbound_eventually
      have hfinal : aBar + bCore * t ≤ towerConstSq B.c B.α m * B.K ^ 2 := by
        rw [towerConstSq_pos B.c B.α hmpos, haBar, hbCore, ← hbeta, ← hC,
          ← hbarTop]
        have htK : t * B.K ≤ B.α := htK_slab t ht
        have hcoeff0 : 0 ≤ barTop + beta * ∑ i ∈ Finset.range m,
            towerFactCoeff m i * towerBarGood B.c C i :=
          add_nonneg hbarTop0 (mul_nonneg hbeta0 hsum0)
        have hKsq0 : 0 ≤ B.K ^ 2 := pow_nonneg (le_of_lt B.hK) 2
        nlinarith [htK, mul_nonneg hcoeff0 hKsq0]
      rw [towerConst_sq B.hc B.hα]
      exact hlimit.trans hfinal

omit [NeZero (Module.finrank Real E)] in
/-- **Point-centered complete Bernstein estimate from barrier cutoffs.**

The cutoff family may depend on the point being estimated.  The family
hypothesis is essential: the strong induction needs lower-order estimates at
the a priori unrelated point selected by the compact-support maximum
principle. -/
theorem estimate_barrier_at
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (hcut : ∀ O : M,
      Nonempty (ShiBarrierCutoffData (I := I) G B.T O))
    (m : Nat)
    (hgrad : TowerNormGradUpTo (I := I) B m) :
    ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  revert hgrad
  induction m using Nat.strong_induction_on with
  | h m IH =>
    intro hgrad
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      intro t ht _ x
      simpa only [pow_zero, one_mul, towerConst_zero, one_pow] using
        B.hw0_bound t ht x
    · classical
      set C : Nat → Real := towerConst B.c B.α with hC
      set beta : Real := towerBeta B.c B.α C m with hbeta
      set barTop : Real := towerBarTop B.c C m with hbarTop
      set aBar : Real := beta * (Nat.factorial (m - 1) : Real) * B.K ^ 2
        with haBar
      set bCore : Real :=
        (barTop + beta * ∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3
        with hbCore
      have hbeta0 : 0 ≤ beta := by
        simpa only [hbeta, hC] using towerBeta_nonneg B.hc B.hα m
      have hbarTop0 : 0 ≤ barTop := by
        simpa only [hbarTop, hC] using towerBarTop_nonneg B.hc B.α m
      have haBar0 : 0 ≤ aBar := by
        rw [haBar]
        exact mul_nonneg
          (mul_nonneg hbeta0 (Nat.cast_nonneg (Nat.factorial (m - 1))))
          (pow_nonneg (le_of_lt B.hK) 2)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (towerFactCoeff_nonneg _ _)
          (by simpa only [hC] using towerBarGood_nonneg B.hc B.α i)
      have hbCore0 : 0 ≤ bCore := by
        rw [hbCore]
        exact mul_nonneg
          (add_nonneg hbarTop0 (mul_nonneg hbeta0 hsum0))
          (pow_nonneg (le_of_lt B.hK) 3)
      have htK_slab : ∀ s : Real, s ∈ Set.Icc 0 B.T → s * B.K ≤ B.α := by
        intro s hs
        calc
          s * B.K ≤ (B.α / B.K) * B.K :=
            mul_le_mul_of_nonneg_right (hs.2.trans B.hTK) (le_of_lt B.hK)
          _ = B.α := div_mul_cancel₀ B.α (ne_of_gt B.hK)
      have hbound_cut : ∀ {O : M}
          (cut : ShiBarrierCutoffData (I := I) G B.T O) (n : Nat),
          2 * cut.err n * B.T * cutErrCoeff m ≤ 1 →
          ∀ s : Real, s ∈ Set.Icc 0 B.T → ∀ y : M,
            GfunLocal (I := I) B (cut.chi n) m s y ≤
              aBar + (bCore +
                9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 *
                  B.K ^ 2) * s := by
        intro O cut n hsmall
        let bErr : Real :=
          9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2
        let bBar : Real := bCore + bErr
        let F : Real → M → Real := GfunLocal (I := I) B (cut.chi n) m
        let w : Real → M → Real := fun s y ↦ (aBar + bBar * s) - F s y
        have hbErr0 : 0 ≤ bErr := by
          dsimp only [bErr]
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (cut.err_nonneg n))
              (BernsteinTower.Gcoef_nonneg (I := I) B m 0))
            (pow_nonneg (le_of_lt B.hK) 2)
        have hbBar0 : 0 ≤ bBar := add_nonneg hbCore0 hbErr0
        have hFcont : ContinuousOn (fun p : Real × M ↦ F p.1 p.2)
            (Set.Icc 0 B.T ×ˢ cut.support n) := by
          rw [show (fun p : Real × M ↦ F p.1 p.2) =
              (fun p : Real × M ↦ ∑ i ∈ Finset.range (m + 1),
                BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i *
                  (cut.chi n p.1 p.2) ^ (i + 1) * B.w i p.1 p.2) by
            funext p
            change GfunLocal (I := I) B (cut.chi n) m p.1 p.2 = _
            rw [GfunLocal]]
          apply continuousOn_finset_sum
          intro i _
          exact (((continuous_const.mul (continuous_fst.pow i)).continuousOn.mul
            ((cut.joint_cont n).pow (i + 1))).mul
              ((B.hw_cont i).mono fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩))
        have hinit : ∀ y : M, F 0 y ≤ aBar := by
          intro y
          have h0mem : (0 : Real) ∈ Set.Icc 0 B.T :=
            ⟨le_rfl, le_of_lt B.hT⟩
          have hF0 : F 0 y =
              BernsteinTower.Gcoef (I := I) B m 0 *
                cut.chi n 0 y * B.w 0 0 y := by
            change GfunLocal (I := I) B (cut.chi n) m 0 y = _
            rw [GfunLocal, Finset.sum_eq_single 0]
            · simp
            · intro i _ hi0
              rcases Nat.eq_zero_or_pos i with rfl | hi
              · exact absurd rfl hi0
              · simp [zero_pow (by omega : i ≠ 0)]
            · simp
          have hGc0 : BernsteinTower.Gcoef (I := I) B m 0 =
              beta * (Nat.factorial (m - 1) : Real) := by
            rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ (0 : Nat) = m),
              towerFactCoeff, Nat.factorial_zero, Nat.cast_one, div_one,
              ← hC, ← hbeta]
          have hchi := cut.range n 0 y h0mem
          have hchi_w : cut.chi n 0 y * B.w 0 0 y ≤ B.K ^ 2 := by
            calc
              cut.chi n 0 y * B.w 0 0 y ≤ 1 * B.w 0 0 y :=
                mul_le_mul_of_nonneg_right hchi.2 (B.hw_nonneg 0 0 h0mem y)
              _ = B.w 0 0 y := one_mul _
              _ ≤ B.K ^ 2 := B.hw0_bound 0 h0mem y
          rw [hF0, hGc0, haBar]
          calc
            beta * (Nat.factorial (m - 1) : Real) *
                  cut.chi n 0 y * B.w 0 0 y =
                (beta * (Nat.factorial (m - 1) : Real)) *
                  (cut.chi n 0 y * B.w 0 0 y) := by ring
            _ ≤ (beta * (Nat.factorial (m - 1) : Real)) * B.K ^ 2 :=
              mul_le_mul_of_nonneg_left hchi_w
                (mul_nonneg hbeta0 (Nat.cast_nonneg (Nat.factorial (m - 1))))
        have hw_out : ∀ s : Real, s ∈ Set.Icc 0 B.T →
            ∀ y : M, y ∉ cut.support n → 0 ≤ w s y := by
          intro s hs y hy
          have hchi0 := cut.support_zero n s hs y hy
          have hF0 : F s y = 0 := by simp [F, GfunLocal, hchi0]
          dsimp only [w]
          rw [hF0, sub_zero]
          exact add_nonneg haBar0 (mul_nonneg hbBar0 hs.1)
        have hw_cont : ContinuousOn (fun p : Real × M ↦ w p.1 p.2)
            (Set.Icc 0 B.T ×ˢ cut.support n) := by
          have haffine : ContinuousOn
              (fun p : Real × M ↦ aBar + bBar * p.1)
              (Set.Icc 0 B.T ×ˢ cut.support n) :=
            (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn
          exact haffine.sub hFcont
        have hw0 : ∀ y : M, 0 ≤ w 0 y := by
          intro y
          dsimp only [w]
          simpa only [mul_zero, add_zero] using sub_nonneg.mpr (hinit y)
        have hsupport : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s →
            ∀ y : M, w s y < 0 →
              ParabolicUpperSupportAt (I := I) G B.T
                (fun _ z ↦ (0 : TangentSpace I z)) w s y := by
          intro s hs hspos y hneg
          have haff0 : 0 ≤ aBar + bBar * s :=
            add_nonneg haBar0 (mul_nonneg hbBar0 hs.1)
          have hFpos : 0 < F s y := by
            dsimp only [w] at hneg
            linarith
          have hchiPos : 0 < cut.chi n s y := by
            by_contra hnot
            have hchi0 : cut.chi n s y = 0 :=
              le_antisymm (le_of_not_gt hnot) (cut.range n s y hs).1
            have : F s y = 0 := by simp [F, GfunLocal, hchi0]
            linarith
          let support := cut.lower_support n s hs hspos y hchiPos
          let Fs : Real → M → Real :=
            GfunLocal (I := I) B support.phi m
          let v : Real → M → Real := fun r z ↦ (aBar + bBar * r) - Fs r z
          have hrec := GfunSupport_parabolic_le (I := I) B hmpos hgrad support
            hs hspos (cut.range n s y hs) (cut.err_nonneg n)
            (fun j hj ↦ by
              have hgrad_j : TowerNormGradUpTo (I := I) B j := by
                intro k hk
                exact hgrad k (hk.trans (Nat.le_of_lt hj))
              exact IH j hj hgrad_j s hs hspos y)
            hsmall
          have hFs_eq : Fs s y = F s y := by
            simp only [Fs, F, GfunLocal, support.eq_at]
          refine
            { v := v
              eq_at := by simp only [v, w, hFs_eq]
              upper_nhds := ?_
              time_diff := ?_
              space_diff_nhds := ?_
              grad_diff := ?_
              operator_nonneg := ?_ }
          · filter_upwards [support.lower_nhds, self_mem_nhdsWithin] with p hp hpslab
            have hmono : Fs p.1 p.2 ≤ F p.1 p.2 := by
              change GfunLocal (I := I) B support.phi m p.1 p.2 ≤
                GfunLocal (I := I) B (cut.chi n) m p.1 p.2
              rw [GfunLocal, GfunLocal]
              apply Finset.sum_le_sum
              intro i _
              calc
                BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i *
                      support.phi p.1 p.2 ^ (i + 1) * B.w i p.1 p.2 =
                    (BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i) *
                      (support.phi p.1 p.2 ^ (i + 1) * B.w i p.1 p.2) := by ring
                _ ≤ (BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i) *
                      (cut.chi n p.1 p.2 ^ (i + 1) * B.w i p.1 p.2) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right
                      (pow_le_pow_left₀ hp.1 hp.2 (i + 1))
                      (B.hw_nonneg i p.1 hpslab.1 p.2))
                    (mul_nonneg
                      (BernsteinTower.Gcoef_nonneg (I := I) B m i)
                      (pow_nonneg hpslab.1.1 i))
                _ = BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i *
                      cut.chi n p.1 p.2 ^ (i + 1) * B.w i p.1 p.2 := by ring
            dsimp only [v, w]
            linarith
          · exact ((differentiableWithinAt_const aBar).add
              ((differentiableWithinAt_id'
                (𝕜 := Real) (s := Set.Icc 0 B.T) (x := s)).const_mul bBar)).sub
              hrec.1
          · filter_upwards [hrec.2.1] with z hz
            simpa only [v, Fs] using mdifferentiableAt_const.sub hz
          · refine (hrec.2.2.1.smul_const_section
                (a := (-1 : Real))).congr_of_eventuallyEq ?_
            filter_upwards [hrec.2.1] with z hz
            exact congrArg (fun b ↦
              (⟨z, b⟩ : TotalSpace E (TangentSpace I : M → Type _))) (by
                calc
                  gradientFun (I := I) (G.metric s) (v s) z =
                      gradientFun (I := I) (G.metric s)
                          (fun _ : M ↦ aBar + bBar * s) z -
                        gradientFun (I := I) (G.metric s) (Fs s) z := by
                    simpa only [v] using
                      gradientFun_sub (I := I) (G.metric s)
                        mdifferentiableAt_const hz
                  _ = -gradientFun (I := I) (G.metric s) (Fs s) z := by
                    rw [gradientFun_const]
                    simp
                  _ = (-1 : Real) •
                      gradientFun (I := I) (G.metric s) (Fs s) z := by simp)
          · have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) s :=
              (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt hs
            have hop := parabolic_aff_nhds (I := I) B.T
              (fun _ z ↦ (0 : TangentSpace I z)) Fs aBar bBar s y
              huniq hrec.1 hrec.2.1 hrec.2.2.1
            rw [show v = (fun r z ↦ (aBar + bBar * r) - Fs r z) from rfl,
              hop]
            dsimp only [bBar, bErr]
            linarith [hrec.2.2.2]
        have hw_nonneg := strict_barrier_cpt_of_upperSupport
          (I := I) G B.T (le_of_lt B.hT)
          (fun _ z ↦ (0 : TangentSpace I z)) w (cut.support n)
          (cut.support_compact n) hw_out hw_cont hw0 hsupport
        intro s hs y
        have hw := hw_nonneg s hs y
        dsimp only [w, bBar, bErr] at hw
        linarith
      intro t ht htpos x
      let cut : ShiBarrierCutoffData (I := I) G B.T x :=
        Classical.choice (hcut x)
      have hwm_le_G :
          t ^ m * B.w m t x ≤ BernsteinTower.Gfun (I := I) B m t x := by
        rw [BernsteinTower.Gfun, ← Finset.sum_erase_add _ _ (by simp :
          m ∈ Finset.range (m + 1))]
        have hrest : 0 ≤ ∑ i ∈ (Finset.range (m + 1)).erase m,
            BernsteinTower.Gcoef (I := I) B m i * t ^ i * B.w i t x := by
          apply Finset.sum_nonneg
          intro i _
          exact mul_nonneg
            (mul_nonneg (BernsteinTower.Gcoef_nonneg (I := I) B m i)
              (pow_nonneg ht.1 i))
            (B.hw_nonneg i t ht x)
        have htop : BernsteinTower.Gcoef (I := I) B m m *
            t ^ m * B.w m t x = t ^ m * B.w m t x := by
          rw [BernsteinTower.Gcoef]
          simp
        rw [htop]
        linarith
      have hsmall_eventually : ∀ᶠ n in Filter.atTop,
          2 * cut.err n * B.T * cutErrCoeff m ≤ 1 := by
        have hlim : Filter.Tendsto
            (fun n ↦ 2 * cut.err n * B.T * cutErrCoeff m)
            Filter.atTop (nhds 0) := by
          simpa only [mul_zero, zero_mul] using
            (((cut.err_tendsto.const_mul 2).mul_const B.T).mul_const
              (cutErrCoeff m))
        filter_upwards [hlim.eventually_lt_const zero_lt_one] with n hn
        exact hn.le
      have hbound_eventually : ∀ᶠ n in Filter.atTop,
          t ^ m * B.w m t x ≤
            aBar + (bCore +
              9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 *
                B.K ^ 2) * t := by
        filter_upwards [hsmall_eventually, cut.center_exhausts t ht] with n hsmall hchi
        have hn := hbound_cut cut n hsmall t ht x
        have hone : GfunLocal (I := I) B (cut.chi n) m t x =
            BernsteinTower.Gfun (I := I) B m t x := by
          simp [GfunLocal, BernsteinTower.Gfun, hchi]
        rw [hone] at hn
        exact hwm_le_G.trans hn
      have herr_tendsto : Filter.Tendsto
          (fun n ↦ 9 * cut.err n *
            BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2)
          Filter.atTop (nhds 0) := by
        simpa only [zero_mul, mul_zero] using
          (((cut.err_tendsto.const_mul 9).mul_const
            (BernsteinTower.Gcoef (I := I) B m 0)).mul_const (B.K ^ 2))
      have hrhs_tendsto : Filter.Tendsto
          (fun n ↦ aBar + (bCore +
            9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 *
              B.K ^ 2) * t)
          Filter.atTop (nhds (aBar + bCore * t)) := by
        have hconst : Filter.Tendsto (fun _ : Nat ↦ aBar + bCore * t)
            Filter.atTop (nhds (aBar + bCore * t)) := tendsto_const_nhds
        simpa only [add_mul, add_assoc, zero_mul, add_zero] using
          (hconst.add (herr_tendsto.mul_const t))
      have hlimit : t ^ m * B.w m t x ≤ aBar + bCore * t :=
        ge_of_tendsto hrhs_tendsto hbound_eventually
      have hfinal : aBar + bCore * t ≤
          towerConstSq B.c B.α m * B.K ^ 2 := by
        rw [towerConstSq_pos B.c B.α hmpos, haBar, hbCore, ← hbeta, ← hC,
          ← hbarTop]
        have htK : t * B.K ≤ B.α := htK_slab t ht
        have hcoeff0 : 0 ≤ barTop + beta * ∑ i ∈ Finset.range m,
            towerFactCoeff m i * towerBarGood B.c C i :=
          add_nonneg hbarTop0 (mul_nonneg hbeta0 hsum0)
        have hKsq0 : 0 ≤ B.K ^ 2 := pow_nonneg (le_of_lt B.hK) 2
        nlinarith [htK, mul_nonneg hcoeff0 hKsq0]
      rw [towerConst_sq B.hc B.hα]
      exact hlimit.trans hfinal

omit [NeZero (Module.finrank Real E)] in
/-- All-order compatibility wrapper for `estimate_cutoff_at`. -/
theorem estimate_of_cutoff
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (hgrad : TowerNormGradOn (I := I) B) :
    ∀ m : Nat, ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  intro m
  exact estimate_cutoff_at (I := I) B cut m (hgrad.upTo m)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Legacy unsupported frontier.**  This statement is too weak for a
complete-noncompact Bernstein argument: metric equivalence and a Ricci lower
bound do not produce quantitative evolving-metric cutoffs, and the abstract
tower does not expose the Kato estimate needed to absorb cutoff-gradient
terms.  Replace its caller by a localized theorem consuming generated cutoff
data and `TowerNormGradOn`; do not fill this proof under the present
interface. -/
theorem estimate_complete
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (Ceq Kric : Real) (hCeq : 1 ≤ Ceq) (hKric : 0 ≤ Kric)
    (hequiv : ∀ t : Real, t ∈ Set.Icc 0 B.T → ∀ x : M,
      ∀ v : TangentSpace I x,
        Ceq⁻¹ * ‖v‖ ^ 2 ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Ceq * ‖v‖ ^ 2)
    (hric : ∀ t : Real, t ∈ Set.Icc 0 B.T → ∀ x : M,
      ∀ v : TangentSpace I x,
        -Kric * (G.metric t).inner x v v ≤
          ricciTensor (I := I) (G.metric t) x v v) :
    ∀ m : ℕ, ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  sorry

end BernsteinTower

end DifferentialGeometry.PDE.RicciFlow
