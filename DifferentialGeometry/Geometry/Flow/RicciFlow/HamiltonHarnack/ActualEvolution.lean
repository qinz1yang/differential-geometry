import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.ReactionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.HeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.HamiltonEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.DifferentiatedSecondBianchi
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MIdentities
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.PerturbedEvolution
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.FrozenSlot

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
  DifferentialGeometry.Integral.Measure in
private theorem freezeAllBut0SField_chartBasis_contMDiffOn
    {q : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (r : Fin q)
    (V : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : M) (j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real) ∞
      (fun y : M =>
        freezeAllBut0SField (I := I) (M := M) A r V y
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) a j y))
      (chartAt H a).source := by
  intro y hy
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hvec :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun z : M =>
          TotalSpace.mk' E (E := fun p : M => TangentSpace I p) z
            (chartBasisVecFiber (I := I) a j z)) y :=
    (chartBasisVec_contMDiffOn (I := I) a j).contMDiffAt
      ((trivializationAt E (TangentSpace I) a).open_baseSet.mem_nhds (by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M)]
        exact hy))
  exact TensorMultilinear.contMDiffAt_section_apply_gen
    (𝕜 := Real) (I := I) (M := M) (n := 1)
    (T := fun z : M => freezeAllBut0SField (I := I) (M := M) A r V z)
    ((freezeAllBut0SField (I := I) (M := M) A r V).contMDiff y)
    (v := fun _ : Fin 1 => fun z : M => chartBasisVecFiber (I := I) a j z)
    (fun _ => hvec)

open DifferentialGeometry.Integral.DivergenceTheorem in
private noncomputable def frozenSlotSharpSection
    {q : Nat}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (r : Fin q)
    (V : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk
    (fun y : M =>
      cotangentSharpGen (I := I) g y
        (freezeAllBut0SField (I := I) (M := M) A r V y))
    (cotangentSharp_gen_contMDiff_total (I := I) g
      (fun a j => freezeAllBut0SField_chartBasis_contMDiffOn
        (I := I) A r V a j))

@[simp] private theorem frozenSlotSharpSection_apply
    {q : Nat}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (r : Fin q)
    (V : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (y : M) :
    frozenSlotSharpSection (I := I) g A r V y =
      cotangentSharpGen (I := I) g y
        (freezeAllBut0SField (I := I) (M := M) A r V y) :=
  rfl

private theorem curvatureActionSummand_mvfderiv
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {q : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (r : Fin q)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hY : (S.family.connection (t : Real) (fun y : M => Y y) x) (X x) = 0)
    (hZ : (S.family.connection (t : Real) (fun y : M => Z y) x) (X x) = 0)
    (hV : forall i,
      (S.family.connection (t : Real) (fun y : M => V i y) x) (X x) = 0) :
    mvfderiv (I := I)
        (fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Y y) (Z y) (V r y)
              (frozenSlotSharpSection (I := I) (S.base.metric (t : Real)) A r V y)))
        x (X x) =
      nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (X x) (Y x) (Z x) (V r x)
            (frozenSlotSharpSection (I := I) (S.base.metric (t : Real)) A r V x)) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (Y x) (Z x) (V r x)
            (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                  1 (S.family.connection (t : Real))
                  (freezeAllBut0SField (I := I) (M := M) A r V)
                  (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                    1 (S.family.connection (t : Real)) (by
                      simpa [SolutionFamily.connection, metricCov] using
                        metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                    (freezeAllBut0SField (I := I) (M := M) A r V))) x) (X x)))) := by
  classical
  let cov := S.family.connection (t : Real)
  let B := freezeAllBut0SField (I := I) (M := M) A r V
  let DB := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 cov B
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      1 cov (by
        simpa [cov, SolutionFamily.connection, metricCov] using
          metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real))) B)
  have hDB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov B DB :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov B _
  let W : Fin 4 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ![Y, Z, V r,
      frozenSlotSharpSection (I := I) (S.base.metric (t : Real)) A r V]
  have heval :=
    (nablaRm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X W x
  have hscalar :
      (fun y : M => S.base.rm04 (t : Real) y (fun i : Fin 4 => W i y)) =
        fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Y y) (Z y) (V r y)
              (frozenSlotSharpSection (I := I)
                (S.base.metric (t : Real)) A r V y)) := by
    funext y
    congr 1
    funext i
    fin_cases i <;> rfl
  have hcons :
      Fin.cons (X x) (fun i : Fin 4 => W i x) =
        vec5 (I := I) (X x) (Y x) (Z x) (V r x)
          (frozenSlotSharpSection (I := I) (S.base.metric (t : Real)) A r V x) := by
    funext i
    fin_cases i <;> rfl
  have hsharp :
      (cov
          (fun y : M =>
            cotangentSharpGen (I := I) (S.base.metric (t : Real)) y (B y)) x)
          (X x) =
        cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (DB x) (X x)) := by
    exact cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
      cov (S.base.metric (t : Real))
      (solution_isMetricCompatible (I := I) S (t : Real)) B DB hDB X x
      (cotangentSharp_gen_mdiffAt (I := I) (S.base.metric (t : Real))
        (fun a j => freezeAllBut0SField_chartBasis_contMDiffOn
          (I := I) A r V a j) x)
  have hcorr :
      (∑ i : Fin 4,
          S.base.rm04 (t : Real) x
            (Function.update (fun j : Fin 4 => W j x) i
              ((cov (fun y : M => W i y) x) (X x)))) =
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (Y x) (Z x) (V r x)
            (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (DB x) (X x)))) := by
    rw [Fin.sum_univ_four]
    have h0 : (cov (fun y : M => W 0 y) x) (X x) = 0 := hY
    have h1 : (cov (fun y : M => W 1 y) x) (X x) = 0 := hZ
    have h2 : (cov (fun y : M => W 2 y) x) (X x) = 0 := hV r
    have h3 :
        (cov (fun y : M => W 3 y) x) (X x) =
          cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (DB x) (X x)) := by
      simpa [W, B, frozenSlotSharpSection_apply] using hsharp
    rw [h0, h1, h2, h3]
    rw [show S.base.rm04 (t : Real) x
        (Function.update (fun j : Fin 4 => W j x) 0 (0 : TangentSpace I x)) = 0 from
      (S.base.rm04 (t : Real) x).map_update_zero _ 0]
    rw [show S.base.rm04 (t : Real) x
        (Function.update (fun j : Fin 4 => W j x) 1 (0 : TangentSpace I x)) = 0 from
      (S.base.rm04 (t : Real) x).map_update_zero _ 1]
    rw [show S.base.rm04 (t : Real) x
        (Function.update (fun j : Fin 4 => W j x) 2 (0 : TangentSpace I x)) = 0 from
      (S.base.rm04 (t : Real) x).map_update_zero _ 2]
    simp only [zero_add, add_zero]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hscalar] at heval
  rw [hcons, hcorr] at heval
  simpa [cov, B, DB] using eq_add_of_sub_eq heval.symm

theorem differentiatedTensorRicciIdentityComponents_of_orthonormalBasis
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n q : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (DA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (D2A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 2))
    (D3A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 3))
    (hDA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q (S.family.connection (t : Real)) A DA)
    (hD3A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 2) (S.family.connection (t : Real)) D2A D3A)
    (hId : forall y,
      Tensor0SRicciIdentityAt (I := I) (S.base.rm13 (t : Real)) (A y) (D2A y))
    (hSkewLast : forall a b c d,
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
        -S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
    (hNablaSkewLast : forall e a b c d,
      nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)) =
        -nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis a) (basis b) (basis d) (basis c))) :
    differentiatedTensorRicciIdentityComponents
      (fun a b c d =>
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun e a b c d =>
        nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)))
      (fun slots => A x (fun r => basis (slots r)))
      (fun e slots => DA x (Fin.cons (basis e) (fun r => basis (slots r))))
      (fun e a b slots =>
        D3A x (Fin.cons (basis e)
          (Fin.cons (basis a) (Fin.cons (basis b) (fun r => basis (slots r)))))) := by
  classical
  let cov := S.family.connection (t : Real)
  let V : Fin n -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun i =>
    (TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov x (basis i)).choose
  have hVx (i : Fin n) : V i x = basis i :=
    (TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov x (basis i)).choose_spec.1
  have hVcov (i j : Fin n) : (cov (fun y : M => V i y) x) (V j x) = 0 :=
    (TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov x (basis i)).choose_spec.2 (V j)
  intro e a slots
  let tail : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun r => V (slots r)
  let leftSlots : Fin (q + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons (V e) (Fin.cons (V a) tail)
  let rightSlots : Fin (q + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons (V a) (Fin.cons (V e) tail)
  have hleftEval := hD3A.eval_smooth_slots (V e) leftSlots x
  have hrightEval := hD3A.eval_smooth_slots (V e) rightSlots x
  have hleftCorr :
      (∑ i : Fin (q + 2),
          D2A x
            (Function.update (fun j : Fin (q + 2) => leftSlots j x) i
              ((cov (fun y : M => leftSlots i y) x) (V e x)))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz : (cov (fun y : M => leftSlots i y) x) (V e x) = 0 := by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hVcov e e
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact hVcov a e
        · exact hVcov (slots i) e
    rw [hz]
    exact (D2A x).map_update_zero _ i
  have hrightCorr :
      (∑ i : Fin (q + 2),
          D2A x
            (Function.update (fun j : Fin (q + 2) => rightSlots j x) i
              ((cov (fun y : M => rightSlots i y) x) (V e x)))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz : (cov (fun y : M => rightSlots i y) x) (V e x) = 0 := by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hVcov a e
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact hVcov e e
        · exact hVcov (slots i) e
    rw [hz]
    exact (D2A x).map_update_zero _ i
  rw [hleftCorr, sub_zero] at hleftEval
  rw [hrightCorr, sub_zero] at hrightEval
  have hleftSlotsX :
      (fun i : Fin (q + 2) => leftSlots i x) =
        metricTraceInput (I := I) (basis e) (basis a)
          (fun r => basis (slots r)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hVx e
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact hVx a
      · exact hVx (slots i)
  have hrightSlotsX :
      (fun i : Fin (q + 2) => rightSlots i x) =
        metricTraceInput (I := I) (basis a) (basis e)
          (fun r => basis (slots r)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hVx a
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact hVx e
      · exact hVx (slots i)
  have hleft :
      D3A x (Fin.cons (basis e)
          (Fin.cons (basis e) (Fin.cons (basis a) (fun r => basis (slots r))))) =
        mvfderiv (I := I)
          (fun y : M => D2A y (fun i : Fin (q + 2) => leftSlots i y)) x (basis e) := by
    rw [hVx e, hleftSlotsX] at hleftEval
    exact hleftEval
  have hright :
      D3A x (Fin.cons (basis e)
          (Fin.cons (basis a) (Fin.cons (basis e) (fun r => basis (slots r))))) =
        mvfderiv (I := I)
          (fun y : M => D2A y (fun i : Fin (q + 2) => rightSlots i y)) x (basis e) := by
    rw [hVx e, hrightSlotsX] at hrightEval
    exact hrightEval
  have hleftDiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => D2A y (fun i : Fin (q + 2) => leftSlots i y)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      D2A leftSlots x).mdifferentiableAt (by simp)
  have hrightDiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => D2A y (fun i : Fin (q + 2) => rightSlots i y)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      D2A rightSlots x).mdifferentiableAt (by simp)
  have hfield :
      (fun y : M =>
          D2A y (fun i : Fin (q + 2) => leftSlots i y) -
            D2A y (fun i : Fin (q + 2) => rightSlots i y)) =
        fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (A y)
            (V e y) (V a y) (fun r => tail r y) := by
    funext y
    have hl : (fun i : Fin (q + 2) => leftSlots i y) =
        metricTraceInput (I := I) (V e y) (V a y) (fun r => tail r y) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have hr : (fun i : Fin (q + 2) => rightSlots i y) =
        metricTraceInput (I := I) (V a y) (V e y) (fun r => tail r y) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    rw [hl, hr]
    exact hId y (V e y) (V a y) (fun r => tail r y)
  have hderivAction :
      D3A x (Fin.cons (basis e)
            (Fin.cons (basis e) (Fin.cons (basis a) (fun r => basis (slots r))))) -
          D3A x (Fin.cons (basis e)
            (Fin.cons (basis a) (Fin.cons (basis e) (fun r => basis (slots r))))) =
        mvfderiv (I := I)
          (fun y : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (A y)
              (V e y) (V a y) (fun r => tail r y)) x (basis e) := by
    rw [hleft, hright, ← hVx e]
    rw [← mvfderiv_sub_at (I := I) (V e x) hleftDiff hrightDiff]
    rw [hfield]
  rw [hderivAction]
  let F : Fin q -> M -> Real := fun r y =>
    S.base.rm04 (t : Real) y
      (vec4 (I := I) (V e y) (V a y) (tail r y)
        (frozenSlotSharpSection (I := I) (S.base.metric (t : Real)) A r tail y))
  have haction :
      (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (A y)
            (V e y) (V a y) (fun r => tail r y)) =
        fun y : M => -∑ r : Fin q, F r y := by
    funext y
    rw [curvatureAction0SAt_eq_rm04_raise (I := I)
      (S.base.metric (t : Real)) (S.base.rm13 (t : Real))
      (S.base.rm04 (t : Real) y)
      (solution_rm04LowersRm13At (I := I) S (t : Real) y)]
    simp only [F, frozenSlotSharpSection_apply, freezeAllBut0SField_apply]
  have hFdiff (r : Fin q) : MDifferentiableAt I 𝓘(Real, Real) (F r) x := by
    let W : Fin 4 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
      ![V e, V a, tail r,
        frozenSlotSharpSection (I := I) (S.base.metric (t : Real)) A r tail]
    have h := (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (S.base.rm04 (t : Real)) W x).mdifferentiableAt (by simp)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [F]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hsumfun : (fun y : M => ∑ r : Fin q, F r y) =
      (Finset.univ : Finset (Fin q)).sum F := by
    funext y
    simp [Finset.sum_apply]
  have hderivSum :
      mvfderiv (I := I) (fun y : M => -∑ r : Fin q, F r y) x (basis e) =
        -∑ r : Fin q, mvfderiv (I := I) (F r) x (basis e) := by
    have hneg := mvfderiv_neg_at (I := I)
      (f := fun y : M => ∑ r : Fin q, F r y) (basis e)
      (by
        rw [hsumfun]
        exact mdiffAt_finset_sum (I := I) (Finset.univ : Finset (Fin q)) F
          (fun r _ => hFdiff r))
    rw [hneg, hsumfun]
    rw [mvfderiv_finset_sum_at (I := I) (Finset.univ : Finset (Fin q))
      F (basis e) (fun r _ => hFdiff r)]
  have hFsummand (r : Fin q) :
      mvfderiv (I := I) (F r) x (basis e) =
        nablaRm04Field (I := I) S (t : Real) x
            (vec5 (I := I) (basis e) (basis e) (basis a) (basis (slots r))
              (frozenSlotSharpSection (I := I)
                (S.base.metric (t : Real)) A r tail x)) +
          S.base.rm04 (t : Real) x
            (vec4 (I := I) (basis e) (basis a) (basis (slots r))
              (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
                (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                  ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    1 (S.family.connection (t : Real))
                    (freezeAllBut0SField (I := I) (M := M) A r tail)
                    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                      1 (S.family.connection (t : Real)) (by
                        simpa [SolutionFamily.connection, metricCov] using
                          metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                      (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
                  (basis e)))) := by
    have h := curvatureActionSummand_mvfderiv (I := I) S t x A r
      (V e) (V e) (V a) tail (hVcov e e) (hVcov a e)
      (fun i => hVcov (slots i) e)
    simpa [F, tail, hVx] using h
  have hactionDeriv :
      mvfderiv (I := I)
          (fun y : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (A y)
              (V e y) (V a y) (fun r => tail r y)) x (basis e) =
        -∑ r : Fin q,
          (nablaRm04Field (I := I) S (t : Real) x
              (vec5 (I := I) (basis e) (basis e) (basis a) (basis (slots r))
                (frozenSlotSharpSection (I := I)
                  (S.base.metric (t : Real)) A r tail x)) +
            S.base.rm04 (t : Real) x
              (vec4 (I := I) (basis e) (basis a) (basis (slots r))
                (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
                  (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                    ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                      1 (S.family.connection (t : Real))
                      (freezeAllBut0SField (I := I) (M := M) A r tail)
                      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                        1 (S.family.connection (t : Real)) (by
                          simpa [SolutionFamily.connection, metricCov] using
                            metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                        (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
                    (basis e))))) := by
    rw [haction, hderivSum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => hFsummand r
  rw [hactionDeriv]
  have hFirst (r : Fin q) :
      nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis e) (basis a) (basis (slots r))
            (frozenSlotSharpSection (I := I)
              (S.base.metric (t : Real)) A r tail x)) =
        ∑ d : Fin n,
          A x (fun p => basis (Function.update slots r d p)) *
            nablaRm04Field (I := I) S (t : Real) x
              (vec5 (I := I) (basis e) (basis e) (basis a)
                (basis (slots r)) (basis d)) := by
    rw [frozenSlotSharpSection_apply]
    rw [cotangent_sharp_orthonormal_basis_expand (I := I)
      (S.base.metric (t : Real)) basis horth]
    rw [tensor_zero_five_vec_five_sum_last]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [freezeAllBut0SField_apply_vec]
    congr 2
    funext p
    by_cases hp : p = r
    · subst hp
      simp [tail, hVx]
    · simp [tail, hVx, hp]
  have hDBcomponent (r : Fin q) (d : Fin n) :
      (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
          ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            1 (S.family.connection (t : Real))
            (freezeAllBut0SField (I := I) (M := M) A r tail)
            (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
              1 (S.family.connection (t : Real)) (by
                simpa [SolutionFamily.connection, metricCov] using
                  metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
              (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
          (basis e)) (fun _ : Fin 1 => basis d) =
        DA x (Fin.cons (basis e)
          (fun p => basis (Function.update slots r d p))) := by
    let B := freezeAllBut0SField (I := I) (M := M) A r tail
    let DB := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection (t : Real)) B
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        1 (S.family.connection (t : Real)) (by
          simpa [SolutionFamily.connection, metricCov] using
            metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real))) B)
    change (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
      (DB x) (basis e)) (fun _ : Fin 1 => basis d) = _
    rw [tensor0S_curry_apply_cons]
    have hfreeze := allBut0SFreezeNabla (I := I)
      (S.family.connection (t : Real)) A r (V e) tail
      (fun i _ => hVcov (slots i) e) (basis d)
    have hDBval :
        DB x (vec2 (I := I) (V e x) (basis d)) =
          totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            1 (S.family.connection (t : Real)) B x
              (vec2 (I := I) (V e x) (basis d)) := by
      rfl
    rw [show Fin.cons (basis e) (fun _ : Fin 1 => basis d) =
        vec2 (I := I) (basis e) (basis d) by
      funext i
      fin_cases i <;> rfl]
    rw [← hVx e, hDBval]
    change totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 (S.family.connection (t : Real))
        (freezeAllBut0SField (I := I) (M := M) A r tail) x
        (vec2 (I := I) (V e x) (basis d)) = _ at hfreeze
    rw [hfreeze]
    rw [totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q (S.family.connection (t : Real)) (V e) A x
      (Function.update (fun i : Fin q => tail i x) r (basis d))]
    rw [← hDA (V e) x
      (Function.update (fun i : Fin q => tail i x) r (basis d))]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · by_cases hi : i = r
      · subst hi
        simp
      · simp [tail, hVx, hi]
  have hSecond (r : Fin q) :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis e) (basis a) (basis (slots r))
            (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                  1 (S.family.connection (t : Real))
                  (freezeAllBut0SField (I := I) (M := M) A r tail)
                  (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                    1 (S.family.connection (t : Real)) (by
                      simpa [SolutionFamily.connection, metricCov] using
                        metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                    (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
                (basis e)))) =
        ∑ d : Fin n,
          DA x (Fin.cons (basis e)
              (fun p => basis (Function.update slots r d p))) *
            S.base.rm04 (t : Real) x
              (vec4 (I := I) (basis e) (basis a) (basis (slots r)) (basis d)) := by
    rw [cotangent_sharp_orthonormal_basis_expand (I := I)
      (S.base.metric (t : Real)) basis horth]
    rw [tensor_zero_four_vec_four_sum_last]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hDBcomponent r d]
  have hFirstSkew (r : Fin q) :
      -(nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis e) (basis a) (basis (slots r))
            (frozenSlotSharpSection (I := I)
              (S.base.metric (t : Real)) A r tail x))) =
        ∑ d : Fin n,
          nablaRm04Field (I := I) S (t : Real) x
              (vec5 (I := I) (basis e) (basis e) (basis a)
                (basis d) (basis (slots r))) *
            A x (fun p => basis (Function.update slots r d p)) := by
    rw [hFirst r, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hNablaSkewLast e e a (slots r) d]
    ring
  have hSecondSkew (r : Fin q) :
      -(S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis e) (basis a) (basis (slots r))
            (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                  1 (S.family.connection (t : Real))
                  (freezeAllBut0SField (I := I) (M := M) A r tail)
                  (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                    1 (S.family.connection (t : Real)) (by
                      simpa [SolutionFamily.connection, metricCov] using
                        metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                    (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
                (basis e))))) =
        ∑ d : Fin n,
          S.base.rm04 (t : Real) x
              (vec4 (I := I) (basis e) (basis a) (basis d) (basis (slots r))) *
            DA x (Fin.cons (basis e)
              (fun p => basis (Function.update slots r d p))) := by
    rw [hSecond r, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hSkewLast e a (slots r) d]
    ring
  have hHalfFirst := half_curvature_skew_action_eq_slots
    (fun i j k l =>
      nablaRm04Field (I := I) S (t : Real) x
        (vec5 (I := I) (basis e) (basis i) (basis j) (basis k) (basis l)))
    (fun indices => A x (fun r => basis (indices r)))
    (hNablaSkewLast e) e a slots
  have hHalfSecond := half_curvature_skew_action_eq_slots
    (fun i j k l =>
      S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
    (fun indices => DA x (Fin.cons (basis e) (fun r => basis (indices r))))
    hSkewLast e a slots
  rw [mul_add, hHalfFirst, hHalfSecond]
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ r : Fin q,
        -(nablaRm04Field (I := I) S (t : Real) x
            (vec5 (I := I) (basis e) (basis e) (basis a) (basis (slots r))
              (frozenSlotSharpSection (I := I)
                (S.base.metric (t : Real)) A r tail x)) +
          S.base.rm04 (t : Real) x
            (vec4 (I := I) (basis e) (basis a) (basis (slots r))
              (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
                (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                  ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    1 (S.family.connection (t : Real))
                    (freezeAllBut0SField (I := I) (M := M) A r tail)
                    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                      1 (S.family.connection (t : Real)) (by
                        simpa [SolutionFamily.connection, metricCov] using
                          metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                      (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
                  (basis e)))))) =
      ∑ r : Fin q,
        (-(nablaRm04Field (I := I) S (t : Real) x
            (vec5 (I := I) (basis e) (basis e) (basis a) (basis (slots r))
              (frozenSlotSharpSection (I := I)
                (S.base.metric (t : Real)) A r tail x))) +
          -(S.base.rm04 (t : Real) x
            (vec4 (I := I) (basis e) (basis a) (basis (slots r))
              (cotangentSharpGen (I := I) (S.base.metric (t : Real)) x
                (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                  ((totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                    1 (S.family.connection (t : Real))
                    (freezeAllBut0SField (I := I) (M := M) A r tail)
                    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
                      1 (S.family.connection (t : Real)) (by
                        simpa [SolutionFamily.connection, metricCov] using
                          metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
                      (freezeAllBut0SField (I := I) (M := M) A r tail))) x)
                  (basis e)))))) := by
        refine Finset.sum_congr rfl fun r _ => by ring
    _ = ∑ r : Fin q,
        ((∑ d : Fin n,
            nablaRm04Field (I := I) S (t : Real) x
                (vec5 (I := I) (basis e) (basis e) (basis a)
                  (basis d) (basis (slots r))) *
              A x (fun p => basis (Function.update slots r d p))) +
          ∑ d : Fin n,
            S.base.rm04 (t : Real) x
                (vec4 (I := I) (basis e) (basis a) (basis d) (basis (slots r))) *
              DA x (Fin.cons (basis e)
                (fun p => basis (Function.update slots r d p)))) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hFirstSkew r, hSecondSkew r]
    _ =
        (∑ r : Fin q, ∑ d : Fin n,
          nablaRm04Field (I := I) S (t : Real) x
              (vec5 (I := I) (basis e) (basis e) (basis a)
                (basis d) (basis (slots r))) *
            A x (fun p => basis (Function.update slots r d p))) +
          ∑ r : Fin q, ∑ d : Fin n,
            S.base.rm04 (t : Real) x
                (vec4 (I := I) (basis e) (basis a) (basis d) (basis (slots r))) *
              DA x (Fin.cons (basis e)
                (fun p => basis (Function.update slots r d p))) := by
        rw [Finset.sum_add_distrib]

theorem covariantTensorSecondDerivativeCommutatorComponents_of_orthonormalBasis
    {n q : Nat} {x : M}
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) q x)
    (D2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (q + 2) x)
    (hId : Tensor0SRicciIdentityAt (I := I) Rm13 A D2A)
    (hSkewLast : forall a b c d,
      Rm04 (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
        -Rm04 (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) :
    covariantTensorSecondDerivativeCommutatorComponents
      (fun a b c d =>
        Rm04 (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun slots => A (fun r => basis (slots r)))
      (fun a b slots =>
        D2A (Fin.cons (basis a) (Fin.cons (basis b) (fun r => basis (slots r))))) := by
  classical
  intro a b slots
  change
    D2A (Fin.cons (basis a) (Fin.cons (basis b) (fun r => basis (slots r)))) -
        D2A (Fin.cons (basis b) (Fin.cons (basis a) (fun r => basis (slots r)))) =
      (1 / 2 : Real) * ∑ c : Fin n, ∑ d : Fin n,
        Rm04 (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)) *
          covariantTensorSkewAction
            (fun slots => A (fun r => basis (slots r))) c d slots
  calc
      D2A (Fin.cons (basis a) (Fin.cons (basis b) (fun r => basis (slots r)))) -
          D2A (Fin.cons (basis b) (Fin.cons (basis a) (fun r => basis (slots r)))) =
        curvatureAction0SAt (I := I) Rm13 A (basis a) (basis b)
          (fun r => basis (slots r)) := by
            have hinputA :
                metricTraceInput (I := I) (basis a) (basis b)
                    (fun r => basis (slots r)) =
                  Fin.cons (basis a) (Fin.cons (basis b) (fun r => basis (slots r))) := by
              funext r
              refine Fin.cases ?_ (fun r => ?_) r
              · rfl
              · refine Fin.cases ?_ (fun r => ?_) r
                · rfl
                · rfl
            have hinputB :
                metricTraceInput (I := I) (basis b) (basis a)
                    (fun r => basis (slots r)) =
                  Fin.cons (basis b) (Fin.cons (basis a) (fun r => basis (slots r))) := by
              funext r
              refine Fin.cases ?_ (fun r => ?_) r
              · rfl
              · refine Fin.cases ?_ (fun r => ?_) r
                · rfl
                · rfl
            simpa only [hinputA, hinputB] using
              hId (basis a) (basis b) (fun r => basis (slots r))
      _ = -∑ r : Fin q, ∑ d : Fin n,
          A (fun p => basis (Function.update slots r d p)) *
            Rm04 (vec4 (I := I) (basis a) (basis b) (basis (slots r)) (basis d)) :=
        curvatureAction0SAt_orthoBasis_eq_sum
          (I := I) g Rm13 Rm04 hLower basis horth A a b slots
      _ = ∑ r : Fin q, ∑ d : Fin n,
          Rm04 (vec4 (I := I) (basis a) (basis b) (basis d) (basis (slots r))) *
            A (fun p => basis (Function.update slots r d p)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hSkewLast a b (slots r) d]
        ring
      _ = (1 / 2 : Real) * ∑ c : Fin n, ∑ d : Fin n,
          Rm04 (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)) *
            covariantTensorSkewAction
              (fun slots => A (fun r => basis (slots r))) c d slots := by
        symm
        exact half_curvature_skew_action_eq_slots
          (fun i j k l =>
            Rm04 (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun indices => A (fun r => basis (indices r))) hSkewLast a b slots

theorem tensorGradientRicciIdentityComponents_of_orthonormalBasis
    {n q : Nat} {x : M}
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (DA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (q + 1) x)
    (D3A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (q + 3) x)
    (hId : Tensor0SRicciIdentityAt (I := I) Rm13 DA D3A)
    (hSkewLast : forall a b c d,
      Rm04 (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
        -Rm04 (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) :
    tensorGradientRicciIdentityComponents
      (fun a b c d =>
        Rm04 (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun e slots => DA (Fin.cons (basis e) (fun r => basis (slots r))))
      (fun e f d slots =>
        D3A (Fin.cons (basis e)
          (Fin.cons (basis f) (Fin.cons (basis d) (fun r => basis (slots r)))))) := by
  have hcomm :=
    covariantTensorSecondDerivativeCommutatorComponents_of_orthonormalBasis
      (I := I) g Rm13 Rm04 hLower basis horth DA D3A hId hSkewLast
  intro e a slots
  have hslots :
      (fun r : Fin (q + 1) =>
        basis ((Fin.cons e slots : Fin (q + 1) -> Fin n) r)) =
        Fin.cons (basis e) (fun r => basis (slots r)) := by
    funext r
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · rfl
  have hDA :
      prependCovariantDerivativeComponents
          (fun d slots => DA (Fin.cons (basis d) (fun r => basis (slots r)))) =
        fun slots : Fin (q + 1) -> Fin n => DA (fun r => basis (slots r)) := by
    funext b
    rw [prependCovariantDerivativeComponents]
    congr 1
    funext r
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · rfl
  rw [hDA]
  simpa only [hslots] using hcomm e a (Fin.cons e slots)

private noncomputable def metricNabla3RicField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (metricCov (I := I) (M := M) g)
    (metricNabla2Ric (I := I) (M := M) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (metricNabla2Ric (I := I) (M := M) g))

noncomputable def hamiltonNablaPField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (metricCov (I := I) (M := M) g) (hamiltonPField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g) (hamiltonPField (I := I) g))

private noncomputable def hamiltonNabla2PField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (metricCov (I := I) (M := M) g) (hamiltonNablaPField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))

noncomputable def hamiltonNabla3PField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (metricCov (I := I) (M := M) g) (hamiltonNabla2PField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g) (hamiltonNabla2PField (I := I) g))

private def vec6 {x : M} (A B C D E F : TangentSpace I x) : Fin 6 -> TangentSpace I x :=
  fun i => if i = 0 then A else if i = 1 then B else if i = 2 then C else
    if i = 3 then D else if i = 4 then E else F

theorem hamiltonNablaPField_apply
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C D : TangentSpace I x) :
    hamiltonNablaPField (I := I) g x (vec4 (I := I) A B C D) =
      metricNabla2Ric (I := I) (M := M) g x (vec4 (I := I) A B C D) -
        metricNabla2Ric (I := I) (M := M) g x (vec4 (I := I) A C B D) := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1
  have hderiv :
      hamiltonNablaPField (I := I) g x =
        metricNabla2Ric (I := I) (M := M) g x -
          (metricNabla2Ric (I := I) (M := M) g x).domDomCongr
            (frontExtendEquiv e) := by
    rw [hamiltonNablaPField, totalNabla0S_apply, hamiltonPField]
    change totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) (M := M) g)
        (metricNablaRic (I := I) (M := M) g -
          Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
            (metricNablaRic (I := I) (M := M) g)) x = _
    rw [sub_eq_add_neg]
    rw [show
      -Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
          (metricNablaRic (I := I) (M := M) g) =
        (-1 : Real) • Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e
          (metricNablaRic (I := I) (M := M) g) by simp]
    rw [totalNabla0SFun_add (I := I), totalNabla0SFun_smul (I := I),
      totalNabla0SFun_domDomCongr (I := I)]
    simp only [metricNabla2Ric, totalNabla0S_apply, neg_one_smul,
      sub_eq_add_neg]
  rw [hderiv, Tensor0SSpace.sub_apply, Tensor0SSpace.domDomCongr_apply]
  congr 1
  apply congrArg (metricNabla2Ric (I := I) (M := M) g x)
  funext q
  fin_cases q <;> rfl

private def hamiltonRicciSquareFieldPerm : Equiv.Perm (Fin 4) where
  toFun q := if q = 0 then 2 else if q = 1 then 0 else if q = 2 then 1 else 3
  invFun q := if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 0 else 3
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def hamiltonCurvatureRicciFieldPerm : Equiv.Perm (Fin 6) where
  toFun q :=
    if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 5 else if q = 4 then 1 else 3
  invFun q :=
    if q = 0 then 1 else if q = 1 then 4 else if q = 2 then 2 else
      if q = 3 then 5 else if q = 4 then 0 else 3
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private noncomputable def hamiltonRicciSquareField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) hamiltonRicciSquareFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRicci (I := I) (M := M) g)
        (metricRicci (I := I) (M := M) g)))

noncomputable def hamiltonCurvatureRicciField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        hamiltonCurvatureRicciFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g)
          (metricRicci (I := I) (M := M) g))))

private noncomputable def metricRicciTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
      (metricNabla2Ric (I := I) (M := M) g) +
    (2 : Real) • hamiltonCurvatureRicciField (I := I) g +
    (-2 : Real) • hamiltonRicciSquareField (I := I) g

private noncomputable def metricNablaRicciTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 (metricCov (I := I) (M := M) g)
    (metricRicciTimeDerivativeField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (metricRicciTimeDerivativeField (I := I) g))

private noncomputable def metricNablaRm04Field
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (metricCov (I := I) (M := M) g)
    (metricRm04 (I := I) (M := M) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g))

private noncomputable def metricNablaRoughRicciField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (traceNablaShuffle 2) (metricNabla3RicField (I := I) g))

private noncomputable def hamiltonRicciSquareProductNablaField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 2)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRic (I := I) (M := M) g)
        (metricRicci (I := I) (M := M) g)) +
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 2)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRicci (I := I) (M := M) g)
        (metricNablaRic (I := I) (M := M) g))

private noncomputable def hamiltonNablaRicciSquareField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 2)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv hamiltonRicciSquareFieldPerm)
        (hamiltonRicciSquareProductNablaField (I := I) g)))

private noncomputable def hamiltonCurvatureRicciProductNablaField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7 :=
  Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 4 2)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRm04Field (I := I) g)
        (metricRicci (I := I) (M := M) g)) +
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 4 2)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g)
        (metricNablaRic (I := I) (M := M) g))

private noncomputable def hamiltonCurvatureRicciInnerNablaField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 4)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv hamiltonCurvatureRicciFieldPerm)
        (hamiltonCurvatureRicciProductNablaField (I := I) g)))

private noncomputable def hamiltonNablaCurvatureRicciField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 2)
      (hamiltonCurvatureRicciInnerNablaField (I := I) g))

private theorem hamiltonNablaCurvatureRicciField_realizes
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (metricCov (I := I) (M := M) g)
      (hamiltonCurvatureRicciField (I := I) g)
      (hamiltonNablaCurvatureRicciField (I := I) g) := by
  let cov := metricCov (I := I) (M := M) g
  let Rm := metricRm04 (I := I) (M := M) g
  let nablaRm := metricNablaRm04Field (I := I) g
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := metricNablaRic (I := I) (M := M) g
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hRm : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov Rm nablaRm := by
    simpa [cov, Rm, nablaRm, metricNablaRm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov Rm
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Rm))
  have hRic : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric nablaRic := by
    simpa [cov, Ric, nablaRic, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Ric))
  have hProduct := nabla0S_product_realizes (I := I) cov
    Rm Ric nablaRm nablaRic hRm hRic
  have hPerm := totalNabla0SRealizes_domDomCongr (I := I) cov
    hamiltonCurvatureRicciFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) Rm Ric)
    (hamiltonCurvatureRicciProductNablaField (I := I) g)
    (by simpa [Rm, Ric, nablaRm, nablaRic,
      hamiltonCurvatureRicciProductNablaField] using hProduct)
  have hInner := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 4) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      hamiltonCurvatureRicciFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) Rm Ric))
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv hamiltonCurvatureRicciFieldPerm)
      (hamiltonCurvatureRicciProductNablaField (I := I) g)) hPerm
  have hOuter := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 2) cov g hmc
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        hamiltonCurvatureRicciFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) Rm Ric)))
    (hamiltonCurvatureRicciInnerNablaField (I := I) g)
    (by simpa [hamiltonCurvatureRicciInnerNablaField] using hInner)
  simpa [cov, Rm, Ric, hamiltonCurvatureRicciField,
    hamiltonNablaCurvatureRicciField] using hOuter

private noncomputable def metricNablaRicciTimeDerivativeExpandedField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricNablaRoughRicciField (I := I) g +
    (2 : Real) • hamiltonNablaCurvatureRicciField (I := I) g +
    (-2 : Real) • hamiltonNablaRicciSquareField (I := I) g

private def ricciFlowConnectionVariationFieldPerm : Equiv.Perm (Fin 3) where
  toFun q := if q = 0 then 2 else if q = 1 then 0 else 1
  invFun q := if q = 0 then 1 else if q = 1 then 2 else 0
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private noncomputable def ricciFlowConnectionVariationField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  (-1 : Real) • metricNablaRic (I := I) (M := M) g +
    (-1 : Real) • Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (Equiv.swap (0 : Fin 3) 1) (metricNablaRic (I := I) (M := M) g) +
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      ricciFlowConnectionVariationFieldPerm
      (metricNablaRic (I := I) (M := M) g)

private def connectionVariationRicciFirstFieldPerm : Equiv.Perm (Fin 5) where
  toFun q :=
    if q = 0 then 2 else if q = 1 then 4 else if q = 2 then 0 else
      if q = 3 then 1 else 3
  invFun q :=
    if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else
      if q = 3 then 4 else 1
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def connectionVariationRicciSecondFieldPerm : Equiv.Perm (Fin 5) where
  toFun q :=
    if q = 0 then 3 else if q = 1 then 4 else if q = 2 then 0 else
      if q = 3 then 1 else 2
  invFun q :=
    if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 4 else
      if q = 3 then 0 else 1
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private noncomputable def connectionVariationRicciFirstField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      connectionVariationRicciFirstFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (ricciFlowConnectionVariationField (I := I) g)
        (metricRicci (I := I) (M := M) g)))

private noncomputable def connectionVariationRicciSecondField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      connectionVariationRicciSecondFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (ricciFlowConnectionVariationField (I := I) g)
        (metricRicci (I := I) (M := M) g)))

private noncomputable def hamiltonPTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricNablaRicciTimeDerivativeField (I := I) g -
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (Equiv.swap (0 : Fin 3) 1)
      (metricNablaRicciTimeDerivativeField (I := I) g) -
    connectionVariationRicciFirstField (I := I) g +
    connectionVariationRicciSecondField (I := I) g

noncomputable def hamiltonNablaPTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (metricCov (I := I) (M := M) g)
    (hamiltonPTimeDerivativeField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (hamiltonPTimeDerivativeField (I := I) g))

theorem hamiltonNablaPField_realizes
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (metricCov (I := I) (M := M) g)
      (hamiltonPField (I := I) g) (hamiltonNablaPField (I := I) g) := by
  simpa [hamiltonNablaPField] using
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (metricCov (I := I) (M := M) g)
      (hamiltonPField (I := I) g)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g)
        (hamiltonPField (I := I) g)))

private theorem hamiltonNablaPTimeDerivativeField_realizes
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (metricCov (I := I) (M := M) g)
      (hamiltonPTimeDerivativeField (I := I) g)
      (hamiltonNablaPTimeDerivativeField (I := I) g) := by
  simpa [hamiltonNablaPTimeDerivativeField] using
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (metricCov (I := I) (M := M) g)
      (hamiltonPTimeDerivativeField (I := I) g)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g)
        (hamiltonPTimeDerivativeField (I := I) g)))

private noncomputable def metricNabla2RicciTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (metricCov (I := I) (M := M) g)
    (metricNablaRicciTimeDerivativeField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (metricNablaRicciTimeDerivativeField (I := I) g))

private noncomputable def metricNabla2Rm04Field
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (metricCov (I := I) (M := M) g)
    (metricNablaRm04Field (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (metricNablaRm04Field (I := I) g))

private noncomputable def hamiltonNabla2CurvatureRicciField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (metricCov (I := I) (M := M) g)
    (hamiltonNablaCurvatureRicciField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (hamiltonNablaCurvatureRicciField (I := I) g))

private noncomputable def hamiltonCurvatureRicciProductNabla2Field
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8 :=
  Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (leibnizLeftEquiv 4 2))
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 5 2)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNabla2Rm04Field (I := I) g)
            (metricRicci (I := I) (M := M) g)) +
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 5 2)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g)
            (metricNablaRic (I := I) (M := M) g))) +
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (leibnizRightEquiv 4 2))
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 4 3)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g)
            (metricNablaRic (I := I) (M := M) g)) +
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 4 3)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g)
            (metricNabla2Ric (I := I) (M := M) g)))

private noncomputable def hamiltonNabla2CurvatureRicciExpectedField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 3)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv (traceNablaShuffle 2))
        (metricTraceFirstTwoField (I := I) (M := M) g
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 5)
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
              (frontExtendEquiv (traceNablaShuffle 4))
              (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
                (frontExtendEquiv (frontExtendEquiv hamiltonCurvatureRicciFieldPerm))
                (hamiltonCurvatureRicciProductNabla2Field (I := I) g)))))))

noncomputable def hamiltonCurvatureRicciRoughLaplacianField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (hamiltonNabla2CurvatureRicciField (I := I) g)

private theorem hamiltonNabla2CurvatureRicciField_eq_expected
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    hamiltonNabla2CurvatureRicciField (I := I) g =
      hamiltonNabla2CurvatureRicciExpectedField (I := I) g := by
  let cov := metricCov (I := I) (M := M) g
  let R := metricRm04 (I := I) (M := M) g
  let RNabla := metricNablaRm04Field (I := I) g
  let RNabla2 := metricNabla2Rm04Field (I := I) g
  let Ric := metricRicci (I := I) (M := M) g
  let RicNabla := metricNablaRic (I := I) (M := M) g
  let RicNabla2 := metricNabla2Ric (I := I) (M := M) g
  let P := tensor0SFieldProduct (∞ : WithTop ℕ∞) R Ric
  let PNabla := hamiltonCurvatureRicciProductNablaField (I := I) g
  let PNabla2 := hamiltonCurvatureRicciProductNabla2Field (I := I) g
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hR : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov R RNabla := by
    simpa [cov, R, RNabla, metricNablaRm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov R
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) R))
  have hRNabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 cov RNabla RNabla2 := by
    simpa [cov, RNabla, RNabla2, metricNabla2Rm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5 cov RNabla
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) RNabla))
  have hRic : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric RicNabla := by
    simpa [cov, Ric, RicNabla, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Ric))
  have hRicNabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov RicNabla RicNabla2 := by
    simpa [cov, RicNabla, RicNabla2, metricNabla2Ric] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov RicNabla
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) RicNabla))
  have hP : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 6 cov P PNabla := by
    simpa [P, PNabla, R, RNabla, Ric, RicNabla,
      hamiltonCurvatureRicciProductNablaField] using
      nabla0S_product_realizes (I := I) cov R Ric RNabla RicNabla hR hRic
  let DLeft :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 5 2)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla2 Ric) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 5 2)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla RicNabla)
  let DRight :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla RicNabla) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R RicNabla2)
  have hLeftProduct : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla Ric) DLeft := by
    simpa [DLeft] using nabla0S_product_realizes (I := I) cov
      RNabla Ric RNabla2 RicNabla hRNabla hRic
  have hRightProduct : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) R RicNabla) DRight := by
    simpa [DRight] using nabla0S_product_realizes (I := I) cov
      R RicNabla RNabla RicNabla2 hR hRicNabla
  have hLeft := totalNabla0SRealizes_domDomCongr (I := I) cov
    (leibnizLeftEquiv 4 2)
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla Ric) DLeft hLeftProduct
  have hRight := totalNabla0SRealizes_domDomCongr (I := I) cov
    (leibnizRightEquiv 4 2)
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) R RicNabla) DRight hRightProduct
  have hPNabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov PNabla PNabla2 := by
    simpa [PNabla, PNabla2, DLeft, DRight, R, RNabla, RNabla2, Ric,
      RicNabla, RicNabla2, hamiltonCurvatureRicciProductNablaField,
      hamiltonCurvatureRicciProductNabla2Field] using
      TotalNabla0SRealizes.add hLeft hRight
  have hPerm := totalNabla0SRealizes_domDomCongr (I := I) cov
    (frontExtendEquiv hamiltonCurvatureRicciFieldPerm) PNabla PNabla2 hPNabla
  have hInnerPerm := totalNabla0SRealizes_domDomCongr (I := I) cov
    (traceNablaShuffle 4)
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv hamiltonCurvatureRicciFieldPerm) PNabla)
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (frontExtendEquiv hamiltonCurvatureRicciFieldPerm)) PNabla2)
    hPerm
  have hInner := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 5) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 4)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv hamiltonCurvatureRicciFieldPerm) PNabla))
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (traceNablaShuffle 4))
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (frontExtendEquiv (frontExtendEquiv hamiltonCurvatureRicciFieldPerm)) PNabla2))
    hInnerPerm
  have hOuterPerm := totalNabla0SRealizes_domDomCongr (I := I) cov
    (traceNablaShuffle 2)
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 4)
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (frontExtendEquiv hamiltonCurvatureRicciFieldPerm) PNabla)))
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 5)
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (frontExtendEquiv (traceNablaShuffle 4))
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
            (frontExtendEquiv (frontExtendEquiv hamiltonCurvatureRicciFieldPerm)) PNabla2))))
    hInner
  have hExpected := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 3) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 2)
      (metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 4)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
            (frontExtendEquiv hamiltonCurvatureRicciFieldPerm) PNabla))))
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (traceNablaShuffle 2))
      (metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 5)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
            (frontExtendEquiv (traceNablaShuffle 4))
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
              (frontExtendEquiv (frontExtendEquiv hamiltonCurvatureRicciFieldPerm))
              PNabla2)))))
    hOuterPerm
  have hCanonical : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov
      (hamiltonNablaCurvatureRicciField (I := I) g)
      (hamiltonNabla2CurvatureRicciField (I := I) g) := by
    simpa [cov, hamiltonNabla2CurvatureRicciField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov
        (hamiltonNablaCurvatureRicciField (I := I) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (metricCov_smooth (I := I) (M := M) g)
          (hamiltonNablaCurvatureRicciField (I := I) g)))
  have hExpected' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov
      (hamiltonNablaCurvatureRicciField (I := I) g)
      (hamiltonNabla2CurvatureRicciExpectedField (I := I) g) := by
    simpa [PNabla, PNabla2, hamiltonNablaCurvatureRicciField,
      hamiltonCurvatureRicciInnerNablaField,
      hamiltonNabla2CurvatureRicciExpectedField] using hExpected
  exact totalNabla0SRealizes_unique hCanonical hExpected'

private noncomputable def ricciFlowConnectionVariationNablaField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (metricCov (I := I) (M := M) g)
    (ricciFlowConnectionVariationField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (ricciFlowConnectionVariationField (I := I) g))

private def ricciPFirstFieldPerm : Equiv.Perm (Fin 5) where
  toFun q :=
    if q = 0 then 2 else if q = 1 then 0 else if q = 2 then 1 else
      if q = 3 then 3 else 4
  invFun q :=
    if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 0 else
      if q = 3 then 3 else 4
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def ricciPSecondFieldPerm : Equiv.Perm (Fin 5) where
  toFun q :=
    if q = 0 then 3 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 1 else 4
  invFun q :=
    if q = 0 then 1 else if q = 1 then 3 else if q = 2 then 2 else
      if q = 3 then 0 else 4
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def ricciPThirdFieldPerm : Equiv.Perm (Fin 5) where
  toFun q :=
    if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 3 else 1
  invFun q :=
    if q = 0 then 1 else if q = 1 then 4 else if q = 2 then 2 else
      if q = 3 then 3 else 0
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private noncomputable def ricciPContractionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 5)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRicci (I := I) (M := M) g)
        (hamiltonPField (I := I) g)))

private noncomputable def ricciPActionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  ricciPContractionField (I := I) g ricciPFirstFieldPerm +
    ricciPContractionField (I := I) g ricciPSecondFieldPerm +
    ricciPContractionField (I := I) g ricciPThirdFieldPerm

private noncomputable def hamiltonPRoughLaplacianField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (hamiltonNabla2PField (I := I) g)

noncomputable def hamiltonDivPRoughLaplacianField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (metricTraceFirstTwoField (I := I) (M := M) g
      (hamiltonNabla3PField (I := I) g))

noncomputable def hamiltonDivPField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (hamiltonNablaPField (I := I) g)

noncomputable def hamiltonMOriginField
    [T2Space M]
    (origin time : Real) (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  hamiltonDivPField (I := I) g + hamiltonCurvatureRicciField (I := I) g +
    (1 / (2 * (time - origin)) : Real) •
      metricRicci (I := I) (M := M) g

private def nablaRicPFirstFieldPerm : Equiv.Perm (Fin 6) where
  toFun q := if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else
    if q = 3 then 1 else if q = 4 then 4 else 5
  invFun q := if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else
    if q = 3 then 1 else if q = 4 then 4 else 5
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def nablaRicPSecondFieldPerm : Equiv.Perm (Fin 6) where
  toFun q := if q = 0 then 2 else if q = 1 then 4 else if q = 2 then 0 else
    if q = 3 then 3 else if q = 4 then 1 else 5
  invFun q := if q = 0 then 2 else if q = 1 then 4 else if q = 2 then 0 else
    if q = 3 then 3 else if q = 4 then 1 else 5
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def nablaRicPThirdFieldPerm : Equiv.Perm (Fin 6) where
  toFun q := if q = 0 then 2 else if q = 1 then 5 else if q = 2 then 0 else
    if q = 3 then 3 else if q = 4 then 4 else 1
  invFun q := if q = 0 then 2 else if q = 1 then 5 else if q = 2 then 0 else
    if q = 3 then 3 else if q = 4 then 4 else 1
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private noncomputable def nablaRicPContractionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 6)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRic (I := I) (M := M) g)
        (hamiltonPField (I := I) g)))

private noncomputable def nablaRicPActionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  nablaRicPContractionField (I := I) g nablaRicPFirstFieldPerm +
    nablaRicPContractionField (I := I) g nablaRicPSecondFieldPerm +
    nablaRicPContractionField (I := I) g nablaRicPThirdFieldPerm

private def ricciNablaPFirstFieldPerm : Equiv.Perm (Fin 6) where
  toFun q := if q = 0 then 3 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 1 else if q = 4 then 4 else 5
  invFun q := if q = 0 then 1 else if q = 1 then 3 else if q = 2 then 2 else
    if q = 3 then 0 else if q = 4 then 4 else 5
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def ricciNablaPSecondFieldPerm : Equiv.Perm (Fin 6) where
  toFun q := if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 3 else if q = 4 then 1 else 5
  invFun q := if q = 0 then 1 else if q = 1 then 4 else if q = 2 then 2 else
    if q = 3 then 3 else if q = 4 then 0 else 5
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def ricciNablaPThirdFieldPerm : Equiv.Perm (Fin 6) where
  toFun q := if q = 0 then 5 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 3 else if q = 4 then 4 else 1
  invFun q := if q = 0 then 1 else if q = 1 then 5 else if q = 2 then 2 else
    if q = 3 then 3 else if q = 4 then 4 else 0
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private noncomputable def quadTraceProductField
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 8))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A))

private theorem metricTraceFirstTwoField_apply_orthonormal_pre
    {n q : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 2))
    (tail : Fin q -> TangentSpace I x) :
    metricTraceFirstTwoField (I := I) (M := M) g A x tail =
      ∑ i : Fin n,
        A x (metricTraceInput (I := I) (basis i) (basis i) tail) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
  unfold metricTrace0S2InBasis
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem quadTraceProductField_apply_orthonormal
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (perm : Equiv.Perm (Fin 8))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8)
    (tail : Fin 4 -> TangentSpace I x) :
    quadTraceProductField (I := I) g perm A x tail =
      ∑ i : Fin n, ∑ j : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A) x
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i) tail)) := by
  rw [quadTraceProductField,
    metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]

private def nablaRPFourthFirstPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 4 else if q = 1 then 5 else if q = 2 then 0 else
    if q = 3 then 2 else if q = 4 then 6 else if q = 5 then 1 else
      if q = 6 then 3 else 7
  invFun q := if q = 0 then 2 else if q = 1 then 5 else if q = 2 then 3 else
    if q = 3 then 6 else if q = 4 then 0 else if q = 5 then 1 else
      if q = 6 then 4 else 7
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def RnablaPFourthFirstPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 5 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 6 else if q = 4 then 4 else if q = 5 then 1 else
      if q = 6 then 3 else 7
  invFun q := if q = 0 then 1 else if q = 1 then 5 else if q = 2 then 2 else
    if q = 3 then 6 else if q = 4 then 4 else if q = 5 then 0 else
      if q = 6 then 3 else 7
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def nablaRPFourthSecondPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 4 else if q = 1 then 5 else if q = 2 then 0 else
    if q = 3 then 2 else if q = 4 then 7 else if q = 5 then 1 else
      if q = 6 then 6 else 3
  invFun q := if q = 0 then 2 else if q = 1 then 5 else if q = 2 then 3 else
    if q = 3 then 7 else if q = 4 then 0 else if q = 5 then 1 else
      if q = 6 then 6 else 4
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def RnablaPFourthSecondPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 5 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 7 else if q = 4 then 4 else if q = 5 then 1 else
      if q = 6 then 6 else 3
  invFun q := if q = 0 then 1 else if q = 1 then 5 else if q = 2 then 2 else
    if q = 3 then 7 else if q = 4 then 4 else if q = 5 then 0 else
      if q = 6 then 6 else 3
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def nablaRPFourthThirdPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 4 else if q = 1 then 6 else if q = 2 then 0 else
    if q = 3 then 2 else if q = 4 then 7 else if q = 5 then 5 else
      if q = 6 then 1 else 3
  invFun q := if q = 0 then 2 else if q = 1 then 6 else if q = 2 then 3 else
    if q = 3 then 7 else if q = 4 then 0 else if q = 5 then 5 else
      if q = 6 then 1 else 4
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def RnablaPFourthThirdPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 6 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 7 else if q = 4 then 4 else if q = 5 then 5 else
      if q = 6 then 1 else 3
  invFun q := if q = 0 then 1 else if q = 1 then 6 else if q = 2 then 2 else
    if q = 3 then 7 else if q = 4 then 4 else if q = 5 then 5 else
      if q = 6 then 0 else 3
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def nablaRicNablaRmFourthPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
    if q = 3 then 1 else if q = 4 then 5 else if q = 5 then 6 else
      if q = 6 then 3 else 7
  invFun q := if q = 0 then 1 else if q = 1 then 3 else if q = 2 then 2 else
    if q = 3 then 6 else if q = 4 then 0 else if q = 5 then 4 else
      if q = 6 then 5 else 7
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private def ricciNabla2RmFourthPerm : Equiv.Perm (Fin 8) where
  toFun q := if q = 0 then 0 else if q = 1 then 2 else if q = 2 then 4 else
    if q = 3 then 1 else if q = 4 then 5 else if q = 5 then 6 else
      if q = 6 then 3 else 7
  invFun q := if q = 0 then 0 else if q = 1 then 3 else if q = 2 then 1 else
    if q = 3 then 6 else if q = 4 then 2 else if q = 5 then 4 else
      if q = 6 then 5 else 7
  left_inv q := by fin_cases q <;> simp
  right_inv q := by fin_cases q <;> simp

private noncomputable def hamiltonNablaPEvolutionReactionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  (2 : Real) • quadTraceProductField (I := I) g nablaRPFourthFirstPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) +
    (2 : Real) • quadTraceProductField (I := I) g RnablaPFourthFirstPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g)
        (hamiltonNablaPField (I := I) g)) +
    (2 : Real) • quadTraceProductField (I := I) g nablaRPFourthSecondPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) +
    (2 : Real) • quadTraceProductField (I := I) g RnablaPFourthSecondPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g)
        (hamiltonNablaPField (I := I) g)) +
    (2 : Real) • quadTraceProductField (I := I) g nablaRPFourthThirdPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) +
    (2 : Real) • quadTraceProductField (I := I) g RnablaPFourthThirdPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g)
        (hamiltonNablaPField (I := I) g)) -
    (2 : Real) • quadTraceProductField (I := I) g nablaRicNablaRmFourthPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricNablaRic (I := I) (M := M) g)
        (metricNablaRm04Field (I := I) g)) -
    (2 : Real) • quadTraceProductField (I := I) g ricciNabla2RmFourthPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRicci (I := I) (M := M) g)
        (metricNabla2Rm04Field (I := I) g))

private noncomputable def ricciNablaPContractionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 6)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRicci (I := I) (M := M) g)
        (hamiltonNablaPField (I := I) g)))

private noncomputable def ricciNablaPActionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  ricciNablaPContractionField (I := I) g ricciNablaPFirstFieldPerm +
    ricciNablaPContractionField (I := I) g ricciNablaPSecondFieldPerm +
    ricciNablaPContractionField (I := I) g ricciNablaPThirdFieldPerm

private noncomputable def hamiltonNablaPHeatField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  hamiltonNablaPTimeDerivativeField (I := I) g +
    nablaRicPActionField (I := I) g + ricciNablaPActionField (I := I) g -
    metricTraceFirstTwoField (I := I) (M := M) g
      (hamiltonNabla3PField (I := I) g)

private noncomputable def hamiltonNabla2PExpectedField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  metricNabla3RicField (I := I) g -
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv (Equiv.swap (1 : Fin 4) 2))
      (metricNabla3RicField (I := I) g)

private theorem hamiltonNabla2PField_eq_expected
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    hamiltonNabla2PField (I := I) g =
      hamiltonNabla2PExpectedField (I := I) g := by
  let cov := metricCov (I := I) (M := M) g
  have hP2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov (hamiltonNablaPField (I := I) g)
      (hamiltonNabla2PField (I := I) g) := by
    simpa [cov, hamiltonNabla2PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov (hamiltonNablaPField (I := I) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (metricCov_smooth (I := I) (M := M) g)
          (hamiltonNablaPField (I := I) g)))
  have hRic3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov (metricNabla2Ric (I := I) (M := M) g)
      (metricNabla3RicField (I := I) g) := by
    simpa [cov, metricNabla3RicField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov
        (metricNabla2Ric (I := I) (M := M) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (metricCov_smooth (I := I) (M := M) g)
          (metricNabla2Ric (I := I) (M := M) g)))
  have hPbase :
      hamiltonNablaPField (I := I) g =
        metricNabla2Ric (I := I) (M := M) g -
          Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
            (Equiv.swap (1 : Fin 4) 2)
            (metricNabla2Ric (I := I) (M := M) g) := by
    apply DFunLike.ext _ _
    intro x
    apply tensor0SSpace_ext (I := I) 4 x
    intro v
    have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
      funext i
      fin_cases i <;> rfl
    rw [hv, hamiltonNablaPField_apply]
    change _ =
      (metricNabla2Ric (I := I) (M := M) g x -
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (Equiv.swap (1 : Fin 4) 2)
          (metricNabla2Ric (I := I) (M := M) g)) x) _
    rw [Tensor0SSpace.sub_apply, Tensor0SField.domDomCongr_apply,
      Tensor0SSpace.domDomCongr_apply]
    congr 1
    apply congrArg (metricNabla2Ric (I := I) (M := M) g x)
    funext q
    fin_cases q <;> rfl
  have hswap := totalNabla0SRealizes_domDomCongr (I := I) cov
      (Equiv.swap (1 : Fin 4) 2)
      (metricNabla2Ric (I := I) (M := M) g)
      (metricNabla3RicField (I := I) g) hRic3
  have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) hswap
  have hP2' := TotalNabla0SRealizes.add hRic3 hneg
  have hP2'' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov (hamiltonNablaPField (I := I) g)
      (hamiltonNabla2PExpectedField (I := I) g) := by
    rw [hPbase]
    simpa only [hamiltonNabla2PExpectedField, neg_one_smul, sub_eq_add_neg] using hP2'
  exact totalNabla0SRealizes_unique hP2 hP2''

private noncomputable def hamiltonPHeatField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  hamiltonPTimeDerivativeField (I := I) g + ricciPActionField (I := I) g -
    hamiltonPRoughLaplacianField (I := I) g

private def curvaturePFirstFieldPerm : Equiv.Perm (Fin 7) where
  toFun q :=
    if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 5 else if q = 4 then 1 else if q = 5 then 3 else 6
  invFun q :=
    if q = 0 then 1 else if q = 1 then 4 else if q = 2 then 2 else
      if q = 3 then 5 else if q = 4 then 0 else if q = 5 then 3 else 6
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def curvaturePSecondFieldPerm : Equiv.Perm (Fin 7) where
  toFun q :=
    if q = 0 then 4 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 6 else if q = 4 then 1 else if q = 5 then 5 else 3
  invFun q :=
    if q = 0 then 1 else if q = 1 then 4 else if q = 2 then 2 else
      if q = 3 then 6 else if q = 4 then 0 else if q = 5 then 5 else 3
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def curvaturePThirdFieldPerm : Equiv.Perm (Fin 7) where
  toFun q :=
    if q = 0 then 5 else if q = 1 then 0 else if q = 2 then 2 else
      if q = 3 then 6 else if q = 4 then 4 else if q = 5 then 1 else 3
  invFun q :=
    if q = 0 then 1 else if q = 1 then 5 else if q = 2 then 2 else
      if q = 3 then 6 else if q = 4 then 4 else if q = 5 then 0 else 3
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def ricciNablaRmFieldPerm : Equiv.Perm (Fin 7) where
  toFun q :=
    if q = 0 then 0 else if q = 1 then 2 else if q = 2 then 1 else
      if q = 3 then 4 else if q = 4 then 5 else if q = 5 then 3 else 6
  invFun q :=
    if q = 0 then 0 else if q = 1 then 2 else if q = 2 then 1 else
      if q = 3 then 5 else if q = 4 then 3 else if q = 5 then 4 else 6
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private noncomputable def doubleTraceProductField
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 7))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A))

private noncomputable def hamiltonPEvolutionReactionField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  (2 : Real) • doubleTraceProductField (I := I) g curvaturePFirstFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g)) +
    (2 : Real) • doubleTraceProductField (I := I) g curvaturePSecondFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g)) +
    (2 : Real) • doubleTraceProductField (I := I) g curvaturePThirdFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g)) +
    (-2 : Real) • doubleTraceProductField (I := I) g ricciNablaRmFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (metricRicci (I := I) (M := M) g)
        (metricNablaRm04Field (I := I) g))

private theorem metricTraceFirstTwoField_apply_orthonormal
    {n q : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 2))
    (tail : Fin q -> TangentSpace I x) :
    metricTraceFirstTwoField (I := I) (M := M) g A x tail =
      ∑ i : Fin n,
        A x (metricTraceInput (I := I) (basis i) (basis i) tail) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
  unfold metricTrace0S2InBasis
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem hamiltonCurvatureRicciRoughLaplacianField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonCurvatureRicciRoughLaplacianField (I := I) g x
        (vec2 (I := I) (basis a) (basis b)) =
      ∑ c : Fin n, ∑ d : Fin n,
        ((∑ e : Fin n,
            metricNabla2Rm04Field (I := I) g x
              (vec6 (I := I) (basis e) (basis e)
                (basis a) (basis c) (basis d) (basis b))) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis c) (basis d)) +
          metricRm04 (I := I) (M := M) g x
              (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) *
            (∑ e : Fin n,
              metricNabla2Ric (I := I) (M := M) g x
                (vec4 (I := I) (basis e) (basis e) (basis c) (basis d))) +
          2 * ∑ e : Fin n,
            metricNablaRm04Field (I := I) g x
                (vec5 (I := I) (basis e)
                  (basis a) (basis c) (basis d) (basis b)) *
              metricNablaRic (I := I) (M := M) g x
                (vec3 (I := I) (basis e) (basis c) (basis d))) := by
  rw [hamiltonCurvatureRicciRoughLaplacianField,
    hamiltonNabla2CurvatureRicciField_eq_expected (I := I) g]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  simp only [hamiltonNabla2CurvatureRicciExpectedField]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  let slots : Fin n -> Fin n -> Fin n -> Fin 8 -> TangentSpace I x :=
    fun e d c i =>
      metricTraceInput (I := I) (basis c) (basis c)
        (fun i =>
          metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec2 (I := I) (basis a) (basis b)))
            (traceNablaShuffle 3 (frontExtendEquiv (traceNablaShuffle 2) i)))
        (traceNablaShuffle 5
          (frontExtendEquiv (traceNablaShuffle 4)
            (frontExtendEquiv (frontExtendEquiv hamiltonCurvatureRicciFieldPerm) i)))
  change (∑ e : Fin n, ∑ d : Fin n, ∑ c : Fin n,
      hamiltonCurvatureRicciProductNabla2Field (I := I) g x (slots e d c)) = _
  have hslots (e d c : Fin n) :
      slots e d c =
        Fin.cons (basis e)
          (Fin.cons (basis e)
            (vec6 (I := I) (basis a) (basis c) (basis d)
              (basis b) (basis c) (basis d))) := by
    funext i
    fin_cases i <;> rfl
  conv_lhs =>
    enter [2, e]
    enter [2, d]
    enter [2, c]
    rw [hslots e d c]
  simp only [hamiltonCurvatureRicciProductNabla2Field,
    ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  let V : Fin n -> Fin n -> Fin n -> Fin 8 -> TangentSpace I x :=
    fun e d c =>
      Fin.cons (basis e)
        (Fin.cons (basis e)
          (vec6 (I := I) (basis a) (basis c) (basis d)
            (basis b) (basis c) (basis d)))
  have hR2 (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizLeftEquiv 4 2) (leibnizLeftEquiv 5 2 i))) ∘
        Fin.castAdd 2) =
      vec6 (I := I) (basis e) (basis e)
        (basis a) (basis c) (basis d) (basis b) := by
    funext i
    fin_cases i <;> rfl
  have hRic0 (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizLeftEquiv 4 2) (leibnizLeftEquiv 5 2 i))) ∘
        Fin.natAdd (5 + 1)) = vec2 (I := I) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  have hR1Left (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizLeftEquiv 4 2) (leibnizRightEquiv 5 2 i))) ∘
        Fin.castAdd (2 + 1)) =
      vec5 (I := I) (basis e) (basis a) (basis c) (basis d) (basis b) := by
    funext i
    fin_cases i <;> rfl
  have hRic1Left (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizLeftEquiv 4 2) (leibnizRightEquiv 5 2 i))) ∘
        Fin.natAdd 5) =
      vec3 (I := I) (basis e) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  have hR1Right (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizRightEquiv 4 2) (leibnizLeftEquiv 4 3 i))) ∘
        Fin.castAdd 3) =
      vec5 (I := I) (basis e) (basis a) (basis c) (basis d) (basis b) := by
    funext i
    fin_cases i <;> rfl
  have hRic1Right (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizRightEquiv 4 2) (leibnizLeftEquiv 4 3 i))) ∘
        Fin.natAdd (4 + 1)) =
      vec3 (I := I) (basis e) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  have hR0 (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizRightEquiv 4 2) (leibnizRightEquiv 4 3 i))) ∘
        Fin.castAdd (3 + 1)) =
      vec4 (I := I) (basis a) (basis c) (basis d) (basis b) := by
    funext i
    fin_cases i <;> rfl
  have hRic2 (e d c : Fin n) :
      ((fun i => V e d c
          (frontExtendEquiv (leibnizRightEquiv 4 2) (leibnizRightEquiv 4 3 i))) ∘
        Fin.natAdd 4) =
      vec4 (I := I) (basis e) (basis e) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  change (∑ e : Fin n, ∑ d : Fin n, ∑ c : Fin n,
      (((metricNabla2Rm04Field (I := I) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizLeftEquiv 4 2)
                (leibnizLeftEquiv 5 2 i))) ∘ Fin.castAdd 2)) *
          (metricRicci (I := I) (M := M) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizLeftEquiv 4 2)
                (leibnizLeftEquiv 5 2 i))) ∘ Fin.natAdd (5 + 1))) +
        (metricNablaRm04Field (I := I) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizLeftEquiv 4 2)
                (leibnizRightEquiv 5 2 i))) ∘ Fin.castAdd (2 + 1))) *
          (metricNablaRic (I := I) (M := M) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizLeftEquiv 4 2)
                (leibnizRightEquiv 5 2 i))) ∘ Fin.natAdd 5))) +
      (((metricNablaRm04Field (I := I) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizRightEquiv 4 2)
                (leibnizLeftEquiv 4 3 i))) ∘ Fin.castAdd 3)) *
          (metricNablaRic (I := I) (M := M) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizRightEquiv 4 2)
                (leibnizLeftEquiv 4 3 i))) ∘ Fin.natAdd (4 + 1))) +
        (metricRm04 (I := I) (M := M) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizRightEquiv 4 2)
                (leibnizRightEquiv 4 3 i))) ∘ Fin.castAdd (3 + 1))) *
          (metricNabla2Ric (I := I) (M := M) g x)
            (((fun i => V e d c
              (frontExtendEquiv (leibnizRightEquiv 4 2)
                (leibnizRightEquiv 4 3 i))) ∘ Fin.natAdd 4)))))) = _
  simp_rw [hR2, hRic0, hR1Left, hRic1Left,
    hR1Right, hRic1Right, hR0, hRic2]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, d]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

private theorem doubleTraceProductField_apply_orthonormal
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (perm : Equiv.Perm (Fin 7))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7)
    (tail : Fin 3 -> TangentSpace I x) :
    doubleTraceProductField (I := I) g perm A x tail =
      ∑ i : Fin n, ∑ j : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A) x
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i) tail)) := by
  rw [doubleTraceProductField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]


private theorem ricciFlowConnectionVariationField_apply
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : TangentSpace I x) :
    ricciFlowConnectionVariationField (I := I) g x
        (vec3 (I := I) A B C) =
      -metricNablaRic (I := I) (M := M) g x (vec3 (I := I) A B C) -
        metricNablaRic (I := I) (M := M) g x (vec3 (I := I) B A C) +
        metricNablaRic (I := I) (M := M) g x (vec3 (I := I) C A B) := by
  rw [ricciFlowConnectionVariationField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul, neg_one_mul,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  have hswap :
      (fun q => vec3 (I := I) A B C ((Equiv.swap (0 : Fin 3) 1) q)) =
        vec3 (I := I) B A C := by
    funext q
    fin_cases q <;> rfl
  have hperm :
      (fun q => vec3 (I := I) A B C (ricciFlowConnectionVariationFieldPerm q)) =
        vec3 (I := I) C A B := by
    funext q
    fin_cases q <;> rfl
  rw [hswap, hperm]
  ring

private theorem connectionVariationRicciFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    connectionVariationRicciFirstField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        ricciFlowConnectionVariationField (I := I) g x
            (vec3 (I := I) (basis a) (basis c) (basis p)) *
          metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis p) (basis b)) := by
  classical
  rw [connectionVariationRicciFirstField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext q
    fin_cases q <;> rfl
  · funext q
    fin_cases q <;> rfl

private theorem connectionVariationRicciSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    connectionVariationRicciSecondField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        ricciFlowConnectionVariationField (I := I) g x
            (vec3 (I := I) (basis b) (basis c) (basis p)) *
          metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis p) (basis a)) := by
  classical
  rw [connectionVariationRicciSecondField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext q
    fin_cases q <;> rfl
  · funext q
    fin_cases q <;> rfl

private theorem hamiltonPTimeDerivativeField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPTimeDerivativeField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      metricNablaRicciTimeDerivativeField (I := I) g x
          (vec3 (I := I) (basis a) (basis b) (basis c)) -
        metricNablaRicciTimeDerivativeField (I := I) g x
          (vec3 (I := I) (basis b) (basis a) (basis c)) -
        ∑ p : Fin n,
          ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) (basis a) (basis c) (basis p)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis p) (basis b)) +
        ∑ p : Fin n,
          ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) (basis b) (basis c) (basis p)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis p) (basis a)) := by
  rw [hamiltonPTimeDerivativeField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_sub,
    Pi.sub_apply, Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  rw [connectionVariationRicciFirstField_apply_orthonormal
    (I := I) g basis horth,
    connectionVariationRicciSecondField_apply_orthonormal
      (I := I) g basis horth]
  have hswap :
      (fun q => vec3 (I := I) (basis a) (basis b) (basis c)
        ((Equiv.swap (0 : Fin 3) 1) q)) =
        vec3 (I := I) (basis b) (basis a) (basis c) := by
    funext q
    fin_cases q <;> rfl
  rw [hswap]

private theorem nablaRicPFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    nablaRicPContractionField (I := I) g nablaRicPFirstFieldPerm x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis a) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis p) (basis b) (basis c)) := by
  classical
  rw [nablaRicPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl

private theorem nablaRicPSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    nablaRicPContractionField (I := I) g nablaRicPSecondFieldPerm x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis b) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis p) (basis c)) := by
  classical
  rw [nablaRicPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl

private theorem nablaRicPThirdField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    nablaRicPContractionField (I := I) g nablaRicPThirdFieldPerm x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis c) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis b) (basis p)) := by
  classical
  rw [nablaRicPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl

private theorem nablaRicPActionField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    nablaRicPActionField (I := I) g x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      (∑ p : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis a) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis p) (basis b) (basis c))) +
      (∑ p : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis b) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis p) (basis c))) +
      ∑ p : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis c) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis b) (basis p)) := by
  rw [nablaRicPActionField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
  rw [nablaRicPFirstField_apply_orthonormal (I := I) g basis horth,
    nablaRicPSecondField_apply_orthonormal (I := I) g basis horth,
    nablaRicPThirdField_apply_orthonormal (I := I) g basis horth]

private theorem ricciNablaPFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    ricciNablaPContractionField (I := I) g ricciNablaPFirstFieldPerm x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis a) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis p) (basis b) (basis c)) := by
  classical
  rw [ricciNablaPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl

private theorem ricciNablaPSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    ricciNablaPContractionField (I := I) g ricciNablaPSecondFieldPerm x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis b) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis p) (basis c)) := by
  classical
  rw [ricciNablaPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl

private theorem ricciNablaPThirdField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    ricciNablaPContractionField (I := I) g ricciNablaPThirdFieldPerm x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis c) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis b) (basis p)) := by
  classical
  rw [ricciNablaPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl

private theorem ricciNablaPActionField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    ricciNablaPActionField (I := I) g x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      (∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis a) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis p) (basis b) (basis c))) +
      (∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis b) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis p) (basis c))) +
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis c) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis b) (basis p)) := by
  rw [ricciNablaPActionField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
  rw [ricciNablaPFirstField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPSecondField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPThirdField_apply_orthonormal (I := I) g basis horth]

private theorem hamiltonPRoughLaplacianField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPRoughLaplacianField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n,
        hamiltonNabla2PField (I := I) g x
          (vec5 (I := I) (basis d) (basis d) (basis a) (basis b) (basis c)) := by
  rw [hamiltonPRoughLaplacianField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  funext q
  fin_cases q <;> rfl

private theorem hamiltonDivPRoughLaplacianField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPRoughLaplacianField (I := I) g x
        (vec2 (I := I) (basis a) (basis b)) =
      ∑ c : Fin n,
        roughLaplacianCovariantDerivativeComponents
          (fun i j k slots => hamiltonNabla3PField (I := I) g x
            (Fin.cons (basis i)
              (vec5 (I := I) (basis j) (basis k)
                (basis (slots 0)) (basis (slots 1)) (basis (slots 2)))))
          c (fun r : Fin 3 => if r = 0 then c else if r = 1 then a else b) := by
  rw [hamiltonDivPRoughLaplacianField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth,
    roughLaplacianCovariantDerivativeComponents]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  funext r
  fin_cases r <;> rfl

private theorem hamiltonNablaPHeatField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    hamiltonNablaPHeatField (I := I) g x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      hamiltonNablaPTimeDerivativeField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) +
        nablaRicPActionField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) +
        ricciNablaPActionField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) -
        ∑ d : Fin n,
          hamiltonNabla3PField (I := I) g x
            (Fin.cons (basis d) (Fin.cons (basis d)
              (Fin.cons (basis q) (Fin.cons (basis a)
                (Fin.cons (basis b) (fun _ : Fin 1 => basis c)))))) := by
  rw [hamiltonNablaPHeatField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_sub,
    Pi.sub_apply, Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply]
  rw [metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine congrArg (fun z =>
      hamiltonNablaPTimeDerivativeField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) +
        nablaRicPActionField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) +
        ricciNablaPActionField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) - z) ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  funext r
  fin_cases r <;> rfl

private theorem nablaRPFourthFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g nablaRPFourthFirstPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis e) (basis c)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRPFourthFirstPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis e) (basis c)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [nablaRPFourthFirstPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec4, vec5, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [nablaRPFourthFirstPerm, Fin.natAdd,
          metricTraceInput_apply, vec3, vec4, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRPFourthFirstPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis e) (basis c)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem nablaRPFourthSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g nablaRPFourthSecondPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis b) (basis e)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRPFourthSecondPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis b) (basis e)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [nablaRPFourthSecondPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec4, vec5, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [nablaRPFourthSecondPerm, Fin.natAdd,
          metricTraceInput_apply, vec3, vec4, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRPFourthSecondPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis b) (basis e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem nablaRPFourthThirdField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g nablaRPFourthThirdPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis d) (basis e)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRPFourthThirdPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis d) (basis e)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [nablaRPFourthThirdPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec4, vec5, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [nablaRPFourthThirdPerm, Fin.natAdd,
          metricTraceInput_apply, vec3, vec4, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRPFourthThirdPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis q) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis d) (basis e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem RnablaPFourthFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g RnablaPFourthFirstPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis d) (basis e) (basis c)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) RnablaPFourthFirstPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis d) (basis e) (basis c)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [RnablaPFourthFirstPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec4, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [RnablaPFourthFirstPerm, Fin.natAdd,
          metricTraceInput_apply, vec4, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) RnablaPFourthFirstPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis d) (basis e) (basis c)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem RnablaPFourthSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g RnablaPFourthSecondPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis d) (basis b) (basis e)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) RnablaPFourthSecondPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis d) (basis b) (basis e)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [RnablaPFourthSecondPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec4, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [RnablaPFourthSecondPerm, Fin.natAdd,
          metricTraceInput_apply, vec4, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) RnablaPFourthSecondPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis d) (basis b) (basis e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem RnablaPFourthThirdField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g RnablaPFourthThirdPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis d) (basis e)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) RnablaPFourthThirdPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis d) (basis e)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [RnablaPFourthThirdPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec4, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [RnablaPFourthThirdPerm, Fin.natAdd,
          metricTraceInput_apply, vec4, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) RnablaPFourthThirdPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonNablaPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis q) (basis a) (basis d) (basis e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem nablaRicNablaRmFourthField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g nablaRicNablaRmFourthPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRic (I := I) (M := M) g)
          (metricNablaRm04Field (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis d) (basis e)) *
          metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRicNablaRmFourthPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricNablaRic (I := I) (M := M) g)
          (metricNablaRm04Field (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis d) (basis e)) *
          metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [nablaRicNablaRmFourthPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec3, vec4, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [nablaRicNablaRmFourthPerm, Fin.natAdd,
          metricTraceInput_apply, vec4, vec5, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) nablaRicNablaRmFourthPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRic (I := I) (M := M) g)
            (metricNablaRm04Field (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis q) (basis d) (basis e)) *
          metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem ricciNabla2RmFourthField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    quadTraceProductField (I := I) g ricciNabla2RmFourthPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRicci (I := I) (M := M) g)
          (metricNabla2Rm04Field (I := I) g)) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis d) (basis e)) *
          metricNabla2Rm04Field (I := I) g x
            (vec6 (I := I) (basis q) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
  classical
  rw [quadTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) ricciNabla2RmFourthPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRicci (I := I) (M := M) g)
          (metricNabla2Rm04Field (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)))) =
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis d) (basis e)) *
          metricNabla2Rm04Field (I := I) g x
            (vec6 (I := I) (basis q) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext r
      fin_cases r <;>
        simp [ricciNabla2RmFourthPerm, Fin.castAdd, Fin.castLE,
          metricTraceInput_apply, vec2, vec4, Function.comp_apply]
    · funext r
      fin_cases r <;>
        simp [ricciNabla2RmFourthPerm, Fin.natAdd,
          metricTraceInput_apply, vec4, vec6, Function.comp_apply]
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) ricciNabla2RmFourthPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRicci (I := I) (M := M) g)
            (metricNabla2Rm04Field (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis d) (basis e)) *
          metricNabla2Rm04Field (I := I) g x
            (vec6 (I := I) (basis q) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem hamiltonPHeatField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPHeatField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      hamiltonPTimeDerivativeField (I := I) g x
          (vec3 (I := I) (basis a) (basis b) (basis c)) +
        ricciPActionField (I := I) g x
          (vec3 (I := I) (basis a) (basis b) (basis c)) -
        ∑ d : Fin n,
          hamiltonNabla2PField (I := I) g x
            (vec5 (I := I) (basis d) (basis d) (basis a) (basis b) (basis c)) := by
  rw [hamiltonPHeatField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_sub,
    Pi.sub_apply, Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply]
  rw [hamiltonPRoughLaplacianField_apply_orthonormal (I := I) g basis horth]

private theorem ricciPFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    ricciPContractionField (I := I) g ricciPFirstFieldPerm x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis a) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis p) (basis b) (basis c)) := by
  classical
  rw [ricciPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext q
    fin_cases q <;> rfl
  · funext q
    fin_cases q <;> rfl

private theorem ricciPSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    ricciPContractionField (I := I) g ricciPSecondFieldPerm x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis b) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis p) (basis c)) := by
  classical
  rw [ricciPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext q
    fin_cases q <;> rfl
  · funext q
    fin_cases q <;> rfl

private theorem ricciPThirdField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    ricciPContractionField (I := I) g ricciPThirdFieldPerm x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis c) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis b) (basis p)) := by
  classical
  rw [ricciPContractionField,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 2
  · funext q
    fin_cases q <;> rfl
  · funext q
    fin_cases q <;> rfl

private theorem ricciPActionField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    ricciPActionField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      (∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis a) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis p) (basis b) (basis c))) +
        (∑ p : Fin n,
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis b) (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) (basis a) (basis p) (basis c))) +
        ∑ p : Fin n,
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis c) (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) (basis a) (basis b) (basis p)) := by
  rw [ricciPActionField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply]
  rw [ricciPFirstField_apply_orthonormal (I := I) g basis horth,
    ricciPSecondField_apply_orthonormal (I := I) g basis horth,
    ricciPThirdField_apply_orthonormal (I := I) g basis horth]

private theorem curvaturePFirstField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    doubleTraceProductField (I := I) g curvaturePFirstFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g)) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis e) (basis c)) := by
  classical
  rw [doubleTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvaturePFirstFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c)))) =
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis e) (basis c)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext q
      fin_cases q <;> rfl
    · funext q
      fin_cases q <;> rfl
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvaturePFirstFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis b)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis e) (basis c)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem curvaturePSecondField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    doubleTraceProductField (I := I) g curvaturePSecondFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g)) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis b) (basis e)) := by
  classical
  rw [doubleTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvaturePSecondFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c)))) =
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis b) (basis e)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext q
      fin_cases q <;> rfl
    · funext q
      fin_cases q <;> rfl
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvaturePSecondFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis a) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis d) (basis b) (basis e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem curvaturePThirdField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    doubleTraceProductField (I := I) g curvaturePThirdFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g)) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis d) (basis e)) := by
  classical
  rw [doubleTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvaturePThirdFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c)))) =
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis d) (basis e)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext q
      fin_cases q <;> rfl
    · funext q
      fin_cases q <;> rfl
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvaturePThirdFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis a) (basis d) (basis e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem ricciNablaRmField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    doubleTraceProductField (I := I) g ricciNablaRmFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRicci (I := I) (M := M) g)
          (metricNablaRm04Field (I := I) g)) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis d) (basis e)) *
          metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
  classical
  rw [doubleTraceProductField_apply_orthonormal (I := I) g basis horth]
  have heval : forall e d : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) ricciNablaRmFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞)
          (metricRicci (I := I) (M := M) g)
          (metricNablaRm04Field (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c)))) =
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis d) (basis e)) *
          metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
    intro e d
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      tensor0SField_product_apply]
    congr 2
    · funext q
      fin_cases q <;> rfl
    · funext q
      fin_cases q <;> rfl
  calc
    (∑ e : Fin n, ∑ d : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) ricciNablaRmFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRicci (I := I) (M := M) g)
            (metricNablaRm04Field (I := I) g))) x
          (metricTraceInput (I := I) (basis d) (basis d)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec3 (I := I) (basis a) (basis b) (basis c))))) =
      ∑ e : Fin n, ∑ d : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis d) (basis e)) *
          metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis d) (basis a) (basis b) (basis e) (basis c)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => heval e d
    _ = _ := Finset.sum_comm

private theorem hamiltonPEvolutionReactionField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPEvolutionReactionField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      hamiltonPEvolutionReactionComponent
        (fun i j k l => metricRm04 (I := I) (M := M) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => metricNablaRm04Field (I := I) g x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b c := by
  rw [hamiltonPEvolutionReactionField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [curvaturePFirstField_apply_orthonormal (I := I) g basis horth,
    curvaturePSecondField_apply_orthonormal (I := I) g basis horth,
    curvaturePThirdField_apply_orthonormal (I := I) g basis horth,
    ricciNablaRmField_apply_orthonormal (I := I) g basis horth]
  simp only [hamiltonPEvolutionReactionComponent, hamiltonPComponent,
    hamiltonPField_apply, hamiltonPAt_apply]
  ring

private theorem hamiltonNablaPEvolutionReactionField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    hamiltonNablaPEvolutionReactionField (I := I) g x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) =
      hamiltonNablaPEvolutionReactionComponent
        (fun i j k l => metricRm04 (I := I) (M := M) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => metricNablaRm04Field (I := I) g x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l m r => metricNabla2Rm04Field (I := I) g x
          (vec6 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m) (basis r)))
        (fun i j k l => hamiltonNablaPField (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) q a b c := by
  rw [hamiltonNablaPEvolutionReactionField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [nablaRPFourthFirstField_apply_orthonormal (I := I) g basis horth,
    RnablaPFourthFirstField_apply_orthonormal (I := I) g basis horth,
    nablaRPFourthSecondField_apply_orthonormal (I := I) g basis horth,
    RnablaPFourthSecondField_apply_orthonormal (I := I) g basis horth,
    nablaRPFourthThirdField_apply_orthonormal (I := I) g basis horth,
    RnablaPFourthThirdField_apply_orthonormal (I := I) g basis horth,
    nablaRicNablaRmFourthField_apply_orthonormal (I := I) g basis horth,
    ricciNabla2RmFourthField_apply_orthonormal (I := I) g basis horth]
  simp only [hamiltonNablaPEvolutionReactionComponent, hamiltonPComponent,
    hamiltonPField_apply, hamiltonPAt_apply, hamiltonNablaPField_apply]
  simp only [Finset.sum_add_distrib]
  ring




private theorem hamiltonRicciSquareField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonRicciSquareField (I := I) g x (vec2 (I := I) A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (metricRicci (I := I) (M := M) g x (vec2 (I := I) A (basis i)) *
            metricRicci (I := I) (M := M) g x (vec2 (I := I) (basis j) B)) := by
  classical
  rw [hamiltonRicciSquareField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  have hleft :
      ((fun q => metricTraceInput (I := I) (basis i) (basis j)
        (vec2 (I := I) A B) (hamiltonRicciSquareFieldPerm q)) ∘ Fin.castAdd 2) =
        vec2 (I := I) A (basis i) := by
    funext q
    fin_cases q <;> rfl
  have hright :
      ((fun q => metricTraceInput (I := I) (basis i) (basis j)
        (vec2 (I := I) A B) (hamiltonRicciSquareFieldPerm q)) ∘ Fin.natAdd 2) =
        vec2 (I := I) (basis j) B := by
    funext q
    fin_cases q <;> rfl
  rw [hleft, hright]

private theorem hamiltonCurvatureRicciField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonCurvatureRicciField (I := I) g x (vec2 (I := I) A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              (metricRm04 (I := I) (M := M) g x
                  (vec4 (I := I) A (basis k) (basis i) B) *
                metricRicci (I := I) (M := M) g x
                  (vec2 (I := I) (basis l) (basis j)))) := by
  classical
  rw [hamiltonCurvatureRicciField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  have hleft :
      ((fun q =>
        metricTraceInput (I := I) (basis k) (basis l)
          (metricTraceInput (I := I) (basis i) (basis j) (vec2 (I := I) A B))
          (hamiltonCurvatureRicciFieldPerm q)) ∘ Fin.castAdd 2) =
        vec4 (I := I) A (basis k) (basis i) B := by
    funext q
    fin_cases q <;> rfl
  have hright :
      ((fun q =>
        metricTraceInput (I := I) (basis k) (basis l)
          (metricTraceInput (I := I) (basis i) (basis j) (vec2 (I := I) A B))
          (hamiltonCurvatureRicciFieldPerm q)) ∘ Fin.natAdd 4) =
        vec2 (I := I) (basis l) (basis j) := by
    funext q
    fin_cases q <;> rfl
  rw [hleft, hright]

private theorem hamiltonRicciSquareField_eq_at_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonRicciSquareField (I := I) g x (vec2 (I := I) A B) =
      hamiltonRicciSquareAt (I := I) g x (vec2 (I := I) A B) := by
  rw [hamiltonRicciSquareField_apply_basis (I := I) g basis gInv hinv,
    hamiltonRicciSquareAt_apply (I := I) g basis gInv hinv]

private theorem hamiltonCurvatureRicciField_eq_at_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonCurvatureRicciField (I := I) g x (vec2 (I := I) A B) =
      hamiltonCurvatureRicciAt (I := I) g x (vec2 (I := I) A B) := by
  rw [hamiltonCurvatureRicciField_apply_basis (I := I) g basis gInv hinv,
    hamiltonCurvatureRicciAt_apply (I := I) g basis gInv hinv]

private theorem ricciNabla2WMP_eq_metricNabla2Ric
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    ricciNabla2WMP (I := I) S t =
      metricNabla2Ric (I := I) (M := M) (S.base.metric t) := by
  have hW1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (S.family.connection t) (S.ricci t)
      (ricciNablaWMP (I := I) S t) :=
    (ricciSpatialWMP (I := I) S).1 t
  have hM1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (S.family.connection t) (S.ricci t)
      (metricNablaRic (I := I) (M := M) (S.base.metric t)) := by
    simpa [SolutionOn.ricci, SolutionFamily.ricci, SolutionOn.family,
      SolutionFamily.connection, metricCov, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2
        (metricCov (I := I) (M := M) (S.base.metric t))
        (metricRicci (I := I) (M := M) (S.base.metric t))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 (metricCov (I := I) (M := M) (S.base.metric t))
          (metricCov_smooth (I := I) (M := M) (S.base.metric t))
          (metricRicci (I := I) (M := M) (S.base.metric t))))
  have hFirst : ricciNablaWMP (I := I) S t =
      metricNablaRic (I := I) (M := M) (S.base.metric t) :=
    totalNabla0SRealizes_unique hW1 hM1
  have hW2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (S.family.connection t)
      (ricciNablaWMP (I := I) S t) (ricciNabla2WMP (I := I) S t) :=
    (ricciSpatialWMP (I := I) S).2 t
  have hM2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (S.family.connection t)
      (metricNablaRic (I := I) (M := M) (S.base.metric t))
      (metricNabla2Ric (I := I) (M := M) (S.base.metric t)) := by
    simpa [SolutionFamily.connection, metricCov, metricNabla2Ric] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3
        (metricCov (I := I) (M := M) (S.base.metric t))
        (metricNablaRic (I := I) (M := M) (S.base.metric t))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 (metricCov (I := I) (M := M) (S.base.metric t))
          (metricCov_smooth (I := I) (M := M) (S.base.metric t))
          (metricNablaRic (I := I) (M := M) (S.base.metric t))))
  rw [hFirst] at hW2
  exact totalNabla0SRealizes_unique hW2 hM2

private theorem hamiltonReactionField_eq_actual
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    ((2 : Real) • hamiltonCurvatureRicciField (I := I) (S.base.metric t) +
        (-2 : Real) • hamiltonRicciSquareField (I := I) (S.base.metric t)) x =
      ricciActualReactAt (I := I) S t x := by
  classical
  let g := S.base.metric t
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
    (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
        (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv := by
    simpa [g, basis, gInv] using
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x
  have hInv : forall i j, gInv i j = gInv j i :=
    invMetric_symm (I := I) (M := M) g x basis gInv hinv
  apply ext0S_basis (I := I) basis
  intro slots
  let a := slots 0
  let b := slots 1
  have hslots : (fun q : Fin 2 => basis (slots q)) =
      vec2 (I := I) (basis a) (basis b) := by
    funext q
    fin_cases q <;> rfl
  have hCurvField := hamiltonCurvatureRicciField_eq_at_basis
    (I := I) g basis gInv hinv (basis a) (basis b)
  have hSquareField := hamiltonRicciSquareField_eq_at_basis
    (I := I) g basis gInv hinv (basis a) (basis b)
  have hCurv := hamiltonCurvatureRicciAt_eq_neg_rm04RicciContractionAt
    (I := I) g basis gInv hinv a b
  have hSquare :
      hamiltonRicciSquareAt (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) =
        DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt
          (I := I) basis gInv (metricRicci (I := I) (M := M) g x) a b := by
    rw [hamiltonRicciSquareAt_apply (I := I) g basis gInv hinv]
    unfold DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt
      DifferentialGeometry.Geometry.Curvature.oneUp02CompAt
    calc
      (∑ i, ∑ j,
          gInv i j *
            (metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis a) (basis i)) *
              metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis j) (basis b)))) =
        ∑ j, ∑ i,
          gInv i j *
            (metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis a) (basis i)) *
              metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis j) (basis b))) := by
          rw [Finset.sum_comm]
      _ = ∑ k,
          (∑ p, gInv k p *
              metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis a) (basis p))) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis k) (basis b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hInv p k]
        ring
  have hActual := actualReact_comp (I := I) (M := M) S t x basis gInv
    (by simpa [g] using hinv) a b
  change
    ((2 : Real) • hamiltonCurvatureRicciField (I := I) g +
        (-2 : Real) • hamiltonRicciSquareField (I := I) g) x
        (fun q : Fin 2 => basis (slots q)) =
      ricciActualReactAt (I := I) S t x
        (fun q : Fin 2 => basis (slots q))
  rw [hslots]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [hCurvField, hSquareField, hCurv, hSquare]
  have hActual' :
      ricciActualReactAt (I := I) S t x
          (vec2 (I := I) (basis a) (basis b)) =
        (-2 : Real) *
            DifferentialGeometry.Geometry.Curvature.rm04RicciContractionAt
              (I := I) basis (metricRm04 (I := I) (M := M) g x) gInv
              (metricRicci (I := I) (M := M) g x) a b -
          2 * DifferentialGeometry.Geometry.Curvature.ricciQuadraticAt
            (I := I) basis gInv (metricRicci (I := I) (M := M) g x) a b := by
    simpa [g, SolutionOn.ricci, SolutionFamily.ricci, SolutionOn.family,
      SolutionFamily.rm04] using hActual
  rw [hActual']
  ring

private theorem metricRicciTimeDerivativeField_hasDerivWithinAt_of_solution
    [CompleteSpace E] [T2Space M] [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => S.ricci s x (vec2 (I := I) v w))
      (metricRicciTimeDerivativeField (I := I) (S.base.metric (t : Real)) x
        (vec2 (I := I) v w)) D.carrier (t : Real) := by
  have hpair := ricciPairDeriv (I := I) S hS t x v w
  refine hpair.congr_deriv ?_
  have hNabla2 := ricciNabla2WMP_eq_metricNabla2Ric (I := I) S (t : Real)
  have hReaction := hamiltonReactionField_eq_actual (I := I) S (t : Real) x
  have hReactionEval := congrArg
    (fun T : Tensor02At (I := I) (M := M) x => T (vec2 (I := I) v w)) hReaction
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul] at hReactionEval
  rw [metricRicciTimeDerivativeField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    ← hNabla2]
  change
    metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
          (ricciNabla2WMP (I := I) S (t : Real) x) (vec2 (I := I) v w) +
        ricciActualReactAt (I := I) S (t : Real) x (vec2 (I := I) v w) =
      metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : Real))
          (ricciNabla2WMP (I := I) S (t : Real) x) (vec2 (I := I) v w) +
        2 * hamiltonCurvatureRicciField (I := I) (S.base.metric (t : Real)) x
          (vec2 (I := I) v w) +
        (-2 : Real) * hamiltonRicciSquareField (I := I) (S.base.metric (t : Real)) x
          (vec2 (I := I) v w)
  linear_combination -hReactionEval

open DifferentialGeometry.Tensor.Coordinates in
private theorem ricciCompInCoordinateFrame_contMDiffAt
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ coordinateFrameSet (I := I) x0)
    (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x0)
          p.1 p.2 i j)
      ((t : Real), x) := by
  let frame := coordinateFrameAt (I := I) x0
  have hdomain :
      D.regular ×ˢ coordinateFrameSet (I := I) x0 ∈
        nhds ((t : Real), x) :=
    prod_mem_nhds (D.regular_isOpen.mem_nhds t.2)
      ((coordinateFrameSet_open (I := I) x0).mem_nhds hx)
  have hmetric : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        metricCompInFrame (I := I) S frame p.1 p.2 i j)
      ((t : Real), x) := by
    simpa only [frame] using
      (coordMetricSmooth (I := I) S hS x0 i j).contMDiffAt hdomain
  have hderiv : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        deriv (fun s : Real =>
          metricCompInFrame (I := I) S frame s p.2 i j) p.1)
      ((t : Real), x) := by
    exact DifferentialGeometry.timeDeriv_smoothAt hmetric (by simp)
  have hsmooth : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => (-1 / 2 : Real) *
        deriv (fun s : Real =>
          metricCompInFrame (I := I) S frame s p.2 i j) p.1)
      ((t : Real), x) :=
    contMDiffAt_const.mul hderiv
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hdomain] with p hp
  have heq :=
    ((metricCompInFrame_hasDerivWithinAt
      (I := I) S hS frame
      (⟨p.1, hp.1⟩ : D.RegularTime) p.2 i j).hasDerivAt
        (D.regular_mem_nhds hp.1)).deriv
  rw [heq]
  ring

open DifferentialGeometry.Tensor.Coordinates in
private theorem tensor0SField_coordinateFrame_mdiffAt
    {q : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (x0 x : M) (hx : x ∈ coordinateFrameSet (I := I) x0)
    (slots : Fin q ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => A y
        (fun r => coordinateFrameAt (I := I) x0 (slots r) y)) x := by
  apply tensor0SField_eval_C1_slots_mdiffAt
  intro r
  exact ((coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffAt
    (coordinateFrameSet_open (I := I) x0) hx (slots r)).of_le (by simp)

open DifferentialGeometry.Tensor.Coordinates in
private theorem totalNabla0S_apply_coordinateFrame
    [T2Space M]
    {q : Nat}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov A nablaA)
    (x0 : M) (d : CoordinateIdx (𝕜 := Real) E)
    (slots : Fin q -> CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
    nablaA x0 (Fin.cons (frame d x0) (fun r => frame (slots r) x0)) =
      mvfderiv (I := I)
          (fun y : M => A y (fun r => frame (slots r) y))
          x0 (frame d x0) -
        ∑ r : Fin q, ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov frame hframe x0 d (slots r) p *
            A x0 (fun s => frame (Function.update slots r p s) x0) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have h := covDerivStepComp_frameComp_eq
    (I := I) cov A nablaA hreal frame hframe
    (coordinateFrameSet_open (I := I) x0)
    (coordinateFrameAt_mem (I := I) x0) (Fin.cons d slots)
  rw [frameTuple_eq_cons] at h
  simp only [Fin.cons_zero, Fin.tail_cons] at h
  have htail : frameTuple (I := I) frame x0 slots =
      (fun r => frame (slots r) x0) := rfl
  rw [htail] at h
  rw [← h]
  simp only [covDerivStepComp, frameExtData, frameComp0S,
    Fin.tail_cons, Fin.cons_zero]
  rfl

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPField_apply_coordinateFrame
    [CompleteSpace E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (d a b c : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
    hamiltonNablaPField (I := I) g x0
        (vec4 (I := I) (frame d x0) (frame a x0) (frame b x0) (frame c x0)) =
      mvfderiv (I := I)
          (fun y : M => hamiltonPField (I := I) g y
            (vec3 (I := I) (frame a y) (frame b y) (frame c y)))
          x0 (frame d x0) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (metricCov (I := I) (M := M) g)
              frame hframe x0 d a p *
            hamiltonPField (I := I) g x0
              (vec3 (I := I) (frame p x0) (frame b x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (metricCov (I := I) (M := M) g)
              frame hframe x0 d b p *
            hamiltonPField (I := I) g x0
              (vec3 (I := I) (frame a x0) (frame p x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (metricCov (I := I) (M := M) g)
              frame hframe x0 d c p *
            hamiltonPField (I := I) g x0
              (vec3 (I := I) (frame a x0) (frame b x0) (frame p x0)) := by
  classical
  dsimp only
  let slots : Fin 3 -> CoordinateIdx (𝕜 := Real) E :=
    fun r => if r = 0 then a else if r = 1 then b else c
  have h := totalNabla0S_apply_coordinateFrame
    (I := I) (metricCov (I := I) (M := M) g)
    (hamiltonPField (I := I) g) (hamiltonNablaPField (I := I) g)
    (hamiltonNablaPField_realizes (I := I) g) x0 d slots
  dsimp only at h
  rw [Fin.sum_univ_three] at h
  have hslot0 : slots 0 = a := by simp [slots]
  have hslot1 : slots 1 = b := by simp [slots]
  have hslot2 : slots 2 = c := by simp [slots]
  have hslots (y : M) :
      (fun r => coordinateFrameAt (I := I) x0 (slots r) y) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a y)
          (coordinateFrameAt (I := I) x0 b y)
          (coordinateFrameAt (I := I) x0 c y) := by
    funext r
    fin_cases r <;> simp [slots, vec3]
  have hcons :
      Fin.cons (coordinateFrameAt (I := I) x0 d x0)
          (fun r => coordinateFrameAt (I := I) x0 (slots r) x0) =
        vec4 (I := I)
          (coordinateFrameAt (I := I) x0 d x0)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 c x0) := by
    rw [hslots x0]
    funext r
    fin_cases r <;> rfl
  have hupdate0 (p : CoordinateIdx (𝕜 := Real) E) :
      (fun r => coordinateFrameAt (I := I) x0
        (Function.update slots (0 : Fin 3) p r) x0) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 p x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 c x0) := by
    funext r
    fin_cases r <;> simp [slots, Function.update, vec3]
  have hupdate1 (p : CoordinateIdx (𝕜 := Real) E) :
      (fun r => coordinateFrameAt (I := I) x0
        (Function.update slots (1 : Fin 3) p r) x0) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 p x0)
          (coordinateFrameAt (I := I) x0 c x0) := by
    funext r
    fin_cases r <;> simp [slots, Function.update, vec3]
  have hupdate2 (p : CoordinateIdx (𝕜 := Real) E) :
      (fun r => coordinateFrameAt (I := I) x0
        (Function.update slots (2 : Fin 3) p r) x0) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 p x0) := by
    funext r
    fin_cases r <;> simp [slots, Function.update, vec3]
  rw [hcons, hslot0, hslot1, hslot2] at h
  simp_rw [hslots, hupdate0, hupdate1, hupdate2] at h
  linear_combination h

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPTimeDerivativeField_apply_coordinateFrame
    [CompleteSpace E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (d a b c : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
    hamiltonNablaPTimeDerivativeField (I := I) g x0
        (vec4 (I := I) (frame d x0) (frame a x0) (frame b x0) (frame c x0)) =
      mvfderiv (I := I)
          (fun y : M => hamiltonPTimeDerivativeField (I := I) g y
            (vec3 (I := I) (frame a y) (frame b y) (frame c y)))
          x0 (frame d x0) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (metricCov (I := I) (M := M) g)
              frame hframe x0 d a p *
            hamiltonPTimeDerivativeField (I := I) g x0
              (vec3 (I := I) (frame p x0) (frame b x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (metricCov (I := I) (M := M) g)
              frame hframe x0 d b p *
            hamiltonPTimeDerivativeField (I := I) g x0
              (vec3 (I := I) (frame a x0) (frame p x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (metricCov (I := I) (M := M) g)
              frame hframe x0 d c p *
            hamiltonPTimeDerivativeField (I := I) g x0
              (vec3 (I := I) (frame a x0) (frame b x0) (frame p x0)) := by
  classical
  dsimp only
  let slots : Fin 3 -> CoordinateIdx (𝕜 := Real) E :=
    fun r => if r = 0 then a else if r = 1 then b else c
  have h := totalNabla0S_apply_coordinateFrame
    (I := I) (metricCov (I := I) (M := M) g)
    (hamiltonPTimeDerivativeField (I := I) g)
    (hamiltonNablaPTimeDerivativeField (I := I) g)
    (hamiltonNablaPTimeDerivativeField_realizes (I := I) g) x0 d slots
  dsimp only at h
  rw [Fin.sum_univ_three] at h
  have hslot0 : slots 0 = a := by simp [slots]
  have hslot1 : slots 1 = b := by simp [slots]
  have hslot2 : slots 2 = c := by simp [slots]
  have hslots (y : M) :
      (fun r => coordinateFrameAt (I := I) x0 (slots r) y) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a y)
          (coordinateFrameAt (I := I) x0 b y)
          (coordinateFrameAt (I := I) x0 c y) := by
    funext r
    fin_cases r <;> simp [slots, vec3]
  have hcons :
      Fin.cons (coordinateFrameAt (I := I) x0 d x0)
          (fun r => coordinateFrameAt (I := I) x0 (slots r) x0) =
        vec4 (I := I)
          (coordinateFrameAt (I := I) x0 d x0)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 c x0) := by
    rw [hslots x0]
    funext r
    fin_cases r <;> rfl
  have hupdate0 (p : CoordinateIdx (𝕜 := Real) E) :
      (fun r => coordinateFrameAt (I := I) x0
        (Function.update slots (0 : Fin 3) p r) x0) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 p x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 c x0) := by
    funext r
    fin_cases r <;> simp [slots, Function.update, vec3]
  have hupdate1 (p : CoordinateIdx (𝕜 := Real) E) :
      (fun r => coordinateFrameAt (I := I) x0
        (Function.update slots (1 : Fin 3) p r) x0) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 p x0)
          (coordinateFrameAt (I := I) x0 c x0) := by
    funext r
    fin_cases r <;> simp [slots, Function.update, vec3]
  have hupdate2 (p : CoordinateIdx (𝕜 := Real) E) :
      (fun r => coordinateFrameAt (I := I) x0
        (Function.update slots (2 : Fin 3) p r) x0) =
        vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 p x0) := by
    funext r
    fin_cases r <;> simp [slots, Function.update, vec3]
  rw [hcons, hslot0, hslot1, hslot2] at h
  simp_rw [hslots, hupdate0, hupdate1, hupdate2] at h
  linear_combination h

open DifferentialGeometry.Tensor.Coordinates in
private theorem metricRicciTimeDerivativeField_fixedBase
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M)
    (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) D.carrier D.regular (coordinateFrameSet (I := I) x0)
      (fun s x =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x0)
          s x i j)
      (fun t x =>
        metricRicciTimeDerivativeField (I := I) (S.base.metric t) x
          (vec2 (I := I)
            (coordinateFrameAt (I := I) x0 i x)
            (coordinateFrameAt (I := I) x0 j x))) := by
  refine fixedBaseOnRegLocal
    (I := I) (timeSet := D.carrier) (regularSet := D.regular)
    (u := coordinateFrameSet (I := I) x0)
    (coordinateFrameSet_open (I := I) x0) D.regular_subset
    (fun {_t} ht => D.regular_mem_nhds ht) ?_ ?_ ?_ ?_
  · intro t ht x hx
    exact (ricciCompInCoordinateFrame_contMDiffAt
      (I := I) S hS x0 ⟨t, ht⟩ x hx i j).of_le
        (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  · intro s _hs x hx
    exact coordRicciMdiff (I := I) S x0 s x hx i j
  · intro t _ht x hx
    let slots : Fin 2 ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E :=
      fun r => if r = 0 then i else j
    have h := tensor0SField_coordinateFrame_mdiffAt
      (I := I) (metricRicciTimeDerivativeField (I := I) (S.base.metric t))
      x0 x hx slots
    convert h using 1
    funext y
    congr 1
    funext r
    fin_cases r <;> simp [slots, vec2]
  · intro t ht x _hx
    exact metricRicciTimeDerivativeField_hasDerivWithinAt_of_solution
      (I := I) S hS ⟨t, ht⟩ x
        (coordinateFrameAt (I := I) x0 i x)
        (coordinateFrameAt (I := I) x0 j x)

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPField_apply_coordinateFrame
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) (x0 : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) :
    hamiltonPField (I := I) (S.base.metric s) x0
        (vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 c x0)) =
      mvfderiv (I := I)
          (fun y : M => ricciCompInFrame (I := I) S
            (coordinateFrameAt (I := I) x0) s y b c)
          x0 (coordinateFrameAt (I := I) x0 a x0) -
        mvfderiv (I := I)
          (fun y : M => ricciCompInFrame (I := I) S
            (coordinateFrameAt (I := I) x0) s y a c)
          x0 (coordinateFrameAt (I := I) x0 b x0) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame
              (S.family.connection s) (coordinateFrameAt (I := I) x0)
              (coordinateFrameAt_isLocalFrame_one (I := I) x0)
              x0 a c p *
            ricciCompInFrame (I := I) S
              (coordinateFrameAt (I := I) x0) s x0 b p +
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame
              (S.family.connection s) (coordinateFrameAt (I := I) x0)
              (coordinateFrameAt_isLocalFrame_one (I := I) x0)
              x0 b c p *
            ricciCompInFrame (I := I) S
              (coordinateFrameAt (I := I) x0) s x0 a p := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hx0 : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  have hnabla (d i j : CoordinateIdx (𝕜 := Real) E) :
      metricNablaRic (I := I) (M := M) (S.base.metric s) x0
          (vec3 (I := I) (frame d x0) (frame i x0) (frame j x0)) =
        nablaRicComp (I := I) S frame s x0 d i j := by
    simp [frame, metricNablaRic, nablaRicComp,
      SolutionFamily.connection, SolutionFamily.ricci, SolutionOn.ricci,
      SolutionOn.family, metricCov, metricRicci]
  have hcov (d i : CoordinateIdx (𝕜 := Real) E) :
      (S.family.connection s) (frame i) x0 (frame d x0) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (S.family.connection s) frame hframe
              x0 d i p • frame p x0 := by
    exact covariantDerivative_eq_sum_christoffel
      (I := I) (S.family.connection s) frame hframe hx0 d i
  have htf : DifferentialGeometry.Geometry.Connection.IsTorsionFree
      (I := I) (S.family.connection s) := by
    simpa [SolutionFamily.connection, SolutionOn.family, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) (S.base.metric s)
  have hgamma (p : CoordinateIdx (𝕜 := Real) E) :
      christoffelSymbolInFrame (S.family.connection s) frame hframe x0 a b p =
        christoffelSymbolInFrame (S.family.connection s) frame hframe x0 b a p := by
    simpa [frame, hframe] using
      DifferentialGeometry.Geometry.Connection.coordinate_christoffel_symm_of_torsionFree
        (I := I) htf x0 a b p
  have hsum (d i j : CoordinateIdx (𝕜 := Real) E) :
      S.ricciAt s x0
          (vec2 (I := I) (frame i x0)
            (∑ p : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection s) frame hframe
                  x0 d j p • frame p x0)) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (S.family.connection s) frame hframe
              x0 d j p *
            ricciCompInFrame (I := I) S frame s x0 i p := by
    let base : Fin 2 -> TangentSpace I x0 :=
      vec2 (I := I) (frame i x0) 0
    have hleft :
        Function.update base (1 : Fin 2)
            (∑ p : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection s) frame hframe
                  x0 d j p • frame p x0) =
          vec2 (I := I) (frame i x0)
            (∑ p : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection s) frame hframe
                  x0 d j p • frame p x0) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [← hleft]
    change (S.ricciAt s x0).toMultilinearMap
        (Function.update base (1 : Fin 2)
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (S.family.connection s) frame hframe
                x0 d j p • frame p x0)) = _
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MultilinearMap.map_update_smul]
    change christoffelSymbolInFrame (S.family.connection s) frame hframe
          x0 d j p *
        S.ricciAt s x0 (Function.update base (1 : Fin 2) (frame p x0)) = _
    have hslot :
        Function.update base (1 : Fin 2) (frame p x0) =
          vec2 (I := I) (frame i x0) (frame p x0) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [hslot]
    rfl
  rw [hamiltonPField_apply, hamiltonPAt_apply,
    hnabla a b c, hnabla b a c,
    coordNablaReal (I := I) S x0 s a b c,
    coordNablaReal (I := I) S x0 s b a c]
  unfold ricciCovDerivCompInFrame
  rw [hcov a b, hcov a c, hcov b a, hcov b c]
  simp_rw [hgamma]
  rw [hsum a b c, hsum b a c]
  ring

open DifferentialGeometry.Tensor.Coordinates in
private theorem nablaRicCompInCoordinateFrame_contMDiffAt
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ coordinateFrameSet (I := I) x0)
    (d a b : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) 2
      (fun p : Real × M =>
        nablaRicComp (I := I) S (coordinateFrameAt (I := I) x0)
          p.1 p.2 d a b)
      ((t : Real), x) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hricci (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 3
        (fun p : Real × M =>
          ricciCompInFrame (I := I) S frame p.1 p.2 i j)
        ((t : Real), x) := by
    exact (by
      simpa only [frame] using
        (ricciCompInCoordinateFrame_contMDiffAt
          (I := I) S hS x0 t x hx i j).of_le
            (by decide : (3 : WithTop ℕ∞) ≤ ∞))
  have hframeSmooth (i : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt I (I.prod (modelWithCornersSelf Real E)) ∞
        (fun y : M =>
          (⟨y, frame i y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa only [frame] using
      (coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffAt
        (coordinateFrameSet_open (I := I) x0) hx i
  have hpartial (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 2
        (fun p : Real × M =>
          mvfderiv (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame p.1 y i j)
            p.2 (frame d p.2))
        ((t : Real), x) := by
    refine DifferentialGeometry.prodExtDerivAt
      (I := I)
      (F := fun p : Real × M =>
        ricciCompInFrame (I := I) S frame p.1 p.2 i j)
      (X := frame d) (t := (t : Real)) (x := x) ?_ ?_
    · exact hricci i j
    · exact hframeSmooth d
  have hgamma (i j k : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 2
        (fun p : Real × M =>
          christoffelSymbolInFrame (S.family.connection p.1) frame hframe
            p.2 i j k)
        ((t : Real), x) := by
    exact (by
      simpa only [frame, hframe] using
        (coordGammaSmoothInf (I := I) S hS x0 t x hx i j k).of_le
          (by decide : (2 : WithTop ℕ∞) ≤ ∞))
  have hfirst :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 2
        (fun p : Real × M =>
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                p.2 d a k *
              ricciCompInFrame (I := I) S frame p.1 p.2 k b)
        ((t : Real), x) := by
    exact ContMDiffAt.sum fun k _ =>
      (hgamma d a k).mul ((hricci k b).of_le (by norm_num))
  have hsecond :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 2
        (fun p : Real × M =>
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                p.2 d b k *
              ricciCompInFrame (I := I) S frame p.1 p.2 a k)
        ((t : Real), x) := by
    exact ContMDiffAt.sum fun k _ =>
      (hgamma d b k).mul ((hricci a k).of_le (by norm_num))
  have hsmooth := ((hpartial a b).sub hfirst).sub hsecond
  refine hsmooth.congr_of_eventuallyEq ?_
  have hbase :
      {p : Real × M | p.2 ∈ coordinateFrameSet (I := I) x0} ∈
        nhds ((t : Real), x) := by
    exact (continuous_snd.tendsto ((t : Real), x)).eventually
      ((coordinateFrameSet_open (I := I) x0).mem_nhds hx)
  filter_upwards [hbase] with p hp
  have hcovA :
      (S.family.connection p.1) (frame a) p.2 (frame d p.2) =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (S.family.connection p.1) frame hframe
              p.2 d a k • frame k p.2 := by
    exact covariantDerivative_eq_sum_christoffel
      (I := I) (S.family.connection p.1) frame hframe hp d a
  have hcovB :
      (S.family.connection p.1) (frame b) p.2 (frame d p.2) =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (S.family.connection p.1) frame hframe
              p.2 d b k • frame k p.2 := by
    exact covariantDerivative_eq_sum_christoffel
      (I := I) (S.family.connection p.1) frame hframe hp d b
  have hsumFirst :
      S.ricciAt p.1 p.2
          (vec2 (I := I)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                  p.2 d a k • frame k p.2)
            (frame b p.2)) =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (S.family.connection p.1) frame hframe
              p.2 d a k *
            ricciCompInFrame (I := I) S frame p.1 p.2 k b := by
    let base : Fin 2 → TangentSpace I p.2 := vec2 (I := I) 0 (frame b p.2)
    have hleft :
        Function.update base (0 : Fin 2)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                  p.2 d a k • frame k p.2) =
          vec2 (I := I)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                  p.2 d a k • frame k p.2)
            (frame b p.2) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [← hleft]
    change (S.ricciAt p.1 p.2).toMultilinearMap
        (Function.update base (0 : Fin 2) (∑ k, _ • frame k p.2)) = _
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MultilinearMap.map_update_smul]
    change christoffelSymbolInFrame (S.family.connection p.1) frame hframe
          p.2 d a k *
        S.ricciAt p.1 p.2
          (Function.update base (0 : Fin 2) (frame k p.2)) = _
    have hslot :
        Function.update base (0 : Fin 2) (frame k p.2) =
          vec2 (I := I) (frame k p.2) (frame b p.2) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [hslot]
    rfl
  have hsumSecond :
      S.ricciAt p.1 p.2
          (vec2 (I := I) (frame a p.2)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                  p.2 d b k • frame k p.2)) =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (S.family.connection p.1) frame hframe
              p.2 d b k *
            ricciCompInFrame (I := I) S frame p.1 p.2 a k := by
    let base : Fin 2 → TangentSpace I p.2 := vec2 (I := I) (frame a p.2) 0
    have hleft :
        Function.update base (1 : Fin 2)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                  p.2 d b k • frame k p.2) =
          vec2 (I := I) (frame a p.2)
            (∑ k : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (S.family.connection p.1) frame hframe
                  p.2 d b k • frame k p.2) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [← hleft]
    change (S.ricciAt p.1 p.2).toMultilinearMap
        (Function.update base (1 : Fin 2) (∑ k, _ • frame k p.2)) = _
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MultilinearMap.map_update_smul]
    change christoffelSymbolInFrame (S.family.connection p.1) frame hframe
          p.2 d b k *
        S.ricciAt p.1 p.2
          (Function.update base (1 : Fin 2) (frame k p.2)) = _
    have hslot :
        Function.update base (1 : Fin 2) (frame k p.2) =
          vec2 (I := I) (frame a p.2) (frame k p.2) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [hslot]
    rfl
  rw [(coordNablaRealOn (I := I) S x0) p.1 p.2 hp d a b]
  unfold ricciCovDerivCompInFrame
  rw [hcovA, hcovB, hsumFirst, hsumSecond]

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPCompInCoordinateFrame_contMDiffAt
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ coordinateFrameSet (I := I) x0)
    (a b c : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) 2
      (fun p : Real × M =>
        hamiltonPField (I := I) (S.base.metric p.1) p.2
          (vec3 (I := I)
            (coordinateFrameAt (I := I) x0 a p.2)
            (coordinateFrameAt (I := I) x0 b p.2)
            (coordinateFrameAt (I := I) x0 c p.2)))
      ((t : Real), x) := by
  have hsmooth :=
    (nablaRicCompInCoordinateFrame_contMDiffAt
      (I := I) S hS x0 t x hx a b c).sub
      (nablaRicCompInCoordinateFrame_contMDiffAt
        (I := I) S hS x0 t x hx b a c)
  simpa [hamiltonPField_apply, hamiltonPAt_apply, metricNablaRic,
    nablaRicComp, SolutionFamily.connection, SolutionFamily.ricci,
    SolutionOn.ricci, SolutionOn.family, metricCov, metricRicci] using hsmooth

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPField_hasDerivWithinAt_coordinateFrame_raw
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (a b c : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let ricciDt := fun i j =>
      metricRicciTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0
        (vec2 (I := I) (frame i x0) (frame j x0))
    let partialRicciDt := fun d i j =>
      mvfderiv (I := I)
        (fun y : M =>
          metricRicciTimeDerivativeField (I := I) (S.base.metric (t : Real)) y
            (vec2 (I := I) (frame i y) (frame j y)))
        x0 (frame d x0)
    let gammaDt := christoffelEvolutionRHSInFrame
      (M := M) (coordInv (I := I) S x0)
      (nablaRicComp (I := I) S frame) (t : Real) x0
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonPField (I := I) (S.base.metric s) x0
          (vec3 (I := I) (frame a x0) (frame b x0) (frame c x0)))
      (partialRicciDt a b c - partialRicciDt b a c -
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            (gammaDt a c p *
                ricciCompInFrame (I := I) S frame (t : Real) x0 b p +
              christoffelSymbolInFrame
                  (S.family.connection (t : Real)) frame
                  (coordinateFrameAt_isLocalFrame_one (I := I) x0)
                  x0 a c p * ricciDt b p) +
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          (gammaDt b c p *
              ricciCompInFrame (I := I) S frame (t : Real) x0 a p +
            christoffelSymbolInFrame
                (S.family.connection (t : Real)) frame
                (coordinateFrameAt_isLocalFrame_one (I := I) x0)
                x0 b c p * ricciDt a p))
      D.carrier (t : Real) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hx0 : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  have hpartial (d i j : CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real =>
          mvfderiv (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame s y i j)
            x0 (frame d x0))
        (mvfderiv (I := I)
          (fun y : M =>
            metricRicciTimeDerivativeField (I := I) (S.base.metric (t : Real)) y
              (vec2 (I := I) (frame i y) (frame j y)))
          x0 (frame d x0))
        D.carrier (t : Real) := by
    exact fixedBaseExtDerivTimeDerivativeOnRegular_apply
      (I := I) (h := metricRicciTimeDerivativeField_fixedBase
        (I := I) S hS x0 i j)
      (t := (t : Real)) t.2 (x := x0) hx0 (frame d x0)
  have hricci (i j : CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real =>
          ricciCompInFrame (I := I) S frame s x0 i j)
        (metricRicciTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0
          (vec2 (I := I) (frame i x0) (frame j x0)))
        D.carrier (t : Real) := by
    simpa [frame, ricciCompInFrame] using
      metricRicciTimeDerivativeField_hasDerivWithinAt_of_solution
        (I := I) S hS t x0 (frame i x0) (frame j x0)
  have hmetric := coordMetricMix (I := I) S hS x0
    (coordMetricDeriv (I := I) S hS x0)
  have hgamma (i j p : CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real =>
          christoffelSymbolInFrame (S.family.connection s) frame hframe
            x0 i j p)
        (christoffelEvolutionRHSInFrame
          (M := M) (coordInv (I := I) S x0)
          (nablaRicComp (I := I) S frame)
          (t : Real) x0 i j p)
        D.carrier (t : Real) := by
    simpa [frame, hframe] using
      coordGammaEvol (I := I) S hS x0 hmetric t x0 hx0 i j p
  have hfirst := (hpartial a b c).sub (hpartial b a c)
  have hprodFirst := HasDerivWithinAt.fun_sum
    (u := Finset.univ) (fun p _ => (hgamma a c p).mul (hricci b p))
  have hprodSecond := HasDerivWithinAt.fun_sum
    (u := Finset.univ) (fun p _ => (hgamma b c p).mul (hricci a p))
  have hraw := (hfirst.sub hprodFirst).add hprodSecond
  refine hraw.congr ?_ ?_
  · intro s _hs
    exact hamiltonPField_apply_coordinateFrame (I := I) S s x0 a b c
  · exact hamiltonPField_apply_coordinateFrame (I := I) S (t : Real) x0 a b c

open DifferentialGeometry.Tensor.Coordinates in
private theorem metricNablaRicciTimeDerivativeField_apply_coordinateFrame
    [CompleteSpace E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (d i j : CoordinateIdx (𝕜 := Real) E) :
    metricNablaRicciTimeDerivativeField (I := I) g x0
        (vec3 (I := I)
          (coordinateFrameAt (I := I) x0 d x0)
          (coordinateFrameAt (I := I) x0 i x0)
          (coordinateFrameAt (I := I) x0 j x0)) =
      mvfderiv (I := I)
          (fun y : M =>
            metricRicciTimeDerivativeField (I := I) g y
              (vec2 (I := I)
                (coordinateFrameAt (I := I) x0 i y)
                (coordinateFrameAt (I := I) x0 j y)))
          x0 (coordinateFrameAt (I := I) x0 d x0) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame
              (metricCov (I := I) (M := M) g)
              (coordinateFrameAt (I := I) x0)
              (coordinateFrameAt_isLocalFrame_one (I := I) x0)
              x0 d i p *
            metricRicciTimeDerivativeField (I := I) g x0
              (vec2 (I := I)
                (coordinateFrameAt (I := I) x0 p x0)
                (coordinateFrameAt (I := I) x0 j x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame
              (metricCov (I := I) (M := M) g)
              (coordinateFrameAt (I := I) x0)
              (coordinateFrameAt_isLocalFrame_one (I := I) x0)
              x0 d j p *
            metricRicciTimeDerivativeField (I := I) g x0
              (vec2 (I := I)
                (coordinateFrameAt (I := I) x0 i x0)
                (coordinateFrameAt (I := I) x0 p x0)) := by
  classical
  let cov := metricCov (I := I) (M := M) g
  let A := metricRicciTimeDerivativeField (I := I) g
  let nablaA := metricNablaRicciTimeDerivativeField (I := I) g
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  let n : Fin 3 -> CoordinateIdx (𝕜 := Real) E :=
    Fin.cons d (Fin.cons i (fun _ => j))
  have hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA := by
    simpa [cov, A, nablaA, metricNablaRicciTimeDerivativeField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov A
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) A))
  have h := covDerivStepComp_frameComp_eq
    (I := I) cov A nablaA hreal frame hframe
    (coordinateFrameSet_open (I := I) x0)
    (coordinateFrameAt_mem (I := I) x0) n
  have hn : frameTuple (I := I) frame x0 n =
      vec3 (I := I) (frame d x0) (frame i x0) (frame j x0) := by
    funext q
    fin_cases q <;> rfl
  have htail (y : M) :
      frameTuple (I := I) frame y (Fin.tail n) =
        vec2 (I := I) (frame i y) (frame j y) := by
    funext q
    fin_cases q <;> rfl
  have hupdateFirst (p : CoordinateIdx (𝕜 := Real) E) :
      frameTuple (I := I) frame x0
          (Function.update (Fin.tail n) (0 : Fin 2) p) =
        vec2 (I := I) (frame p x0) (frame j x0) := by
    funext q
    fin_cases q <;> simp [frameTuple, n, Function.update, vec2]
  have hupdateSecond (p : CoordinateIdx (𝕜 := Real) E) :
      frameTuple (I := I) frame x0
          (Function.update (Fin.tail n) (1 : Fin 2) p) =
        vec2 (I := I) (frame i x0) (frame p x0) := by
    funext q
    fin_cases q <;> simp [frameTuple, n, Function.update, vec2]
  have hn0 : n 0 = d := rfl
  have htail0 : Fin.tail n 0 = i := rfl
  have htail1 : Fin.tail n 1 = j := rfl
  rw [← hn, ← h]
  simp only [covDerivStepComp, frameExtData, frameComp0S,
    Fin.sum_univ_two]
  simp_rw [htail, hupdateFirst, hupdateSecond]
  simp only [cov, A, frame, hn0, htail0, htail1]
  ring

private theorem connectionVariationRicciFirstField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B C : TangentSpace I x) :
    connectionVariationRicciFirstField (I := I) g x
        (vec3 (I := I) A B C) =
      ∑ p : Idx, ∑ q : Idx,
        gInv p q *
          (ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) A C (basis p)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis q) B)) := by
  classical
  rw [connectionVariationRicciFirstField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  have hleft :
      ((fun r => metricTraceInput (I := I) (basis p) (basis q)
        (vec3 (I := I) A B C) (connectionVariationRicciFirstFieldPerm r)) ∘
          Fin.castAdd 2) =
        vec3 (I := I) A C (basis p) := by
    funext r
    fin_cases r <;> rfl
  have hright :
      ((fun r => metricTraceInput (I := I) (basis p) (basis q)
        (vec3 (I := I) A B C) (connectionVariationRicciFirstFieldPerm r)) ∘
          Fin.natAdd 3) =
        vec2 (I := I) (basis q) B := by
    funext r
    fin_cases r <;> rfl
  rw [hleft, hright]

private theorem connectionVariationRicciSecondField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B C : TangentSpace I x) :
    connectionVariationRicciSecondField (I := I) g x
        (vec3 (I := I) A B C) =
      ∑ p : Idx, ∑ q : Idx,
        gInv p q *
          (ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) B C (basis p)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis q) A)) := by
  classical
  rw [connectionVariationRicciSecondField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  have hleft :
      ((fun r => metricTraceInput (I := I) (basis p) (basis q)
        (vec3 (I := I) A B C) (connectionVariationRicciSecondFieldPerm r)) ∘
          Fin.castAdd 2) =
        vec3 (I := I) B C (basis p) := by
    funext r
    fin_cases r <;> rfl
  have hright :
      ((fun r => metricTraceInput (I := I) (basis p) (basis q)
        (vec3 (I := I) A B C) (connectionVariationRicciSecondFieldPerm r)) ∘
          Fin.natAdd 3) =
        vec2 (I := I) (basis q) A := by
    funext r
    fin_cases r <;> rfl
  rw [hleft, hright]

open DifferentialGeometry.Tensor.Coordinates in
private theorem christoffelEvolutionRHSInFrame_eq_connectionVariationField
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) (x0 : M)
    (i j p : CoordinateIdx (𝕜 := Real) E) :
    christoffelEvolutionRHSInFrame
        (M := M) (coordInv (I := I) S x0)
        (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x0))
        s x0 i j p =
      ∑ q : CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x0 s x0 p q *
          ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
            (vec3 (I := I)
              (coordinateFrameAt (I := I) x0 i x0)
              (coordinateFrameAt (I := I) x0 j x0)
              (coordinateFrameAt (I := I) x0 q x0)) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  have hnabla (d a b : CoordinateIdx (𝕜 := Real) E) :
      nablaRicComp (I := I) S frame s x0 d a b =
        metricNablaRic (I := I) (M := M) (S.base.metric s) x0
          (vec3 (I := I) (frame d x0) (frame a x0) (frame b x0)) := by
    simp [frame, metricNablaRic, nablaRicComp,
      SolutionFamily.connection, SolutionFamily.ricci, SolutionOn.ricci,
      SolutionOn.family, metricCov, metricRicci]
  unfold christoffelEvolutionRHSInFrame christoffelVariationLoweredRHSInFrame
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ricciFlowConnectionVariationField_apply]
  rw [hnabla i j q, hnabla j i q, hnabla q i j]

open DifferentialGeometry.Tensor.Coordinates in
private theorem christoffelEvolutionRHSInFrame_ricci_contraction
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) (x0 : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let basis := coordinateFrameAtToBasis (I := I) x0
    let gInv := fun p q => coordInv (I := I) S x0 s x0 p q
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        christoffelEvolutionRHSInFrame
            (M := M) (coordInv (I := I) S x0)
            (nablaRicComp (I := I) S frame) s x0 i j p *
          ricciCompInFrame (I := I) S frame s x0 k p) =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            (ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
                (vec3 (I := I) (basis i) (basis j) (basis p)) *
              metricRicci (I := I) (M := M) (S.base.metric s) x0
                (vec2 (I := I) (basis q) (basis k))) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let gInv := fun p q => coordInv (I := I) S x0 s x0 p q
  have hbasis (p : CoordinateIdx (𝕜 := Real) E) :
      basis p = frame p x0 := by
    exact coordinateFrameAt_toBasis_apply (I := I) x0 p
  have hinv : MetricInverseInBasisGen
      (I := I) (M := M) (S.base.metric s) x0 basis gInv := by
    simpa [basis, gInv, SolutionOn.family] using coordInvReal (I := I) S x0 s
  have hInv (p q : CoordinateIdx (𝕜 := Real) E) :
      gInv p q = gInv q p :=
    invMetric_symm (I := I) (M := M) (S.base.metric s) x0 basis gInv hinv p q
  have hRicciComp (p q : CoordinateIdx (𝕜 := Real) E) :
      ricciCompInFrame (I := I) S frame s x0 p q =
        metricRicci (I := I) (M := M) (S.base.metric s) x0
          (vec2 (I := I) (basis p) (basis q)) := by
    change S.ricciAt s x0
        (vec2 (I := I) (frame p x0) (frame q x0)) =
      metricRicci (I := I) (M := M) (S.base.metric s) x0
        (vec2 (I := I) (basis p) (basis q))
    rw [hbasis p, hbasis q, SolutionOn.ricciAt_eq]
    rfl
  have hRic (p q : CoordinateIdx (𝕜 := Real) E) :
      metricRicci (I := I) (M := M) (S.base.metric s) x0
          (vec2 (I := I) (basis p) (basis q)) =
        metricRicci (I := I) (M := M) (S.base.metric s) x0
          (vec2 (I := I) (basis q) (basis p)) :=
    metricRicciAt_symm (I := I) (M := M) (S.base.metric s) x0
      (basis p) (basis q)
  simp_rw [christoffelEvolutionRHSInFrame_eq_connectionVariationField
    (I := I) S s x0]
  calc
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame i x0) (frame j x0) (frame q x0))) *
          ricciCompInFrame (I := I) S frame s x0 k p) =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (basis i) (basis j) (basis q)) *
            metricRicci (I := I) (M := M) (S.base.metric s) x0
              (vec2 (I := I) (basis k) (basis p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hRicciComp k p]
        simp only [hbasis]
    _ = ∑ q : CoordinateIdx (𝕜 := Real) E,
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (basis i) (basis j) (basis q)) *
            metricRicci (I := I) (M := M) (S.base.metric s) x0
              (vec2 (I := I) (basis k) (basis p)) := by
        rw [Finset.sum_comm]
    _ = ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            (ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
                (vec3 (I := I) (basis i) (basis j) (basis p)) *
              metricRicci (I := I) (M := M) (S.base.metric s) x0
                (vec2 (I := I) (basis q) (basis k))) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hInv q p, hRic k q]
        ring

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPTimeDerivativeField_apply_coordinateFrame
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) (x0 : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let ricciDt := fun i j =>
      metricRicciTimeDerivativeField (I := I) (S.base.metric s) x0
        (vec2 (I := I) (frame i x0) (frame j x0))
    let partialRicciDt := fun d i j =>
      mvfderiv (I := I)
        (fun y : M =>
          metricRicciTimeDerivativeField (I := I) (S.base.metric s) y
            (vec2 (I := I) (frame i y) (frame j y)))
        x0 (frame d x0)
    let gammaDt := christoffelEvolutionRHSInFrame
      (M := M) (coordInv (I := I) S x0)
      (nablaRicComp (I := I) S frame) s x0
    hamiltonPTimeDerivativeField (I := I) (S.base.metric s) x0
        (vec3 (I := I) (frame a x0) (frame b x0) (frame c x0)) =
      partialRicciDt a b c - partialRicciDt b a c -
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            (gammaDt a c p *
                ricciCompInFrame (I := I) S frame s x0 b p +
              christoffelSymbolInFrame
                  (S.family.connection s) frame
                  (coordinateFrameAt_isLocalFrame_one (I := I) x0)
                  x0 a c p * ricciDt b p) +
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          (gammaDt b c p *
              ricciCompInFrame (I := I) S frame s x0 a p +
            christoffelSymbolInFrame
                (S.family.connection s) frame
                (coordinateFrameAt_isLocalFrame_one (I := I) x0)
                x0 b c p * ricciDt a p) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let gInv := fun p q => coordInv (I := I) S x0 s x0 p q
  have hinv : MetricInverseInBasisGen
      (I := I) (M := M) (S.base.metric s) x0 basis gInv := by
    simpa [basis, gInv, SolutionOn.family] using coordInvReal (I := I) S x0 s
  have hfirst :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelEvolutionRHSInFrame
                (M := M) (coordInv (I := I) S x0)
                (nablaRicComp (I := I) S frame) s x0 a c p *
            ricciCompInFrame (I := I) S frame s x0 b p) =
        connectionVariationRicciFirstField (I := I) (S.base.metric s) x0
          (vec3 (I := I) (frame a x0) (frame b x0) (frame c x0)) := by
    rw [christoffelEvolutionRHSInFrame_ricci_contraction
      (I := I) S s x0 a c b]
    rw [connectionVariationRicciFirstField_apply_basis
      (I := I) (S.base.metric s) basis gInv hinv]
    simp only [frame, basis, gInv, coordinateFrameAt_toBasis_apply]
  have hsecond :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelEvolutionRHSInFrame
                (M := M) (coordInv (I := I) S x0)
                (nablaRicComp (I := I) S frame) s x0 b c p *
            ricciCompInFrame (I := I) S frame s x0 a p) =
        connectionVariationRicciSecondField (I := I) (S.base.metric s) x0
          (vec3 (I := I) (frame a x0) (frame b x0) (frame c x0)) := by
    rw [christoffelEvolutionRHSInFrame_ricci_contraction
      (I := I) S s x0 b c a]
    rw [connectionVariationRicciSecondField_apply_basis
      (I := I) (S.base.metric s) basis gInv hinv]
    simp only [frame, basis, gInv, coordinateFrameAt_toBasis_apply]
  have htf : DifferentialGeometry.Geometry.Connection.IsTorsionFree
      (I := I) (metricCov (I := I) (M := M) (S.base.metric s)) := by
    exact
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) (S.base.metric s)
  have hgamma (p : CoordinateIdx (𝕜 := Real) E) :
      christoffelSymbolInFrame
          (metricCov (I := I) (M := M) (S.base.metric s)) frame
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 a b p =
        christoffelSymbolInFrame
          (metricCov (I := I) (M := M) (S.base.metric s)) frame
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 b a p := by
    simpa [frame] using
      DifferentialGeometry.Geometry.Connection.coordinate_christoffel_symm_of_torsionFree
        (I := I) htf x0 a b p
  have hgammaSum :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame
              (metricCov (I := I) (M := M) (S.base.metric s)) frame
              (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 a b p *
            metricRicciTimeDerivativeField (I := I) (S.base.metric s) x0
              (vec2 (I := I) (frame p x0) (frame c x0))) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame
              (metricCov (I := I) (M := M) (S.base.metric s)) frame
              (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 b a p *
            metricRicciTimeDerivativeField (I := I) (S.base.metric s) x0
              (vec2 (I := I) (frame p x0) (frame c x0)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hgamma p]
  rw [hamiltonPTimeDerivativeField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_sub,
    Pi.sub_apply, Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  have hswap :
      (fun q => vec3 (I := I) (frame a x0) (frame b x0) (frame c x0)
        ((Equiv.swap (0 : Fin 3) 1) q)) =
        vec3 (I := I) (frame b x0) (frame a x0) (frame c x0) := by
    funext q
    fin_cases q <;> rfl
  rw [hswap,
    metricNablaRicciTimeDerivativeField_apply_coordinateFrame
      (I := I) (S.base.metric s) x0 a b c,
    metricNablaRicciTimeDerivativeField_apply_coordinateFrame
      (I := I) (S.base.metric s) x0 b a c,
    ← hfirst, ← hsecond]
  simp only [SolutionFamily.connection, SolutionOn.family]
  simp only [frame, metricCov] at hgammaSum ⊢
  rw [hgammaSum]
  simp only [Finset.sum_add_distrib]
  ring

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPField_hasDerivWithinAt_coordinateFrame
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (a b c : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonPField (I := I) (S.base.metric s) x0
          (vec3 (I := I)
            (coordinateFrameAt (I := I) x0 a x0)
            (coordinateFrameAt (I := I) x0 b x0)
            (coordinateFrameAt (I := I) x0 c x0)))
      (hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0
        (vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x0)
          (coordinateFrameAt (I := I) x0 b x0)
          (coordinateFrameAt (I := I) x0 c x0)))
      D.carrier (t : Real) := by
  have hraw := hamiltonPField_hasDerivWithinAt_coordinateFrame_raw
    (I := I) S hS t x0 a b c
  exact hraw.congr_deriv
    (hamiltonPTimeDerivativeField_apply_coordinateFrame
      (I := I) S (t : Real) x0 a b c).symm

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPField_deriv_of_coord
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (V : (Fin 3 -> CoordinateIdx (𝕜 := Real) E) -> Real)
    (hD : forall m, HasDerivWithinAt
      (fun s : Real => hamiltonPField (I := I) (S.base.metric s) x0
        (fun q => coordinateFrameAt (I := I) x0 (m q) x0))
      (V m) D.carrier (t : Real))
    (v : Fin 3 -> TangentSpace I x0) :
    HasDerivWithinAt
      (fun s : Real => hamiltonPField (I := I) (S.base.metric s) x0 v)
      (∑ m : Fin 3 -> CoordinateIdx (𝕜 := Real) E,
        V m * ∏ q : Fin 3,
          (coordinateFrameAtToBasis (I := I) x0).coord (m q) (v q))
      D.carrier (t : Real) := by
  classical
  have hexp :
      (fun s : Real => hamiltonPField (I := I) (S.base.metric s) x0 v) =
        fun s : Real =>
          ∑ m : Fin 3 -> CoordinateIdx (𝕜 := Real) E,
            hamiltonPField (I := I) (S.base.metric s) x0
                (fun q => coordinateFrameAt (I := I) x0 (m q) x0) *
              ∏ q : Fin 3,
                (coordinateFrameAtToBasis (I := I) x0).coord (m q) (v q) := by
    funext s
    rw [tensor0S_apply_eq_sum
      (I := I) (coordinateFrameAtToBasis (I := I) x0)
        (hamiltonPField (I := I) (S.base.metric s) x0) v]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [component0S_apply]
    congr 2
    funext q
    exact coordinateFrameAt_toBasis_apply (I := I) x0 (m q)
  rw [hexp]
  refine HasDerivWithinAt.fun_sum ?_
  intro m _
  exact (hD m).mul_const _

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPField_hasDerivWithinAt_of_solution
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (v : Fin 3 -> TangentSpace I x0) :
    HasDerivWithinAt
      (fun s : Real => hamiltonPField (I := I) (S.base.metric s) x0 v)
      (hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0 v)
      D.carrier (t : Real) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let V : (Fin 3 -> CoordinateIdx (𝕜 := Real) E) -> Real := fun m =>
    hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0
      (fun q => frame (m q) x0)
  have hD (m : Fin 3 -> CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real => hamiltonPField (I := I) (S.base.metric s) x0
          (fun q => frame (m q) x0))
        (V m) D.carrier (t : Real) := by
    have hvec :
        (fun q => frame (m q) x0) =
          vec3 (I := I) (frame (m 0) x0) (frame (m 1) x0) (frame (m 2) x0) := by
      funext q
      fin_cases q <;> rfl
    change HasDerivWithinAt _
      (hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0
        (fun q => frame (m q) x0)) _ _
    rw [hvec]
    simpa only [frame] using
      hamiltonPField_hasDerivWithinAt_coordinateFrame
        (I := I) S hS t x0 (m 0) (m 1) (m 2)
  have htransport := hamiltonPField_deriv_of_coord
    (I := I) S x0 t V hD v
  refine htransport.congr_deriv ?_
  have hexp := tensor0S_apply_eq_sum
    (I := I) (coordinateFrameAtToBasis (I := I) x0)
      (hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x0) v
  simpa only [V, frame, component0S_apply, coordinateFrameAt_toBasis_apply] using
    hexp.symm

theorem hamiltonPAt_hasDerivWithinAt_of_ricci_flow
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (v : Fin 3 -> TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => hamiltonPAt (I := I) (S.base.metric s) x v)
      (hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x v)
      D.carrier (t : Real) := by
  simpa only [hamiltonPField_apply] using
    hamiltonPField_hasDerivWithinAt_of_solution (I := I) S hS t x v

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonPTimeDerivativeField_fixedBase
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (a b c : CoordinateIdx (𝕜 := Real) E) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) D.carrier D.regular (coordinateFrameSet (I := I) x0)
      (fun s x =>
        hamiltonPField (I := I) (S.base.metric s) x
          (vec3 (I := I)
            (coordinateFrameAt (I := I) x0 a x)
            (coordinateFrameAt (I := I) x0 b x)
            (coordinateFrameAt (I := I) x0 c x)))
      (fun t x =>
        hamiltonPTimeDerivativeField (I := I) (S.base.metric t) x
          (vec3 (I := I)
            (coordinateFrameAt (I := I) x0 a x)
            (coordinateFrameAt (I := I) x0 b x)
            (coordinateFrameAt (I := I) x0 c x))) := by
  let slots : Fin 3 -> CoordinateIdx (𝕜 := Real) E :=
    fun r => if r = 0 then a else if r = 1 then b else c
  refine fixedBaseOnRegLocal
    (I := I) (timeSet := D.carrier) (regularSet := D.regular)
    (u := coordinateFrameSet (I := I) x0)
    (coordinateFrameSet_open (I := I) x0) D.regular_subset
    (fun {_t} ht => D.regular_mem_nhds ht) ?_ ?_ ?_ ?_
  · intro t ht x hx
    exact hamiltonPCompInCoordinateFrame_contMDiffAt
      (I := I) S hS x0 ⟨t, ht⟩ x hx a b c
  · intro s _hs x hx
    have h := tensor0SField_coordinateFrame_mdiffAt
      (I := I) (hamiltonPField (I := I) (S.base.metric s))
      x0 x hx slots
    convert h using 1
    funext y
    congr 1
    funext r
    fin_cases r <;> simp [slots, vec3]
  · intro t _ht x hx
    have h := tensor0SField_coordinateFrame_mdiffAt
      (I := I) (hamiltonPTimeDerivativeField (I := I) (S.base.metric t))
      x0 x hx slots
    convert h using 1
    funext y
    congr 1
    funext r
    fin_cases r <;> simp [slots, vec3]
  · intro t ht x _hx
    exact hamiltonPField_hasDerivWithinAt_of_solution
      (I := I) S hS ⟨t, ht⟩ x
        (vec3 (I := I)
          (coordinateFrameAt (I := I) x0 a x)
          (coordinateFrameAt (I := I) x0 b x)
          (coordinateFrameAt (I := I) x0 c x))

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPField_hasDerivWithinAt_coordinateFrame
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (d a b c : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let gammaDt := christoffelEvolutionRHSInFrame
      (M := M) (coordInv (I := I) S x0)
      (nablaRicComp (I := I) S frame) (t : Real) x0
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonNablaPField (I := I) (S.base.metric s) x0
          (vec4 (I := I)
            (frame d x0) (frame a x0) (frame b x0) (frame c x0)))
      (hamiltonNablaPTimeDerivativeField
            (I := I) (S.base.metric (t : Real)) x0
            (vec4 (I := I)
              (frame d x0) (frame a x0) (frame b x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDt d a p *
            hamiltonPField (I := I) (S.base.metric (t : Real)) x0
              (vec3 (I := I) (frame p x0) (frame b x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDt d b p *
            hamiltonPField (I := I) (S.base.metric (t : Real)) x0
              (vec3 (I := I) (frame a x0) (frame p x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDt d c p *
            hamiltonPField (I := I) (S.base.metric (t : Real)) x0
              (vec3 (I := I) (frame a x0) (frame b x0) (frame p x0)))
      D.carrier (t : Real) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  let gammaDt := christoffelEvolutionRHSInFrame
    (M := M) (coordInv (I := I) S x0)
    (nablaRicComp (I := I) S frame) (t : Real) x0
  have hx0 : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  have hpartial :
      HasDerivWithinAt
        (fun s : Real =>
          mvfderiv (I := I)
            (fun y : M => hamiltonPField (I := I) (S.base.metric s) y
              (vec3 (I := I) (frame a y) (frame b y) (frame c y)))
            x0 (frame d x0))
        (mvfderiv (I := I)
          (fun y : M =>
            hamiltonPTimeDerivativeField
              (I := I) (S.base.metric (t : Real)) y
              (vec3 (I := I) (frame a y) (frame b y) (frame c y)))
          x0 (frame d x0))
        D.carrier (t : Real) := by
    exact fixedBaseExtDerivTimeDerivativeOnRegular_apply
      (I := I) (h := hamiltonPTimeDerivativeField_fixedBase
        (I := I) S hS x0 a b c)
      (t := (t : Real)) t.2 (x := x0) hx0 (frame d x0)
  have hP (i j k : CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real =>
          hamiltonPField (I := I) (S.base.metric s) x0
            (vec3 (I := I) (frame i x0) (frame j x0) (frame k x0)))
        (hamiltonPTimeDerivativeField
          (I := I) (S.base.metric (t : Real)) x0
          (vec3 (I := I) (frame i x0) (frame j x0) (frame k x0)))
        D.carrier (t : Real) := by
    exact hamiltonPField_hasDerivWithinAt_of_solution
      (I := I) S hS t x0
        (vec3 (I := I) (frame i x0) (frame j x0) (frame k x0))
  have hmetric := coordMetricMix (I := I) S hS x0
    (coordMetricDeriv (I := I) S hS x0)
  have hgamma (i j p : CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real =>
          christoffelSymbolInFrame (S.family.connection s) frame hframe
            x0 i j p)
        (gammaDt i j p) D.carrier (t : Real) := by
    simpa [frame, hframe, gammaDt] using
      coordGammaEvol (I := I) S hS x0 hmetric t x0 hx0 i j p
  have hfirst := HasDerivWithinAt.fun_sum
    (u := Finset.univ) (fun p _ => (hgamma d a p).mul (hP p b c))
  have hsecond := HasDerivWithinAt.fun_sum
    (u := Finset.univ) (fun p _ => (hgamma d b p).mul (hP a p c))
  have hthird := HasDerivWithinAt.fun_sum
    (u := Finset.univ) (fun p _ => (hgamma d c p).mul (hP a b p))
  have hraw := ((hpartial.sub hfirst).sub hsecond).sub hthird
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_) ?_).congr_deriv ?_
  · simpa [frame, hframe, SolutionFamily.connection, SolutionOn.family, metricCov] using
      hamiltonNablaPField_apply_coordinateFrame
        (I := I) (S.base.metric s) x0 d a b c
  · simpa [frame, hframe, SolutionFamily.connection, SolutionOn.family, metricCov] using
      hamiltonNablaPField_apply_coordinateFrame
        (I := I) (S.base.metric (t : Real)) x0 d a b c
  · have htime := hamiltonNablaPTimeDerivativeField_apply_coordinateFrame
      (I := I) (S.base.metric (t : Real)) x0 d a b c
    dsimp only at htime
    simp only [SolutionFamily.connection, SolutionOn.family, metricCov] at htime ⊢
    rw [htime]
    simp_rw [Finset.sum_add_distrib]
    ring

private def connectionVariationPFirstFieldPerm : Equiv.Perm (Fin 6) where
  toFun q :=
    if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else
      if q = 3 then 1 else if q = 4 then 4 else 5
  invFun q :=
    if q = 0 then 2 else if q = 1 then 3 else if q = 2 then 0 else
      if q = 3 then 1 else if q = 4 then 4 else 5
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def connectionVariationPSecondFieldPerm : Equiv.Perm (Fin 6) where
  toFun q :=
    if q = 0 then 2 else if q = 1 then 4 else if q = 2 then 0 else
      if q = 3 then 3 else if q = 4 then 1 else 5
  invFun q :=
    if q = 0 then 2 else if q = 1 then 4 else if q = 2 then 0 else
      if q = 3 then 3 else if q = 4 then 1 else 5
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private def connectionVariationPThirdFieldPerm : Equiv.Perm (Fin 6) where
  toFun q :=
    if q = 0 then 2 else if q = 1 then 5 else if q = 2 then 0 else
      if q = 3 then 3 else if q = 4 then 4 else 1
  invFun q :=
    if q = 0 then 2 else if q = 1 then 5 else if q = 2 then 0 else
      if q = 3 then 3 else if q = 4 then 4 else 1
  left_inv q := by
    fin_cases q <;> simp
  right_inv q := by
    fin_cases q <;> simp

private noncomputable def connectionVariationPFirstField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      connectionVariationPFirstFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (ricciFlowConnectionVariationField (I := I) g)
        (hamiltonPField (I := I) g)))

private noncomputable def connectionVariationPSecondField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      connectionVariationPSecondFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (ricciFlowConnectionVariationField (I := I) g)
        (hamiltonPField (I := I) g)))

private noncomputable def connectionVariationPThirdField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      connectionVariationPThirdFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞)
        (ricciFlowConnectionVariationField (I := I) g)
        (hamiltonPField (I := I) g)))

private noncomputable def hamiltonNablaPActualTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  hamiltonNablaPTimeDerivativeField (I := I) g -
    connectionVariationPFirstField (I := I) g -
    connectionVariationPSecondField (I := I) g -
    connectionVariationPThirdField (I := I) g

private theorem connectionVariationPFirstField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (D A B C : TangentSpace I x) :
    connectionVariationPFirstField (I := I) g x
        (vec4 (I := I) D A B C) =
      ∑ p : Idx, ∑ q : Idx,
        gInv p q *
          (ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) D A (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) (basis q) B C)) := by
  rw [connectionVariationPFirstField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 1
  · apply congrArg (fun slots =>
      ricciFlowConnectionVariationField (I := I) g x slots)
    funext r
    fin_cases r <;> rfl
  · apply congrArg (fun slots => hamiltonPField (I := I) g x slots)
    funext r
    fin_cases r <;> rfl

private theorem connectionVariationPSecondField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (D A B C : TangentSpace I x) :
    connectionVariationPSecondField (I := I) g x
        (vec4 (I := I) D A B C) =
      ∑ p : Idx, ∑ q : Idx,
        gInv p q *
          (ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) D B (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) A (basis q) C)) := by
  rw [connectionVariationPSecondField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 1
  · apply congrArg (fun slots =>
      ricciFlowConnectionVariationField (I := I) g x slots)
    funext r
    fin_cases r <;> rfl
  · apply congrArg (fun slots => hamiltonPField (I := I) g x slots)
    funext r
    fin_cases r <;> rfl

private theorem connectionVariationPThirdField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (D A B C : TangentSpace I x) :
    connectionVariationPThirdField (I := I) g x
        (vec4 (I := I) D A B C) =
      ∑ p : Idx, ∑ q : Idx,
        gInv p q *
          (ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) D C (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) A B (basis q))) := by
  rw [connectionVariationPThirdField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  congr 1
  · apply congrArg (fun slots =>
      ricciFlowConnectionVariationField (I := I) g x slots)
    funext r
    fin_cases r <;> rfl
  · apply congrArg (fun slots => hamiltonPField (I := I) g x slots)
    funext r
    fin_cases r <;> rfl

open DifferentialGeometry.Tensor.Coordinates in
private theorem christoffelEvolutionRHSInFrame_tensor_contraction
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (A : CoordinateIdx (𝕜 := Real) E -> Real) :
    let frame := coordinateFrameAt (I := I) x0
    let gInv := fun p q => coordInv (I := I) S x0 s x0 p q
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        christoffelEvolutionRHSInFrame
            (M := M) (coordInv (I := I) S x0)
            (nablaRicComp (I := I) S frame) s x0 i j p * A p) =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            (ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame i x0) (frame j x0) (frame p x0)) *
              A q) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let gInv := fun p q => coordInv (I := I) S x0 s x0 p q
  have hinv : MetricInverseInBasisGen
      (I := I) (M := M) (S.base.metric s) x0 basis gInv := by
    simpa [basis, gInv, SolutionOn.family] using
      coordInvReal (I := I) S x0 s
  have hInv (p q : CoordinateIdx (𝕜 := Real) E) :
      gInv p q = gInv q p :=
    invMetric_symm (I := I) (M := M) (S.base.metric s) x0
      basis gInv hinv p q
  simp_rw [christoffelEvolutionRHSInFrame_eq_connectionVariationField
    (I := I) S s x0]
  calc
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame i x0) (frame j x0) (frame q x0))) * A p) =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            (ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame i x0) (frame j x0) (frame q x0)) *
              A p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ q : CoordinateIdx (𝕜 := Real) E,
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            (ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame i x0) (frame j x0) (frame q x0)) *
              A p) := by
        rw [Finset.sum_comm]
    _ = ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          gInv p q *
            (ricciFlowConnectionVariationField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame i x0) (frame j x0) (frame p x0)) *
              A q) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hInv q p]

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPActualTimeDerivativeField_apply_coordinateFrame
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) (x0 : M)
    (d a b c : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let gammaDt := christoffelEvolutionRHSInFrame
      (M := M) (coordInv (I := I) S x0)
      (nablaRicComp (I := I) S frame) s x0
    hamiltonNablaPActualTimeDerivativeField
          (I := I) (S.base.metric s) x0
          (vec4 (I := I)
            (frame d x0) (frame a x0) (frame b x0) (frame c x0)) =
      hamiltonNablaPTimeDerivativeField
            (I := I) (S.base.metric s) x0
            (vec4 (I := I)
              (frame d x0) (frame a x0) (frame b x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDt d a p *
            hamiltonPField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame p x0) (frame b x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDt d b p *
            hamiltonPField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame a x0) (frame p x0) (frame c x0)) -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDt d c p *
            hamiltonPField (I := I) (S.base.metric s) x0
              (vec3 (I := I) (frame a x0) (frame b x0) (frame p x0)) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let gInv := fun p q => coordInv (I := I) S x0 s x0 p q
  have hinv : MetricInverseInBasisGen
      (I := I) (M := M) (S.base.metric s) x0 basis gInv := by
    simpa [basis, gInv, SolutionOn.family] using
      coordInvReal (I := I) S x0 s
  rw [hamiltonNablaPActualTimeDerivativeField]
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply,
    Tensor0SSpace.sub_apply]
  rw [connectionVariationPFirstField_apply_basis
      (I := I) (S.base.metric s) basis gInv hinv,
    connectionVariationPSecondField_apply_basis
      (I := I) (S.base.metric s) basis gInv hinv,
    connectionVariationPThirdField_apply_basis
      (I := I) (S.base.metric s) basis gInv hinv]
  simp only [basis, gInv, coordinateFrameAt_toBasis_apply]
  rw [← christoffelEvolutionRHSInFrame_tensor_contraction
      (I := I) S s x0 d a
        (fun p => hamiltonPField (I := I) (S.base.metric s) x0
          (vec3 (I := I) (frame p x0) (frame b x0) (frame c x0))),
    ← christoffelEvolutionRHSInFrame_tensor_contraction
      (I := I) S s x0 d b
        (fun p => hamiltonPField (I := I) (S.base.metric s) x0
          (vec3 (I := I) (frame a x0) (frame p x0) (frame c x0))),
    ← christoffelEvolutionRHSInFrame_tensor_contraction
      (I := I) S s x0 d c
        (fun p => hamiltonPField (I := I) (S.base.metric s) x0
          (vec3 (I := I) (frame a x0) (frame b x0) (frame p x0)))]

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPField_hasDerivWithinAt_coordinateFrame_actual
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (d a b c : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonNablaPField (I := I) (S.base.metric s) x0
          (vec4 (I := I)
            (coordinateFrameAt (I := I) x0 d x0)
            (coordinateFrameAt (I := I) x0 a x0)
            (coordinateFrameAt (I := I) x0 b x0)
            (coordinateFrameAt (I := I) x0 c x0)))
      (hamiltonNablaPActualTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0
          (vec4 (I := I)
            (coordinateFrameAt (I := I) x0 d x0)
            (coordinateFrameAt (I := I) x0 a x0)
            (coordinateFrameAt (I := I) x0 b x0)
            (coordinateFrameAt (I := I) x0 c x0)))
      D.carrier (t : Real) := by
  have hraw := hamiltonNablaPField_hasDerivWithinAt_coordinateFrame
    (I := I) S hS t x0 d a b c
  exact hraw.congr_deriv
    (hamiltonNablaPActualTimeDerivativeField_apply_coordinateFrame
      (I := I) S (t : Real) x0 d a b c).symm

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPField_deriv_of_coord
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (V : (Fin 4 -> CoordinateIdx (𝕜 := Real) E) -> Real)
    (hD : forall m, HasDerivWithinAt
      (fun s : Real => hamiltonNablaPField (I := I) (S.base.metric s) x0
        (fun q => coordinateFrameAt (I := I) x0 (m q) x0))
      (V m) D.carrier (t : Real))
    (v : Fin 4 -> TangentSpace I x0) :
    HasDerivWithinAt
      (fun s : Real => hamiltonNablaPField (I := I) (S.base.metric s) x0 v)
      (∑ m : Fin 4 -> CoordinateIdx (𝕜 := Real) E,
        V m * ∏ q : Fin 4,
          (coordinateFrameAtToBasis (I := I) x0).coord (m q) (v q))
      D.carrier (t : Real) := by
  classical
  have hexp :
      (fun s : Real => hamiltonNablaPField (I := I) (S.base.metric s) x0 v) =
        fun s : Real =>
          ∑ m : Fin 4 -> CoordinateIdx (𝕜 := Real) E,
            hamiltonNablaPField (I := I) (S.base.metric s) x0
                (fun q => coordinateFrameAt (I := I) x0 (m q) x0) *
              ∏ q : Fin 4,
                (coordinateFrameAtToBasis (I := I) x0).coord (m q) (v q) := by
    funext s
    rw [tensor0S_apply_eq_sum
      (I := I) (coordinateFrameAtToBasis (I := I) x0)
        (hamiltonNablaPField (I := I) (S.base.metric s) x0) v]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [component0S_apply]
    congr 2
    funext q
    exact coordinateFrameAt_toBasis_apply (I := I) x0 (m q)
  rw [hexp]
  refine HasDerivWithinAt.fun_sum ?_
  intro m _
  exact (hD m).mul_const _

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonNablaPField_hasDerivWithinAt_of_solution
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (v : Fin 4 -> TangentSpace I x0) :
    HasDerivWithinAt
      (fun s : Real => hamiltonNablaPField (I := I) (S.base.metric s) x0 v)
      (hamiltonNablaPActualTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0 v)
      D.carrier (t : Real) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let V : (Fin 4 -> CoordinateIdx (𝕜 := Real) E) -> Real := fun m =>
    hamiltonNablaPActualTimeDerivativeField
      (I := I) (S.base.metric (t : Real)) x0
        (fun q => frame (m q) x0)
  have hD (m : Fin 4 -> CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real => hamiltonNablaPField (I := I) (S.base.metric s) x0
          (fun q => frame (m q) x0))
        (V m) D.carrier (t : Real) := by
    have hvec :
        (fun q => frame (m q) x0) =
          vec4 (I := I) (frame (m 0) x0) (frame (m 1) x0)
            (frame (m 2) x0) (frame (m 3) x0) := by
      funext q
      fin_cases q <;> rfl
    change HasDerivWithinAt _
      (hamiltonNablaPActualTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0
          (fun q => frame (m q) x0)) _ _
    rw [hvec]
    simpa only [frame] using
      hamiltonNablaPField_hasDerivWithinAt_coordinateFrame_actual
        (I := I) S hS t x0 (m 0) (m 1) (m 2) (m 3)
  have htransport := hamiltonNablaPField_deriv_of_coord
    (I := I) S x0 t V hD v
  refine htransport.congr_deriv ?_
  have hexp := tensor0S_apply_eq_sum
    (I := I) (coordinateFrameAtToBasis (I := I) x0)
      (hamiltonNablaPActualTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0) v
  simpa only [V, frame, component0S_apply, coordinateFrameAt_toBasis_apply] using
    hexp.symm

private noncomputable def ricciNablaPTraceField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        (Equiv.swap (1 : Fin 6) 2)
        (tensor0SFieldProduct (s := 2) (q := 4) (∞ : WithTop ℕ∞)
          (metricRicci (I := I) (M := M) g :
            Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) 2)
          (hamiltonNablaPField (I := I) g))))

private noncomputable def hamiltonDivPTimeDerivativeField
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  metricTraceFirstTwoField (I := I) (M := M) g
      (hamiltonNablaPActualTimeDerivativeField (I := I) g) +
    (2 : Real) • ricciNablaPTraceField (I := I) g

private theorem ricciNablaPTraceField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    ricciNablaPTraceField (I := I) g x (vec2 (I := I) A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              (metricRicci (I := I) (M := M) g x
                  (vec2 (I := I) (basis k) (basis i)) *
                hamiltonNablaPField (I := I) g x
                  (vec4 (I := I) (basis l) (basis j) A B))) := by
  rw [ricciNablaPTraceField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply]
  have hleft :
      ((fun q => metricTraceInput (I := I) (basis k) (basis l)
        (metricTraceInput (I := I) (basis i) (basis j)
          (vec2 (I := I) A B)) ((Equiv.swap (1 : Fin 6) 2) q)) ∘
          Fin.castAdd 4) =
        vec2 (I := I) (basis k) (basis i) := by
    funext q
    fin_cases q <;> rfl
  have hright :
      ((fun q => metricTraceInput (I := I) (basis k) (basis l)
        (metricTraceInput (I := I) (basis i) (basis j)
          (vec2 (I := I) A B)) ((Equiv.swap (1 : Fin 6) 2) q)) ∘
          Fin.natAdd 2) =
        vec4 (I := I) (basis l) (basis j) A B := by
    funext q
    fin_cases q <;> rfl
  rw [hleft, hright]

private theorem hamiltonDivPTimeDerivativeField_apply_basis
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonDivPTimeDerivativeField (I := I) g x (vec2 (I := I) A B) =
      (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          hamiltonNablaPActualTimeDerivativeField (I := I) g x
            (vec4 (I := I) (basis i) (basis j) A B)) +
        2 * ricciNablaPTraceField (I := I) g x
          (vec2 (I := I) A B) := by
  rw [hamiltonDivPTimeDerivativeField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  have htrace (i j : Idx) :
      metricTraceInput (I := I) (basis i) (basis j) (vec2 (I := I) A B) =
        vec4 (I := I) (basis i) (basis j) A B := by
    funext q
    fin_cases q <;> rfl
  simp_rw [htrace]

private theorem inverse_metric_derivative_trace_contraction
    {Idx : Type*} [Fintype Idx]
    (gInv Ric NP : Idx -> Idx -> Real)
    (hInv : forall i j, gInv i j = gInv j i) :
    (∑ i, ∑ j,
        (2 * ∑ k, ∑ l, gInv i k * gInv j l * Ric k l) * NP i j) =
      2 * ∑ i, ∑ j, gInv i j *
        (∑ k, ∑ l, gInv k l * (Ric k i * NP l j)) := by
  classical
  have hreorder :
      (∑ i, ∑ j, ∑ k, ∑ l,
        gInv i j * gInv k l * Ric k i * NP l j) =
      ∑ l, ∑ j, ∑ k, ∑ i,
        gInv i j * gInv k l * Ric k i * NP l j := by
    calc
      (∑ i, ∑ j, ∑ k, ∑ l,
          gInv i j * gInv k l * Ric k i * NP l j) =
        ∑ i, ∑ j, ∑ l, ∑ k,
          gInv i j * gInv k l * Ric k i * NP l j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ l, ∑ j, ∑ k,
          gInv i j * gInv k l * Ric k i * NP l j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ l, ∑ i, ∑ j, ∑ k,
          gInv i j * gInv k l * Ric k i * NP l j := by
            rw [Finset.sum_comm]
      _ = ∑ l, ∑ j, ∑ i, ∑ k,
          gInv i j * gInv k l * Ric k i * NP l j := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ l, ∑ j, ∑ k, ∑ i,
          gInv i j * gInv k l * Ric k i * NP l j := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_comm]
  have hterm :
      (∑ l, ∑ j, ∑ k, ∑ i,
        gInv i j * gInv k l * Ric k i * NP l j) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        gInv i k * gInv j l * Ric k l * NP i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hInv l j, hInv k i]
    ring_nf
  calc
    (∑ i, ∑ j,
        (2 * ∑ k, ∑ l, gInv i k * gInv j l * Ric k l) * NP i j) =
      2 * ∑ i, ∑ j, ∑ k, ∑ l,
        gInv i k * gInv j l * Ric k l * NP i j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          ring_nf
    _ = 2 * ∑ l, ∑ j, ∑ k, ∑ i,
        gInv i j * gInv k l * Ric k i * NP l j := by rw [hterm]
    _ = 2 * ∑ i, ∑ j, ∑ k, ∑ l,
        gInv i j * gInv k l * Ric k i * NP l j := by rw [hreorder]
    _ = 2 * ∑ i, ∑ j, gInv i j *
        (∑ k, ∑ l, gInv k l * (Ric k i * NP l j)) := by
          simp only [Finset.mul_sum]
          ring_nf

open DifferentialGeometry.Tensor.Coordinates in
private theorem inverseMetricEvolution_hamiltonNablaP_contraction
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x0 : M) (A B : TangentSpace I x0) :
    let frame := coordinateFrameAt (I := I) x0
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricEvolutionRHSInFrame
            (I := I) S (coordInv (I := I) S x0) frame t x0 i j *
          hamiltonNablaPField (I := I) (S.base.metric t) x0
            (vec4 (I := I) (frame i x0) (frame j x0) A B)) =
      2 * ricciNablaPTraceField (I := I) (S.base.metric t) x0
        (vec2 (I := I) A B) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let g := S.base.metric t
  let gInv := fun i j => coordInv (I := I) S x0 t x0 i j
  let Ric := fun i j => metricRicci (I := I) (M := M) g x0
    (vec2 (I := I) (basis i) (basis j))
  let NP := fun i j => hamiltonNablaPField (I := I) g x0
    (vec4 (I := I) (basis i) (basis j) A B)
  have hinv : MetricInverseInBasisGen
      (I := I) (M := M) g x0 basis gInv := by
    simpa [g, basis, gInv, SolutionOn.family] using
      coordInvReal (I := I) S x0 t
  have hInv (i j : CoordinateIdx (𝕜 := Real) E) :
      gInv i j = gInv j i :=
    invMetric_symm (I := I) (M := M) g x0 basis gInv hinv i j
  have hRicComp (i j : CoordinateIdx (𝕜 := Real) E) :
      ricciCompInFrame (I := I) S frame t x0 i j = Ric i j := by
    change S.ricciAt t x0
        (vec2 (I := I) (frame i x0) (frame j x0)) =
      metricRicci (I := I) (M := M) g x0
        (vec2 (I := I) (basis i) (basis j))
    rw [show basis i = frame i x0 from
        coordinateFrameAt_toBasis_apply (I := I) x0 i,
      show basis j = frame j x0 from
        coordinateFrameAt_toBasis_apply (I := I) x0 j,
      SolutionOn.ricciAt_eq]
    rfl
  have hRaised (i j : CoordinateIdx (𝕜 := Real) E) :
      raisedRicciCompInFrame
          (I := I) S (coordInv (I := I) S x0) frame t x0 i j =
        ∑ k, ∑ l, gInv i k * gInv j l * Ric k l := by
    rw [raisedRicciCompInFrame_apply]
    simp_rw [hRicComp]
    rfl
  have hInvDt (i j : CoordinateIdx (𝕜 := Real) E) :
      inverseMetricEvolutionRHSInFrame
          (I := I) S (coordInv (I := I) S x0) frame t x0 i j =
        2 * (∑ k, ∑ l, gInv i k * gInv j l * Ric k l) := by
    rw [inverseMetricEvolutionRHSInFrame, hRaised]
  have hNPComp (i j : CoordinateIdx (𝕜 := Real) E) :
      hamiltonNablaPField (I := I) g x0
          (vec4 (I := I) (frame i x0) (frame j x0) A B) = NP i j := by
    simp only [NP, basis, frame, coordinateFrameAt_toBasis_apply]
  have hTrace := ricciNablaPTraceField_apply_basis
    (I := I) g basis gInv hinv A B
  calc
    (∑ i, ∑ j,
        inverseMetricEvolutionRHSInFrame
            (I := I) S (coordInv (I := I) S x0) frame t x0 i j *
          hamiltonNablaPField (I := I) g x0
            (vec4 (I := I) (frame i x0) (frame j x0) A B)) =
      ∑ i, ∑ j,
        (2 * ∑ k, ∑ l, gInv i k * gInv j l * Ric k l) * NP i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hInvDt, hNPComp]
    _ = 2 * ∑ i, ∑ j, gInv i j *
        (∑ k, ∑ l, gInv k l * (Ric k i * NP l j)) :=
      inverse_metric_derivative_trace_contraction gInv Ric NP hInv
    _ = 2 * ricciNablaPTraceField (I := I) g x0
        (vec2 (I := I) A B) := by rw [hTrace]

theorem hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
    [T2Space M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv)
    (A B : TangentSpace I x) :
    hamiltonDivPAt (I := I) g x (vec2 (I := I) A B) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * hamiltonNablaPField (I := I) g x
          (vec4 (I := I) (basis i) (basis j) A B) := by
  rw [hamiltonDivPAt_apply (I := I) g basis gInv hinv A B]
  simp only [hamiltonNablaPField_apply, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [metricNabla2Ric_last_two_symm (I := I) (M := M)]

theorem hamiltonMOriginField_apply
    [T2Space M]
    (origin time : Real) (g : SmoothRiemannianMetric I M) (x : M) :
    hamiltonMOriginField (I := I) origin time g x =
      hamiltonDivPAt (I := I) g x +
        hamiltonCurvatureRicciAt (I := I) g x +
        (1 / (2 * (time - origin)) : Real) •
          metricRicci (I := I) (M := M) g x := by
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
    (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
        (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
  apply tensor0SSpace_ext (I := I) 2 x
  intro v
  let A := v 0
  let B := v 1
  have hv : v = vec2 (I := I) A B := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  have hdiv :
      hamiltonDivPField (I := I) g x (vec2 (I := I) A B) =
        hamiltonDivPAt (I := I) g x (vec2 (I := I) A B) := by
    rw [hamiltonDivPField, metricTraceFirstTwoField_apply,
      metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
    rw [metricTrace0S2InBasis]
    trans ∑ i, ∑ j, gInv i j * hamiltonNablaPField (I := I) g x
      (vec4 (I := I) (basis i) (basis j) A B)
    · refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      apply congrArg (hamiltonNablaPField (I := I) g x)
      funext k
      fin_cases k <;> rfl
    · exact (hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
        (I := I) g basis gInv hinv A B).symm
  rw [hamiltonMOriginField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply]
  rw [hdiv, hamiltonCurvatureRicciField_eq_at_basis
    (I := I) g basis gInv hinv A B]

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonDivPAt_hasDerivWithinAt_coordinateFrame
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (a b : CoordinateIdx (𝕜 := Real) E) :
    let frame := coordinateFrameAt (I := I) x0
    let gInv := fun s i j => coordInv (I := I) S x0 s x0 i j
    let gInvDt := fun i j =>
      inverseMetricEvolutionRHSInFrame
        (I := I) S (coordInv (I := I) S x0) frame (t : Real) x0 i j
    let gammaDt := christoffelEvolutionRHSInFrame
      (M := M) (coordInv (I := I) S x0)
      (nablaRicComp (I := I) S frame) (t : Real) x0
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonDivPAt (I := I) (S.base.metric s) x0
          (vec2 (I := I) (frame a x0) (frame b x0)))
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          (gInvDt i j *
              hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x0
                (vec4 (I := I)
                  (frame i x0) (frame j x0) (frame a x0) (frame b x0)) +
            gInv (t : Real) i j *
              (hamiltonNablaPTimeDerivativeField
                    (I := I) (S.base.metric (t : Real)) x0
                    (vec4 (I := I)
                      (frame i x0) (frame j x0) (frame a x0) (frame b x0)) -
                ∑ p : CoordinateIdx (𝕜 := Real) E,
                  gammaDt i j p *
                    hamiltonPField (I := I) (S.base.metric (t : Real)) x0
                      (vec3 (I := I) (frame p x0) (frame a x0) (frame b x0)) -
                ∑ p : CoordinateIdx (𝕜 := Real) E,
                  gammaDt i a p *
                    hamiltonPField (I := I) (S.base.metric (t : Real)) x0
                      (vec3 (I := I) (frame j x0) (frame p x0) (frame b x0)) -
                ∑ p : CoordinateIdx (𝕜 := Real) E,
                  gammaDt i b p *
                    hamiltonPField (I := I) (S.base.metric (t : Real)) x0
                      (vec3 (I := I) (frame j x0) (frame a x0) (frame p x0)))))
      D.carrier (t : Real) := by
  classical
  dsimp only
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let gInv := fun s i j => coordInv (I := I) S x0 s x0 i j
  let gInvDt := fun i j =>
    inverseMetricEvolutionRHSInFrame
      (I := I) S (coordInv (I := I) S x0) frame (t : Real) x0 i j
  let gammaDt := christoffelEvolutionRHSInFrame
    (M := M) (coordInv (I := I) S x0)
    (nablaRicComp (I := I) S frame) (t : Real) x0
  have hx0 : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  have hinv (s : Real) : MetricInverseInBasisGen
      (I := I) (M := M) (S.base.metric s) x0 basis (gInv s) := by
    simpa [basis, gInv, SolutionOn.family] using
      coordInvReal (I := I) S x0 s
  have happ (s : Real) :
      hamiltonDivPAt (I := I) (S.base.metric s) x0
          (vec2 (I := I) (frame a x0) (frame b x0)) =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv s i j *
              hamiltonNablaPField (I := I) (S.base.metric s) x0
                (vec4 (I := I)
                  (frame i x0) (frame j x0) (frame a x0) (frame b x0)) := by
    simpa only [basis, gInv, coordinateFrameAt_toBasis_apply] using
      hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
        (I := I) (S.base.metric s) basis (gInv s) (hinv s)
          (frame a x0) (frame b x0)
  have hInv (i j : CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt (fun s : Real => gInv s i j) (gInvDt i j)
        D.carrier (t : Real) := by
    simpa only [gInv, gInvDt, frame] using
      coordInvEvol (I := I) S hS x0 t x0 hx0 i j
  have hNabla (i j : CoordinateIdx (𝕜 := Real) E) :=
    hamiltonNablaPField_hasDerivWithinAt_coordinateFrame
      (I := I) S hS t x0 i j a b
  have hraw := HasDerivWithinAt.fun_sum
    (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
    (fun i _ => HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
      (fun j _ => (hInv i j).mul (hNabla i j)))
  refine hraw.congr ?_ ?_
  · intro s _hs
    exact happ s
  · exact happ (t : Real)

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonDivPAt_hasDerivWithinAt_coordinateFrame_actual
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (a b : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonDivPAt (I := I) (S.base.metric s) x0
          (vec2 (I := I)
            (coordinateFrameAt (I := I) x0 a x0)
            (coordinateFrameAt (I := I) x0 b x0)))
      (hamiltonDivPTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0
          (vec2 (I := I)
            (coordinateFrameAt (I := I) x0 a x0)
            (coordinateFrameAt (I := I) x0 b x0)))
      D.carrier (t : Real) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let basis := coordinateFrameAtToBasis (I := I) x0
  let g := S.base.metric (t : Real)
  let gInv := fun i j => coordInv (I := I) S x0 (t : Real) x0 i j
  let gInvDt := fun i j =>
    inverseMetricEvolutionRHSInFrame
      (I := I) S (coordInv (I := I) S x0) frame (t : Real) x0 i j
  have hinv : MetricInverseInBasisGen
      (I := I) (M := M) g x0 basis gInv := by
    simpa [g, basis, gInv, SolutionOn.family] using
      coordInvReal (I := I) S x0 (t : Real)
  have hraw := hamiltonDivPAt_hasDerivWithinAt_coordinateFrame
    (I := I) S hS t x0 a b
  have hactual (i j : CoordinateIdx (𝕜 := Real) E) :=
    hamiltonNablaPActualTimeDerivativeField_apply_coordinateFrame
      (I := I) S (t : Real) x0 i j a b
  have hmetric := inverseMetricEvolution_hamiltonNablaP_contraction
    (I := I) S (t : Real) x0 (frame a x0) (frame b x0)
  have hfield := hamiltonDivPTimeDerivativeField_apply_basis
    (I := I) g basis gInv hinv (frame a x0) (frame b x0)
  refine hraw.congr_deriv ?_
  calc
    (∑ i, ∑ j,
        (gInvDt i j *
              hamiltonNablaPField (I := I) g x0
                (vec4 (I := I)
                  (frame i x0) (frame j x0) (frame a x0) (frame b x0)) +
          gInv i j *
            (hamiltonNablaPTimeDerivativeField (I := I) g x0
                (vec4 (I := I)
                  (frame i x0) (frame j x0) (frame a x0) (frame b x0)) -
              ∑ p, christoffelEvolutionRHSInFrame
                    (M := M) (coordInv (I := I) S x0)
                    (nablaRicComp (I := I) S frame) (t : Real) x0 i j p *
                  hamiltonPField (I := I) g x0
                    (vec3 (I := I)
                      (frame p x0) (frame a x0) (frame b x0)) -
              ∑ p, christoffelEvolutionRHSInFrame
                    (M := M) (coordInv (I := I) S x0)
                    (nablaRicComp (I := I) S frame) (t : Real) x0 i a p *
                  hamiltonPField (I := I) g x0
                    (vec3 (I := I)
                      (frame j x0) (frame p x0) (frame b x0)) -
              ∑ p, christoffelEvolutionRHSInFrame
                    (M := M) (coordInv (I := I) S x0)
                    (nablaRicComp (I := I) S frame) (t : Real) x0 i b p *
                  hamiltonPField (I := I) g x0
                    (vec3 (I := I)
                      (frame j x0) (frame a x0) (frame p x0))))) =
      ∑ i, ∑ j,
        (gInvDt i j *
              hamiltonNablaPField (I := I) g x0
                (vec4 (I := I)
                  (frame i x0) (frame j x0) (frame a x0) (frame b x0)) +
          gInv i j *
            hamiltonNablaPActualTimeDerivativeField (I := I) g x0
              (vec4 (I := I)
                (frame i x0) (frame j x0) (frame a x0) (frame b x0))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hactual i j]
    _ =
      (∑ i, ∑ j,
        gInvDt i j *
          hamiltonNablaPField (I := I) g x0
            (vec4 (I := I)
              (frame i x0) (frame j x0) (frame a x0) (frame b x0))) +
      ∑ i, ∑ j,
        gInv i j *
          hamiltonNablaPActualTimeDerivativeField (I := I) g x0
            (vec4 (I := I)
              (frame i x0) (frame j x0) (frame a x0) (frame b x0)) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ricciNablaPTraceField (I := I) g x0
          (vec2 (I := I) (frame a x0) (frame b x0)) +
        ∑ i, ∑ j,
          gInv i j *
            hamiltonNablaPActualTimeDerivativeField (I := I) g x0
              (vec4 (I := I)
                (frame i x0) (frame j x0) (frame a x0) (frame b x0)) := by
        rw [show
          (∑ i, ∑ j,
            gInvDt i j *
              hamiltonNablaPField (I := I) g x0
                (vec4 (I := I)
                  (frame i x0) (frame j x0) (frame a x0) (frame b x0))) =
            2 * ricciNablaPTraceField (I := I) g x0
              (vec2 (I := I) (frame a x0) (frame b x0)) by
                simpa only [g, gInvDt, frame] using hmetric]
    _ = hamiltonDivPTimeDerivativeField (I := I) g x0
          (vec2 (I := I) (frame a x0) (frame b x0)) := by
        rw [hfield]
        simp only [basis, frame, coordinateFrameAt_toBasis_apply]
        ring_nf

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonDivPAt_deriv_of_coord
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (V : (Fin 2 -> CoordinateIdx (𝕜 := Real) E) -> Real)
    (hD : forall m, HasDerivWithinAt
      (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x0
        (fun q => coordinateFrameAt (I := I) x0 (m q) x0))
      (V m) D.carrier (t : Real))
    (v : Fin 2 -> TangentSpace I x0) :
    HasDerivWithinAt
      (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x0 v)
      (∑ m : Fin 2 -> CoordinateIdx (𝕜 := Real) E,
        V m * ∏ q : Fin 2,
          (coordinateFrameAtToBasis (I := I) x0).coord (m q) (v q))
      D.carrier (t : Real) := by
  classical
  have hexp :
      (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x0 v) =
        fun s : Real =>
          ∑ m : Fin 2 -> CoordinateIdx (𝕜 := Real) E,
            hamiltonDivPAt (I := I) (S.base.metric s) x0
                (fun q => coordinateFrameAt (I := I) x0 (m q) x0) *
              ∏ q : Fin 2,
                (coordinateFrameAtToBasis (I := I) x0).coord (m q) (v q) := by
    funext s
    rw [tensor0S_apply_eq_sum
      (I := I) (coordinateFrameAtToBasis (I := I) x0)
        (hamiltonDivPAt (I := I) (S.base.metric s) x0) v]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [component0S_apply]
    congr 2
    funext q
    exact coordinateFrameAt_toBasis_apply (I := I) x0 (m q)
  rw [hexp]
  refine HasDerivWithinAt.fun_sum ?_
  intro m _
  exact (hD m).mul_const _

open DifferentialGeometry.Tensor.Coordinates in
private theorem hamiltonDivPAt_hasDerivWithinAt_of_solution
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x0 : M) (v : Fin 2 -> TangentSpace I x0) :
    HasDerivWithinAt
      (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x0 v)
      (hamiltonDivPTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0 v)
      D.carrier (t : Real) := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let V : (Fin 2 -> CoordinateIdx (𝕜 := Real) E) -> Real := fun m =>
    hamiltonDivPTimeDerivativeField
      (I := I) (S.base.metric (t : Real)) x0
        (fun q => frame (m q) x0)
  have hD (m : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x0
          (fun q => frame (m q) x0))
        (V m) D.carrier (t : Real) := by
    have hvec :
        (fun q => frame (m q) x0) =
          vec2 (I := I) (frame (m 0) x0) (frame (m 1) x0) := by
      funext q
      fin_cases q <;> rfl
    change HasDerivWithinAt _
      (hamiltonDivPTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0
          (fun q => frame (m q) x0)) _ _
    rw [hvec]
    simpa only [frame] using
      hamiltonDivPAt_hasDerivWithinAt_coordinateFrame_actual
        (I := I) S hS t x0 (m 0) (m 1)
  have htransport := hamiltonDivPAt_deriv_of_coord
    (I := I) S x0 t V hD v
  refine htransport.congr_deriv ?_
  have hexp := tensor0S_apply_eq_sum
    (I := I) (coordinateFrameAtToBasis (I := I) x0)
      (hamiltonDivPTimeDerivativeField
        (I := I) (S.base.metric (t : Real)) x0) v
  simpa only [V, frame, component0S_apply, coordinateFrameAt_toBasis_apply] using
    hexp.symm

private theorem basisInvMetric_hasDerivWithinAt_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => basisInvMetric (I := I) (S.base.metric s) x basis i j)
      (2 *
        (∑ a : Idx, ∑ b : Idx,
          basisInvMetric (I := I) (S.base.metric (t : Real)) x basis i a *
            basisInvMetric (I := I) (S.base.metric (t : Real)) x basis j b *
              metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
                (vec2 (I := I) (basis a) (basis b))))
      D.carrier (t : Real) := by
  classical
  let metric : Real -> Idx -> Idx -> Real := fun s a b =>
    (S.base.metric s).inner x (basis a) (basis b)
  let ric : Idx -> Idx -> Real := fun a b =>
    metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
      (vec2 (I := I) (basis a) (basis b))
  let gInv : Real -> Idx -> Idx -> Real := fun s =>
    basisInvMetric (I := I) (S.base.metric s) x basis
  let G : Real -> (Idx -> Real) →L[Real] (Idx -> Real) := fun s =>
    matrixCLM (Idx := Idx) (metric s)
  let Gdot : (Idx -> Real) →L[Real] (Idx -> Real) :=
    matrixCLM (Idx := Idx) (fun a b => (-2 : Real) * ric a b)
  let InvG : (Idx -> Real) →L[Real] (Idx -> Real) :=
    ContinuousLinearMap.inverse (G (t : Real))
  let dInv : (Idx -> Real) →L[Real] (Idx -> Real) :=
    -(InvG * Gdot * InvG)
  have hinv (s : Real) :
      MetricInverseInBasisGen (I := I) (M := M) (S.base.metric s) x basis (gInv s) := by
    simpa only [gInv] using
      basisInvMetric_real (I := I) (S.base.metric s) x basis
  have hGInv (s : Real) :
      G s * matrixCLM (Idx := Idx) (gInv s) =
        ContinuousLinearMap.id Real (Idx -> Real) := by
    ext v a
    simpa [G, metric, mul_apply_eq_comp] using
      metric_mul_inverse_apply (metric s) (gInv s) (fun p q => (hinv s p q).2) v a
  have hInvG (s : Real) :
      matrixCLM (Idx := Idx) (gInv s) * G s =
        ContinuousLinearMap.id Real (Idx -> Real) := by
    ext v a
    simpa [G, metric, mul_apply_eq_comp] using
      inverse_mul_metric_apply (metric s) (gInv s) (fun p q => (hinv s p q).1) v a
  have hGinvertible (s : Real) : (G s).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (hGInv s) (hInvG s)
  have hInverse (s : Real) :
      ContinuousLinearMap.inverse (G s) = matrixCLM (Idx := Idx) (gInv s) :=
    ContinuousLinearMap.inverse_eq (hGInv s) (hInvG s)
  have hG : HasDerivWithinAt G Gdot D.carrier (t : Real) := by
    dsimp only [G, Gdot]
    unfold matrixCLM
    simpa [metric, ric] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          ∑ b : Idx, metric s a b • frameEntryCLM (Idx := Idx) a b)
        (A' := fun a =>
          ∑ b : Idx, ((-2 : Real) * ric a b) • frameEntryCLM (Idx := Idx) a b)
        (s := D.carrier) (x := (t : Real))
        (fun a _ha => by
          simpa using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s => metric s a b • frameEntryCLM (Idx := Idx) a b)
              (A' := fun b =>
                ((-2 : Real) * ric a b) • frameEntryCLM (Idx := Idx) a b)
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                (metric_derivWithin_eq_neg_two_ricci
                  (I := I) S hS t x (basis a) (basis b)).smul_const
                    (frameEntryCLM (Idx := Idx) a b)))))
  have hInv :
      HasDerivWithinAt
        (fun s : Real => ContinuousLinearMap.inverse (G s))
        dInv D.carrier (t : Real) := by
    have hF :=
      (hasFDerivAt_clmInv (G (t : Real)) (hGinvertible (t : Real))).comp_hasFDerivWithinAt
        (t : Real) hG.hasFDerivWithinAt
    have hderiv := hF.hasDerivWithinAt
    rw [show (ContinuousLinearMap.inverse ∘ G) =
      (fun s : Real => ContinuousLinearMap.inverse (G s)) by rfl] at hderiv
    simpa [dInv, InvG, ContinuousLinearMap.mulLeftRight_apply] using hderiv
  have hApp := hInv.clm_apply
    (hasDerivWithinAt_const
      (x := (t : Real)) (s := D.carrier)
      (c := Pi.single (M := fun _ : Idx => Real) j (1 : Real)))
  have hProj :=
    (hasDerivWithinAt_const
      (x := (t : Real)) (s := D.carrier)
      (c := (ContinuousLinearMap.proj i : (Idx -> Real) →L[Real] Real))).clm_apply hApp
  have hsymm : forall a b : Idx, gInv (t : Real) a b = gInv (t : Real) b a := by
    exact basisInvMetric_symm (I := I) (S.base.metric (t : Real)) x basis
  have hentry := matrixInvDerivEntry
    (Idx := Idx) (gInv := gInv (t : Real)) (ric := ric) hsymm i j
  refine (hProj.congr_deriv ?_).congr ?_ ?_
  · simpa [dInv, InvG, Gdot, hInverse, ContinuousLinearMap.mulLeftRight_apply,
      gInv, ric] using hentry
  · intro s _hs
    rw [hInverse s]
    simp [gInv, sum_mul_pi_single]
  · rw [hInverse (t : Real)]
    simp [gInv, sum_mul_pi_single]

noncomputable def oneTimeUhlenbeckVector
    [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (t s : Real) (X : TangentSpace I x) : TangentSpace I x :=
  X + (s - t) • ricciEndAt (I := I) g
    (metricRicci (I := I) (M := M) g x) X

omit [FiniteDimensional Real E] in
private theorem tensor02At_apply_affine_slots {x : M}
    (T : Tensor02At (I := I) (M := M) x)
    (A B RA RB : TangentSpace I x) (r : Real) :
    T (vec2 (I := I) (A + r • RA) (B + r • RB)) =
      T (vec2 (I := I) A B) +
        r * T (vec2 (I := I) RA B) +
        r * T (vec2 (I := I) A RB) +
        (r * r) * T (vec2 (I := I) RA RB) := by
  have hfirst (X Y Z : TangentSpace I x) :
      T (vec2 (I := I) (X + r • Y) Z) =
        T (vec2 (I := I) X Z) + r * T (vec2 (I := I) Y Z) := by
    let base : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hslot : vec2 (I := I) (X + r • Y) Z =
        Function.update base (0 : Fin 2) (X + r • Y) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [hslot, T.map_update_add, T.map_update_smul]
    congr 2 <;> congr 1 <;> funext q <;>
      fin_cases q <;> simp [base, vec2, Function.update]
  have hsecond (X Y Z : TangentSpace I x) :
      T (vec2 (I := I) X (Y + r • Z)) =
        T (vec2 (I := I) X Y) + r * T (vec2 (I := I) X Z) := by
    let base : Fin 2 -> TangentSpace I x := vec2 (I := I) X Y
    have hslot : vec2 (I := I) X (Y + r • Z) =
        Function.update base (1 : Fin 2) (Y + r • Z) := by
      funext q
      fin_cases q <;> simp [base, vec2, Function.update]
    rw [hslot, T.map_update_add, T.map_update_smul]
    congr 2 <;> congr 1 <;> funext q <;>
      fin_cases q <;> simp [base, vec2, Function.update]
  calc
    T (vec2 (I := I) (A + r • RA) (B + r • RB)) =
        T (vec2 (I := I) (A + r • RA) B) +
          r * T (vec2 (I := I) (A + r • RA) RB) :=
      hsecond (A + r • RA) B RB
    _ = _ := by rw [hfirst A RA B, hfirst A RA RB]; ring

omit [FiniteDimensional Real E] in
private theorem tensor02At_hasDerivWithinAt_affine_slots
    {x : M} {D : Set Real} {t : Real}
    (T : Real -> Tensor02At (I := I) (M := M) x)
    (T' : Tensor02At (I := I) (M := M) x)
    (hD : forall X Y, HasDerivWithinAt
      (fun s : Real => T s (vec2 (I := I) X Y))
      (T' (vec2 (I := I) X Y)) D t)
    (A B RA RB : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => T s
        (vec2 (I := I) (A + (s - t) • RA) (B + (s - t) • RB)))
      (T' (vec2 (I := I) A B) +
        T t (vec2 (I := I) RA B) + T t (vec2 (I := I) A RB)) D t := by
  have hexp :
      (fun s : Real => T s
        (vec2 (I := I) (A + (s - t) • RA) (B + (s - t) • RB))) =
      fun s : Real =>
        T s (vec2 (I := I) A B) +
          (s - t) * T s (vec2 (I := I) RA B) +
          (s - t) * T s (vec2 (I := I) A RB) +
          ((s - t) * (s - t)) * T s (vec2 (I := I) RA RB) := by
    funext s
    exact tensor02At_apply_affine_slots (T s) A B RA RB (s - t)
  rw [hexp]
  have hshift : HasDerivWithinAt (fun s : Real => s - t) 1 D t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hRA := hshift.mul (hD RA B)
  have hRB := hshift.mul (hD A RB)
  have hquad := (hshift.mul hshift).mul (hD RA RB)
  have hsum := (((hD A B).add hRA).add hRB).add hquad
  have hderiv :
      T' (vec2 (I := I) A B) +
          (1 * T t (vec2 (I := I) RA B) +
            (t - t) * T' (vec2 (I := I) RA B)) +
          (1 * T t (vec2 (I := I) A RB) +
            (t - t) * T' (vec2 (I := I) A RB)) +
          ((1 * (t - t) + (t - t) * 1) *
              T t (vec2 (I := I) RA RB) +
            (((fun s : Real => s - t) * fun s : Real => s - t) t) *
              T' (vec2 (I := I) RA RB)) =
        T' (vec2 (I := I) A B) +
          T t (vec2 (I := I) RA B) + T t (vec2 (I := I) A RB) := by
    simp only [Pi.mul_apply]
    ring
  refine (hsum.congr_deriv hderiv).congr ?_ ?_
  · intro s _
    rfl
  · rfl

omit [FiniteDimensional Real E] in
private theorem tensor04At_apply_affine_slots {x : M}
    (T : Tensor04At (I := I) (M := M) x)
    (A B C D RA RB RC RD : TangentSpace I x) (r : Real) :
    T (vec4 (I := I) (A + r • RA) (B + r • RB) (C + r • RC) (D + r • RD)) =
      T (vec4 (I := I) A B C D) +
        r * T (vec4 (I := I) RA B C D) +
        r * T (vec4 (I := I) A RB C D) +
        (r * r) * T (vec4 (I := I) RA RB C D) +
        r * T (vec4 (I := I) A B RC D) +
        (r * r) * T (vec4 (I := I) RA B RC D) +
        (r * r) * T (vec4 (I := I) A RB RC D) +
        (r * r * r) * T (vec4 (I := I) RA RB RC D) +
        r * T (vec4 (I := I) A B C RD) +
        (r * r) * T (vec4 (I := I) RA B C RD) +
        (r * r) * T (vec4 (I := I) A RB C RD) +
        (r * r * r) * T (vec4 (I := I) RA RB C RD) +
        (r * r) * T (vec4 (I := I) A B RC RD) +
        (r * r * r) * T (vec4 (I := I) RA B RC RD) +
        (r * r * r) * T (vec4 (I := I) A RB RC RD) +
        (r * r * r * r) * T (vec4 (I := I) RA RB RC RD) := by
  have hfirst (X Y Z W V : TangentSpace I x) :
      T (vec4 (I := I) (X + r • Y) Z W V) =
        T (vec4 (I := I) X Z W V) + r * T (vec4 (I := I) Y Z W V) := by
    let base : Fin 4 -> TangentSpace I x := vec4 (I := I) X Z W V
    have hslot : vec4 (I := I) (X + r • Y) Z W V =
        Function.update base (0 : Fin 4) (X + r • Y) := by
      funext q
      fin_cases q <;> simp [base, vec4, Function.update]
    rw [hslot, T.map_update_add, T.map_update_smul]
    congr 2 <;> congr 1 <;> funext q <;>
      fin_cases q <;> simp [base, vec4, Function.update]
  have hsecond (X Y Z W V : TangentSpace I x) :
      T (vec4 (I := I) X (Y + r • Z) W V) =
        T (vec4 (I := I) X Y W V) + r * T (vec4 (I := I) X Z W V) := by
    let base : Fin 4 -> TangentSpace I x := vec4 (I := I) X Y W V
    have hslot : vec4 (I := I) X (Y + r • Z) W V =
        Function.update base (1 : Fin 4) (Y + r • Z) := by
      funext q
      fin_cases q <;> simp [base, vec4, Function.update]
    rw [hslot, T.map_update_add, T.map_update_smul]
    congr 2 <;> congr 1 <;> funext q <;>
      fin_cases q <;> simp [base, vec4, Function.update]
  have hthird (X Y Z W V : TangentSpace I x) :
      T (vec4 (I := I) X Y (Z + r • W) V) =
        T (vec4 (I := I) X Y Z V) + r * T (vec4 (I := I) X Y W V) := by
    let base : Fin 4 -> TangentSpace I x := vec4 (I := I) X Y Z V
    have hslot : vec4 (I := I) X Y (Z + r • W) V =
        Function.update base (2 : Fin 4) (Z + r • W) := by
      funext q
      fin_cases q <;> simp [base, vec4, Function.update]
    rw [hslot, T.map_update_add, T.map_update_smul]
    congr 2 <;> congr 1 <;> funext q <;>
      fin_cases q <;> simp [base, vec4, Function.update]
  have hfourth (X Y Z W V : TangentSpace I x) :
      T (vec4 (I := I) X Y Z (W + r • V)) =
        T (vec4 (I := I) X Y Z W) + r * T (vec4 (I := I) X Y Z V) := by
    let base : Fin 4 -> TangentSpace I x := vec4 (I := I) X Y Z W
    have hslot : vec4 (I := I) X Y Z (W + r • V) =
        Function.update base (3 : Fin 4) (W + r • V) := by
      funext q
      fin_cases q <;> simp [base, vec4, Function.update]
    rw [hslot, T.map_update_add, T.map_update_smul]
    congr 2 <;> congr 1 <;> funext q <;>
      fin_cases q <;> simp [base, vec4, Function.update]
  have hfirstTwo (X Y Z W V U : TangentSpace I x) :
      T (vec4 (I := I) (X + r • Y) (Z + r • W) V U) =
        T (vec4 (I := I) X Z V U) +
          r * T (vec4 (I := I) Y Z V U) +
          r * T (vec4 (I := I) X W V U) +
          (r * r) * T (vec4 (I := I) Y W V U) := by
    rw [hsecond (X + r • Y) Z W V U, hfirst X Y Z V U,
      hfirst X Y W V U]
    ring
  rw [hfourth (A + r • RA) (B + r • RB) (C + r • RC) D RD,
    hthird (A + r • RA) (B + r • RB) C RC D,
    hthird (A + r • RA) (B + r • RB) C RC RD,
    hfirstTwo A RA B RB C D, hfirstTwo A RA B RB RC D,
    hfirstTwo A RA B RB C RD, hfirstTwo A RA B RB RC RD]
  ring

omit [FiniteDimensional Real E] in
private theorem tensor04At_hasDerivWithinAt_affine_slots
    {x : M} {Dset : Set Real} {t : Real}
    (T : Real -> Tensor04At (I := I) (M := M) x)
    (T' : Real)
    (A B C D RA RB RC RD : TangentSpace I x)
    (hbase : HasDerivWithinAt
      (fun s : Real => T s (vec4 (I := I) A B C D)) T' Dset t)
    (hDiff : forall X Y Z W, DifferentiableWithinAt Real
      (fun s : Real => T s (vec4 (I := I) X Y Z W)) Dset t)
    :
    HasDerivWithinAt
      (fun s : Real => T s
        (vec4 (I := I) (A + (s - t) • RA) (B + (s - t) • RB)
          (C + (s - t) • RC) (D + (s - t) • RD)))
      (T' +
        T t (vec4 (I := I) RA B C D) +
        T t (vec4 (I := I) A RB C D) +
        T t (vec4 (I := I) A B RC D) +
        T t (vec4 (I := I) A B C RD)) Dset t := by
  have hexp :
      (fun s : Real => T s
        (vec4 (I := I) (A + (s - t) • RA) (B + (s - t) • RB)
          (C + (s - t) • RC) (D + (s - t) • RD))) =
      fun s : Real =>
        T s (vec4 (I := I) A B C D) +
          (s - t) * T s (vec4 (I := I) RA B C D) +
          (s - t) * T s (vec4 (I := I) A RB C D) +
          ((s - t) * (s - t)) * T s (vec4 (I := I) RA RB C D) +
          (s - t) * T s (vec4 (I := I) A B RC D) +
          ((s - t) * (s - t)) * T s (vec4 (I := I) RA B RC D) +
          ((s - t) * (s - t)) * T s (vec4 (I := I) A RB RC D) +
          ((s - t) * (s - t) * (s - t)) * T s (vec4 (I := I) RA RB RC D) +
          (s - t) * T s (vec4 (I := I) A B C RD) +
          ((s - t) * (s - t)) * T s (vec4 (I := I) RA B C RD) +
          ((s - t) * (s - t)) * T s (vec4 (I := I) A RB C RD) +
          ((s - t) * (s - t) * (s - t)) * T s (vec4 (I := I) RA RB C RD) +
          ((s - t) * (s - t)) * T s (vec4 (I := I) A B RC RD) +
          ((s - t) * (s - t) * (s - t)) * T s (vec4 (I := I) RA B RC RD) +
          ((s - t) * (s - t) * (s - t)) * T s (vec4 (I := I) A RB RC RD) +
          ((s - t) * (s - t) * (s - t) * (s - t)) *
            T s (vec4 (I := I) RA RB RC RD) := by
    funext s
    exact tensor04At_apply_affine_slots
      (T s) A B C D RA RB RC RD (s - t)
  rw [hexp]
  have hshift : HasDerivWithinAt (fun s : Real => s - t) 1 Dset t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hshift2 := hshift.mul hshift
  have hshift3 := hshift2.mul hshift
  have hshift4 := hshift3.mul hshift
  have hD (X Y Z W : TangentSpace I x) :=
    (hDiff X Y Z W).hasDerivWithinAt
  have hsum0 := hbase.add (hshift.mul (hD RA B C D))
  have hsum1 := hsum0.add (hshift.mul (hD A RB C D))
  have hsum2 := hsum1.add (hshift2.mul (hD RA RB C D))
  have hsum3 := hsum2.add (hshift.mul (hD A B RC D))
  have hsum4 := hsum3.add (hshift2.mul (hD RA B RC D))
  have hsum5 := hsum4.add (hshift2.mul (hD A RB RC D))
  have hsum6 := hsum5.add (hshift3.mul (hD RA RB RC D))
  have hsum7 := hsum6.add (hshift.mul (hD A B C RD))
  have hsum8 := hsum7.add (hshift2.mul (hD RA B C RD))
  have hsum9 := hsum8.add (hshift2.mul (hD A RB C RD))
  have hsum10 := hsum9.add (hshift3.mul (hD RA RB C RD))
  have hsum11 := hsum10.add (hshift2.mul (hD A B RC RD))
  have hsum12 := hsum11.add (hshift3.mul (hD RA B RC RD))
  have hsum13 := hsum12.add (hshift3.mul (hD A RB RC RD))
  have hsum := hsum13.add (hshift4.mul (hD RA RB RC RD))
  refine (hsum.congr_deriv ?_).congr ?_ ?_
  · simp only [Pi.mul_apply, sub_self, mul_zero, zero_mul,
      one_mul, add_zero]
  · intro s _
    rfl
  · rfl

private theorem rm04Base_differentiableWithinAt_of_solution
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (v : Fin 4 -> TangentSpace I x) :
    DifferentiableWithinAt Real
      (fun s : Real => S.base.rm04 s x v) D.carrier (t : Real) := by
  classical
  have hexp :
      (fun s : Real => S.base.rm04 s x v) =
        fun s : Real =>
          ∑ m : Fin 4 -> Fin n,
            S.base.rm04 s x (fun q => basis (m q)) *
              ∏ q : Fin 4, basis.coord (m q) (v q) := by
    funext s
    rw [tensor0S_apply_eq_sum (I := I) basis (S.base.rm04 s x) v]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [component0S_apply]
  rw [hexp]
  refine DifferentiableWithinAt.fun_sum ?_
  intro m _
  exact (rm04Base_of_solution_any (I := I) S hS t x basis horth m).differentiableWithinAt.mul_const _

private theorem hamiltonRmReact_add_ricci_slot_actions
    {Idx : Type*} [Fintype Idx]
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (hRm : Rm04Symm R)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (a b c d : Idx) :
    DifferentialGeometry.Geometry.Connection.hamiltonRmReact
        (fun q => R (q 0) (q 1) (q 2) (q 3)) ![a, b, c, d] +
        (∑ p : Idx, Ric a p * R p b c d) +
        (∑ p : Idx, Ric b p * R a p c d) +
        (∑ p : Idx, Ric c p * R a b p d) +
        (∑ p : Idx, Ric d p * R a b c p) =
      hamiltonRmReactionComponent R a b c d := by
  classical
  have htrace' (i j : Idx) : (∑ e : Idx, R i e j e) = -Ric i j := by
    calc
      (∑ e : Idx, R i e j e) = ∑ e : Idx, -R e i j e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hRm.swap12]
      _ = -(∑ e : Idx, R e i j e) := by rw [Finset.sum_neg_distrib]
      _ = -Ric i j := by rw [hTrace]
  have hslot (i : Idx) (F : Idx -> Real) :
      (∑ e : Idx, ∑ f : Idx, R i e f e * F f) =
        -(∑ f : Idx, Ric i f * F f) := by
    calc
      (∑ e : Idx, ∑ f : Idx, R i e f e * F f) =
          ∑ f : Idx, ∑ e : Idx, R i e f e * F f := Finset.sum_comm
      _ = ∑ f : Idx, (∑ e : Idx, R i e f e) * F f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.sum_mul]
      _ = -(∑ f : Idx, Ric i f * F f) := by
        simp only [htrace', neg_mul, Finset.sum_neg_distrib]
  unfold DifferentialGeometry.Geometry.Connection.hamiltonRmReact
    hamiltonRmReactionComponent hamiltonBComponent
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, neg_mul, sub_neg_eq_add]
  rw [hslot a (fun f => R f b c d), hslot b (fun f => R a f c d),
    hslot c (fun f => R a b f d), hslot d (fun f => R a b c f)]
  ring

private theorem inverse_metric_double_trace_drift
    {Idx : Type*} [Fintype Idx]
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (hRic : forall i j, Ric i j = Ric j i)
    (a b : Idx) :
    2 * (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
        Ric i j * R a k i b * Ric k j) +
      2 * (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
        Ric k l * R a k i b * Ric l i) =
      ∑ c : Idx, ∑ d : Idx,
        (((∑ p : Idx, Ric c p * R a p d b) +
              ∑ p : Idx, Ric d p * R a c p b) * Ric c d +
          R a c d b *
            ((∑ p : Idx, Ric c p * Ric p d) +
              ∑ p : Idx, Ric d p * Ric c p)) := by
  classical
  have hRmSecond :
      (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) =
        ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          (Ric c p * R a p d b) * Ric c d := by
    calc
      (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) =
        ∑ i : Idx, ∑ l : Idx, ∑ k : Idx,
          Ric k l * R a k i b * Ric l i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ i : Idx, ∑ k : Idx,
          Ric k l * R a k i b * Ric l i := Finset.sum_comm
      _ = ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          (Ric c p * R a p d b) * Ric c d := by
            refine Finset.sum_congr rfl fun c _ => ?_
            refine Finset.sum_congr rfl fun d _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hRic p c]
  have hRmThird :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j) =
        ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          (Ric d p * R a c p b) * Ric c d := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j) =
        ∑ i : Idx, ∑ k : Idx, ∑ j : Idx,
          Ric i j * R a k i b * Ric k j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
          Ric i j * R a k i b * Ric k j := Finset.sum_comm
      _ = ∑ k : Idx, ∑ j : Idx, ∑ i : Idx,
          Ric i j * R a k i b * Ric k j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          (Ric d p * R a c p b) * Ric c d := by
            refine Finset.sum_congr rfl fun c _ => ?_
            refine Finset.sum_congr rfl fun d _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hRic d p]
  have hRicFirst :
      (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) =
        ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          R a c d b * (Ric c p * Ric p d) := by
    calc
      (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) =
        ∑ k : Idx, ∑ i : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i := Finset.sum_comm
      _ = ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          R a c d b * (Ric c p * Ric p d) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            refine Finset.sum_congr rfl fun d _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            ring
  have hRicSecond :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j) =
        ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          R a c d b * (Ric d p * Ric c p) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j) =
        ∑ i : Idx, ∑ k : Idx, ∑ j : Idx,
          Ric i j * R a k i b * Ric k j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
          Ric i j * R a k i b * Ric k j := Finset.sum_comm
      _ = ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          R a c d b * (Ric d p * Ric c p) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            refine Finset.sum_congr rfl fun d _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            ring
  symm
  calc
    (∑ c : Idx, ∑ d : Idx,
        (((∑ p : Idx, Ric c p * R a p d b) +
              ∑ p : Idx, Ric d p * R a c p b) * Ric c d +
          R a c d b *
            ((∑ p : Idx, Ric c p * Ric p d) +
              ∑ p : Idx, Ric d p * Ric c p))) =
      (∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          (Ric c p * R a p d b) * Ric c d) +
        (∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          (Ric d p * R a c p b) * Ric c d) +
        (∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          R a c d b * (Ric c p * Ric p d)) +
        ∑ c : Idx, ∑ d : Idx, ∑ p : Idx,
          R a c d b * (Ric d p * Ric c p) := by
            simp only [add_mul, mul_add, Finset.sum_add_distrib,
              Finset.sum_mul, Finset.mul_sum]
            ring
    _ =
      (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j) +
        (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) +
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j := by
            rw [← hRmSecond, ← hRmThird, ← hRicFirst, ← hRicSecond]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
          Ric i j * R a k i b * Ric k j) +
        2 * (∑ i : Idx, ∑ k : Idx, ∑ l : Idx,
          Ric k l * R a k i b * Ric l i) := by ring

private theorem tensor04At_apply_ricciEnd_slot_orthonormal
    {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (Ric : Tensor02At (I := I) (M := M) x)
    (T : Tensor04At (I := I) (M := M) x)
    (slots : Fin 4 -> Idx) (r : Fin 4) :
    T (Function.update (fun i => basis (slots i)) r
        (ricciEndAt (I := I) g Ric (basis (slots r)))) =
      ∑ p : Idx,
        Ric (vec2 (I := I) (basis (slots r)) (basis p)) *
          T (Function.update (fun i => basis (slots i)) r (basis p)) := by
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hrepr (p : Idx) :
      basis.repr (ricciEndAt (I := I) g Ric (basis (slots r))) p =
        Ric (vec2 (I := I) (basis (slots r)) (basis p)) := by
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [ricciEnd_inner, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hend :
      ricciEndAt (I := I) g Ric (basis (slots r)) =
        ∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis (slots r))) p • basis p :=
    (basis.sum_repr (ricciEndAt (I := I) g Ric (basis (slots r)))).symm
  rw [hend]
  change T.toMultilinearMap
      (Function.update (fun i => basis (slots i)) r
        (∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis (slots r))) p • basis p)) = _
  rw [MultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_update_smul, hrepr, smul_eq_mul]
  rfl

private noncomputable def hamiltonRmRoughLaplacianField
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
    (nablaKRm04Field (I := I) S t 2)

private theorem hamiltonRmRoughLaplacianField_apply_orthonormal
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c d : Fin n) :
    hamiltonRmRoughLaplacianField (I := I) S t x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
      ∑ e : Fin n, nablaKRm04Field (I := I) S t 2 x
        (vec6 (I := I) (basis e) (basis e)
          (basis a) (basis b) (basis c) (basis d)) := by
  rw [hamiltonRmRoughLaplacianField,
    metricTraceFirstTwoField_apply_orthonormal
      (I := I) (S.base.metric t) basis horth]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  funext q
  fin_cases q <;> rfl

private theorem hamiltonRmRoughLaplacianField_eq_component_orthonormal
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (m : Fin 4 -> Fin n) :
    tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (nablaKRm04Field (I := I) S t 2 x))
        (fun i => basis i) m =
      hamiltonRmRoughLaplacianField (I := I) S t x
        (fun q => basis (m q)) := by
  rw [tensor0SComponent_apply, metricTrace0S2TensorInBasis_apply,
    hamiltonRmRoughLaplacianField,
    metricTraceFirstTwoField_apply_orthonormal
      (I := I) (S.base.metric t) basis horth]
  unfold metricTrace0S2InBasis identityInvMetric diagonalInvMetric
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem hamiltonNablaPActualTimeDerivativeField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (d a b c : Fin n) :
    hamiltonNablaPActualTimeDerivativeField (I := I) g x
        (vec4 (I := I) (basis d) (basis a) (basis b) (basis c)) =
      hamiltonNablaPTimeDerivativeField (I := I) g x
          (vec4 (I := I) (basis d) (basis a) (basis b) (basis c)) -
        (∑ p : Fin n,
          ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) (basis d) (basis a) (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) (basis p) (basis b) (basis c))) -
        (∑ p : Fin n,
          ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) (basis d) (basis b) (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) (basis a) (basis p) (basis c))) -
        ∑ p : Fin n,
          ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) (basis d) (basis c) (basis p)) *
            hamiltonPField (I := I) g x
              (vec3 (I := I) (basis a) (basis b) (basis p)) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [hamiltonNablaPActualTimeDerivativeField]
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply]
  rw [connectionVariationPFirstField_apply_basis
      (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv,
    connectionVariationPSecondField_apply_basis
      (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv,
    connectionVariationPThirdField_apply_basis
      (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem hamiltonDivPTimeDerivativeField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPTimeDerivativeField (I := I) g x
        (vec2 (I := I) (basis a) (basis b)) =
      (∑ c : Fin n,
        hamiltonNablaPActualTimeDerivativeField (I := I) g x
          (vec4 (I := I) (basis c) (basis c) (basis a) (basis b))) +
        2 * ∑ c : Fin n, ∑ p : Fin n,
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis c) (basis p)) *
            hamiltonNablaPField (I := I) g x
              (vec4 (I := I) (basis c) (basis p) (basis a) (basis b)) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [hamiltonDivPTimeDerivativeField_apply_basis
    (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv]
  have htrace := ricciNablaPTraceField_apply_basis
    (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv
      (basis a) (basis b)
  rw [htrace]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

private theorem uhlenbeck_time_derivative_trace_expand
    {Idx : Type*} [Fintype Idx]
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (NP NPt : Idx -> Idx -> Idx -> Idx -> Real)
    (hRic : forall i j, Ric i j = Ric j i)
    (a b : Idx) :
    (∑ c : Idx,
      uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic
        (fun slots : Fin 3 -> Idx => P (slots 0) (slots 1) (slots 2))
        (fun d slots => NP d (slots 0) (slots 1) (slots 2))
        (fun d slots => NPt d (slots 0) (slots 1) (slots 2)) c
        (fun r : Fin 3 => if r = 0 then c else if r = 1 then a else b)) =
      (∑ c : Idx,
        (NPt c c a b -
          (∑ p : Idx,
            ricciFlowConnectionVariationOrthonormal nablaRic c c p * P p a b) -
          (∑ p : Idx,
            ricciFlowConnectionVariationOrthonormal nablaRic c a p * P c p b) -
          (∑ p : Idx,
            ricciFlowConnectionVariationOrthonormal nablaRic c b p * P c a p))) +
        2 * (∑ c : Idx, ∑ p : Idx, Ric c p * NP c p a b) +
        (∑ p : Idx, Ric a p * (∑ c : Idx, NP c c p b)) +
        ∑ p : Idx, Ric b p * (∑ c : Idx, NP c c a p) := by
  classical
  have htrace :
      (∑ c : Idx, ∑ p : Idx, Ric c p * NP p c a b) =
        ∑ c : Idx, ∑ p : Idx, Ric c p * NP c p a b := by
    calc
      (∑ c : Idx, ∑ p : Idx, Ric c p * NP p c a b) =
          ∑ p : Idx, ∑ c : Idx, Ric c p * NP p c a b :=
        Finset.sum_comm
      _ = ∑ c : Idx, ∑ p : Idx, Ric c p * NP c p a b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hRic p c]
  have houtA :
      (∑ c : Idx, ∑ p : Idx, Ric a p * NP c c p b) =
        ∑ p : Idx, Ric a p * (∑ c : Idx, NP c c p b) := by
    calc
      (∑ c : Idx, ∑ p : Idx, Ric a p * NP c c p b) =
          ∑ p : Idx, ∑ c : Idx, Ric a p * NP c c p b :=
        Finset.sum_comm
      _ = ∑ p : Idx, Ric a p * (∑ c : Idx, NP c c p b) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
  have houtB :
      (∑ c : Idx, ∑ p : Idx, Ric b p * NP c c a p) =
        ∑ p : Idx, Ric b p * (∑ c : Idx, NP c c a p) := by
    calc
      (∑ c : Idx, ∑ p : Idx, Ric b p * NP c c a p) =
          ∑ p : Idx, ∑ c : Idx, Ric b p * NP c c a p :=
        Finset.sum_comm
      _ = ∑ p : Idx, Ric b p * (∑ c : Idx, NP c c a p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
  simp only [uhlenbeckTimeDerivativeOfCovariantDerivative,
    covariantTensorRicciSlotAction, Fin.sum_univ_three, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero, Fin.reduceEq,
    zero_ne_one, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [htrace, houtA, houtB]
  ring

private theorem tensor02At_apply_ricciEnd_first_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (Ric : Tensor02At (I := I) (M := M) x)
    (T : Tensor02At (I := I) (M := M) x)
    (a b : Idx) :
    T (vec2 (I := I) (ricciEndAt (I := I) g Ric (basis a)) (basis b)) =
      ∑ p : Idx, Ric (vec2 (I := I) (basis a) (basis p)) *
        T (vec2 (I := I) (basis p) (basis b)) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hrepr (p : Idx) :
      basis.repr (ricciEndAt (I := I) g Ric (basis a)) p =
        Ric (vec2 (I := I) (basis a) (basis p)) := by
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [ricciEnd_inner, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hend :
      ricciEndAt (I := I) g Ric (basis a) =
        ∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis a)) p • basis p :=
    (basis.sum_repr (ricciEndAt (I := I) g Ric (basis a))).symm
  rw [hend]
  let slots : Fin 2 -> TangentSpace I x := vec2 (I := I) 0 (basis b)
  have hvec :
      vec2 (I := I)
          (∑ p : Idx,
            basis.repr (ricciEndAt (I := I) g Ric (basis a)) p • basis p)
          (basis b) =
        Function.update slots (0 : Fin 2)
          (∑ p : Idx,
            basis.repr (ricciEndAt (I := I) g Ric (basis a)) p • basis p) := by
    funext q
    fin_cases q <;> simp [slots, vec2, Function.update]
  rw [hvec]
  change T.toMultilinearMap
      (Function.update slots (0 : Fin 2)
        (∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis a)) p • basis p)) = _
  rw [MultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_update_smul, hrepr]
  change Ric (vec2 (I := I) (basis a) (basis p)) *
      T (Function.update slots (0 : Fin 2) (basis p)) =
    Ric (vec2 (I := I) (basis a) (basis p)) *
      T (vec2 (I := I) (basis p) (basis b))
  congr 1
  apply congrArg T
  funext q
  fin_cases q <;> simp [slots, vec2, Function.update]

private theorem tensor02At_apply_ricciEnd_second_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (Ric : Tensor02At (I := I) (M := M) x)
    (T : Tensor02At (I := I) (M := M) x)
    (a b : Idx) :
    T (vec2 (I := I) (basis a) (ricciEndAt (I := I) g Ric (basis b))) =
      ∑ p : Idx, Ric (vec2 (I := I) (basis b) (basis p)) *
        T (vec2 (I := I) (basis a) (basis p)) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hrepr (p : Idx) :
      basis.repr (ricciEndAt (I := I) g Ric (basis b)) p =
        Ric (vec2 (I := I) (basis b) (basis p)) := by
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [ricciEnd_inner, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hend :
      ricciEndAt (I := I) g Ric (basis b) =
        ∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis b)) p • basis p :=
    (basis.sum_repr (ricciEndAt (I := I) g Ric (basis b))).symm
  rw [hend]
  let slots : Fin 2 -> TangentSpace I x := vec2 (I := I) (basis a) 0
  have hvec :
      vec2 (I := I) (basis a)
          (∑ p : Idx,
            basis.repr (ricciEndAt (I := I) g Ric (basis b)) p • basis p) =
        Function.update slots (1 : Fin 2)
          (∑ p : Idx,
            basis.repr (ricciEndAt (I := I) g Ric (basis b)) p • basis p) := by
    funext q
    fin_cases q <;> simp [slots, vec2, Function.update]
  rw [hvec]
  change T.toMultilinearMap
      (Function.update slots (1 : Fin 2)
        (∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis b)) p • basis p)) = _
  rw [MultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_update_smul, hrepr]
  change Ric (vec2 (I := I) (basis b) (basis p)) *
      T (Function.update slots (1 : Fin 2) (basis p)) =
    Ric (vec2 (I := I) (basis b) (basis p)) *
      T (vec2 (I := I) (basis a) (basis p))
  congr 1
  apply congrArg T
  funext q
  fin_cases q <;> simp [slots, vec2, Function.update]

private theorem hamiltonDivPTimeDerivativeField_apply_orthonormal_expanded
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPTimeDerivativeField (I := I) g x
        (vec2 (I := I) (basis a) (basis b)) =
      (∑ c : Fin n,
        (hamiltonNablaPTimeDerivativeField (I := I) g x
              (vec4 (I := I) (basis c) (basis c) (basis a) (basis b)) -
          (∑ p : Fin n,
            ricciFlowConnectionVariationOrthonormal
                (fun i j k => metricNablaRic (I := I) (M := M) g x
                  (vec3 (I := I) (basis i) (basis j) (basis k))) c c p *
              hamiltonPField (I := I) g x
                (vec3 (I := I) (basis p) (basis a) (basis b))) -
          (∑ p : Fin n,
            ricciFlowConnectionVariationOrthonormal
                (fun i j k => metricNablaRic (I := I) (M := M) g x
                  (vec3 (I := I) (basis i) (basis j) (basis k))) c a p *
              hamiltonPField (I := I) g x
                (vec3 (I := I) (basis c) (basis p) (basis b))) -
          (∑ p : Fin n,
            ricciFlowConnectionVariationOrthonormal
                (fun i j k => metricNablaRic (I := I) (M := M) g x
                  (vec3 (I := I) (basis i) (basis j) (basis k))) c b p *
              hamiltonPField (I := I) g x
                (vec3 (I := I) (basis c) (basis a) (basis p))))) +
        2 * ∑ c : Fin n, ∑ p : Fin n,
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis c) (basis p)) *
            hamiltonNablaPField (I := I) g x
              (vec4 (I := I) (basis c) (basis p) (basis a) (basis b)) := by
  rw [hamiltonDivPTimeDerivativeField_apply_orthonormal
    (I := I) g basis horth]
  refine congrArg₂ (fun u v : Real => u + 2 * v) ?_ rfl
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hamiltonNablaPActualTimeDerivativeField_apply_orthonormal
    (I := I) g basis horth]
  simp_rw [ricciFlowConnectionVariationField_apply (I := I) g x]
  rfl

private theorem hamiltonDivPAt_apply_ricciEnd_first_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPAt (I := I) g x
        (vec2 (I := I)
          (ricciEndAt (I := I) g
            (metricRicci (I := I) (M := M) g x) (basis a))
          (basis b)) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis a) (basis p)) *
          (∑ c : Fin n,
            hamiltonNablaPField (I := I) g x
              (vec4 (I := I) (basis c) (basis c) (basis p) (basis b))) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [tensor02At_apply_ricciEnd_first_orthonormal
    (I := I) g basis horth (metricRicci (I := I) (M := M) g x)
      (hamiltonDivPAt (I := I) g x) a b]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hdiv := hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
    (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv
      (basis p) (basis b)
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] using hdiv

private theorem hamiltonDivPAt_apply_ricciEnd_second_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPAt (I := I) g x
        (vec2 (I := I) (basis a)
          (ricciEndAt (I := I) g
            (metricRicci (I := I) (M := M) g x) (basis b))) =
      ∑ p : Fin n,
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis b) (basis p)) *
          (∑ c : Fin n,
            hamiltonNablaPField (I := I) g x
              (vec4 (I := I) (basis c) (basis c) (basis a) (basis p))) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [tensor02At_apply_ricciEnd_second_orthonormal
    (I := I) g basis horth (metricRicci (I := I) (M := M) g x)
      (hamiltonDivPAt (I := I) g x) a b]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hdiv := hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
    (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv
      (basis a) (basis p)
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] using hdiv

private theorem hamiltonDivPTimeDerivativeField_add_ricciEnd_eq_uhlenbeck_trace_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPTimeDerivativeField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) +
        hamiltonDivPAt (I := I) g x
          (vec2 (I := I)
            (ricciEndAt (I := I) g
              (metricRicci (I := I) (M := M) g x) (basis a))
            (basis b)) +
        hamiltonDivPAt (I := I) g x
          (vec2 (I := I) (basis a)
            (ricciEndAt (I := I) g
              (metricRicci (I := I) (M := M) g x) (basis b))) =
      ∑ c : Fin n,
        uhlenbeckTimeDerivativeOfCovariantDerivative
          (fun i j => metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i j k => metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun slots : Fin 3 -> Fin n => hamiltonPField (I := I) g x
            (vec3 (I := I)
              (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          (fun d slots => hamiltonNablaPField (I := I) g x
            (vec4 (I := I)
              (basis d) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          (fun d slots => hamiltonNablaPTimeDerivativeField (I := I) g x
            (vec4 (I := I)
              (basis d) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          c (fun r : Fin 3 => if r = 0 then c else if r = 1 then a else b) := by
  have hRic (i j : Fin n) :
      metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis j) (basis i)) :=
    metricRicciAt_symm (I := I) (M := M) g x (basis i) (basis j)
  rw [hamiltonDivPTimeDerivativeField_apply_orthonormal_expanded
      (I := I) g basis horth,
    hamiltonDivPAt_apply_ricciEnd_first_orthonormal
      (I := I) g basis horth,
    hamiltonDivPAt_apply_ricciEnd_second_orthonormal
      (I := I) g basis horth]
  exact (uhlenbeck_time_derivative_trace_expand
    (fun i j => metricRicci (I := I) (M := M) g x
      (vec2 (I := I) (basis i) (basis j)))
    (fun i j k => metricNablaRic (I := I) (M := M) g x
      (vec3 (I := I) (basis i) (basis j) (basis k)))
    (fun i j k => hamiltonPField (I := I) g x
      (vec3 (I := I) (basis i) (basis j) (basis k)))
    (fun i j k l => hamiltonNablaPField (I := I) g x
      (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
    (fun i j k l => hamiltonNablaPTimeDerivativeField (I := I) g x
      (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
    hRic a b).symm

private theorem hamiltonDivPAt_hasDerivWithinAt_oneTimeUhlenbeckVector
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    HasDerivWithinAt
      (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x
        (vec2 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      (∑ c : Fin n,
        uhlenbeckTimeDerivativeOfCovariantDerivative
          (fun i j => metricRicci (I := I) (M := M)
            (S.base.metric (t : Real)) x
              (vec2 (I := I) (basis i) (basis j)))
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric (t : Real)) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun slots : Fin 3 -> Fin n => hamiltonPField
            (I := I) (S.base.metric (t : Real)) x
              (vec3 (I := I)
                (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          (fun d slots => hamiltonNablaPField
            (I := I) (S.base.metric (t : Real)) x
              (vec4 (I := I)
                (basis d) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          (fun d slots => hamiltonNablaPTimeDerivativeField
            (I := I) (S.base.metric (t : Real)) x
              (vec4 (I := I)
                (basis d) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          c (fun r : Fin 3 => if r = 0 then c else if r = 1 then a else b))
      D.carrier (t : Real) := by
  let g := S.base.metric (t : Real)
  let Ric := metricRicci (I := I) (M := M) g x
  let RA := ricciEndAt (I := I) g Ric (basis a)
  let RB := ricciEndAt (I := I) g Ric (basis b)
  have hfixed (X Y : TangentSpace I x) :=
    hamiltonDivPAt_hasDerivWithinAt_of_solution
      (I := I) S hS t x (vec2 (I := I) X Y)
  have hchain := tensor02At_hasDerivWithinAt_affine_slots
    (I := I)
    (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x)
    (hamiltonDivPTimeDerivativeField (I := I) g x)
    hfixed (basis a) (basis b) RA RB
  have htrace :=
    hamiltonDivPTimeDerivativeField_add_ricciEnd_eq_uhlenbeck_trace_of_orthonormal
      (I := I) g basis (by simpa only [g] using horth) a b
  refine (hchain.congr_deriv (by simpa only [g, Ric, RA, RB] using htrace)).congr ?_ ?_
  · intro s _
    simp only [oneTimeUhlenbeckVector, g, Ric, RA, RB]
  · simp only [oneTimeUhlenbeckVector, g, Ric, RA, RB]

private theorem hamiltonDivPHeatComponent_add_roughLaplacian_eq_timeDerivative_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPHeatComponent
          (fun i j => metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i j k => metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j k l => hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j k l => hamiltonNablaPTimeDerivativeField (I := I) g x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j k l m r => hamiltonNabla3PField (I := I) g x
            (Fin.cons (basis i)
              (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
          a b +
        hamiltonDivPRoughLaplacianField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) =
      ∑ c : Fin n,
        uhlenbeckTimeDerivativeOfCovariantDerivative
          (fun i j => metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i j k => metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun slots : Fin 3 -> Fin n => hamiltonPField (I := I) g x
            (vec3 (I := I)
              (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          (fun d slots => hamiltonNablaPField (I := I) g x
            (vec4 (I := I)
              (basis d) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          (fun d slots => hamiltonNablaPTimeDerivativeField (I := I) g x
            (vec4 (I := I)
              (basis d) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))))
          c (fun r : Fin 3 => if r = 0 then c else if r = 1 then a else b) := by
  rw [hamiltonDivPHeatComponent,
    hamiltonDivPRoughLaplacianField_apply_orthonormal
      (I := I) g basis horth]
  simp_rw [uhlenbeckHeatNablaPComponent]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sub_add_cancel]
  simp only [hamiltonPComponent, hamiltonPField_apply, hamiltonPAt_apply]

private theorem hamiltonDivPAt_hasDerivWithinAt_oneTimeUhlenbeck_heat
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    HasDerivWithinAt
      (fun s : Real => hamiltonDivPAt (I := I) (S.base.metric s) x
        (vec2 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      (hamiltonDivPHeatComponent
          (fun i j => metricRicci (I := I) (M := M)
            (S.base.metric (t : Real)) x
              (vec2 (I := I) (basis i) (basis j)))
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric (t : Real)) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j k l => hamiltonNablaPField
            (I := I) (S.base.metric (t : Real)) x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j k l => hamiltonNablaPTimeDerivativeField
            (I := I) (S.base.metric (t : Real)) x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j k l m r => hamiltonNabla3PField
            (I := I) (S.base.metric (t : Real)) x
              (Fin.cons (basis i)
                (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
          a b +
        hamiltonDivPRoughLaplacianField
          (I := I) (S.base.metric (t : Real)) x
            (vec2 (I := I) (basis a) (basis b)))
      D.carrier (t : Real) := by
  have h := hamiltonDivPAt_hasDerivWithinAt_oneTimeUhlenbeckVector
    (I := I) S hS t x basis horth a b
  exact h.congr_deriv
    (hamiltonDivPHeatComponent_add_roughLaplacian_eq_timeDerivative_of_orthonormal
      (I := I) (S.base.metric (t : Real)) basis horth a b).symm

private theorem metricRicciTimeDerivativeField_add_ricciEnd_eq_heat_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    metricRicciTimeDerivativeField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) +
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I)
            (ricciEndAt (I := I) g
              (metricRicci (I := I) (M := M) g x) (basis a))
            (basis b)) +
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis a)
            (ricciEndAt (I := I) g
              (metricRicci (I := I) (M := M) g x) (basis b))) =
      metricTraceFirstTwoField (I := I) (M := M) g
          (metricNabla2Ric (I := I) (M := M) g) x
            (vec2 (I := I) (basis a) (basis b)) +
        hamiltonRicciReactionComponent
          (fun i j k l => metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis i) (basis j))) a b := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hcurv :
      hamiltonCurvatureRicciField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) =
        hamiltonCurvatureRicciComponent
          (fun i j k l => metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis i) (basis j))) a b := by
    rw [hamiltonCurvatureRicciField_apply_basis
      (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [hamiltonCurvatureRicciComponent, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
  have hsquare :
      hamiltonRicciSquareField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) =
        ∑ p : Fin n,
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis a) (basis p)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis p) (basis b)) := by
    rw [hamiltonRicciSquareField_apply_basis
      (I := I) g basis (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hfirst := tensor02At_apply_ricciEnd_first_orthonormal
    (I := I) g basis horth (metricRicci (I := I) (M := M) g x)
      (metricRicci (I := I) (M := M) g x) a b
  have hsecond := tensor02At_apply_ricciEnd_second_orthonormal
    (I := I) g basis horth (metricRicci (I := I) (M := M) g x)
      (metricRicci (I := I) (M := M) g x) a b
  have hsymm (i j : Fin n) :
      metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis j) (basis i)) :=
    metricRicciAt_symm (I := I) (M := M) g x (basis i) (basis j)
  have hsecond' :
      metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis a)
            (ricciEndAt (I := I) g
              (metricRicci (I := I) (M := M) g x) (basis b))) =
        ∑ p : Fin n,
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis a) (basis p)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis p) (basis b)) := by
    rw [hsecond]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hsymm b p]
    ring
  rw [metricRicciTimeDerivativeField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [hcurv, hsquare, hfirst, hsecond']
  unfold hamiltonRicciReactionComponent hamiltonCurvatureRicciComponent
  ring

private theorem metricRicci_hasDerivWithinAt_oneTimeUhlenbeck_heat
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    HasDerivWithinAt
      (fun s : Real => metricRicci (I := I) (M := M) (S.base.metric s) x
        (vec2 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
          (metricNabla2Ric (I := I) (M := M) (S.base.metric (t : Real))) x
            (vec2 (I := I) (basis a) (basis b)) +
        hamiltonRicciReactionComponent
          (fun i j k l => S.base.rm04 (t : Real) x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M)
            (S.base.metric (t : Real)) x
              (vec2 (I := I) (basis i) (basis j))) a b)
      D.carrier (t : Real) := by
  let g := S.base.metric (t : Real)
  let Ric := metricRicci (I := I) (M := M) g x
  let RA := ricciEndAt (I := I) g Ric (basis a)
  let RB := ricciEndAt (I := I) g Ric (basis b)
  have hfixed (X Y : TangentSpace I x) :
      HasDerivWithinAt
        (fun s : Real => metricRicci (I := I) (M := M) (S.base.metric s) x
          (vec2 (I := I) X Y))
        (metricRicciTimeDerivativeField (I := I) g x
          (vec2 (I := I) X Y)) D.carrier (t : Real) := by
    simpa [SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricci,
      SolutionFamily.metric, g] using
        metricRicciTimeDerivativeField_hasDerivWithinAt_of_solution
          (I := I) S hS t x X Y
  have hchain := tensor02At_hasDerivWithinAt_affine_slots
    (I := I)
    (fun s : Real => metricRicci (I := I) (M := M) (S.base.metric s) x)
    (metricRicciTimeDerivativeField (I := I) g x) hfixed
    (basis a) (basis b) RA RB
  have hheat := metricRicciTimeDerivativeField_add_ricciEnd_eq_heat_of_orthonormal
    (I := I) g basis (by simpa only [g] using horth) a b
  refine (hchain.congr_deriv (by
    simpa only [g, Ric, RA, RB, SolutionFamily.rm04] using hheat)).congr ?_ ?_
  · intro s _
    simp only [oneTimeUhlenbeckVector, g, Ric, RA, RB]
  · simp only [oneTimeUhlenbeckVector, g, Ric, RA, RB]

private theorem hamiltonShiftedRicci_hasDerivWithinAt_oneTimeUhlenbeck_heat
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    HasDerivWithinAt
      (fun s : Real =>
        (1 / (2 * (s - clock.origin))) *
          metricRicci (I := I) (M := M) (S.base.metric s) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis a))
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis b))))
      ((1 / (2 * clock.elapsed)) *
          metricTraceFirstTwoField (I := I) (M := M) (S.base.metric clock.time)
            (metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time)) x
              (vec2 (I := I) (basis a) (basis b)) +
        hamiltonShiftedRicciHeatComponent clock
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M)
            (S.base.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b)
      D.carrier clock.time := by
  let t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
    ⟨clock.time, ht⟩
  have hsub : HasDerivAt (fun s : Real => s - clock.origin) 1 clock.time :=
    (hasDerivAt_id clock.time).sub_const clock.origin
  have hsubne : clock.time - clock.origin ≠ 0 := by
    simpa only [HarnackClock.elapsed] using clock.elapsed_ne_zero
  have hcoef : HasDerivWithinAt
      (fun s : Real => 1 / (2 * (s - clock.origin)))
      (-(1 / (2 * clock.elapsed ^ 2))) D.carrier clock.time := by
    have hinv := hsub.inv hsubne
    have hscaled := HasDerivAt.const_mul (1 / 2 : Real) hinv
    refine ((hscaled.congr_of_eventuallyEq ?_).congr_deriv ?_).hasDerivWithinAt
    · filter_upwards [] with s
      simp only [one_div, Pi.inv_apply]
      rw [mul_inv_rev]
      norm_num
      ring
    · simp only [HarnackClock.elapsed]
      field_simp [hsubne]
  have hric := metricRicci_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS t x basis horth a b
  have hprod := hcoef.mul hric
  refine hprod.congr_deriv ?_
  simp only [oneTimeUhlenbeckVector, t, sub_self, zero_smul, add_zero]
  unfold hamiltonShiftedRicciHeatComponent hamiltonRicciReactionComponent
  simp only [HarnackClock.elapsed] at hsubne ⊢
  rw [SolutionFamily.rm04]
  field_simp [hsubne]
  ring

private theorem metricNablaRicciTimeDerivativeExpandedField_realizes
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (metricCov (I := I) (M := M) g)
      (metricRicciTimeDerivativeField (I := I) g)
      (metricNablaRicciTimeDerivativeExpandedField (I := I) g) := by
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := metricNablaRic (I := I) (M := M) g
  let nabla2Ric := metricNabla2Ric (I := I) (M := M) g
  let nabla3Ric := metricNabla3RicField (I := I) g
  let Rm := metricRm04 (I := I) (M := M) g
  let nablaRm := metricNablaRm04Field (I := I) g
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hRic : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric nablaRic := by
    simpa [cov, Ric, nablaRic, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Ric))
  have hRic2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov nablaRic nabla2Ric := by
    simpa [cov, nablaRic, nabla2Ric, metricNabla2Ric] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov nablaRic
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) nablaRic))
  have hRic3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov nabla2Ric nabla3Ric := by
    simpa [cov, nabla2Ric, nabla3Ric, metricNabla3RicField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov nabla2Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) nabla2Ric))
  have hRm : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov Rm nablaRm := by
    simpa [cov, Rm, nablaRm, metricNablaRm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov Rm
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Rm))
  have hRough := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 2) cov g hmc nabla2Ric nabla3Ric hRic3
  have hSquareProduct := nabla0S_product_realizes (I := I) cov
    Ric Ric nablaRic nablaRic hRic hRic
  have hSquarePerm := totalNabla0SRealizes_domDomCongr (I := I) cov
    hamiltonRicciSquareFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric Ric)
    (hamiltonRicciSquareProductNablaField (I := I) g)
    (by simpa [Ric, nablaRic, hamiltonRicciSquareProductNablaField] using hSquareProduct)
  have hSquare := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 2) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      hamiltonRicciSquareFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric Ric))
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv hamiltonRicciSquareFieldPerm)
      (hamiltonRicciSquareProductNablaField (I := I) g)) hSquarePerm
  have hCurvatureProduct := nabla0S_product_realizes (I := I) cov
    Rm Ric nablaRm nablaRic hRm hRic
  have hCurvaturePerm := totalNabla0SRealizes_domDomCongr (I := I) cov
    hamiltonCurvatureRicciFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) Rm Ric)
    (hamiltonCurvatureRicciProductNablaField (I := I) g)
    (by simpa [Rm, Ric, nablaRm, nablaRic,
      hamiltonCurvatureRicciProductNablaField] using hCurvatureProduct)
  have hCurvatureInner := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 4) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      hamiltonCurvatureRicciFieldPerm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) Rm Ric))
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv hamiltonCurvatureRicciFieldPerm)
      (hamiltonCurvatureRicciProductNablaField (I := I) g)) hCurvaturePerm
  have hCurvature := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 2) cov g hmc
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
        hamiltonCurvatureRicciFieldPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) Rm Ric)))
    (hamiltonCurvatureRicciInnerNablaField (I := I) g)
    (by simpa [hamiltonCurvatureRicciInnerNablaField] using hCurvatureInner)
  have hRough' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov
      (metricTraceFirstTwoField (I := I) (M := M) g nabla2Ric)
      (metricNablaRoughRicciField (I := I) g) := by
    simpa [metricNablaRoughRicciField] using hRough
  have hSquare' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov
      (hamiltonRicciSquareField (I := I) g)
      (hamiltonNablaRicciSquareField (I := I) g) := by
    simpa [Ric, hamiltonRicciSquareField,
      hamiltonNablaRicciSquareField] using hSquare
  have hCurvature' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov
      (hamiltonCurvatureRicciField (I := I) g)
      (hamiltonNablaCurvatureRicciField (I := I) g) := by
    simpa [Rm, Ric, hamiltonCurvatureRicciField,
      hamiltonNablaCurvatureRicciField] using hCurvature
  simpa [cov, nabla2Ric, metricRicciTimeDerivativeField,
    metricNablaRicciTimeDerivativeExpandedField] using
    ((hRough'.add (hCurvature'.smul (2 : Real))).add
      (hSquare'.smul (-2 : Real)))

private theorem metricNablaRicciTimeDerivativeExpandedField_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    metricNablaRicciTimeDerivativeExpandedField (I := I) g =
      metricNablaRicciTimeDerivativeField (I := I) g := by
  exact totalNabla0SRealizes_unique
    (metricNablaRicciTimeDerivativeExpandedField_realizes (I := I) g)
    (by
      simpa [metricNablaRicciTimeDerivativeField] using
        (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2
          (metricCov (I := I) (M := M) g)
          (metricRicciTimeDerivativeField (I := I) g)
          (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
            2 (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g)
            (metricRicciTimeDerivativeField (I := I) g))))

private theorem metricNablaRoughRicciField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    metricNablaRoughRicciField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ e : Fin n, metricNabla3RicField (I := I) g x
        (vec5 (I := I) (basis a) (basis e) (basis e) (basis b) (basis c)) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [metricNablaRoughRicciField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
  unfold metricTrace0S2InBasis
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  congr 1
  funext q
  fin_cases q <;> rfl

private theorem hamiltonNablaRicciSquareField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonNablaRicciSquareField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n,
        (metricNablaRic (I := I) (M := M) g x
              (vec3 (I := I) (basis a) (basis b) (basis d)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis d) (basis c)) +
          metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis b) (basis d)) *
            metricNablaRic (I := I) (M := M) g x
              (vec3 (I := I) (basis a) (basis d) (basis c))) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [hamiltonNablaRicciSquareField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
  unfold metricTrace0S2InBasis
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  have hslots :
      (fun i => metricTraceInput (I := I) (basis d) (basis d)
          (vec3 (I := I) (basis a) (basis b) (basis c))
            (traceNablaShuffle 2
              (frontExtendEquiv hamiltonRicciSquareFieldPerm i))) =
        vec5 (I := I) (basis a) (basis b) (basis d) (basis d) (basis c) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots, hamiltonRicciSquareProductNablaField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    Tensor0SSpace.add_apply]
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply]
  have hleftNabla :
      ((fun i => vec5 (I := I) (basis a) (basis b) (basis d) (basis d) (basis c)
          (leibnizLeftEquiv 2 2 i)) ∘ Fin.castAdd 2) =
        vec3 (I := I) (basis a) (basis b) (basis d) := by
    funext q
    fin_cases q <;> rfl
  have hleftRic :
      ((fun i => vec5 (I := I) (basis a) (basis b) (basis d) (basis d) (basis c)
          (leibnizLeftEquiv 2 2 i)) ∘ Fin.natAdd (2 + 1)) =
        vec2 (I := I) (basis d) (basis c) := by
    funext q
    fin_cases q <;> rfl
  have hrightRic :
      ((fun i => vec5 (I := I) (basis a) (basis b) (basis d) (basis d) (basis c)
          (leibnizRightEquiv 2 2 i)) ∘ Fin.castAdd (2 + 1)) =
        vec2 (I := I) (basis b) (basis d) := by
    funext q
    fin_cases q <;> rfl
  have hrightNabla :
      ((fun i => vec5 (I := I) (basis a) (basis b) (basis d) (basis d) (basis c)
          (leibnizRightEquiv 2 2 i)) ∘ Fin.natAdd 2) =
        vec3 (I := I) (basis a) (basis d) (basis c) := by
    funext q
    fin_cases q <;> rfl
  rw [hleftNabla, hleftRic, hrightRic, hrightNabla]

private theorem hamiltonCurvatureRicciInnerNablaField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c e : Fin n) :
    hamiltonCurvatureRicciInnerNablaField (I := I) g x
        (vec5 (I := I) (basis a) (basis e) (basis e) (basis b) (basis c)) =
      ∑ d : Fin n,
        (metricNablaRm04Field (I := I) g x
              (vec5 (I := I) (basis a) (basis b) (basis d) (basis e) (basis c)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis d) (basis e)) +
          metricRm04 (I := I) (M := M) g x
              (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
            metricNablaRic (I := I) (M := M) g x
              (vec3 (I := I) (basis a) (basis d) (basis e))) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [hamiltonCurvatureRicciInnerNablaField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
  unfold metricTrace0S2InBasis
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  let slots : Fin 7 -> TangentSpace I x :=
    Fin.cons (basis a)
      (Fin.cons (basis b)
        (Fin.cons (basis d)
          (Fin.cons (basis e)
            (Fin.cons (basis c) (vec2 (I := I) (basis d) (basis e))))))
  have hslots :
      (fun i => metricTraceInput (I := I) (basis d) (basis d)
          (vec5 (I := I) (basis a) (basis e) (basis e) (basis b) (basis c))
            (traceNablaShuffle 4
              (frontExtendEquiv hamiltonCurvatureRicciFieldPerm i))) = slots := by
    funext q
    fin_cases q <;> rfl
  rw [hslots, hamiltonCurvatureRicciProductNablaField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    Tensor0SSpace.add_apply]
  rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply]
  have hleftNabla :
      ((fun i => slots (leibnizLeftEquiv 4 2 i)) ∘ Fin.castAdd 2) =
        vec5 (I := I) (basis a) (basis b) (basis d) (basis e) (basis c) := by
    funext q
    fin_cases q <;> rfl
  have hleftRic :
      ((fun i => slots (leibnizLeftEquiv 4 2 i)) ∘ Fin.natAdd (4 + 1)) =
        vec2 (I := I) (basis d) (basis e) := by
    funext q
    fin_cases q <;> rfl
  have hrightRm :
      ((fun i => slots (leibnizRightEquiv 4 2 i)) ∘ Fin.castAdd (2 + 1)) =
        vec4 (I := I) (basis b) (basis d) (basis e) (basis c) := by
    funext q
    fin_cases q <;> rfl
  have hrightNabla :
      ((fun i => slots (leibnizRightEquiv 4 2 i)) ∘ Fin.natAdd 4) =
        vec3 (I := I) (basis a) (basis d) (basis e) := by
    funext q
    fin_cases q <;> rfl
  rw [hleftNabla, hleftRic, hrightRm, hrightNabla]

private theorem hamiltonNablaCurvatureRicciField_apply_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonNablaCurvatureRicciField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      ∑ d : Fin n, ∑ e : Fin n,
        (metricNablaRm04Field (I := I) g x
              (vec5 (I := I) (basis a) (basis b) (basis d) (basis e) (basis c)) *
            metricRicci (I := I) (M := M) g x
              (vec2 (I := I) (basis d) (basis e)) +
          metricRm04 (I := I) (M := M) g x
              (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
            metricNablaRic (I := I) (M := M) g x
              (vec3 (I := I) (basis a) (basis d) (basis e))) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [hamiltonNablaCurvatureRicciField, metricTraceFirstTwoField_apply,
    metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
  unfold metricTrace0S2InBasis
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have heval : forall e : Fin n,
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 2)
          (hamiltonCurvatureRicciInnerNablaField (I := I) g)) x
          (metricTraceInput (I := I) (basis e) (basis e)
            (vec3 (I := I) (basis a) (basis b) (basis c))) =
        ∑ d : Fin n,
          (metricNablaRm04Field (I := I) g x
                (vec5 (I := I) (basis a) (basis b) (basis d) (basis e) (basis c)) *
              metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis d) (basis e)) +
            metricRm04 (I := I) (M := M) g x
                (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
              metricNablaRic (I := I) (M := M) g x
                (vec3 (I := I) (basis a) (basis d) (basis e))) := by
    intro e
    rw [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
    have hslots :
        (fun i => metricTraceInput (I := I) (basis e) (basis e)
            (vec3 (I := I) (basis a) (basis b) (basis c))
              (traceNablaShuffle 2 i)) =
          vec5 (I := I) (basis a) (basis e) (basis e) (basis b) (basis c) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots]
    exact hamiltonCurvatureRicciInnerNablaField_apply_orthonormal
      (I := I) g basis horth a b c e
  calc
    (∑ e : Fin n,
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 2)
          (hamiltonCurvatureRicciInnerNablaField (I := I) g)) x
          (metricTraceInput (I := I) (basis e) (basis e)
            (vec3 (I := I) (basis a) (basis b) (basis c)))) =
        ∑ e : Fin n, ∑ d : Fin n,
          (metricNablaRm04Field (I := I) g x
                (vec5 (I := I) (basis a) (basis b) (basis d) (basis e) (basis c)) *
              metricRicci (I := I) (M := M) g x
                (vec2 (I := I) (basis d) (basis e)) +
            metricRm04 (I := I) (M := M) g x
                (vec4 (I := I) (basis b) (basis d) (basis e) (basis c)) *
              metricNablaRic (I := I) (M := M) g x
                (vec3 (I := I) (basis a) (basis d) (basis e))) := by
          refine Finset.sum_congr rfl fun e _ => heval e
    _ = _ := Finset.sum_comm

private theorem metricNablaRm04Field_eq_nablaRm04Field
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    metricNablaRm04Field (I := I) (S.base.metric t) =
      nablaRm04Field (I := I) S t := by
  exact totalNabla0SRealizes_unique
    (by
      simpa [SolutionFamily.connection, SolutionFamily.rm04, metricCov,
        metricNablaRm04Field] using
        (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 4
          (metricCov (I := I) (M := M) (S.base.metric t))
          (metricRm04 (I := I) (M := M) (S.base.metric t))
          (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
            4 (metricCov (I := I) (M := M) (S.base.metric t))
            (metricCov_smooth (I := I) (M := M) (S.base.metric t))
            (metricRm04 (I := I) (M := M) (S.base.metric t)))))
    (by
      simpa [SolutionFamily.connection, SolutionFamily.rm04, metricCov] using
        (nablaRm04Field_realizes (I := I) S t))

private theorem hamiltonNablaRawRicciReactionComponent_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    metricNablaRicciTimeDerivativeField (I := I) (S.base.metric t) x
          (vec3 (I := I) (basis a) (basis b) (basis c)) -
        covariantDerivativeRoughLaplacianComponents
          (fun e f d (slots : Fin 2 -> Fin n) =>
            metricNabla3RicField (I := I) (S.base.metric t) x
              (Fin.cons (basis e)
                (Fin.cons (basis f)
                  (Fin.cons (basis d) (fun r => basis (slots r))))))
          a (fun q : Fin 2 => if q = 0 then b else c) =
      hamiltonNablaRawRicciReactionComponent
        (fun i j k l => S.base.rm04 t x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l m => nablaRm04Field (I := I) S t x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j => metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) (S.base.metric t) x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b c := by
  have hExpanded := congrArg
    (fun A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3 =>
      A x (vec3 (I := I) (basis a) (basis b) (basis c)))
    (metricNablaRicciTimeDerivativeExpandedField_eq
      (I := I) (S.base.metric t))
  simp only [metricNablaRicciTimeDerivativeExpandedField,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    smul_eq_mul] at hExpanded
  have hRough := metricNablaRoughRicciField_apply_orthonormal
    (I := I) (S.base.metric t) basis horth a b c
  have hSquare := hamiltonNablaRicciSquareField_apply_orthonormal
    (I := I) (S.base.metric t) basis horth a b c
  have hCurvature := hamiltonNablaCurvatureRicciField_apply_orthonormal
    (I := I) (S.base.metric t) basis horth a b c
  rw [metricNablaRm04Field_eq_nablaRm04Field (I := I) S t] at hCurvature
  rw [hRough, hSquare, hCurvature] at hExpanded
  have hTrace :
      covariantDerivativeRoughLaplacianComponents
          (fun e f d (slots : Fin 2 -> Fin n) =>
            metricNabla3RicField (I := I) (S.base.metric t) x
              (Fin.cons (basis e)
                (Fin.cons (basis f)
                  (Fin.cons (basis d) (fun r => basis (slots r))))))
          a (fun q : Fin 2 => if q = 0 then b else c) =
        ∑ e : Fin n, metricNabla3RicField (I := I) (S.base.metric t) x
          (vec5 (I := I) (basis a) (basis e) (basis e) (basis b) (basis c)) := by
    rw [covariantDerivativeRoughLaplacianComponents]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hTrace, hamiltonNablaRawRicciReactionComponent]
  simp only [SolutionFamily.rm04]
  linear_combination -hExpanded

private theorem metricRicci_nabla20SRealizesAt
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nabla20SRealizesAt (I := I) 2
      (metricCov (I := I) (M := M) g)
      (metricRicci (I := I) (M := M) g)
      (metricNablaRic (I := I) (M := M) g) x
      (metricNabla2Ric (I := I) (M := M) g x) := by
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let D1 := metricNablaRic (I := I) (M := M) g
  let D2 := metricNabla2Ric (I := I) (M := M) g
  have h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric D1 := by
    simpa [cov, Ric, D1, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by
            simpa [cov] using metricCov_smooth (I := I) (M := M) g) Ric))
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov D1 D2 := by
    simpa [cov, D1, D2, metricNabla2Ric] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov D1
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by
            simpa [cov] using metricCov_smooth (I := I) (M := M) g) D1))
  have h1' : Nabla0SSectionRealizes (I := I) 2 cov Ric D1 := by
    intro y X slots
    exact h1 X y slots
  exact ⟨by simpa [cov, Ric, D1] using h1', fun X slots => h2 X x slots⟩

private theorem metricNablaRic_nabla20SRealizesAt
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nabla20SRealizesAt (I := I) 3
      (metricCov (I := I) (M := M) g)
      (metricNablaRic (I := I) (M := M) g)
      (metricNabla2Ric (I := I) (M := M) g) x
      (metricNabla3RicField (I := I) g x) := by
  let cov := metricCov (I := I) (M := M) g
  let D1 := metricNablaRic (I := I) (M := M) g
  let D2 := metricNabla2Ric (I := I) (M := M) g
  let D3 := metricNabla3RicField (I := I) g
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov D1 D2 := by
    simpa [cov, D1, D2, metricNabla2Ric] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov D1
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by
            simpa [cov] using metricCov_smooth (I := I) (M := M) g) D1))
  have h3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov D2 D3 := by
    simpa [cov, D2, D3, metricNabla3RicField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov D2
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by
            simpa [cov] using metricCov_smooth (I := I) (M := M) g) D2))
  have h2' : Nabla0SSectionRealizes (I := I) 3 cov D1 D2 := by
    intro y X slots
    exact h2 X y slots
  exact ⟨by simpa [cov, D1, D2] using h2', fun X slots => h3 X x slots⟩

private theorem hamiltonPField_nabla20SRealizesAt
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nabla20SRealizesAt (I := I) 3
      (metricCov (I := I) (M := M) g)
      (hamiltonPField (I := I) g)
      (hamiltonNablaPField (I := I) g) x
      (hamiltonNabla2PField (I := I) g x) := by
  have h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (metricCov (I := I) (M := M) g)
      (hamiltonPField (I := I) g) (hamiltonNablaPField (I := I) g) := by
    simpa [hamiltonNablaPField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 (metricCov (I := I) (M := M) g)
        (hamiltonPField (I := I) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g) (hamiltonPField (I := I) g)))
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 (metricCov (I := I) (M := M) g)
      (hamiltonNablaPField (I := I) g) (hamiltonNabla2PField (I := I) g) := by
    simpa [hamiltonNabla2PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 (metricCov (I := I) (M := M) g)
        (hamiltonNablaPField (I := I) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g)
          (hamiltonNablaPField (I := I) g)))
  exact ⟨fun y X slots => h1 X y slots, fun X slots => h2 X x slots⟩

private theorem hamiltonNablaPField_nabla20SRealizesAt
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nabla20SRealizesAt (I := I) 4
      (metricCov (I := I) (M := M) g)
      (hamiltonNablaPField (I := I) g)
      (hamiltonNabla2PField (I := I) g) x
      (hamiltonNabla3PField (I := I) g x) := by
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 (metricCov (I := I) (M := M) g)
      (hamiltonNablaPField (I := I) g) (hamiltonNabla2PField (I := I) g) := by
    simpa [hamiltonNabla2PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 (metricCov (I := I) (M := M) g)
        (hamiltonNablaPField (I := I) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g)
          (hamiltonNablaPField (I := I) g)))
  have h3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 (metricCov (I := I) (M := M) g)
      (hamiltonNabla2PField (I := I) g) (hamiltonNabla3PField (I := I) g) := by
    simpa [hamiltonNabla3PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5 (metricCov (I := I) (M := M) g)
        (hamiltonNabla2PField (I := I) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g)
          (hamiltonNabla2PField (I := I) g)))
  exact ⟨fun y X slots => h2 X y slots, fun X slots => h3 X x slots⟩

private theorem hamiltonPField_ricciIdentityAt_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    Tensor0SRicciIdentityAt (I := I) (S.base.rm13 (t : Real))
      (hamiltonPField (I := I) (S.base.metric (t : Real)) x)
      (hamiltonNabla2PField (I := I) (S.base.metric (t : Real)) x) := by
  let g := S.base.metric (t : Real)
  let cov := S.family.connection (t : Real)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      cov (1 : WithTop ℕ∞) := connSmoothOfSol (I := I) S (t : Real)
  have htor : cov.torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S t)
    simpa [DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt, cov] using htf x
  exact tensor0S_ricciIdentity_of_torsionFree
    (I := I) cov hcov (S.base.rm13 (t : Real))
    (hamiltonPField (I := I) g)
    (hamiltonNablaPField (I := I) g)
    (hamiltonPField (I := I) g x)
    (hamiltonNablaPField (I := I) g x)
    (hamiltonNabla2PField (I := I) g x)
    (rm13OfSol (I := I) S (t : Real)) rfl rfl
    (by simpa [g, cov, SolutionFamily.connection, metricCov] using
      hamiltonPField_nabla20SRealizesAt (I := I) g x) htor

private theorem hamiltonNablaPField_ricciIdentityAt_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    Tensor0SRicciIdentityAt (I := I) (S.base.rm13 (t : Real))
      (hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x)
      (hamiltonNabla3PField (I := I) (S.base.metric (t : Real)) x) := by
  let g := S.base.metric (t : Real)
  let cov := S.family.connection (t : Real)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      cov (1 : WithTop ℕ∞) := connSmoothOfSol (I := I) S (t : Real)
  have htor : cov.torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S t)
    simpa [DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt, cov] using htf x
  exact tensor0S_ricciIdentity_of_torsionFree
    (I := I) cov hcov (S.base.rm13 (t : Real))
    (hamiltonNablaPField (I := I) g)
    (hamiltonNabla2PField (I := I) g)
    (hamiltonNablaPField (I := I) g x)
    (hamiltonNabla2PField (I := I) g x)
    (hamiltonNabla3PField (I := I) g x)
    (rm13OfSol (I := I) S (t : Real)) rfl rfl
    (by simpa [g, cov, SolutionFamily.connection, metricCov] using
      hamiltonNablaPField_nabla20SRealizesAt (I := I) g x) htor

private theorem metricRicci_ricciIdentityAt_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    Tensor0SRicciIdentityAt (I := I) (S.base.rm13 (t : Real))
      (metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x)
      (metricNabla2Ric (I := I) (M := M) (S.base.metric (t : Real)) x) := by
  let g := S.base.metric (t : Real)
  let cov := S.family.connection (t : Real)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      cov (1 : WithTop ℕ∞) := connSmoothOfSol (I := I) S (t : Real)
  have htor : cov.torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S t)
    simpa [DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt, cov] using htf x
  exact tensor0S_ricciIdentity_of_torsionFree
    (I := I) cov hcov (S.base.rm13 (t : Real))
    (metricRicci (I := I) (M := M) g)
    (metricNablaRic (I := I) (M := M) g)
    (metricRicci (I := I) (M := M) g x)
    (metricNablaRic (I := I) (M := M) g x)
    (metricNabla2Ric (I := I) (M := M) g x)
    (rm13OfSol (I := I) S (t : Real)) rfl rfl
    (by simpa [g, cov, SolutionFamily.connection, metricCov] using
      metricRicci_nabla20SRealizesAt (I := I) g x) htor

private theorem metricNablaRic_ricciIdentityAt_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) :
    Tensor0SRicciIdentityAt (I := I) (S.base.rm13 (t : Real))
      (metricNablaRic (I := I) (M := M) (S.base.metric (t : Real)) x)
      (metricNabla3RicField (I := I) (S.base.metric (t : Real)) x) := by
  let g := S.base.metric (t : Real)
  let cov := S.family.connection (t : Real)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      cov (1 : WithTop ℕ∞) := connSmoothOfSol (I := I) S (t : Real)
  have htor : cov.torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S t)
    simpa [DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt, cov] using htf x
  exact tensor0S_ricciIdentity_of_torsionFree
    (I := I) cov hcov (S.base.rm13 (t : Real))
    (metricNablaRic (I := I) (M := M) g)
    (metricNabla2Ric (I := I) (M := M) g)
    (metricNablaRic (I := I) (M := M) g x)
    (metricNabla2Ric (I := I) (M := M) g x)
    (metricNabla3RicField (I := I) g x)
    (rm13OfSol (I := I) S (t : Real)) rfl rfl
    (by simpa [g, cov, SolutionFamily.connection, metricCov] using
      metricNablaRic_nabla20SRealizesAt (I := I) g x) htor

theorem differentiatedRicciIdentityComponents_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    differentiatedTensorRicciIdentityComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun e a b c d => nablaRm04Field (I := I) S (t : Real) x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)))
      (fun slots => metricRicci (I := I) (M := M)
        (S.base.metric (t : Real)) x (fun r => basis (slots r)))
      (fun e slots => metricNablaRic (I := I) (M := M)
        (S.base.metric (t : Real)) x
          (Fin.cons (basis e) (fun r => basis (slots r))))
      (fun e a b slots => metricNabla3RicField (I := I)
        (S.base.metric (t : Real)) x
          (Fin.cons (basis e)
            (Fin.cons (basis a) (Fin.cons (basis b)
              (fun r => basis (slots r)))))) := by
  let g := S.base.metric (t : Real)
  have hDA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (S.family.connection (t : Real))
      (metricRicci (I := I) (M := M) g)
      (metricNablaRic (I := I) (M := M) g) := by
    simpa [g, SolutionFamily.connection, metricCov, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 (metricCov (I := I) (M := M) g)
        (metricRicci (I := I) (M := M) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g)
          (metricRicci (I := I) (M := M) g)))
  have hD3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 (S.family.connection (t : Real))
      (metricNabla2Ric (I := I) (M := M) g)
      (metricNabla3RicField (I := I) g) := by
    simpa [g, SolutionFamily.connection, metricCov, metricNabla3RicField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 (metricCov (I := I) (M := M) g)
        (metricNabla2Ric (I := I) (M := M) g)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g)
          (metricNabla2Ric (I := I) (M := M) g)))
  have hOutput : Rm04OutputSkewAt (I := I) (S.base.rm04 (t : Real) x) :=
    rm04OutputSkew_regular (I := I) S S.base.rm13 S.base.rm04
      (fun tau => rm13OfSol (I := I) S (tau : Real))
      (fun tau y => solution_rm04LowersRm13At (I := I) S (tau : Real) y) t x
  have hNablaSymm : NablaRmSymmAt (I := I)
      (nablaRm04Field (I := I) S (t : Real) x) := by
    simpa [nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
      SolutionFamily.rm04, metricCov, metricRm04,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Curvature.metricRm04] using
      (DifferentialGeometry.Geometry.Connection.levi_civita_covariant_riemann_symmetries
        (I := I) (M := M) g (x := x))
  exact differentiatedTensorRicciIdentityComponents_of_orthonormalBasis
    (I := I) S t x basis horth
    (metricRicci (I := I) (M := M) g)
    (metricNablaRic (I := I) (M := M) g)
    (metricNabla2Ric (I := I) (M := M) g)
    (metricNabla3RicField (I := I) g) hDA hD3
    (fun y => metricRicci_ricciIdentityAt_of_solution (I := I) S t y)
    (fun a b c d => hOutput (basis a) (basis b) (basis c) (basis d))
    (fun e a b c d => hNablaSymm.1
      (basis e) (basis a) (basis b) (basis c) (basis d))

theorem gradientRicciIdentityComponents_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    tensorGradientRicciIdentityComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun e slots => metricNablaRic (I := I) (M := M)
        (S.base.metric (t : Real)) x
          (Fin.cons (basis e) (fun r => basis (slots r))))
      (fun e f d slots => metricNabla3RicField (I := I)
        (S.base.metric (t : Real)) x
          (Fin.cons (basis e)
            (Fin.cons (basis f) (Fin.cons (basis d)
              (fun r => basis (slots r)))))) := by
  have hOutput : Rm04OutputSkewAt (I := I) (S.base.rm04 (t : Real) x) :=
    rm04OutputSkew_regular (I := I) S S.base.rm13 S.base.rm04
      (fun tau => rm13OfSol (I := I) S (tau : Real))
      (fun tau y => solution_rm04LowersRm13At (I := I) S (tau : Real) y) t x
  exact tensorGradientRicciIdentityComponents_of_orthonormalBasis
    (I := I) (S.base.metric (t : Real)) (S.base.rm13 (t : Real))
    (S.base.rm04 (t : Real) x)
    (solution_rm04LowersRm13At (I := I) S (t : Real) x)
    basis horth
    (metricNablaRic (I := I) (M := M) (S.base.metric (t : Real)) x)
    (metricNabla3RicField (I := I) (S.base.metric (t : Real)) x)
    (metricNablaRic_ricciIdentityAt_of_solution (I := I) S t x)
    (fun a b c d => hOutput (basis a) (basis b) (basis c) (basis d))

private theorem differentiatedHamiltonPIdentityComponents_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    differentiatedTensorRicciIdentityComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun e a b c d => nablaRm04Field (I := I) S (t : Real) x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)))
      (fun slots => hamiltonPField (I := I) (S.base.metric (t : Real)) x
        (fun r => basis (slots r)))
      (fun e slots => hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x
        (Fin.cons (basis e) (fun r => basis (slots r))))
      (fun e a b slots => hamiltonNabla3PField
        (I := I) (S.base.metric (t : Real)) x
          (Fin.cons (basis e)
            (Fin.cons (basis a) (Fin.cons (basis b)
              (fun r => basis (slots r)))))) := by
  have hDA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 (S.family.connection (t : Real))
      (hamiltonPField (I := I) (S.base.metric (t : Real)))
      (hamiltonNablaPField (I := I) (S.base.metric (t : Real))) := by
    simpa [SolutionFamily.connection, metricCov, hamiltonNablaPField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3
        (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
        (hamiltonPField (I := I) (S.base.metric (t : Real)))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
          (metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
          (hamiltonPField (I := I) (S.base.metric (t : Real)))))
  have hD3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 (S.family.connection (t : Real))
      (hamiltonNabla2PField (I := I) (S.base.metric (t : Real)))
      (hamiltonNabla3PField (I := I) (S.base.metric (t : Real))) := by
    simpa [SolutionFamily.connection, metricCov, hamiltonNabla3PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5
        (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
        (hamiltonNabla2PField (I := I) (S.base.metric (t : Real)))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
          (metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real)))
          (hamiltonNabla2PField (I := I) (S.base.metric (t : Real)))))
  have hOutput : Rm04OutputSkewAt (I := I) (S.base.rm04 (t : Real) x) :=
    rm04OutputSkew_regular (I := I) S S.base.rm13 S.base.rm04
      (fun tau => rm13OfSol (I := I) S (tau : Real))
      (fun tau y => solution_rm04LowersRm13At (I := I) S (tau : Real) y) t x
  have hNablaSymm : NablaRmSymmAt (I := I)
      (nablaRm04Field (I := I) S (t : Real) x) := by
    simpa [nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
      SolutionFamily.rm04, metricCov, metricRm04,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Curvature.metricRm04] using
      (DifferentialGeometry.Geometry.Connection.levi_civita_covariant_riemann_symmetries
        (I := I) (M := M) (S.base.metric (t : Real)) (x := x))
  exact differentiatedTensorRicciIdentityComponents_of_orthonormalBasis
    (I := I) S t x basis horth
    (hamiltonPField (I := I) (S.base.metric (t : Real)))
    (hamiltonNablaPField (I := I) (S.base.metric (t : Real)))
    (hamiltonNabla2PField (I := I) (S.base.metric (t : Real)))
    (hamiltonNabla3PField (I := I) (S.base.metric (t : Real))) hDA hD3
    (fun y => hamiltonPField_ricciIdentityAt_of_solution (I := I) S t y)
    (fun a b c d => hOutput (basis a) (basis b) (basis c) (basis d))
    (fun e a b c d => hNablaSymm.1
      (basis e) (basis a) (basis b) (basis c) (basis d))

private theorem gradientHamiltonPIdentityComponents_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    tensorGradientRicciIdentityComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun e slots => hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x
        (Fin.cons (basis e) (fun r => basis (slots r))))
      (fun e f d slots => hamiltonNabla3PField
        (I := I) (S.base.metric (t : Real)) x
          (Fin.cons (basis e)
            (Fin.cons (basis f) (Fin.cons (basis d)
              (fun r => basis (slots r)))))) := by
  have hOutput : Rm04OutputSkewAt (I := I) (S.base.rm04 (t : Real) x) :=
    rm04OutputSkew_regular (I := I) S S.base.rm13 S.base.rm04
      (fun tau => rm13OfSol (I := I) S (tau : Real))
      (fun tau y => solution_rm04LowersRm13At (I := I) S (tau : Real) y) t x
  exact tensorGradientRicciIdentityComponents_of_orthonormalBasis
    (I := I) (S.base.metric (t : Real)) (S.base.rm13 (t : Real))
    (S.base.rm04 (t : Real) x)
    (solution_rm04LowersRm13At (I := I) S (t : Real) x)
    basis horth
    (hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x)
    (hamiltonNabla3PField (I := I) (S.base.metric (t : Real)) x)
    (hamiltonNablaPField_ricciIdentityAt_of_solution (I := I) S t x)
    (fun a b c d => hOutput (basis a) (basis b) (basis c) (basis d))

private theorem curvatureSecondDerivativeCommutatorComponents_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    covariantTensorSecondDerivativeCommutatorComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun slots => S.base.rm04 (t : Real) x (fun r => basis (slots r)))
      (fun a b slots => nablaKRm04Field (I := I) S (t : Real) 2 x
        (Fin.cons (basis a) (Fin.cons (basis b)
          (fun r => basis (slots r))))) := by
  have hOutput : Rm04OutputSkewAt (I := I) (S.base.rm04 (t : Real) x) :=
    rm04OutputSkew_regular (I := I) S S.base.rm13 S.base.rm04
      (fun tau => rm13OfSol (I := I) S (tau : Real))
      (fun tau y => solution_rm04LowersRm13At (I := I) S (tau : Real) y) t x
  exact covariantTensorSecondDerivativeCommutatorComponents_of_orthonormalBasis
    (I := I) (S.base.metric (t : Real)) (S.base.rm13 (t : Real))
    (S.base.rm04 (t : Real) x)
    (solution_rm04LowersRm13At (I := I) S (t : Real) x)
    basis horth (S.base.rm04 (t : Real) x)
    (nablaKRm04Field (I := I) S (t : Real) 2 x)
    (nablaKRm04_ricciIdentityAt (I := I) S t 0 x)
    (fun a b c d => hOutput (basis a) (basis b) (basis c) (basis d))

private def hamiltonRmComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l => S.base.rm04 t x
    (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))

private noncomputable def hamiltonRicciComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Real :=
  fun i j => metricRicci (I := I) (M := M) (S.base.metric t) x
    (vec2 (I := I) (basis i) (basis j))

private noncomputable def hamiltonNablaRmComponentOfSolution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l m => nablaRm04Field (I := I) S t x
    (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m))

private noncomputable def hamiltonNablaRicciComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Real :=
  fun i j k => metricNablaRic (I := I) (M := M) (S.base.metric t) x
    (vec3 (I := I) (basis i) (basis j) (basis k))

private noncomputable def hamiltonNablaRicciTimeComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Real :=
  fun i j k => metricNablaRicciTimeDerivativeField (I := I) (S.base.metric t) x
    (vec3 (I := I) (basis i) (basis j) (basis k))

private noncomputable def hamiltonNablaPTimeComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l => hamiltonNablaPTimeDerivativeField (I := I)
    (S.base.metric t) x (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))

private noncomputable def hamiltonNabla3RicciComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l m => metricNabla3RicField (I := I) (S.base.metric t) x
    (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m))

private noncomputable def hamiltonNabla2RmComponentOfSolution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l m p => nablaKRm04Field (I := I) S t 2 x
    (Fin.cons (basis i)
      (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis p)))

private noncomputable def hamiltonNablaPComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l => hamiltonNablaPField (I := I) (S.base.metric t) x
    (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))

private noncomputable def hamiltonNabla3PComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l m p => hamiltonNabla3PField (I := I) (S.base.metric t) x
    (Fin.cons (basis i)
      (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis p)))

private noncomputable def hamiltonDivPComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Real :=
  fun i j => ∑ k : Fin n,
    hamiltonNablaPComponentOfSolution (I := I) S t x basis k k i j

private theorem hamiltonDivPComponentOfSolution_eq_hamiltonDivPAt_orthonormal
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPComponentOfSolution (I := I) S t x basis a b =
      hamiltonDivPAt (I := I) (S.base.metric t) x
        (vec2 (I := I) (basis a) (basis b)) := by
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (S.base.metric t) basis horth
  rw [hamiltonDivPAt_apply (I := I) (S.base.metric t) basis
      (fun i j => if i = j then (1 : Real) else 0) hinv
      (basis a) (basis b)]
  unfold hamiltonDivPComponentOfSolution hamiltonNablaPComponentOfSolution
  simp_rw [hamiltonNablaPField_apply]
  simp only [Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [metricNabla2Ric_last_two_symm (I := I) (M := M)]

private theorem hamilton_nabla_P_components_skew_of_solution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    forall d a b c,
      hamiltonNablaPComponentOfSolution (I := I) S t x basis d a b c =
        -hamiltonNablaPComponentOfSolution (I := I) S t x basis d b a c := by
  intro d a b c
  simp only [hamiltonNablaPComponentOfSolution]
  rw [hamiltonNablaPField_apply, hamiltonNablaPField_apply]
  ring

private theorem hamilton_differentiated_P_identity_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    differentiatedTensorRicciIdentityComponents
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
      (fun slots : Fin 3 -> Fin n => hamiltonPComponent
        (hamiltonNablaRicciComponentOfSolution
          (I := I) S (t : Real) x basis) (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Fin n) => hamiltonNablaPComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Fin n) => hamiltonNabla3PComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1) (slots 2)) := by
  have hR :
      hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun a b c d => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hNablaR :
      hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun e a b c d => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hP :
      (fun slots : Fin 3 -> Fin n => hamiltonPComponent
        (hamiltonNablaRicciComponentOfSolution
          (I := I) S (t : Real) x basis) (slots 0) (slots 1) (slots 2)) =
        (fun slots : Fin 3 -> Fin n =>
          hamiltonPField (I := I) (S.base.metric (t : Real)) x
            (fun r => basis (slots r))) := by
    funext slots
    have hslots : (fun r : Fin 3 => basis (slots r)) =
        vec3 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots, hamiltonPField_apply, hamiltonPAt_apply]
    rfl
  have hNablaP :
      (fun e (slots : Fin 3 -> Fin n) => hamiltonNablaPComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1) (slots 2)) =
        (fun e (slots : Fin 3 -> Fin n) =>
          hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x
            (Fin.cons (basis e) (fun r => basis (slots r)))) := by
    funext e slots
    simp only [hamiltonNablaPComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hD3P :
      (fun e f d (slots : Fin 3 -> Fin n) => hamiltonNabla3PComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1) (slots 2)) =
        (fun e f d (slots : Fin 3 -> Fin n) =>
          hamiltonNabla3PField (I := I) (S.base.metric (t : Real)) x
            (Fin.cons (basis e)
              (Fin.cons (basis f) (Fin.cons (basis d)
                (fun r => basis (slots r)))))) := by
    funext e f d slots
    simp only [hamiltonNabla3PComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hR, hNablaR, hP, hNablaP, hD3P]
  exact differentiatedHamiltonPIdentityComponents_of_solution
    (I := I) S t x basis horth

private theorem hamilton_gradient_P_identity_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    tensorGradientRicciIdentityComponents
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (fun e (slots : Fin 3 -> Fin n) => hamiltonNablaPComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Fin n) => hamiltonNabla3PComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1) (slots 2)) := by
  have hR :
      hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun a b c d => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hNablaP :
      (fun e (slots : Fin 3 -> Fin n) => hamiltonNablaPComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1) (slots 2)) =
        (fun e (slots : Fin 3 -> Fin n) =>
          hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x
            (Fin.cons (basis e) (fun r => basis (slots r)))) := by
    funext e slots
    simp only [hamiltonNablaPComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hD3P :
      (fun e f d (slots : Fin 3 -> Fin n) => hamiltonNabla3PComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1) (slots 2)) =
        (fun e f d (slots : Fin 3 -> Fin n) =>
          hamiltonNabla3PField (I := I) (S.base.metric (t : Real)) x
            (Fin.cons (basis e)
              (Fin.cons (basis f) (Fin.cons (basis d)
                (fun r => basis (slots r)))))) := by
    funext e f d slots
    simp only [hamiltonNabla3PComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hR, hNablaP, hD3P]
  exact gradientHamiltonPIdentityComponents_of_solution
    (I := I) S t x basis horth

private theorem hamilton_curvature_second_derivative_commutator_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    covariantTensorSecondDerivativeCommutatorComponents
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (fun slots : Fin 4 -> Fin n =>
        hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
          (slots 0) (slots 1) (slots 2) (slots 3))
      (fun a b (slots : Fin 4 -> Fin n) =>
        hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis
          a b (slots 0) (slots 1) (slots 2) (slots 3)) := by
  have hR :
      hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun a b c d => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hA :
      (fun slots : Fin 4 -> Fin n =>
        hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
          (slots 0) (slots 1) (slots 2) (slots 3)) =
        (fun slots : Fin 4 -> Fin n =>
          S.base.rm04 (t : Real) x (fun r => basis (slots r))) := by
    funext slots
    simp only [hamiltonRmComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hD2 :
      (fun a b (slots : Fin 4 -> Fin n) =>
        hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis
          a b (slots 0) (slots 1) (slots 2) (slots 3)) =
        (fun a b (slots : Fin 4 -> Fin n) =>
          nablaKRm04Field (I := I) S (t : Real) 2 x
            (Fin.cons (basis a) (Fin.cons (basis b)
              (fun r => basis (slots r))))) := by
    funext a b slots
    simp only [hamiltonNabla2RmComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hA, hD2, hR]
  exact curvatureSecondDerivativeCommutatorComponents_of_solution
    (I := I) S t x basis horth

private theorem hamilton_differentiated_ricci_identity_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    differentiatedTensorRicciIdentityComponents
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
      (fun slots : Fin 2 -> Fin n => hamiltonRicciComponentOfSolution
        (I := I) S (t : Real) x basis (slots 0) (slots 1))
      (fun e (slots : Fin 2 -> Fin n) => hamiltonNablaRicciComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1))
      (fun e f d (slots : Fin 2 -> Fin n) => hamiltonNabla3RicciComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1)) := by
  have hR :
      hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun a b c d => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hNablaR :
      hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun e a b c d => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hRic :
      (fun slots : Fin 2 -> Fin n => hamiltonRicciComponentOfSolution
        (I := I) S (t : Real) x basis (slots 0) (slots 1)) =
        (fun slots : Fin 2 -> Fin n => metricRicci (I := I) (M := M)
          (S.base.metric (t : Real)) x (fun r => basis (slots r))) := by
    funext slots
    simp only [hamiltonRicciComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hNablaRic :
      (fun e (slots : Fin 2 -> Fin n) => hamiltonNablaRicciComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1)) =
        (fun e (slots : Fin 2 -> Fin n) => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
            (Fin.cons (basis e) (fun r => basis (slots r)))) := by
    funext e slots
    simp only [hamiltonNablaRicciComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hD3 :
      (fun e f d (slots : Fin 2 -> Fin n) => hamiltonNabla3RicciComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1)) =
        (fun e f d (slots : Fin 2 -> Fin n) => metricNabla3RicField (I := I)
          (S.base.metric (t : Real)) x
            (Fin.cons (basis e)
              (Fin.cons (basis f) (Fin.cons (basis d)
                (fun r => basis (slots r)))))) := by
    funext e f d slots
    simp only [hamiltonNabla3RicciComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hR, hNablaR, hRic, hNablaRic, hD3]
  exact differentiatedRicciIdentityComponents_of_solution (I := I) S t x basis horth

private theorem hamilton_gradient_ricci_identity_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    tensorGradientRicciIdentityComponents
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (fun e (slots : Fin 2 -> Fin n) => hamiltonNablaRicciComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1))
      (fun e f d (slots : Fin 2 -> Fin n) => hamiltonNabla3RicciComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1)) := by
  have hR :
      hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis =
        (fun a b c d => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := rfl
  have hNablaRic :
      (fun e (slots : Fin 2 -> Fin n) => hamiltonNablaRicciComponentOfSolution
        (I := I) S (t : Real) x basis e (slots 0) (slots 1)) =
        (fun e (slots : Fin 2 -> Fin n) => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
            (Fin.cons (basis e) (fun r => basis (slots r)))) := by
    funext e slots
    simp only [hamiltonNablaRicciComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  have hD3 :
      (fun e f d (slots : Fin 2 -> Fin n) => hamiltonNabla3RicciComponentOfSolution
        (I := I) S (t : Real) x basis e f d (slots 0) (slots 1)) =
        (fun e f d (slots : Fin 2 -> Fin n) => metricNabla3RicField (I := I)
          (S.base.metric (t : Real)) x
            (Fin.cons (basis e)
              (Fin.cons (basis f) (Fin.cons (basis d)
                (fun r => basis (slots r)))))) := by
    funext e f d slots
    simp only [hamiltonNabla3RicciComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hR, hNablaRic, hD3]
  exact gradientRicciIdentityComponents_of_solution (I := I) S t x basis horth

private theorem hamilton_bianchi_trace_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    SecondBianchiAt (I := I) (nablaRm04Field (I := I) S t x) ∧
      NablaRmSymmAt (I := I) (nablaRm04Field (I := I) S t x) ∧
        NablaRicTraceAt (I := I) basis
          (fun i j => if i = j then (1 : Real) else 0)
          (nablaRm04Field (I := I) S t x)
          (metricNablaRic (I := I) (M := M) (S.base.metric t) x) := by
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (S.base.metric t) basis horth
  simpa [nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
    SolutionFamily.rm04, metricNablaRic, metricCov, metricRm04, metricRicci,
    DifferentialGeometry.Geometry.Curvature.metricCov,
    DifferentialGeometry.Geometry.Curvature.metricRm04,
    DifferentialGeometry.Geometry.Curvature.metricRicci] using
    (DifferentialGeometry.Geometry.Connection.levi_civita_bianchi_trace_identities
      (I := I) (M := M) (S.base.metric t) basis
        (fun i j => if i = j then (1 : Real) else 0) hinv)

private theorem hamilton_contracted_curvature_derivative_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    contractedCurvatureDerivativeComponents
      (hamiltonNablaRmComponentOfSolution (I := I) S t x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S t x basis) := by
  intro p q r
  have hcore := hamilton_bianchi_trace_components_of_solution
    (I := I) S t x basis horth
  have hDiv := curvature_divergence_eq_hamiltonP (I := I) basis
    (fun i j => if i = j then (1 : Real) else 0)
    (nablaRm04Field (I := I) S t x)
    (metricNablaRic (I := I) (M := M) (S.base.metric t) x)
    hcore.1 hcore.2.1 hcore.2.2 (basis r) (basis q) (basis p)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hamiltonP_apply] at hDiv
  rw [metricNablaRic_last_two_symm (I := I) (M := M) (S.base.metric t) x
    (basis q) (basis r) (basis p),
    metricNablaRic_last_two_symm (I := I) (M := M) (S.base.metric t) x
      (basis r) (basis q) (basis p)] at hDiv
  simpa [hamiltonNablaRmComponentOfSolution,
    hamiltonNablaRicciComponentOfSolution] using hDiv

private theorem hamilton_differentiated_curvature_divergence_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    differentiatedCurvatureDivergenceComponents
      (hamiltonNabla2RmComponentOfSolution (I := I) S t x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S t x basis) := by
  intro d a e b
  let fixedNabla2Rm :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x :=
    DifferentialGeometry.Tensor0SBundle.tensor0SCurry
      (I := I) (M := M) 5 x (nablaKRm04Field (I := I) S t 2 x) (basis d)
  let fixedNabla2Ric :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
    DifferentialGeometry.Tensor0SBundle.tensor0SCurry
      (I := I) (M := M) 3 x
        (metricNabla2Ric (I := I) (M := M) (S.base.metric t) x) (basis d)
  have hSecond : SecondBianchiAt (I := I) fixedNabla2Rm := by
    intro A X Y Z W
    have h := DifferentialGeometry.Geometry.Connection.canRmSecond_nabla
      (I := I) (M := M) (S.base.metric t) (basis d) A X Y Z W
    simpa [fixedNabla2Rm, Tensor0SBundle.tensor0S_curry_apply_cons,
      nablaKRm04Field, SolutionOn.family, SolutionFamily.connection,
      SolutionFamily.rm04, metricCov, metricRm04,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Curvature.metricRm04] using h
  have hRmSymm : NablaRmSymmAt (I := I) fixedNabla2Rm := by
    have h :=
      DifferentialGeometry.Geometry.Connection.levi_civita_second_covariant_riemann_symmetries
        (I := I) (M := M) (S.base.metric t) (x := x)
    refine ⟨?_, ?_, ?_⟩
    · intro A X Y Z W
      simpa [fixedNabla2Rm,
        Tensor0SBundle.tensor0S_curry_apply_cons,
        nablaKRm04Field, SolutionOn.family, SolutionFamily.connection,
        SolutionFamily.rm04, metricCov, metricRm04,
        DifferentialGeometry.Geometry.Curvature.metricCov,
        DifferentialGeometry.Geometry.Curvature.metricRm04] using
        h.1 (basis d) A X Y Z W
    · intro A X Y Z W
      simpa [fixedNabla2Rm,
        Tensor0SBundle.tensor0S_curry_apply_cons,
        nablaKRm04Field, SolutionOn.family, SolutionFamily.connection,
        SolutionFamily.rm04, metricCov, metricRm04,
        DifferentialGeometry.Geometry.Curvature.metricCov,
        DifferentialGeometry.Geometry.Curvature.metricRm04] using
        h.2.1 (basis d) A X Y Z W
    · intro A X Y Z W
      simpa [fixedNabla2Rm,
        Tensor0SBundle.tensor0S_curry_apply_cons,
        nablaKRm04Field, SolutionOn.family, SolutionFamily.connection,
        SolutionFamily.rm04, metricCov, metricRm04,
        DifferentialGeometry.Geometry.Curvature.metricCov,
        DifferentialGeometry.Geometry.Curvature.metricRm04] using
        h.2.2 (basis d) A X Y Z W
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (S.base.metric t) basis horth
  have hRicTrace : NablaRicTraceAt (I := I) basis
      (fun i j => if i = j then (1 : Real) else 0)
      fixedNabla2Rm fixedNabla2Ric := by
    intro A B C
    have h :=
      DifferentialGeometry.Geometry.Connection.levi_civita_second_covariant_ricci_eq_riemann_trace
        (I := I) (M := M) (S.base.metric t) basis
        (fun i j => if i = j then (1 : Real) else 0) hinv
        (basis d) A B C
    simpa [fixedNabla2Rm, fixedNabla2Ric,
      Tensor0SBundle.tensor0S_curry_apply_cons,
      DifferentialGeometry.Tensor.RSTensor.metricTrace_finCons_vec3_eq_vec4,
      nablaKRm04Field, SolutionOn.family, SolutionFamily.connection,
      SolutionFamily.rm04, metricNabla2Ric, metricNablaRic, metricRicci,
      metricCov, metricRm04,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Curvature.metricRm04] using h
  have hDiv := curvature_divergence_eq_hamiltonP (I := I) basis
    (fun i j => if i = j then (1 : Real) else 0)
    fixedNabla2Rm fixedNabla2Ric hSecond hRmSymm hRicTrace
    (basis e) (basis b) (basis a)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at hDiv
  simpa [hamiltonNabla2RmComponentOfSolution,
    hamiltonNablaPComponentOfSolution, fixedNabla2Rm, fixedNabla2Ric,
    Tensor0SBundle.tensor0S_curry_apply_cons,
    DifferentialGeometry.Tensor.RSTensor.metricTrace_finCons_vec3_eq_vec4,
    hamiltonNablaPField_apply] using hDiv

private theorem hamilton_rm_components_symm_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Rm04Symm (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis) := by
  have hRm13 := fun tau :
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D =>
    rm13OfSol (I := I) S (tau : Real)
  have hLower := fun
      (tau : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (y : M) =>
    solution_rm04LowersRm13At (I := I) S (tau : Real) y
  have hInput := rm04InputSkew_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hOutput := rm04OutputSkew_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hPair := rm04PairSymm_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hFirst := rm04FirstBianchi_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j k l
    simpa [hamiltonRmComponentOfSolution] using
      hInput (basis j) (basis i) (basis k) (basis l)
  · intro i j k l
    simpa [hamiltonRmComponentOfSolution] using
      hOutput (basis i) (basis j) (basis k) (basis l)
  · intro i j k l
    simpa [hamiltonRmComponentOfSolution] using
      hPair (basis i) (basis j) (basis k) (basis l)
  · intro i j k l
    simpa [hamiltonRmComponentOfSolution] using
      hFirst (basis i) (basis j) (basis k) (basis l)

private theorem hamilton_nabla_rm_components_pair_symm_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    forall e,
      Rm04PairSymm
        (hamiltonNablaRmComponentOfSolution (I := I) S t x basis e) := by
  have hSymm := (hamilton_bianchi_trace_components_of_solution
    (I := I) S t x basis horth).2.1
  intro e
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    simpa [hamiltonNablaRmComponentOfSolution] using
      hSymm.2.1 (basis e) (basis b) (basis a) (basis c) (basis d)
  · intro a b c d
    simpa [hamiltonNablaRmComponentOfSolution] using
      hSymm.1 (basis e) (basis a) (basis b) (basis c) (basis d)
  · intro a b c d
    simpa [hamiltonNablaRmComponentOfSolution] using
      hSymm.2.2 (basis e) (basis a) (basis b) (basis c) (basis d)

private theorem hamilton_curvature_ricci_trace_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    curvatureRicciTraceComponents
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis) := by
  intro i j
  symm
  simpa [hamiltonRmComponentOfSolution, hamiltonRicciComponentOfSolution,
    SolutionOn.ricci, SolutionFamily.ricci] using
    (ricci_diag_eq_sum_rm04_diag_of_orthonormal
      (I := I) (S.base.metric (t : Real)) basis
      (S.ricci (t : Real)) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real))
      (ricciTraceOfSol (I := I) S (t : Real))
      (solution_rm04LowersRm13At (I := I) S (t : Real) x) horth i j)

private theorem rm04_hasDerivWithinAt_oneTimeUhlenbeck_heat
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c d : Fin n) :
    HasDerivWithinAt
      (fun s : Real => S.base.rm04 s x
        (vec4 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis c))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis d))))
      (hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) +
        hamiltonRmReactionComponent
          (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
          a b c d)
      D.carrier (t : Real) := by
  classical
  let g := S.base.metric (t : Real)
  let RicT := metricRicci (I := I) (M := M) g x
  let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
  let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
  let slots : Fin 4 -> Fin n := fun q =>
    if q = 0 then a else if q = 1 then b else if q = 2 then c else d
  let RA := ricciEndAt (I := I) g RicT (basis a)
  let RB := ricciEndAt (I := I) g RicT (basis b)
  let RC := ricciEndAt (I := I) g RicT (basis c)
  let RD := ricciEndAt (I := I) g RicT (basis d)
  have hslots : (fun q => basis (slots q)) =
      vec4 (I := I) (basis a) (basis b) (basis c) (basis d) := by
    funext q
    fin_cases q <;> rfl
  have hbase := rm04Base_of_solution_any
    (I := I) S hS t x basis horth slots
  rw [hslots] at hbase
  have hdiff (A B C D : TangentSpace I x) :=
    rm04Base_differentiableWithinAt_of_solution
      (I := I) S hS t x basis horth (vec4 (I := I) A B C D)
  have hmove := tensor04At_hasDerivWithinAt_affine_slots
    (I := I) (fun s : Real => S.base.rm04 s x)
    (tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (nablaKRm04Field (I := I) S (t : Real) 2 x))
        (fun i => basis i) slots +
      DifferentialGeometry.Geometry.Connection.hamiltonRmReact
        (fun q : Fin 4 -> Fin n =>
          S.base.rm04 (t : Real) x (fun p => basis (q p))) slots)
    (basis a) (basis b) (basis c) (basis d) RA RB RC RD hbase hdiff
  have hrough := hamiltonRmRoughLaplacianField_eq_component_orthonormal
    (I := I) S (t : Real) basis horth slots
  rw [hslots] at hrough
  have hRfun :
      (fun q : Fin 4 -> Fin n =>
        S.base.rm04 (t : Real) x (fun p => basis (q p))) =
        fun q => R (q 0) (q 1) (q 2) (q 3) := by
    funext q
    apply congrArg (S.base.rm04 (t : Real) x)
    funext p
    fin_cases p <;> rfl
  have hslotsMatrix : slots = ![a, b, c, d] := by
    funext q
    fin_cases q <;> rfl
  have h0left :
      Function.update (fun i => basis (slots i)) (0 : Fin 4)
          (ricciEndAt (I := I) g RicT (basis (slots 0))) =
        vec4 (I := I) RA (basis b) (basis c) (basis d) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4, RA]
  have h0right (p : Fin n) :
      Function.update (fun i => basis (slots i)) (0 : Fin 4) (basis p) =
        vec4 (I := I) (basis p) (basis b) (basis c) (basis d) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4]
  have h0core := tensor04At_apply_ricciEnd_slot_orthonormal
    (I := I) g basis horth RicT (S.base.rm04 (t : Real) x) slots (0 : Fin 4)
  rw [h0left] at h0core
  simp_rw [h0right] at h0core
  have h0 :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) RA (basis b) (basis c) (basis d)) =
        ∑ p : Fin n, Ric a p * R p b c d := by
    simpa only [slots, ↓reduceIte, Ric, RicT, R,
      hamiltonRicciComponentOfSolution, hamiltonRmComponentOfSolution, g] using h0core
  have h1left :
      Function.update (fun i => basis (slots i)) (1 : Fin 4)
          (ricciEndAt (I := I) g RicT (basis (slots 1))) =
        vec4 (I := I) (basis a) RB (basis c) (basis d) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4, RB]
  have h1right (p : Fin n) :
      Function.update (fun i => basis (slots i)) (1 : Fin 4) (basis p) =
        vec4 (I := I) (basis a) (basis p) (basis c) (basis d) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4]
  have h1core := tensor04At_apply_ricciEnd_slot_orthonormal
    (I := I) g basis horth RicT (S.base.rm04 (t : Real) x) slots (1 : Fin 4)
  rw [h1left] at h1core
  simp_rw [h1right] at h1core
  have hslots1 : slots (1 : Fin 4) = b := by simp [slots]
  rw [hslots1] at h1core
  have h1 :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) RB (basis c) (basis d)) =
        ∑ p : Fin n, Ric b p * R a p c d := by
    simpa only [Ric, RicT, R,
      hamiltonRicciComponentOfSolution, hamiltonRmComponentOfSolution, g] using h1core
  have h2left :
      Function.update (fun i => basis (slots i)) (2 : Fin 4)
          (ricciEndAt (I := I) g RicT (basis (slots 2))) =
        vec4 (I := I) (basis a) (basis b) RC (basis d) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4, RC]
  have h2right (p : Fin n) :
      Function.update (fun i => basis (slots i)) (2 : Fin 4) (basis p) =
        vec4 (I := I) (basis a) (basis b) (basis p) (basis d) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4]
  have h2core := tensor04At_apply_ricciEnd_slot_orthonormal
    (I := I) g basis horth RicT (S.base.rm04 (t : Real) x) slots (2 : Fin 4)
  rw [h2left] at h2core
  simp_rw [h2right] at h2core
  have hslots2 : slots (2 : Fin 4) = c := by simp [slots]
  rw [hslots2] at h2core
  have h2 :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) RC (basis d)) =
        ∑ p : Fin n, Ric c p * R a b p d := by
    simpa only [Ric, RicT, R,
      hamiltonRicciComponentOfSolution, hamiltonRmComponentOfSolution, g] using h2core
  have h3left :
      Function.update (fun i => basis (slots i)) (3 : Fin 4)
          (ricciEndAt (I := I) g RicT (basis (slots 3))) =
        vec4 (I := I) (basis a) (basis b) (basis c) RD := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4, RD]
  have h3right (p : Fin n) :
      Function.update (fun i => basis (slots i)) (3 : Fin 4) (basis p) =
        vec4 (I := I) (basis a) (basis b) (basis c) (basis p) := by
    funext q
    fin_cases q <;> simp [slots, Function.update, vec4]
  have h3core := tensor04At_apply_ricciEnd_slot_orthonormal
    (I := I) g basis horth RicT (S.base.rm04 (t : Real) x) slots (3 : Fin 4)
  rw [h3left] at h3core
  simp_rw [h3right] at h3core
  have hslots3 : slots (3 : Fin 4) = d := by simp [slots]
  rw [hslots3] at h3core
  have h3 :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) RD) =
        ∑ p : Fin n, Ric d p * R a b c p := by
    simpa only [Ric, RicT, R,
      hamiltonRicciComponentOfSolution, hamiltonRmComponentOfSolution, g] using h3core
  have hRm := hamilton_rm_components_symm_of_solution
    (I := I) S t x basis
  have hTrace := hamilton_curvature_ricci_trace_components_of_solution
    (I := I) S t x basis horth
  have hreaction := hamiltonRmReact_add_ricci_slot_actions
    R Ric hRm hTrace a b c d
  have hderiv :
      (tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin n))
            (nablaKRm04Field (I := I) S (t : Real) 2 x))
          (fun i => basis i) slots +
        DifferentialGeometry.Geometry.Connection.hamiltonRmReact
          (fun q : Fin 4 -> Fin n =>
            S.base.rm04 (t : Real) x (fun p => basis (q p))) slots +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) RA (basis b) (basis c) (basis d)) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) RB (basis c) (basis d)) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) RC (basis d)) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) RD)) =
        hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) +
        hamiltonRmReactionComponent R a b c d := by
    rw [hrough, hRfun, hslotsMatrix, h0, h1, h2, h3]
    linear_combination hreaction
  refine (hmove.congr_deriv hderiv).congr ?_ ?_
  · intro s _
    simp only [oneTimeUhlenbeckVector, g, RicT, RA, RB, RC, RD]
  · simp only [oneTimeUhlenbeckVector, g, RicT, RA, RB, RC, RD]

private theorem rm04_hasDerivWithinAt_oneTimeUhlenbeck_external
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a c d b : Fin n) :
    HasDerivWithinAt
      (fun s : Real => S.base.rm04 s x
        (vec4 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
          (basis c) (basis d)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      (hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
          (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) +
        DifferentialGeometry.Geometry.Connection.hamiltonRmReact
          (fun q : Fin 4 -> Fin n =>
            S.base.rm04 (t : Real) x (fun p => basis (q p))) ![a, c, d, b] +
        S.base.rm04 (t : Real) x
          (vec4 (I := I)
            (ricciEndAt (I := I) (S.base.metric (t : Real))
              (metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x)
              (basis a))
            (basis c) (basis d) (basis b)) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis c) (basis d)
            (ricciEndAt (I := I) (S.base.metric (t : Real))
              (metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x)
              (basis b))))
      D.carrier (t : Real) := by
  classical
  let g := S.base.metric (t : Real)
  let RicT := metricRicci (I := I) (M := M) g x
  let slots : Fin 4 -> Fin n := ![a, c, d, b]
  let RA := ricciEndAt (I := I) g RicT (basis a)
  let RB := ricciEndAt (I := I) g RicT (basis b)
  have hslots : (fun q => basis (slots q)) =
      vec4 (I := I) (basis a) (basis c) (basis d) (basis b) := by
    funext q
    fin_cases q <;> rfl
  have hbase := rm04Base_of_solution_any
    (I := I) S hS t x basis horth slots
  rw [hslots] at hbase
  have hdiff (A B C D : TangentSpace I x) :=
    rm04Base_differentiableWithinAt_of_solution
      (I := I) S hS t x basis horth (vec4 (I := I) A B C D)
  have hmove := tensor04At_hasDerivWithinAt_affine_slots
    (I := I) (fun s : Real => S.base.rm04 s x)
    (tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (nablaKRm04Field (I := I) S (t : Real) 2 x))
        (fun i => basis i) slots +
      DifferentialGeometry.Geometry.Connection.hamiltonRmReact
        (fun q : Fin 4 -> Fin n =>
          S.base.rm04 (t : Real) x (fun p => basis (q p))) slots)
    (basis a) (basis c) (basis d) (basis b) RA 0 0 RB hbase hdiff
  have hrough := hamiltonRmRoughLaplacianField_eq_component_orthonormal
    (I := I) S (t : Real) basis horth slots
  rw [hslots] at hrough
  have hzero1 :
      S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) 0 (basis d) (basis b)) = 0 := by
    have hvec :
        vec4 (I := I) (basis a) 0 (basis d) (basis b) =
          Function.update
            (vec4 (I := I) (basis a) (basis c) (basis d) (basis b))
            (1 : Fin 4) 0 := by
      funext q
      fin_cases q <;> rfl
    rw [hvec]
    exact (S.base.rm04 (t : Real) x).map_update_zero _ (1 : Fin 4)
  have hzero2 :
      S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis c) 0 (basis b)) = 0 := by
    have hvec :
        vec4 (I := I) (basis a) (basis c) 0 (basis b) =
          Function.update
            (vec4 (I := I) (basis a) (basis c) (basis d) (basis b))
            (2 : Fin 4) 0 := by
      funext q
      fin_cases q <;> rfl
    rw [hvec]
    exact (S.base.rm04 (t : Real) x).map_update_zero _ (2 : Fin 4)
  refine (hmove.congr_deriv ?_).congr ?_ ?_
  · rw [hrough]
    rw [hzero1, hzero2]
    simp [slots, RA, RB, g, RicT]
  · intro s _
    simp [oneTimeUhlenbeckVector, g, RicT, RA, RB]
  · simp [oneTimeUhlenbeckVector, g, RicT, RA, RB]

private noncomputable def oneTimeUhlenbeckCurvatureRicciComponent
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (a b : Fin n) (s : Real) : Real :=
  ∑ c : Fin n, ∑ d : Fin n,
    S.base.rm04 s x
        (vec4 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric t) t s (basis a))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric t) t s (basis c))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric t) t s (basis d))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric t) t s (basis b))) *
      metricRicci (I := I) (M := M) (S.base.metric s) x
        (vec2 (I := I)
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric t) t s (basis c))
          (oneTimeUhlenbeckVector
            (I := I) (S.base.metric t) t s (basis d)))

private theorem oneTimeUhlenbeckCurvatureRicciComponent_hasDerivWithinAt
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    HasDerivWithinAt
      (oneTimeUhlenbeckCurvatureRicciComponent
        (I := I) S (t : Real) x basis a b)
      (∑ c : Fin n, ∑ d : Fin n,
        ((hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
              (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) +
            hamiltonRmReactionComponent
              (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
              a c d b) *
          hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis c d +
        hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis a c d b *
          (metricTraceFirstTwoField (I := I) (M := M)
                (S.base.metric (t : Real))
                (metricNabla2Ric (I := I) (M := M)
                  (S.base.metric (t : Real))) x
              (vec2 (I := I) (basis c) (basis d)) +
            hamiltonRicciReactionComponent
              (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
              (hamiltonRicciComponentOfSolution
                (I := I) S (t : Real) x basis) c d)))
      D.carrier (t : Real) := by
  classical
  unfold oneTimeUhlenbeckCurvatureRicciComponent
  refine HasDerivWithinAt.fun_sum ?_
  intro c _
  refine HasDerivWithinAt.fun_sum ?_
  intro d _
  have hRm := rm04_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS t x basis horth a c d b
  have hRic := metricRicci_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS t x basis horth c d
  refine (hRm.mul hRic).congr_deriv ?_
  simp only [oneTimeUhlenbeckVector, sub_self, zero_smul, add_zero]
  rfl

private theorem hamiltonCurvatureRicciAt_hasDerivWithinAt_oneTimeUhlenbeck_raw
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
    let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
    let rawRmDt := fun c d =>
      hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
          (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) +
        DifferentialGeometry.Geometry.Connection.hamiltonRmReact
          (fun q : Fin 4 -> Fin n =>
            S.base.rm04 (t : Real) x (fun p => basis (q p))) ![a, c, d, b] +
        S.base.rm04 (t : Real) x
          (vec4 (I := I)
            (ricciEndAt (I := I) (S.base.metric (t : Real))
              (metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x)
              (basis a))
            (basis c) (basis d) (basis b)) +
        S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis c) (basis d)
            (ricciEndAt (I := I) (S.base.metric (t : Real))
              (metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x)
              (basis b)))
    let ricDt := fun c d =>
      metricRicciTimeDerivativeField (I := I) (S.base.metric (t : Real)) x
        (vec2 (I := I) (basis c) (basis d))
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonCurvatureRicciAt (I := I) (S.base.metric s) x
          (vec2 (I := I)
            (oneTimeUhlenbeckVector
              (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
            (oneTimeUhlenbeckVector
              (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      ((∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          2 * Ric i j * R a k i b * Ric k j) +
        (∑ i : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          2 * Ric k l * R a k i b * Ric l i) +
        ∑ c : Fin n, ∑ d : Fin n,
          (rawRmDt c d * Ric c d + R a c d b * ricDt c d))
      D.carrier (t : Real) := by
  classical
  dsimp only
  let g := S.base.metric (t : Real)
  let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
  let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
  let rawRmDt := fun c d =>
    hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
        (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) +
      DifferentialGeometry.Geometry.Connection.hamiltonRmReact
        (fun q : Fin 4 -> Fin n =>
          S.base.rm04 (t : Real) x (fun p => basis (q p))) ![a, c, d, b] +
      S.base.rm04 (t : Real) x
        (vec4 (I := I)
          (ricciEndAt (I := I) g
            (metricRicci (I := I) (M := M) g x) (basis a))
          (basis c) (basis d) (basis b)) +
      S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis c) (basis d)
          (ricciEndAt (I := I) g
            (metricRicci (I := I) (M := M) g x) (basis b)))
  let ricDt := fun c d =>
    metricRicciTimeDerivativeField (I := I) g x
      (vec2 (I := I) (basis c) (basis d))
  let gInv := fun s : Real =>
    basisInvMetric (I := I) (S.base.metric s) x basis
  let A := fun s : Real =>
    oneTimeUhlenbeckVector (I := I) g (t : Real) s (basis a)
  let B := fun s : Real =>
    oneTimeUhlenbeckVector (I := I) g (t : Real) s (basis b)
  let Rm := fun s c d =>
    S.base.rm04 s x (vec4 (I := I) (A s) (basis c) (basis d) (B s))
  let Ricci := fun s c d =>
    metricRicci (I := I) (M := M) (S.base.metric s) x
      (vec2 (I := I) (basis c) (basis d))
  have hinv (s : Real) : MetricInverseInBasisGen
      (I := I) (M := M) (S.base.metric s) x basis (gInv s) := by
    simpa only [gInv] using
      basisInvMetric_real (I := I) (S.base.metric s) x basis
  have hdeltaFun : gInv (t : Real) = identityInvMetric (Idx := Fin n) := by
    exact invBasis_unique (I := I) (S.base.metric (t : Real)) x basis _ _
      (hinv (t : Real))
      (metricInverseInBasis_identity_of_orthonormal
        (I := I) (S.base.metric (t : Real)) basis horth)
  have hdelta (i j : Fin n) :
      gInv (t : Real) i j = if i = j then (1 : Real) else 0 := by
    rw [hdeltaFun]
    rfl
  have hInv (i j : Fin n) :
      HasDerivWithinAt (fun s : Real => gInv s i j) (2 * Ric i j)
        D.carrier (t : Real) := by
    have h := basisInvMetric_hasDerivWithinAt_of_solution
      (I := I) S hS t x basis i j
    have h' : HasDerivWithinAt (fun s : Real => gInv s i j)
        (2 * (∑ p : Fin n, ∑ q : Fin n,
          gInv (t : Real) i p * gInv (t : Real) j q * Ric p q))
        D.carrier (t : Real) := by
      simpa only [gInv, Ric, hamiltonRicciComponentOfSolution] using h
    refine h'.congr_deriv ?_
    simp [hdelta]
  have hRm (c d : Fin n) :
      HasDerivWithinAt (fun s : Real => Rm s c d) (rawRmDt c d)
        D.carrier (t : Real) := by
    simpa only [Rm, A, B, rawRmDt, g] using
      rm04_hasDerivWithinAt_oneTimeUhlenbeck_external
        (I := I) S hS t x basis horth a c d b
  have hRic (c d : Fin n) :
      HasDerivWithinAt (fun s : Real => Ricci s c d) (ricDt c d)
        D.carrier (t : Real) := by
    simpa [Ricci, ricDt, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci, SolutionFamily.metric, g] using
      metricRicciTimeDerivativeField_hasDerivWithinAt_of_solution
        (I := I) S hS t x (basis c) (basis d)
  have hRmAt (c d : Fin n) : Rm (t : Real) c d = R a c d b := by
    simp [Rm, A, B, R, oneTimeUhlenbeckVector,
      hamiltonRmComponentOfSolution]
  have hRicAt (c d : Fin n) : Ricci (t : Real) c d = Ric c d := by
    simp [Ricci, Ric, hamiltonRicciComponentOfSolution]
  have hinner (i j : Fin n) :=
    HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset (Fin n)))
      (fun k _ => HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset (Fin n)))
        (fun l _ => (hInv k l).mul ((hRm k i).mul (hRic l j))))
  have hraw :=
    HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset (Fin n)))
      (fun i _ => HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset (Fin n)))
        (fun j _ => (hInv i j).mul (hinner i j)))
  refine (hraw.congr_deriv ?_).congr ?_ ?_
  · have hRawRmSwap :
        (∑ d : Fin n, ∑ c : Fin n, rawRmDt c d * Ric c d) =
          ∑ c : Fin n, ∑ d : Fin n, rawRmDt c d * Ric c d :=
      Finset.sum_comm
    have hRicDtSwap :
        (∑ d : Fin n, ∑ c : Fin n, R a c d b * ricDt c d) =
          ∑ c : Fin n, ∑ d : Fin n, R a c d b * ricDt c d :=
      Finset.sum_comm
    change _ =
      ((∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          2 * Ric i j * R a k i b * Ric k j) +
        (∑ i : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          2 * Ric k l * R a k i b * Ric l i) +
        ∑ c : Fin n, ∑ d : Fin n,
          (rawRmDt c d * Ric c d + R a c d b * ricDt c d))
    simp only [hdelta, hRmAt, hRicAt, Pi.mul_apply, ite_mul,
      one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    rw [hRawRmSwap, hRicDtSwap]
    ring_nf
  · intro s _hs
    simpa only [gInv, Rm, Ricci, A, B, g, SolutionFamily.rm04,
      Pi.mul_apply] using
      (hamiltonCurvatureRicciAt_apply
        (I := I) (S.base.metric s) basis (gInv s) (hinv s) (A s) (B s))
  · simpa only [gInv, Rm, Ricci, A, B, g, SolutionFamily.rm04,
      Pi.mul_apply] using
      (hamiltonCurvatureRicciAt_apply
        (I := I) (S.base.metric (t : Real)) basis (gInv (t : Real))
          (hinv (t : Real)) (A (t : Real)) (B (t : Real)))

private theorem hamiltonCurvatureRicciAt_hasDerivWithinAt_oneTimeUhlenbeck_heat
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
    let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonCurvatureRicciAt (I := I) (S.base.metric s) x
          (vec2 (I := I)
            (oneTimeUhlenbeckVector
              (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
            (oneTimeUhlenbeckVector
              (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      (∑ c : Fin n, ∑ d : Fin n,
        ((hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
              (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) +
            hamiltonRmReactionComponent R a c d b) * Ric c d +
          R a c d b *
            (metricTraceFirstTwoField (I := I) (M := M)
                  (S.base.metric (t : Real))
                  (metricNabla2Ric (I := I) (M := M)
                    (S.base.metric (t : Real))) x
                (vec2 (I := I) (basis c) (basis d)) +
              hamiltonRicciReactionComponent R Ric c d)))
      D.carrier (t : Real) := by
  classical
  dsimp only
  let g := S.base.metric (t : Real)
  let RicT := metricRicci (I := I) (M := M) g x
  let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
  let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
  let lapRm := fun c d =>
    hamiltonRmRoughLaplacianField (I := I) S (t : Real) x
      (vec4 (I := I) (basis a) (basis c) (basis d) (basis b))
  let lapRic := fun c d =>
    metricTraceFirstTwoField (I := I) (M := M) g
      (metricNabla2Ric (I := I) (M := M) g) x
        (vec2 (I := I) (basis c) (basis d))
  let rawRmDt := fun c d =>
    lapRm c d +
      DifferentialGeometry.Geometry.Connection.hamiltonRmReact
        (fun q : Fin 4 -> Fin n =>
          S.base.rm04 (t : Real) x (fun p => basis (q p))) ![a, c, d, b] +
      S.base.rm04 (t : Real) x
        (vec4 (I := I)
          (ricciEndAt (I := I) g RicT (basis a))
          (basis c) (basis d) (basis b)) +
      S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis c) (basis d)
          (ricciEndAt (I := I) g RicT (basis b)))
  let ricDt := fun c d =>
    metricRicciTimeDerivativeField (I := I) g x
      (vec2 (I := I) (basis c) (basis d))
  have hRaw := hamiltonCurvatureRicciAt_hasDerivWithinAt_oneTimeUhlenbeck_raw
    (I := I) S hS t x basis horth a b
  dsimp only at hRaw
  refine hRaw.congr_deriv ?_
  have hRicSymm (i j : Fin n) : Ric i j = Ric j i := by
    change metricRicci (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis j)) =
      metricRicci (I := I) (M := M) g x
        (vec2 (I := I) (basis j) (basis i))
    exact metricRicciAt_symm (I := I) (M := M) g x (basis i) (basis j)
  have hRmSymm := hamilton_rm_components_symm_of_solution
    (I := I) S t x basis
  have hTrace := hamilton_curvature_ricci_trace_components_of_solution
    (I := I) S t x basis horth
  have hRfun :
      (fun q : Fin 4 -> Fin n =>
        S.base.rm04 (t : Real) x (fun p => basis (q p))) =
        fun q => R (q 0) (q 1) (q 2) (q 3) := by
    funext q
    apply congrArg (S.base.rm04 (t : Real) x)
    funext p
    fin_cases p <;> rfl
  have hExtFirst (c d : Fin n) :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (ricciEndAt (I := I) g RicT (basis a))
            (basis c) (basis d) (basis b)) =
        ∑ p : Fin n, Ric a p * R p c d b := by
    let slots : Fin 4 -> Fin n := ![a, c, d, b]
    have hcore := tensor04At_apply_ricciEnd_slot_orthonormal
      (I := I) g basis horth RicT (S.base.rm04 (t : Real) x) slots (0 : Fin 4)
    have hleft :
        Function.update (fun i => basis (slots i)) (0 : Fin 4)
            (ricciEndAt (I := I) g RicT (basis (slots 0))) =
          vec4 (I := I) (ricciEndAt (I := I) g RicT (basis a))
            (basis c) (basis d) (basis b) := by
      funext q
      fin_cases q <;> simp [slots, Function.update, vec4]
    have hright (p : Fin n) :
        Function.update (fun i => basis (slots i)) (0 : Fin 4) (basis p) =
          vec4 (I := I) (basis p) (basis c) (basis d) (basis b) := by
      funext q
      fin_cases q <;> simp [slots, Function.update, vec4]
    rw [hleft] at hcore
    simp_rw [hright] at hcore
    have hslots0 : slots (0 : Fin 4) = a := by simp [slots]
    rw [hslots0] at hcore
    simpa only [slots, ↓reduceIte, Ric, RicT, R,
      hamiltonRicciComponentOfSolution, hamiltonRmComponentOfSolution, g] using hcore
  have hExtFourth (c d : Fin n) :
      S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis a) (basis c) (basis d)
            (ricciEndAt (I := I) g RicT (basis b))) =
        ∑ p : Fin n, Ric b p * R a c d p := by
    let slots : Fin 4 -> Fin n := ![a, c, d, b]
    have hcore := tensor04At_apply_ricciEnd_slot_orthonormal
      (I := I) g basis horth RicT (S.base.rm04 (t : Real) x) slots (3 : Fin 4)
    have hleft :
        Function.update (fun i => basis (slots i)) (3 : Fin 4)
            (ricciEndAt (I := I) g RicT (basis (slots 3))) =
          vec4 (I := I) (basis a) (basis c) (basis d)
            (ricciEndAt (I := I) g RicT (basis b)) := by
      funext q
      fin_cases q <;> simp [slots, Function.update, vec4]
    have hright (p : Fin n) :
        Function.update (fun i => basis (slots i)) (3 : Fin 4) (basis p) =
          vec4 (I := I) (basis a) (basis c) (basis d) (basis p) := by
      funext q
      fin_cases q <;> simp [slots, Function.update, vec4]
    rw [hleft] at hcore
    simp_rw [hright] at hcore
    have hslots3 : slots (3 : Fin 4) = b := by simp [slots]
    rw [hslots3] at hcore
    simpa only [slots, ↓reduceIte, Ric, RicT, R,
      hamiltonRicciComponentOfSolution, hamiltonRmComponentOfSolution, g] using hcore
  have hRmHeat (c d : Fin n) :
      rawRmDt c d +
          ((∑ p : Fin n, Ric c p * R a p d b) +
            ∑ p : Fin n, Ric d p * R a c p b) =
        lapRm c d + hamiltonRmReactionComponent R a c d b := by
    have hreaction := hamiltonRmReact_add_ricci_slot_actions
      R Ric hRmSymm hTrace a c d b
    unfold rawRmDt
    rw [hRfun, hExtFirst c d, hExtFourth c d]
    linear_combination hreaction
  have hRicFirst (c d : Fin n) :
      RicT (vec2 (I := I) (ricciEndAt (I := I) g RicT (basis c)) (basis d)) =
        ∑ p : Fin n, Ric c p * Ric p d := by
    simpa only [Ric, RicT, hamiltonRicciComponentOfSolution, g] using
      tensor02At_apply_ricciEnd_first_orthonormal
        (I := I) g basis horth RicT RicT c d
  have hRicSecond (c d : Fin n) :
      RicT (vec2 (I := I) (basis c) (ricciEndAt (I := I) g RicT (basis d))) =
        ∑ p : Fin n, Ric d p * Ric c p := by
    simpa only [Ric, RicT, hamiltonRicciComponentOfSolution, g] using
      tensor02At_apply_ricciEnd_second_orthonormal
        (I := I) g basis horth RicT RicT c d
  have hRicHeat (c d : Fin n) :
      ricDt c d +
          ((∑ p : Fin n, Ric c p * Ric p d) +
            ∑ p : Fin n, Ric d p * Ric c p) =
        lapRic c d + hamiltonRicciReactionComponent R Ric c d := by
    have hheat := metricRicciTimeDerivativeField_add_ricciEnd_eq_heat_of_orthonormal
      (I := I) g basis (by simpa only [g] using horth) c d
    rw [hRicFirst c d, hRicSecond c d] at hheat
    change ricDt c d + (∑ p : Fin n, Ric c p * Ric p d) +
          (∑ p : Fin n, Ric d p * Ric c p) =
        lapRic c d + hamiltonRicciReactionComponent R Ric c d at hheat
    linear_combination hheat
  have hDrift := inverse_metric_double_trace_drift R Ric hRicSymm a b
  have hDrift' :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          2 * Ric i j * R a k i b * Ric k j) +
        (∑ i : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          2 * Ric k l * R a k i b * Ric l i) =
      ∑ c : Fin n, ∑ d : Fin n,
        (((∑ p : Fin n, Ric c p * R a p d b) +
              ∑ p : Fin n, Ric d p * R a c p b) * Ric c d +
          R a c d b *
            ((∑ p : Fin n, Ric c p * Ric p d) +
              ∑ p : Fin n, Ric d p * Ric c p)) := by
    simpa only [Finset.mul_sum, mul_assoc] using hDrift
  rw [hDrift']
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← hRmHeat c d, ← hRicHeat c d]
  ring

private theorem hamilton_ricci_components_symm_of_solution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    forall i j,
      hamiltonRicciComponentOfSolution (I := I) S t x basis i j =
        hamiltonRicciComponentOfSolution (I := I) S t x basis j i := by
  intro i j
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (S.base.metric t) basis horth
  simpa [hamiltonRicciComponentOfSolution] using
    (metricRicciSymm (I := I) (M := M) (S.base.metric t) basis
      (fun p q => if p = q then (1 : Real) else 0) hinv i j)

private theorem hamilton_nabla_ricci_components_symm_of_solution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    forall i j k,
      hamiltonNablaRicciComponentOfSolution (I := I) S t x basis i j k =
        hamiltonNablaRicciComponentOfSolution (I := I) S t x basis i k j := by
  intro i j k
  simpa [hamiltonNablaRicciComponentOfSolution] using
    (metricNablaRic_last_two_symm (I := I) (M := M) (S.base.metric t) x
      (basis i) (basis j) (basis k))

private theorem hamilton_raw_ricci_reaction_derivative_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    forall i j k,
      hamiltonNablaRicciTimeComponentOfSolution (I := I) S t x basis i j k -
          covariantDerivativeRoughLaplacianComponents
            (fun e f d (slots : Fin 2 -> Fin n) =>
              hamiltonNabla3RicciComponentOfSolution
                (I := I) S t x basis e f d (slots 0) (slots 1)) i
            (fun q : Fin 2 => if q = 0 then j else k) =
        hamiltonNablaRawRicciReactionComponent
          (hamiltonRmComponentOfSolution (I := I) S t x basis)
          (hamiltonNablaRmComponentOfSolution (I := I) S t x basis)
          (hamiltonRicciComponentOfSolution (I := I) S t x basis)
          (hamiltonNablaRicciComponentOfSolution (I := I) S t x basis) i j k := by
  intro i j k
  have hD3 :
      (fun e f d (slots : Fin 2 -> Fin n) =>
          hamiltonNabla3RicciComponentOfSolution
            (I := I) S t x basis e f d (slots 0) (slots 1)) =
        (fun e f d (slots : Fin 2 -> Fin n) =>
          metricNabla3RicField (I := I) (S.base.metric t) x
            (Fin.cons (basis e)
              (Fin.cons (basis f)
                (Fin.cons (basis d) (fun r => basis (slots r)))))) := by
    funext e f d slots
    simp only [hamiltonNabla3RicciComponentOfSolution]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hD3]
  change
    metricNablaRicciTimeDerivativeField (I := I) (S.base.metric t) x
          (vec3 (I := I) (basis i) (basis j) (basis k)) -
        covariantDerivativeRoughLaplacianComponents
          (fun e f d (slots : Fin 2 -> Fin n) =>
            metricNabla3RicField (I := I) (S.base.metric t) x
              (Fin.cons (basis e)
                (Fin.cons (basis f)
                  (Fin.cons (basis d) (fun r => basis (slots r))))))
          i (fun q : Fin 2 => if q = 0 then j else k) =
      hamiltonNablaRawRicciReactionComponent
        (fun p q r s => S.base.rm04 t x
          (vec4 (I := I) (basis p) (basis q) (basis r) (basis s)))
        (fun p q r s u => nablaRm04Field (I := I) S t x
          (vec5 (I := I) (basis p) (basis q) (basis r) (basis s) (basis u)))
        (fun p q => metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 (I := I) (basis p) (basis q)))
        (fun p q r => metricNablaRic (I := I) (M := M) (S.base.metric t) x
          (vec3 (I := I) (basis p) (basis q) (basis r))) i j k
  exact hamiltonNablaRawRicciReactionComponent_of_solution
    (I := I) S t x basis horth i j k

private theorem hamiltonP_evolution_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPHeatComponent
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciTimeComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNabla3RicciComponentOfSolution (I := I) S (t : Real) x basis)
        a b c =
      hamiltonPEvolutionReactionComponent
        (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        a b c := by
  have hcore := hamilton_bianchi_trace_components_of_solution
    (I := I) S (t : Real) x basis horth
  exact hamiltonP_evolution
    (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRicciTimeComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNabla3RicciComponentOfSolution (I := I) S (t : Real) x basis)
    (hamilton_differentiated_ricci_identity_components_of_solution
      (I := I) S t x basis horth)
    (hamilton_gradient_ricci_identity_components_of_solution
      (I := I) S t x basis horth)
    (hamilton_contracted_curvature_derivative_components_of_solution
      (I := I) S (t : Real) x basis horth)
    (hamilton_rm_components_symm_of_solution (I := I) S t x basis).swap12
    (hamilton_rm_components_symm_of_solution (I := I) S t x basis).swap34
    (hamilton_rm_components_symm_of_solution (I := I) S t x basis).pair
    (hamilton_curvature_ricci_trace_components_of_solution
      (I := I) S t x basis horth)
    (fun d i j k l => hcore.2.1.2.1
      (basis d) (basis j) (basis i) (basis k) (basis l))
    (fun i j k l m => hcore.1
      (basis i) (basis j) (basis k) (basis l) (basis m))
    (hamilton_ricci_components_symm_of_solution
      (I := I) S (t : Real) x basis horth)
    (hamilton_nabla_ricci_components_symm_of_solution
      (I := I) S (t : Real) x basis)
    (hamilton_raw_ricci_reaction_derivative_components_of_solution
      (I := I) S (t : Real) x basis horth) a b c

theorem hamiltonP_evolution_of_ricci_flow
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPHeatComponent
        (fun i j => metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k => metricNablaRicciTimeDerivativeField
          (I := I) (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l m => metricNabla3RicField
          (I := I) (S.base.metric (t : Real)) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        a b c =
      hamiltonPEvolutionReactionComponent
        (fun i j k l => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        a b c := by
  change hamiltonPHeatComponent
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciTimeComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNabla3RicciComponentOfSolution (I := I) S (t : Real) x basis)
      a b c =
    hamiltonPEvolutionReactionComponent
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
      a b c
  exact hamiltonP_evolution_components_of_solution
    (I := I) S t x basis horth a b c

theorem hamiltonP_time_derivative_component_eq_field
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPTimeDerivativeComponent
        (fun i j => metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k => metricNablaRicciTimeDerivativeField
          (I := I) (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b c =
      hamiltonPTimeDerivativeField (I := I) (S.base.metric (t : Real)) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) := by
  rw [hamiltonPTimeDerivativeField_apply_orthonormal
    (I := I) (S.base.metric (t : Real)) basis horth a b c]
  unfold hamiltonPTimeDerivativeComponent
  simp only [ricciFlowConnectionVariationOrthonormal]
  simp_rw [ricciFlowConnectionVariationField_apply]

private theorem hamiltonNabla2PExpectedField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 (metricCov (I := I) (M := M) g)
        (hamiltonNabla2PExpectedField (I := I) g) =
      hamiltonNabla3PField (I := I) g := by
  unfold hamiltonNabla3PField
  rw [← hamiltonNabla2PField_eq_expected (I := I) g]
  funext x
  rfl

private theorem ricciPContractionField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 5)) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (ricciPContractionField (I := I) g perm) =
      metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (traceNablaShuffle 3)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
            (frontExtendEquiv perm)
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
              (leibnizLeftEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricNablaRic (I := I) (M := M) g)
                (hamiltonPField (I := I) g)) +
            Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
              (leibnizRightEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricRicci (I := I) (M := M) g)
                (hamiltonNablaPField (I := I) g))))) := by
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let P := hamiltonPField (I := I) g
  let RicNabla := metricNablaRic (I := I) (M := M) g
  let PNabla := hamiltonNablaPField (I := I) g
  have hRic : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric RicNabla := by
    simpa [cov, Ric, RicNabla, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Ric))
  have hP : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov P PNabla := by
    simpa [cov, P, PNabla, hamiltonNablaPField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov P
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) P))
  have hProd := nabla0S_product_realizes (I := I) cov Ric P RicNabla PNabla hRic hP
  have hProd' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric P)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 3)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) RicNabla P) +
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 3)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric PNabla)) := by
    simpa [Ric, P, RicNabla, PNabla] using hProd
  have hPerm := totalNabla0SRealizes_domDomCongr (I := I) cov perm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric P)
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 3)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) RicNabla P) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric PNabla)) hProd'
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hTrace := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 3) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric P))
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendEquiv perm)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RicNabla P) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric PNabla))) (by
      simpa only [Nat.reduceAdd] using hPerm)
  have hUnique := totalNabla0SRealizes_unique
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov
      (ricciPContractionField (I := I) g perm)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        3 cov (metricCov_smooth (I := I) (M := M) g)
        (ricciPContractionField (I := I) g perm)))
    (by simpa [ricciPContractionField, cov, Ric, P, RicNabla, PNabla] using hTrace)
  funext x
  simpa [totalNabla0S_apply, Nat.reduceAdd, ricciPContractionField,
    cov, Ric, P, RicNabla, PNabla] using congrArg
    (fun A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4 => A x) hUnique

private theorem metricTraceFirstTwoField_nabla_eq
    [T2Space M]
    {s : Nat}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (ANabla : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 2) (metricCov (I := I) (M := M) g) A ANabla) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s (metricCov (I := I) (M := M) g)
        (metricTraceFirstTwoField (I := I) (M := M) g A) =
      metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (traceNablaShuffle s) ANabla) := by
  let cov := metricCov (I := I) (M := M) g
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hTrace := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := s) cov g hmc A ANabla (by simpa [cov] using hA)
  have hUnique := totalNabla0SRealizes_unique
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov
      (metricTraceFirstTwoField (I := I) (M := M) g A)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        s cov (metricCov_smooth (I := I) (M := M) g)
        (metricTraceFirstTwoField (I := I) (M := M) g A))) hTrace
  funext x
  simpa [totalNabla0S_apply, cov] using congrArg
    (fun B : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) => B x) hUnique

private theorem hamiltonPRoughLaplacianField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (hamiltonPRoughLaplacianField (I := I) g) =
      metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (traceNablaShuffle 3) (hamiltonNabla3PField (I := I) g)) := by
  let cov := metricCov (I := I) (M := M) g
  have hCanonical := totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) 5 cov (hamiltonNabla2PExpectedField (I := I) g)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g)
      (hamiltonNabla2PExpectedField (I := I) g))
  have hExpected : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 cov (hamiltonNabla2PExpectedField (I := I) g)
      (hamiltonNabla3PField (I := I) g) := by
    intro X x slots
    have h := hCanonical X x slots
    simp only [totalNabla0S_apply] at h
    rw [hamiltonNabla2PExpectedField_nabla_eq (I := I) g] at h
    exact h
  rw [hamiltonPRoughLaplacianField, hamiltonNabla2PField_eq_expected (I := I) g]
  exact metricTraceFirstTwoField_nabla_eq (I := I) g
    (hamiltonNabla2PExpectedField (I := I) g)
    (hamiltonNabla3PField (I := I) g) (by simpa [cov] using hExpected)

private theorem ricciPFirstContractionField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (ricciPContractionField (I := I) g ricciPFirstFieldPerm) =
      nablaRicPContractionField (I := I) g nablaRicPFirstFieldPerm +
        ricciNablaPContractionField (I := I) g ricciNablaPFirstFieldPerm := by
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  rw [congrFun (ricciPContractionField_nabla_eq
    (I := I) g ricciPFirstFieldPerm) x]
  simp only [Pi.add_apply, Tensor0SSpace.add_apply]
  rw [nablaRicPFirstField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPFirstField_apply_orthonormal (I := I) g basis horth]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  have hTerm (p : Fin (Module.finrank Real (TangentSpace I x))) :
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 3)
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (frontExtendEquiv ricciPFirstFieldPerm)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricNablaRic (I := I) (M := M) g) (hamiltonPField (I := I) g)) +
            Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricRicci (I := I) (M := M) g)
                (hamiltonNablaPField (I := I) g))))) x
          (metricTraceInput (I := I) (basis p) (basis p)
            (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
              (basis (slots 2)) (basis (slots 3)))) =
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis (slots 0)) (basis (slots 1)) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis p) (basis (slots 2)) (basis (slots 3))) +
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis (slots 1)) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis (slots 0)) (basis p)
              (basis (slots 2)) (basis (slots 3))) := by
    simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
      tensor0SField_product_apply]
    congr 1
    · congr 2
      · funext r
        fin_cases r <;> rfl
      · funext r
        fin_cases r <;> rfl
    · congr 2
      · funext r
        fin_cases r <;> rfl
      · funext r
        fin_cases r <;> rfl
  simp_rw [hTerm, Finset.sum_add_distrib]

private theorem ricciPSecondContractionField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (ricciPContractionField (I := I) g ricciPSecondFieldPerm) =
      nablaRicPContractionField (I := I) g nablaRicPSecondFieldPerm +
        ricciNablaPContractionField (I := I) g ricciNablaPSecondFieldPerm := by
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  rw [congrFun (ricciPContractionField_nabla_eq
    (I := I) g ricciPSecondFieldPerm) x]
  simp only [Pi.add_apply, Tensor0SSpace.add_apply]
  rw [nablaRicPSecondField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPSecondField_apply_orthonormal (I := I) g basis horth]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  have hTerm (p : Fin (Module.finrank Real (TangentSpace I x))) :
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 3)
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (frontExtendEquiv ricciPSecondFieldPerm)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricNablaRic (I := I) (M := M) g) (hamiltonPField (I := I) g)) +
            Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricRicci (I := I) (M := M) g)
                (hamiltonNablaPField (I := I) g))))) x
          (metricTraceInput (I := I) (basis p) (basis p)
            (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
              (basis (slots 2)) (basis (slots 3)))) =
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis (slots 0)) (basis (slots 2)) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis (slots 1)) (basis p) (basis (slots 3))) +
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis (slots 2)) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
              (basis p) (basis (slots 3))) := by
    simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
      tensor0SField_product_apply]
    congr 1
    · congr 2
      · funext r
        fin_cases r <;> rfl
      · funext r
        fin_cases r <;> rfl
    · congr 2
      · funext r
        fin_cases r <;> rfl
      · funext r
        fin_cases r <;> rfl
  simp_rw [hTerm, Finset.sum_add_distrib]

private theorem ricciPThirdContractionField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (ricciPContractionField (I := I) g ricciPThirdFieldPerm) =
      nablaRicPContractionField (I := I) g nablaRicPThirdFieldPerm +
        ricciNablaPContractionField (I := I) g ricciNablaPThirdFieldPerm := by
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  rw [congrFun (ricciPContractionField_nabla_eq
    (I := I) g ricciPThirdFieldPerm) x]
  simp only [Pi.add_apply, Tensor0SSpace.add_apply]
  rw [nablaRicPThirdField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPThirdField_apply_orthonormal (I := I) g basis horth]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  have hTerm (p : Fin (Module.finrank Real (TangentSpace I x))) :
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 3)
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (frontExtendEquiv ricciPThirdFieldPerm)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricNablaRic (I := I) (M := M) g) (hamiltonPField (I := I) g)) +
            Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 3)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞)
                (metricRicci (I := I) (M := M) g)
                (hamiltonNablaPField (I := I) g))))) x
          (metricTraceInput (I := I) (basis p) (basis p)
            (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
              (basis (slots 2)) (basis (slots 3)))) =
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis (slots 0)) (basis (slots 3)) (basis p)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis (slots 1)) (basis (slots 2)) (basis p)) +
        metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis (slots 3)) (basis p)) *
          hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
              (basis (slots 2)) (basis p)) := by
    simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
      ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
      tensor0SField_product_apply]
    congr 1
    · congr 2
      · funext r
        fin_cases r <;> rfl
      · funext r
        fin_cases r <;> rfl
    · congr 2
      · funext r
        fin_cases r <;> rfl
      · funext r
        fin_cases r <;> rfl
  simp_rw [hTerm, Finset.sum_add_distrib]

private theorem ricciPActionField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g) (ricciPActionField (I := I) g) =
      nablaRicPActionField (I := I) g + ricciNablaPActionField (I := I) g := by
  funext x
  rw [ricciPActionField]
  repeat' rw [totalNabla0SFun_add (I := I)]
  rw [congrFun (ricciPFirstContractionField_nabla_eq (I := I) g) x,
    congrFun (ricciPSecondContractionField_nabla_eq (I := I) g) x,
    congrFun (ricciPThirdContractionField_nabla_eq (I := I) g) x]
  rw [nablaRicPActionField, ricciNablaPActionField]
  simp only [ContMDiffSection.coe_add, Pi.add_apply]
  abel

private theorem hamiltonPHeatField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g) (hamiltonPHeatField (I := I) g) =
      hamiltonNablaPTimeDerivativeField (I := I) g +
        nablaRicPActionField (I := I) g + ricciNablaPActionField (I := I) g -
        metricTraceFirstTwoField (I := I) (M := M) g
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
            (traceNablaShuffle 3) (hamiltonNabla3PField (I := I) g)) := by
  funext x
  rw [hamiltonPHeatField, sub_eq_add_neg]
  rw [show -hamiltonPRoughLaplacianField (I := I) g =
      (-1 : Real) • hamiltonPRoughLaplacianField (I := I) g by simp]
  rw [totalNabla0SFun_add (I := I), totalNabla0SFun_add (I := I),
    totalNabla0SFun_smul (I := I)]
  rw [congrFun (ricciPActionField_nabla_eq (I := I) g) x,
    congrFun (hamiltonPRoughLaplacianField_nabla_eq (I := I) g) x]
  simp only [hamiltonNablaPTimeDerivativeField, totalNabla0S_apply,
    Pi.add_apply, Pi.sub_apply, neg_one_smul, sub_eq_add_neg]
  abel

private theorem uhlenbeckNablaHeatPComponent_eq_hamiltonPHeatFieldNabla_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    uhlenbeckNablaHeatPComponent
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l => hamiltonNablaPTimeDerivativeField (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l m r => hamiltonNabla3PField (I := I) g x
          (Fin.cons (basis i)
            (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
        q a b c =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 (metricCov (I := I) (M := M) g) (hamiltonPHeatField (I := I) g) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) := by
  rw [uhlenbeckNablaHeatPComponent,
    congrFun (hamiltonPHeatField_nabla_eq (I := I) g) x]
  simp only [uhlenbeckCovariantDerivativeOfTimeDerivative,
    covariantDerivativeRoughLaplacianComponents,
    Pi.add_apply, Pi.sub_apply, Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply]
  rw [nablaRicPActionField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPActionField_apply_orthonormal (I := I) g basis horth,
    metricTraceFirstTwoField_apply_orthonormal (I := I) g basis horth]
  simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  have hTrace (d : Fin n) :
      (fun i => metricTraceInput (I := I) (basis d) (basis d)
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c))
            (traceNablaShuffle 3 i)) =
        Fin.cons (basis q)
          (vec5 (I := I) (basis d) (basis d) (basis a) (basis b) (basis c)) := by
    funext i
    fin_cases i <;> rfl
  simp_rw [hTrace]
  simp [hamiltonPComponent, Function.update_apply,
    covariantTensorNablaRicciSlotAction, covariantTensorRicciSlotAction]
  simp [Fin.sum_univ_three]

private theorem hamiltonPHeatComponent_eq_hamiltonPHeatField_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPHeatComponent
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k => metricNablaRicciTimeDerivativeField (I := I) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l m => metricNabla3RicField (I := I) g x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m))) a b c =
      hamiltonPHeatField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) := by
  rw [hamiltonPHeatComponent, hamiltonPHeatField_apply_orthonormal
    (I := I) g basis horth]
  simp only [uhlenbeckHeatNablaRicciComponent,
    uhlenbeckTimeDerivativeOfCovariantDerivative,
    roughLaplacianCovariantDerivativeComponents,
    covariantTensorRicciSlotAction]
  rw [hamiltonPTimeDerivativeField_apply_orthonormal (I := I) g basis horth,
    ricciPActionField_apply_orthonormal (I := I) g basis horth,
    hamiltonNabla2PField_eq_expected (I := I) g]
  simp only [hamiltonNabla2PExpectedField, ContMDiffSection.coe_sub, Pi.sub_apply,
    Tensor0SSpace.sub_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply]
  have hConnection (i j k : Fin n) :
      ricciFlowConnectionVariationOrthonormal
          (fun p q r => metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis p) (basis q) (basis r))) i j k =
        ricciFlowConnectionVariationOrthonormal
          (fun p q r => metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis p) (basis q) (basis r))) j i k := by
    unfold ricciFlowConnectionVariationOrthonormal
    change
      -metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis i) (basis j) (basis k)) -
          metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis j) (basis i) (basis k)) +
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis k) (basis i) (basis j)) =
        -metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis j) (basis i) (basis k)) -
          metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis i) (basis j) (basis k)) +
        metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis k) (basis j) (basis i))
    rw [metricNablaRic_last_two_symm (I := I) (M := M) g x
      (basis k) (basis i) (basis j)]
    ring
  have hRic (i j : Fin n) :
      metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)) =
        metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis j) (basis i)) :=
    metricRicciAt_symm (I := I) (M := M) g x (basis i) (basis j)
  have htraceSwap (d : Fin n) :
      (fun i => vec5 (I := I) (basis d) (basis d) (basis a) (basis b) (basis c)
          (frontExtendEquiv (Equiv.swap (1 : Fin 4) 2) i)) =
        vec5 (I := I) (basis d) (basis d) (basis b) (basis a) (basis c) := by
    funext i
    fin_cases i <;> rfl
  simp only [Fin.sum_univ_two, Function.update_apply, Fin.isValue,
    ↓reduceIte, one_ne_zero, zero_ne_one]
  simp_rw [ricciFlowConnectionVariationField_apply,
    hamiltonPField_apply, hamiltonPAt_apply]
  simp_rw [htraceSwap]
  simp_rw [hConnection]
  simp_rw [hRic]
  unfold ricciFlowConnectionVariationOrthonormal
  have hsum_sub (f h : Fin n -> Real) :
      (∑ d, (f d - h d)) = (∑ d, f d) - (∑ d, h d) :=
    Finset.sum_sub_distrib (s := Finset.univ) f h
  ring_nf
  simp_rw [hsum_sub]
  abel

private theorem hamiltonPHeatField_eq_reaction_of_orthonormal
    [CompleteSpace E] [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPHeatField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      hamiltonPEvolutionReactionField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) := by
  let D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ 0
  let S : SolutionOn (I := I) (M := M) D := ⟨⟨fun _ => g⟩⟩
  let t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
    ⟨0, Set.mem_univ 0⟩
  rw [← hamiltonPHeatComponent_eq_hamiltonPHeatField_of_orthonormal
      (I := I) g basis horth a b c,
    hamiltonPEvolutionReactionField_apply_orthonormal (I := I) g basis horth]
  have h := hamiltonP_evolution_components_of_solution
    (I := I) S t x basis horth a b c
  unfold hamiltonRmComponentOfSolution hamiltonRicciComponentOfSolution
    hamiltonNablaRmComponentOfSolution hamiltonNablaRicciComponentOfSolution
    hamiltonNablaRicciTimeComponentOfSolution
    hamiltonNabla3RicciComponentOfSolution at h
  unfold SolutionFamily.rm04 at h
  rw [← metricNablaRm04Field_eq_nablaRm04Field (I := I) S (t : Real)] at h
  simpa [S] using h

private theorem hamiltonPHeatField_eq_reaction
    [CompleteSpace E] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    hamiltonPHeatField (I := I) g =
      hamiltonPEvolutionReactionField (I := I) g := by
  apply DFunLike.ext _ _
  intro x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 3 => basis (slots r)) =
        vec3 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  exact hamiltonPHeatField_eq_reaction_of_orthonormal
    (I := I) g basis horth (slots 0) (slots 1) (slots 2)

private theorem tensor0SAt_apply_ricciEnd_slot_orthonormal
    {s : Nat} {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (Ric : Tensor02At (I := I) (M := M) x)
    (T : Tensor0SSpace s I x) (slots : Fin s -> Idx) (r : Fin s) :
    T (Function.update (fun i => basis (slots i)) r
        (ricciEndAt (I := I) g Ric (basis (slots r)))) =
      ∑ p : Idx,
        Ric (vec2 (I := I) (basis (slots r)) (basis p)) *
          T (Function.update (fun i => basis (slots i)) r (basis p)) := by
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hrepr (p : Idx) :
      basis.repr (ricciEndAt (I := I) g Ric (basis (slots r))) p =
        Ric (vec2 (I := I) (basis (slots r)) (basis p)) := by
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [ricciEnd_inner, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hend :
      ricciEndAt (I := I) g Ric (basis (slots r)) =
        ∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis (slots r))) p • basis p :=
    (basis.sum_repr (ricciEndAt (I := I) g Ric (basis (slots r)))).symm
  rw [hend]
  change T.toMultilinearMap
      (Function.update (fun i => basis (slots i)) r
        (∑ p : Idx,
          basis.repr (ricciEndAt (I := I) g Ric (basis (slots r))) p • basis p)) = _
  rw [MultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MultilinearMap.map_update_smul, hrepr, smul_eq_mul]
  rfl

theorem hamiltonP_fixed_heat_component_of_ricci_flow
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    let g := S.base.metric (t : Real)
    let derivs := CanonicalSpatialDerivs0S.ofSmoothConnection
      (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (hamiltonPField (I := I) g)
    let Ric := metricRicci (I := I) (M := M) g x
    let RicEnd := (ricciEndAt (I := I) g Ric).toContinuousLinearMap
    deriv (fun r : Real => hamiltonPField (I := I)
        (S.base.metric r) x
        (vec3 (I := I) (basis a) (basis b) (basis c))) (t : Real) -
        metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n)) (derivs.nabla2A x)
          (vec3 (I := I) (basis a) (basis b) (basis c)) +
        covariantEndomorphismAction0S (I := I)
          (hamiltonPField (I := I) g x) RicEnd
          (vec3 (I := I) (basis a) (basis b) (basis c)) =
      hamiltonPEvolutionReactionComponent
        (fun i j k l => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b c := by
  classical
  dsimp only
  let g := S.base.metric (t : Real)
  let Ric := metricRicci (I := I) (M := M) g x
  let RicEnd := (ricciEndAt (I := I) g Ric).toContinuousLinearMap
  let slots : Fin 3 -> Fin n := ![a, b, c]
  have hslots : (fun i => basis (slots i)) =
      vec3 (I := I) (basis a) (basis b) (basis c) := by
    funext i
    fin_cases i <;> rfl
  have htimeWithin := hamiltonPAt_hasDerivWithinAt_of_ricci_flow
    (I := I) S hS t x (vec3 (I := I) (basis a) (basis b) (basis c))
  have htimeAt := htimeWithin.hasDerivAt (D.regular_mem_nhds t.2)
  have htime :
      deriv (fun r : Real => hamiltonPField (I := I)
          (S.base.metric r) x
          (vec3 (I := I) (basis a) (basis b) (basis c))) (t : Real) =
        hamiltonPTimeDerivativeField (I := I) g x
          (vec3 (I := I) (basis a) (basis b) (basis c)) := by
    rw [show (fun r : Real => hamiltonPField (I := I)
        (S.base.metric r) x
        (vec3 (I := I) (basis a) (basis b) (basis c))) =
      fun r : Real => hamiltonPAt (I := I) (S.base.metric r) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) by
          funext r
          rw [hamiltonPField_apply]]
    exact htimeAt.deriv
  have hsecond :
      (CanonicalSpatialDerivs0S.ofSmoothConnection
          (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g)
          (hamiltonPField (I := I) g)).nabla2A =
        hamiltonNabla2PField (I := I) g := by
    rfl
  have haction :
      covariantEndomorphismAction0S (I := I)
          (hamiltonPField (I := I) g x) RicEnd
          (fun i => basis (slots i)) =
        ricciPActionField (I := I) g x (fun i => basis (slots i)) := by
    rw [covariantEndomorphismAction0S_apply, Fin.sum_univ_three]
    simp only [RicEnd, LinearMap.coe_toContinuousLinearMap']
    simp_rw [tensor0SAt_apply_ricciEnd_slot_orthonormal
      (I := I) g basis horth Ric]
    have hright := congrArg (ricciPActionField (I := I) g x) hslots
    rw [hright, ricciPActionField_apply_orthonormal (I := I) g basis horth]
    have hupdate0 (p : Fin n) :
        Function.update (fun i => basis (slots i)) (0 : Fin 3) (basis p) =
          vec3 (I := I) (basis p) (basis b) (basis c) := by
      funext i
      fin_cases i <;> simp [slots, Function.update, vec3]
    have hupdate1 (p : Fin n) :
        Function.update (fun i => basis (slots i)) (1 : Fin 3) (basis p) =
          vec3 (I := I) (basis a) (basis p) (basis c) := by
      funext i
      fin_cases i <;> simp [slots, Function.update, vec3]
    have hupdate2 (p : Fin n) :
        Function.update (fun i => basis (slots i)) (2 : Fin 3) (basis p) =
          vec3 (I := I) (basis a) (basis b) (basis p) := by
      funext i
      fin_cases i <;> simp [slots, Function.update, vec3]
    simp_rw [hupdate0, hupdate1, hupdate2]
    rfl
  have hrough :
      metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (hamiltonNabla2PField (I := I) g x)
          (vec3 (I := I) (basis a) (basis b) (basis c)) =
        metricTraceFirstTwoField (I := I) (M := M) g
          (hamiltonNabla2PField (I := I) g) x
          (vec3 (I := I) (basis a) (basis b) (basis c)) := by
    rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin n))
        (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth)]
    rw [metricTrace0S2TensorInBasis_apply]
  calc
    deriv (fun r : Real => hamiltonPField (I := I)
        (S.base.metric r) x
        (vec3 (I := I) (basis a) (basis b) (basis c))) (t : Real) -
        metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          ((CanonicalSpatialDerivs0S.ofSmoothConnection
            (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g)
            (hamiltonPField (I := I) g)).nabla2A x)
          (vec3 (I := I) (basis a) (basis b) (basis c)) +
        covariantEndomorphismAction0S (I := I)
          (hamiltonPField (I := I) g x) RicEnd
          (vec3 (I := I) (basis a) (basis b) (basis c)) =
      hamiltonPHeatField (I := I) g x
        (vec3 (I := I) (basis a) (basis b) (basis c)) := by
          rw [htime, hsecond, hrough, ← hslots, haction, hslots]
          simp only [hamiltonPHeatField, hamiltonPRoughLaplacianField,
            ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add,
            Pi.add_apply, Tensor0SSpace.sub_apply, Tensor0SSpace.add_apply]
          ring
    _ = hamiltonPHeatComponent
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k => metricNablaRicciTimeDerivativeField (I := I) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l m => metricNabla3RicField (I := I) g x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        a b c :=
      (hamiltonPHeatComponent_eq_hamiltonPHeatField_of_orthonormal
        (I := I) g basis horth a b c).symm
    _ = _ := hamiltonP_evolution_of_ricci_flow
      (I := I) S t x basis horth a b c

private theorem doubleTraceProductField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 7))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7)
    (ANabla : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 (metricCov (I := I) (M := M) g) A ANabla) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (doubleTraceProductField (I := I) g perm A) =
      metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 3)
          (metricTraceFirstTwoField (I := I) (M := M) g
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 5)
              (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
                (frontExtendEquiv perm) ANabla)))) := by
  let cov := metricCov (I := I) (M := M) g
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hPerm := totalNabla0SRealizes_domDomCongr (I := I) cov perm A ANabla
    (by simpa [cov] using hA)
  have hInner := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 5) cov g hmc
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A)
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (frontExtendEquiv perm) ANabla) (by
        simpa only [Nat.reduceAdd] using hPerm)
  have hOuter := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
    (s := 3) cov g hmc
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A))
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 5)
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (frontExtendEquiv perm) ANabla))) hInner
  have hUnique := totalNabla0SRealizes_unique
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov
      (doubleTraceProductField (I := I) g perm A)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        3 cov (metricCov_smooth (I := I) (M := M) g)
        (doubleTraceProductField (I := I) g perm A)))
    (by simpa [doubleTraceProductField] using hOuter)
  funext x
  simpa [totalNabla0S_apply, Nat.reduceAdd, cov] using congrArg
    (fun B : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4 => B x) hUnique

private theorem doubleTraceNablaField_apply_orthonormal
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8)
    (tail : Fin 4 -> TangentSpace I x) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (traceNablaShuffle 3)
          (metricTraceFirstTwoField (I := I) (M := M) g
            (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
              (traceNablaShuffle 5) A))) x tail =
      ∑ i : Fin n, ∑ j : Fin n,
        A x (Fin.cons (tail 0)
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (fun r : Fin 3 => tail r.succ)))) := by
  rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  congr 1
  let Z := tail 0
  let tail' := fun r : Fin 3 => tail r.succ
  change (fun r : Fin 8 =>
      metricTraceInput (I := I) (basis j) (basis j)
        (fun s : Fin 6 =>
          metricTraceInput (I := I) (basis i) (basis i) tail
            (traceNablaShuffle 3 s)) (traceNablaShuffle 5 r)) =
    Fin.cons Z
      (metricTraceInput (I := I) (basis j) (basis j)
        (metricTraceInput (I := I) (basis i) (basis i) tail'))
  have htail : tail = Fin.cons Z tail' := by
    funext r
    fin_cases r <;> rfl
  have hinner := traceNablaShuffle_metricTraceInput (I := I)
    (a := basis i) (b := basis i) (Z := Z) (tail := tail')
  have hinner' :
      (fun s : Fin 6 =>
        metricTraceInput (I := I) (basis i) (basis i) tail
          (traceNablaShuffle 3 s)) =
        Fin.cons Z (metricTraceInput (I := I) (basis i) (basis i) tail') := by
    calc
      (fun s : Fin 6 =>
          metricTraceInput (I := I) (basis i) (basis i) tail
            (traceNablaShuffle 3 s)) =
          fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (Fin.cons Z tail')
              (traceNablaShuffle 3 s) := by rw [htail]
      _ = _ := by
        change metricTraceInput (I := I) (basis i) (basis i)
            (Fin.cons Z tail') ∘ traceNablaShuffle 3 = _
        exact hinner
  have houter := traceNablaShuffle_metricTraceInput (I := I)
    (a := basis j) (b := basis j) (Z := Z)
    (tail := metricTraceInput (I := I) (basis i) (basis i) tail')
  rw [hinner']
  change metricTraceInput (I := I) (basis j) (basis j)
      (Fin.cons Z (metricTraceInput (I := I) (basis i) (basis i) tail')) ∘
        traceNablaShuffle 5 = _
  exact houter

private theorem curvaturePFirstField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (doubleTraceProductField (I := I) g curvaturePFirstFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) =
      quadTraceProductField (I := I) g nablaRPFourthFirstPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) +
        quadTraceProductField (I := I) g RnablaPFourthFirstPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g)
            (hamiltonNablaPField (I := I) g)) := by
  let cov := metricCov (I := I) (M := M) g
  let R := metricRm04 (I := I) (M := M) g
  let RNabla := metricNablaRm04Field (I := I) g
  let P := hamiltonPField (I := I) g
  let PNabla := hamiltonNablaPField (I := I) g
  let D :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla P) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R PNabla)
  have hR : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov R RNabla := by
    simpa [cov, R, RNabla, metricNablaRm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov R
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) R))
  have hP : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov P PNabla := by
    simpa [cov, P, PNabla, hamiltonNablaPField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov P
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) P))
  have hProd : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) R P) D := by
    simpa [D] using nabla0S_product_realizes (I := I) cov
      R P RNabla PNabla hR hP
  rw [doubleTraceProductField_nabla_eq (I := I) g curvaturePFirstFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) R P) D hProd]
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply]
  rw [hslots]
  change _ =
    quadTraceProductField (I := I) g nablaRPFourthFirstPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla P) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3))) +
      quadTraceProductField (I := I) g RnablaPFourthFirstPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R PNabla) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3)))
  rw [nablaRPFourthFirstField_apply_orthonormal (I := I) g basis horth,
    RnablaPFourthFirstField_apply_orthonormal (I := I) g basis horth]
  rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  simp only [Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  simp_rw [metricTraceFirstTwoField_apply_orthonormal_pre (I := I) g basis horth]
  simp only [D, Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
    tensor0SField_product_apply]
  have htraceInputs
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      (fun r : Fin 8 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5 r)) =
        (Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x) := by
    have hvec :
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3)) =
          Fin.cons (basis (slots 0))
            (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
              (basis (slots 3))) := by
      funext k
      fin_cases k <;> rfl
    rw [hvec]
    have hinner := traceNablaShuffle_metricTraceInput (I := I)
      (a := basis i) (b := basis i) (Z := basis (slots 0))
      (tail := vec3 (I := I) (basis (slots 1)) (basis (slots 2))
        (basis (slots 3)))
    rw [show (fun s : Fin 6 =>
          metricTraceInput (I := I) (basis i) (basis i)
            (Fin.cons (basis (slots 0))
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3)))) (traceNablaShuffle 3 s)) =
        Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis i) (basis i)
            (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
              (basis (slots 3)))) by
      change metricTraceInput (I := I) (basis i) (basis i)
          (Fin.cons (basis (slots 0))
            (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
              (basis (slots 3)))) ∘ traceNablaShuffle 3 = _
      exact hinner]
    change metricTraceInput (I := I) (basis j) (basis j)
        (Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis i) (basis i)
            (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
              (basis (slots 3))))) ∘ traceNablaShuffle 5 = _
    exact traceNablaShuffle_metricTraceInput (I := I)
      (a := basis j) (b := basis j) (Z := basis (slots 0))
      (tail := metricTraceInput (I := I) (basis i) (basis i)
        (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3))))
  have hRNabla
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      (fun r : Fin 5 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizLeftEquiv 4 3 (Fin.castAdd 3 r))))) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis j) (basis i) (basis (slots 2)) := by
    funext r
    rw [show metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizLeftEquiv 4 3 (Fin.castAdd 3 r)))) =
        ((Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
          (frontExtendEquiv curvaturePFirstFieldPerm
            (leibnizLeftEquiv 4 3 (Fin.castAdd 3 r)))) by
      exact congrFun (htraceInputs i j)
        (frontExtendEquiv curvaturePFirstFieldPerm
          (leibnizLeftEquiv 4 3 (Fin.castAdd 3 r)))]
    fin_cases r <;> rfl
  have hP
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      (fun r : Fin 3 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizLeftEquiv 4 3 (Fin.natAdd 5 r))))) =
        vec3 (I := I) (basis j) (basis i) (basis (slots 3)) := by
    funext r
    rw [show metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizLeftEquiv 4 3 (Fin.natAdd 5 r)))) =
        ((Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
          (frontExtendEquiv curvaturePFirstFieldPerm
            (leibnizLeftEquiv 4 3 (Fin.natAdd 5 r)))) by
      exact congrFun (htraceInputs i j)
        (frontExtendEquiv curvaturePFirstFieldPerm
          (leibnizLeftEquiv 4 3 (Fin.natAdd 5 r)))]
    fin_cases r <;> rfl
  have hR
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      (fun r : Fin 4 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizRightEquiv 4 3 (Fin.castAdd 4 r))))) =
        vec4 (I := I) (basis (slots 1)) (basis j)
          (basis i) (basis (slots 2)) := by
    funext r
    rw [show metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizRightEquiv 4 3 (Fin.castAdd 4 r)))) =
        ((Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
          (frontExtendEquiv curvaturePFirstFieldPerm
            (leibnizRightEquiv 4 3 (Fin.castAdd 4 r)))) by
      exact congrFun (htraceInputs i j)
        (frontExtendEquiv curvaturePFirstFieldPerm
          (leibnizRightEquiv 4 3 (Fin.castAdd 4 r)))]
    fin_cases r <;> rfl
  have hPNabla
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      (fun r : Fin 4 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizRightEquiv 4 3 (Fin.natAdd 4 r))))) =
        vec4 (I := I) (basis (slots 0)) (basis j)
          (basis i) (basis (slots 3)) := by
    funext r
    rw [show metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizRightEquiv 4 3 (Fin.natAdd 4 r)))) =
        ((Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
          (frontExtendEquiv curvaturePFirstFieldPerm
            (leibnizRightEquiv 4 3 (Fin.natAdd 4 r)))) by
      exact congrFun (htraceInputs i j)
        (frontExtendEquiv curvaturePFirstFieldPerm
          (leibnizRightEquiv 4 3 (Fin.natAdd 4 r)))]
    fin_cases r <;> rfl
  have hRNablaComp
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizLeftEquiv 4 3 k)))) ∘ Fin.castAdd 3) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis j) (basis i) (basis (slots 2)) := by
    funext r
    exact congrFun (hRNabla i j) r
  have hPComp
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizLeftEquiv 4 3 k)))) ∘ Fin.natAdd (4 + 1)) =
        vec3 (I := I) (basis j) (basis i) (basis (slots 3)) := by
    funext r
    exact congrFun (hP i j) r
  have hRComp
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizRightEquiv 4 3 k)))) ∘ Fin.castAdd (3 + 1)) =
        vec4 (I := I) (basis (slots 1)) (basis j)
          (basis i) (basis (slots 2)) := by
    funext r
    exact congrFun (hR i j) r
  have hPNablaComp
      (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        metricTraceInput (I := I) (basis j) (basis j)
          (fun s : Fin 6 =>
            metricTraceInput (I := I) (basis i) (basis i)
              (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
                (basis (slots 2)) (basis (slots 3)))
              (traceNablaShuffle 3 s))
          (traceNablaShuffle 5
            (frontExtendEquiv curvaturePFirstFieldPerm
              (leibnizRightEquiv 4 3 k)))) ∘ Fin.natAdd 4) =
        vec4 (I := I) (basis (slots 0)) (basis j)
          (basis i) (basis (slots 3)) := by
    funext r
    exact congrFun (hPNabla i j) r
  simp_rw [hRNablaComp, hPComp, hRComp, hPNablaComp]
  let A := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    RNabla x (vec5 (I := I) (basis (slots 0)) (basis (slots 1))
        (basis i) (basis j) (basis (slots 2))) *
      P x (vec3 (I := I) (basis i) (basis j) (basis (slots 3)))
  let B := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    R x (vec4 (I := I) (basis (slots 1)) (basis i)
        (basis j) (basis (slots 2))) *
      PNabla x (vec4 (I := I) (basis (slots 0)) (basis i)
        (basis j) (basis (slots 3)))
  change (∑ i, ∑ j, (A j i + B j i)) =
    (∑ i, ∑ j, A i j) + ∑ i, ∑ j, B i j
  rw [show (∑ i, ∑ j, (A j i + B j i)) =
      (∑ i, ∑ j, A j i) + ∑ i, ∑ j, B j i by
    simp only [Finset.sum_add_distrib]]
  rw [show (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, A i j) = ∑ j, ∑ i, A i j).symm,
    show (∑ i, ∑ j, B j i) = ∑ i, ∑ j, B i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, B i j) = ∑ j, ∑ i, B i j).symm]

private theorem curvaturePSecondField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (doubleTraceProductField (I := I) g curvaturePSecondFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) =
      quadTraceProductField (I := I) g nablaRPFourthSecondPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) +
        quadTraceProductField (I := I) g RnablaPFourthSecondPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g)
            (hamiltonNablaPField (I := I) g)) := by
  let cov := metricCov (I := I) (M := M) g
  let R := metricRm04 (I := I) (M := M) g
  let RNabla := metricNablaRm04Field (I := I) g
  let P := hamiltonPField (I := I) g
  let PNabla := hamiltonNablaPField (I := I) g
  let D :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla P) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R PNabla)
  have hR : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov R RNabla := by
    simpa [cov, R, RNabla, metricNablaRm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov R
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) R))
  have hP : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov P PNabla := by
    simpa [cov, P, PNabla, hamiltonNablaPField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov P
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) P))
  have hProd : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) R P) D := by
    simpa [D] using nabla0S_product_realizes (I := I) cov
      R P RNabla PNabla hR hP
  rw [doubleTraceProductField_nabla_eq (I := I) g curvaturePSecondFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) R P) D hProd]
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  change _ =
    quadTraceProductField (I := I) g nablaRPFourthSecondPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla P) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3))) +
      quadTraceProductField (I := I) g RnablaPFourthSecondPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R PNabla) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3)))
  rw [nablaRPFourthSecondField_apply_orthonormal (I := I) g basis horth,
    RnablaPFourthSecondField_apply_orthonormal (I := I) g basis horth,
    doubleTraceNablaField_apply_orthonormal (I := I) g basis horth]
  simp only [D, Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
    tensor0SField_product_apply]
  have htail :
      (fun r : Fin 3 =>
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) r.succ) =
        vec3 (I := I) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [htail]
  have hzero :
      vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) 0 = basis (slots 0) := by
    simp [vec4]
  rw [hzero]
  let W : Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin 8 -> TangentSpace I x := fun i j =>
    Fin.cons (basis (slots 0))
      (metricTraceInput (I := I) (basis j) (basis j)
        (metricTraceInput (I := I) (basis i) (basis i)
          (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
            (basis (slots 3)))))
  have hRNabla (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizLeftEquiv 4 3 k))) ∘
          Fin.castAdd 3) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis j) (basis i) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  have hP (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizLeftEquiv 4 3 k))) ∘
          Fin.natAdd (4 + 1)) =
        vec3 (I := I) (basis j) (basis (slots 2)) (basis i) := by
    funext r
    fin_cases r <;> rfl
  have hR (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizRightEquiv 4 3 k))) ∘
          Fin.castAdd (3 + 1)) =
        vec4 (I := I) (basis (slots 1)) (basis j)
          (basis i) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  have hPNabla (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizRightEquiv 4 3 k))) ∘
          Fin.natAdd 4) =
        vec4 (I := I) (basis (slots 0)) (basis j)
          (basis (slots 2)) (basis i) := by
    funext r
    fin_cases r <;> rfl
  have hRNablaComp (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        (Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizLeftEquiv 4 3 k))) ∘
          Fin.castAdd 3) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis j) (basis i) (basis (slots 3)) := by
    simpa only [W] using hRNabla i j
  have hPComp (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        (Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizLeftEquiv 4 3 k))) ∘
          Fin.natAdd (4 + 1)) =
        vec3 (I := I) (basis j) (basis (slots 2)) (basis i) := by
    simpa only [W] using hP i j
  have hRComp (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        (Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizRightEquiv 4 3 k))) ∘
          Fin.castAdd (3 + 1)) =
        vec4 (I := I) (basis (slots 1)) (basis j)
          (basis i) (basis (slots 3)) := by
    simpa only [W] using hR i j
  have hPNablaComp (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 =>
        (Fin.cons (basis (slots 0))
          (metricTraceInput (I := I) (basis j) (basis j)
            (metricTraceInput (I := I) (basis i) (basis i)
              (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
                (basis (slots 3))))) : Fin 8 -> TangentSpace I x)
        (frontExtendEquiv curvaturePSecondFieldPerm (leibnizRightEquiv 4 3 k))) ∘
          Fin.natAdd 4) =
        vec4 (I := I) (basis (slots 0)) (basis j)
          (basis (slots 2)) (basis i) := by
    exact hPNabla i j
  conv_lhs =>
    enter [2, i]
    enter [2, j]
    rw [hRNablaComp i j, hPComp i j, hRComp i j, hPNablaComp i j]
  let A := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    RNabla x (vec5 (I := I) (basis (slots 0)) (basis (slots 1))
        (basis i) (basis j) (basis (slots 3))) *
      P x (vec3 (I := I) (basis i) (basis (slots 2)) (basis j))
  let B := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    R x (vec4 (I := I) (basis (slots 1)) (basis i)
        (basis j) (basis (slots 3))) *
      PNabla x (vec4 (I := I) (basis (slots 0)) (basis i)
        (basis (slots 2)) (basis j))
  change (∑ i, ∑ j, (A j i + B j i)) =
    (∑ i, ∑ j, A i j) + ∑ i, ∑ j, B i j
  rw [show (∑ i, ∑ j, (A j i + B j i)) =
      (∑ i, ∑ j, A j i) + ∑ i, ∑ j, B j i by
    simp only [Finset.sum_add_distrib]]
  rw [show (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, A i j) = ∑ j, ∑ i, A i j).symm,
    show (∑ i, ∑ j, B j i) = ∑ i, ∑ j, B i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, B i j) = ∑ j, ∑ i, B i j).symm]

private theorem curvaturePThirdField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (doubleTraceProductField (I := I) g curvaturePThirdFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g) (hamiltonPField (I := I) g))) =
      quadTraceProductField (I := I) g nablaRPFourthThirdPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRm04Field (I := I) g) (hamiltonPField (I := I) g)) +
        quadTraceProductField (I := I) g RnablaPFourthThirdPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRm04 (I := I) (M := M) g)
            (hamiltonNablaPField (I := I) g)) := by
  let cov := metricCov (I := I) (M := M) g
  let R := metricRm04 (I := I) (M := M) g
  let RNabla := metricNablaRm04Field (I := I) g
  let P := hamiltonPField (I := I) g
  let PNabla := hamiltonNablaPField (I := I) g
  let D :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla P) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 4 3)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R PNabla)
  have hR : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov R RNabla := by
    simpa [cov, R, RNabla, metricNablaRm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov R
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) R))
  have hP : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov P PNabla := by
    simpa [cov, P, PNabla, hamiltonNablaPField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov P
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) P))
  have hProd : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) R P) D := by
    simpa [D] using nabla0S_product_realizes (I := I) cov
      R P RNabla PNabla hR hP
  rw [doubleTraceProductField_nabla_eq (I := I) g curvaturePThirdFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) R P) D hProd]
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  change _ =
    quadTraceProductField (I := I) g nablaRPFourthThirdPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RNabla P) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3))) +
      quadTraceProductField (I := I) g RnablaPFourthThirdPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) R PNabla) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3)))
  rw [nablaRPFourthThirdField_apply_orthonormal (I := I) g basis horth,
    RnablaPFourthThirdField_apply_orthonormal (I := I) g basis horth,
    doubleTraceNablaField_apply_orthonormal (I := I) g basis horth]
  simp only [D, Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
    tensor0SField_product_apply]
  have htail :
      (fun r : Fin 3 =>
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) r.succ) =
        vec3 (I := I) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [htail]
  have hzero :
      vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) 0 = basis (slots 0) := by
    simp [vec4]
  rw [hzero]
  let W : Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin 8 -> TangentSpace I x := fun i j =>
    Fin.cons (basis (slots 0))
      (metricTraceInput (I := I) (basis j) (basis j)
        (metricTraceInput (I := I) (basis i) (basis i)
          (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
            (basis (slots 3)))))
  have hRNabla (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePThirdFieldPerm (leibnizLeftEquiv 4 3 k))) ∘
          Fin.castAdd 3) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 2))
          (basis j) (basis i) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  have hP (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePThirdFieldPerm (leibnizLeftEquiv 4 3 k))) ∘
          Fin.natAdd (4 + 1)) =
        vec3 (I := I) (basis (slots 1)) (basis j) (basis i) := by
    funext r
    fin_cases r <;> rfl
  have hR (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePThirdFieldPerm (leibnizRightEquiv 4 3 k))) ∘
          Fin.castAdd (3 + 1)) =
        vec4 (I := I) (basis (slots 2)) (basis j)
          (basis i) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  have hPNabla (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv curvaturePThirdFieldPerm (leibnizRightEquiv 4 3 k))) ∘
          Fin.natAdd 4) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis j) (basis i) := by
    funext r
    fin_cases r <;> rfl
  dsimp only [W] at hRNabla hP hR hPNabla
  conv_lhs =>
    enter [2, i]
    enter [2, j]
    rw [hRNabla i j, hP i j, hR i j, hPNabla i j]
  let A := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    RNabla x (vec5 (I := I) (basis (slots 0)) (basis (slots 2))
        (basis i) (basis j) (basis (slots 3))) *
      P x (vec3 (I := I) (basis (slots 1)) (basis i) (basis j))
  let B := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    R x (vec4 (I := I) (basis (slots 2)) (basis i)
        (basis j) (basis (slots 3))) *
      PNabla x (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
        (basis i) (basis j))
  change (∑ i, ∑ j, (A j i + B j i)) =
    (∑ i, ∑ j, A i j) + ∑ i, ∑ j, B i j
  rw [show (∑ i, ∑ j, (A j i + B j i)) =
      (∑ i, ∑ j, A j i) + ∑ i, ∑ j, B j i by
    simp only [Finset.sum_add_distrib]]
  rw [show (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, A i j) = ∑ j, ∑ i, A i j).symm,
    show (∑ i, ∑ j, B j i) = ∑ i, ∑ j, B i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, B i j) = ∑ j, ∑ i, B i j).symm]

private theorem ricciNablaRmField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (doubleTraceProductField (I := I) g ricciNablaRmFieldPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRicci (I := I) (M := M) g)
            (metricNablaRm04Field (I := I) g))) =
      quadTraceProductField (I := I) g nablaRicNablaRmFourthPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricNablaRic (I := I) (M := M) g)
            (metricNablaRm04Field (I := I) g)) +
        quadTraceProductField (I := I) g ricciNabla2RmFourthPerm
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (metricRicci (I := I) (M := M) g)
            (metricNabla2Rm04Field (I := I) g)) := by
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let RicNabla := metricNablaRic (I := I) (M := M) g
  let RNabla := metricNablaRm04Field (I := I) g
  let RNabla2 := metricNabla2Rm04Field (I := I) g
  let D :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv 2 5)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RicNabla RNabla) +
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv 2 5)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric RNabla2)
  have hRic : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric RicNabla := by
    simpa [cov, Ric, RicNabla, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) Ric))
  have hRNabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 cov RNabla RNabla2 := by
    simpa [cov, RNabla, RNabla2, metricNabla2Rm04Field] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5 cov RNabla
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) RNabla))
  have hProd : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 7 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric RNabla) D := by
    simpa [D] using nabla0S_product_realizes (I := I) cov
      Ric RNabla RicNabla RNabla2 hRic hRNabla
  rw [doubleTraceProductField_nabla_eq (I := I) g ricciNablaRmFieldPerm
    (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric RNabla) D hProd]
  funext x
  obtain ⟨basis, horth⟩ := exists_gOrthonormalBasis (I := I) g x
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun r : Fin 4 => basis (slots r)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [component0S_apply, component0S_apply, hslots]
  change _ =
    quadTraceProductField (I := I) g nablaRicNablaRmFourthPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) RicNabla RNabla) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3))) +
      quadTraceProductField (I := I) g ricciNabla2RmFourthPerm
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) Ric RNabla2) x
          (vec4 (I := I) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3)))
  rw [nablaRicNablaRmFourthField_apply_orthonormal (I := I) g basis horth,
    ricciNabla2RmFourthField_apply_orthonormal (I := I) g basis horth,
    doubleTraceNablaField_apply_orthonormal (I := I) g basis horth]
  simp only [D, Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
    tensor0SField_product_apply]
  have htail :
      (fun r : Fin 3 =>
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) r.succ) =
        vec3 (I := I) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  rw [htail]
  have hzero :
      vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) 0 = basis (slots 0) := by
    simp [vec4]
  rw [hzero]
  let W : Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin 8 -> TangentSpace I x := fun i j =>
    Fin.cons (basis (slots 0))
      (metricTraceInput (I := I) (basis j) (basis j)
        (metricTraceInput (I := I) (basis i) (basis i)
          (vec3 (I := I) (basis (slots 1)) (basis (slots 2))
            (basis (slots 3)))))
  have hRicNabla (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv ricciNablaRmFieldPerm (leibnizLeftEquiv 2 5 k))) ∘
          Fin.castAdd 5) =
        vec3 (I := I) (basis (slots 0)) (basis j) (basis i) := by
    funext r
    fin_cases r <;> rfl
  have hRNabla (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv ricciNablaRmFieldPerm (leibnizLeftEquiv 2 5 k))) ∘
          Fin.natAdd (2 + 1)) =
        vec5 (I := I) (basis j) (basis (slots 1))
          (basis (slots 2)) (basis i) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  have hRic (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv ricciNablaRmFieldPerm (leibnizRightEquiv 2 5 k))) ∘
          Fin.castAdd (5 + 1)) =
        vec2 (I := I) (basis j) (basis i) := by
    funext r
    fin_cases r <;> rfl
  have hRNabla2 (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      ((fun k : Fin 8 => W i j
        (frontExtendEquiv ricciNablaRmFieldPerm (leibnizRightEquiv 2 5 k))) ∘
          Fin.natAdd 2) =
        vec6 (I := I) (basis (slots 0)) (basis j) (basis (slots 1))
          (basis (slots 2)) (basis i) (basis (slots 3)) := by
    funext r
    fin_cases r <;> rfl
  dsimp only [W] at hRicNabla hRNabla hRic hRNabla2
  conv_lhs =>
    enter [2, i]
    enter [2, j]
    rw [hRicNabla i j, hRNabla i j, hRic i j, hRNabla2 i j]
  let A := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    RicNabla x (vec3 (I := I) (basis (slots 0)) (basis i) (basis j)) *
      RNabla x (vec5 (I := I) (basis i) (basis (slots 1))
        (basis (slots 2)) (basis j) (basis (slots 3)))
  let B := fun i j : Fin (Module.finrank Real (TangentSpace I x)) =>
    Ric x (vec2 (I := I) (basis i) (basis j)) *
      RNabla2 x (vec6 (I := I) (basis (slots 0)) (basis i) (basis (slots 1))
        (basis (slots 2)) (basis j) (basis (slots 3)))
  change (∑ i, ∑ j, (A j i + B j i)) =
    (∑ i, ∑ j, A i j) + ∑ i, ∑ j, B i j
  rw [show (∑ i, ∑ j, (A j i + B j i)) =
      (∑ i, ∑ j, A j i) + ∑ i, ∑ j, B j i by
    simp only [Finset.sum_add_distrib]]
  rw [show (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, A i j) = ∑ j, ∑ i, A i j).symm,
    show (∑ i, ∑ j, B j i) = ∑ i, ∑ j, B i j by
      simpa only using (Finset.sum_comm :
        (∑ i, ∑ j, B i j) = ∑ j, ∑ i, B i j).symm]

private theorem hamiltonPEvolutionReactionField_nabla_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (metricCov (I := I) (M := M) g)
        (hamiltonPEvolutionReactionField (I := I) g) =
      hamiltonNablaPEvolutionReactionField (I := I) g := by
  funext x
  rw [hamiltonPEvolutionReactionField, hamiltonNablaPEvolutionReactionField]
  repeat' rw [totalNabla0SFun_add (I := I)]
  repeat' rw [totalNabla0SFun_smul (I := I)]
  rw [congrFun (curvaturePFirstField_nabla_eq (I := I) g) x,
    congrFun (curvaturePSecondField_nabla_eq (I := I) g) x,
    congrFun (curvaturePThirdField_nabla_eq (I := I) g) x,
    congrFun (ricciNablaRmField_nabla_eq (I := I) g) x]
  simp only [ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, smul_add, neg_smul]
  abel

private theorem metricNabla2Rm04Field_eq_nablaKRm04Field_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    metricNabla2Rm04Field (I := I) (S.base.metric t) =
      nablaKRm04Field (I := I) S t 2 := by
  apply totalNabla0SRealizes_unique
  · simpa [metricNabla2Rm04Field, metricNablaRm04Field,
      SolutionFamily.connection, metricCov] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5
        (metricCov (I := I) (M := M) (S.base.metric t))
        (metricNablaRm04Field (I := I) (S.base.metric t))
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 (metricCov (I := I) (M := M) (S.base.metric t))
          (metricCov_smooth (I := I) (M := M) (S.base.metric t))
          (metricNablaRm04Field (I := I) (S.base.metric t))))
  · simpa [nablaKRm04Field, nabla2Rm04Field, nablaRm04Field,
      SolutionOn.family, SolutionFamily.connection, SolutionFamily.rm04,
      metricCov] using (nablaKRm04Field_realizes (I := I) S t 1)

private theorem hamiltonCurvatureRicciRoughLaplacianField_apply_orthonormal_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonCurvatureRicciRoughLaplacianField
        (I := I) (S.base.metric t) x
        (vec2 (I := I) (basis a) (basis b)) =
      ∑ c : Fin n, ∑ d : Fin n,
        (hamiltonRmRoughLaplacianField (I := I) S t x
              (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) *
            metricRicci (I := I) (M := M) (S.base.metric t) x
              (vec2 (I := I) (basis c) (basis d)) +
          S.base.rm04 t x
              (vec4 (I := I) (basis a) (basis c) (basis d) (basis b)) *
            metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
              (metricNabla2Ric (I := I) (M := M) (S.base.metric t)) x
                (vec2 (I := I) (basis c) (basis d)) +
          2 * ∑ e : Fin n,
            nablaRm04Field (I := I) S t x
                (vec5 (I := I) (basis e)
                  (basis a) (basis c) (basis d) (basis b)) *
              metricNablaRic (I := I) (M := M) (S.base.metric t) x
                (vec3 (I := I) (basis e) (basis c) (basis d))) := by
  have hRicLap (c d : Fin n) :
      metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (metricNabla2Ric (I := I) (M := M) (S.base.metric t)) x
            (vec2 (I := I) (basis c) (basis d)) =
        ∑ e : Fin n,
          metricNabla2Ric (I := I) (M := M) (S.base.metric t) x
            (vec4 (I := I) (basis e) (basis e) (basis c) (basis d)) := by
    rw [metricTraceFirstTwoField_apply_orthonormal
      (I := I) (S.base.metric t) basis horth]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [hamiltonCurvatureRicciRoughLaplacianField_apply_orthonormal
      (I := I) (S.base.metric t) basis horth a b,
    metricNabla2Rm04Field_eq_nablaKRm04Field_of_solution (I := I) S t]
  simp_rw [← hamiltonRmRoughLaplacianField_apply_orthonormal
    (I := I) S t basis horth, ← hRicLap]
  rw [metricNablaRm04Field_eq_nablaRm04Field (I := I) S t,
    SolutionFamily.rm04]

private theorem hamiltonCurvatureRicciAt_hasDerivWithinAt_oneTimeUhlenbeck
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
    let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonCurvatureRicciAt (I := I) (S.base.metric s) x
          (vec2 (I := I)
            (oneTimeUhlenbeckVector
              (I := I) (S.base.metric (t : Real)) (t : Real) s (basis a))
            (oneTimeUhlenbeckVector
              (I := I) (S.base.metric (t : Real)) (t : Real) s (basis b))))
      (hamiltonCurvatureRicciRoughLaplacianField
            (I := I) (S.base.metric (t : Real)) x
              (vec2 (I := I) (basis a) (basis b)) +
        hamiltonCurvatureRicciHeatComponent R Ric
          (hamiltonNablaRmComponentOfSolution
            (I := I) S (t : Real) x basis)
          (hamiltonNablaRicciComponentOfSolution
            (I := I) S (t : Real) x basis) a b)
      D.carrier (t : Real) := by
  dsimp only
  have h := hamiltonCurvatureRicciAt_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS t x basis horth a b
  dsimp only at h
  refine h.congr_deriv ?_
  rw [hamiltonCurvatureRicciRoughLaplacianField_apply_orthonormal_of_solution
    (I := I) S (t : Real) basis horth a b]
  unfold hamiltonCurvatureRicciHeatComponent
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold hamiltonRmComponentOfSolution hamiltonRicciComponentOfSolution
    hamiltonNablaRmComponentOfSolution hamiltonNablaRicciComponentOfSolution
  ring

private theorem hamiltonMAt_hasDerivWithinAt_oneTimeUhlenbeck_heat
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let R := fun i j k l => S.base.rm04 clock.time x
      (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))
    let Ric := fun i j => metricRicci (I := I) (M := M)
      (S.base.metric clock.time) x (vec2 (I := I) (basis i) (basis j))
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonDivPAt (I := I) (S.base.metric s) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis a))
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis b))) +
          hamiltonCurvatureRicciAt (I := I) (S.base.metric s) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis a))
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis b))) +
          (1 / (2 * (s - clock.origin))) *
            metricRicci (I := I) (M := M) (S.base.metric s) x
              (vec2 (I := I)
                (oneTimeUhlenbeckVector
                  (I := I) (S.base.metric clock.time) clock.time s (basis a))
                (oneTimeUhlenbeckVector
                  (I := I) (S.base.metric clock.time) clock.time s (basis b))))
      (hamiltonDivPRoughLaplacianField
            (I := I) (S.base.metric clock.time) x
              (vec2 (I := I) (basis a) (basis b)) +
          hamiltonCurvatureRicciRoughLaplacianField
            (I := I) (S.base.metric clock.time) x
              (vec2 (I := I) (basis a) (basis b)) +
          (1 / (2 * clock.elapsed)) *
            metricTraceFirstTwoField (I := I) (M := M)
              (S.base.metric clock.time)
              (metricNabla2Ric (I := I) (M := M)
                (S.base.metric clock.time)) x
                (vec2 (I := I) (basis a) (basis b)) +
        hamiltonMHeatComponent clock R Ric
          (hamiltonNablaRmComponentOfSolution
            (I := I) S clock.time x basis)
          (hamiltonNablaRicciComponentOfSolution
            (I := I) S clock.time x basis)
          (hamiltonNablaPComponentOfSolution
            (I := I) S clock.time x basis)
          (hamiltonNablaPTimeComponentOfSolution
            (I := I) S clock.time x basis)
          (hamiltonNabla3PComponentOfSolution
            (I := I) S clock.time x basis) a b)
      D.carrier clock.time := by
  dsimp only
  let t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
    ⟨clock.time, ht⟩
  have hDiv := hamiltonDivPAt_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS t x basis horth a b
  have hCurvature :=
    hamiltonCurvatureRicciAt_hasDerivWithinAt_oneTimeUhlenbeck
      (I := I) S hS t x basis horth a b
  dsimp only at hCurvature
  have hShift := hamiltonShiftedRicci_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS clock ht x basis horth a b
  have h := (hDiv.add hCurvature).add hShift
  refine h.congr_deriv ?_
  unfold hamiltonMHeatComponent
  unfold hamiltonRmComponentOfSolution hamiltonRicciComponentOfSolution
    hamiltonNablaRmComponentOfSolution hamiltonNablaRicciComponentOfSolution
    hamiltonNablaPComponentOfSolution hamiltonNablaPTimeComponentOfSolution
    hamiltonNabla3PComponentOfSolution
  ring

private theorem hamiltonNablaP_nablaHeat_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    uhlenbeckNablaHeatPComponent
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPTimeComponentOfSolution
          (I := I) S (t : Real) x basis)
        (hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis)
        q a b c =
      hamiltonNablaPEvolutionReactionComponent
        (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis) q a b c := by
  let g := S.base.metric (t : Real)
  calc
    _ = totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 (metricCov (I := I) (M := M) g) (hamiltonPHeatField (I := I) g) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) :=
      uhlenbeckNablaHeatPComponent_eq_hamiltonPHeatFieldNabla_of_orthonormal
        (I := I) g basis horth q a b c
    _ = totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 (metricCov (I := I) (M := M) g)
          (hamiltonPEvolutionReactionField (I := I) g) x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) := by
      rw [hamiltonPHeatField_eq_reaction (I := I) g]
    _ = hamiltonNablaPEvolutionReactionField (I := I) g x
          (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) := by
      rw [congrFun (hamiltonPEvolutionReactionField_nabla_eq (I := I) g) x]
    _ = hamiltonNablaPEvolutionReactionComponent
          (fun i j k l => metricRm04 (I := I) (M := M) g x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M) g x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i j k l m => metricNablaRm04Field (I := I) g x
            (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
          (fun i j k => metricNablaRic (I := I) (M := M) g x
            (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j k l m r => metricNabla2Rm04Field (I := I) g x
            (vec6 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m) (basis r)))
          (fun i j k l => hamiltonNablaPField (I := I) g x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) q a b c :=
      hamiltonNablaPEvolutionReactionField_apply_orthonormal
        (I := I) g basis horth q a b c
    _ = _ := by
      rw [metricNabla2Rm04Field_eq_nablaKRm04Field_of_solution
        (I := I) S (t : Real)]
      have hslots (i j k l m r : Fin n) :
          vec6 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m) (basis r) =
            Fin.cons (basis i)
              (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r)) := by
        funext p
        fin_cases p <;> rfl
      simp_rw [hslots]
      unfold hamiltonRmComponentOfSolution hamiltonRicciComponentOfSolution
        hamiltonNablaRmComponentOfSolution hamiltonNablaRicciComponentOfSolution
        hamiltonNabla2RmComponentOfSolution hamiltonNablaPComponentOfSolution
      dsimp only [g]
      rw [SolutionFamily.rm04,
        metricNablaRm04Field_eq_nablaRm04Field (I := I) S (t : Real)]

private theorem hamiltonDivP_evolution_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPHeatComponent
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPTimeComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis) a b =
      hamiltonDivPEvolutionComponent
        (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
        (fun i j => hamiltonDivPAt (I := I) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j))) a b := by
  have hcore := hamilton_bianchi_trace_components_of_solution
    (I := I) S (t : Real) x basis horth
  exact hamiltonDivP_evolution
    (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
    (fun i j => hamiltonDivPAt (I := I) (S.base.metric (t : Real)) x
      (vec2 (I := I) (basis i) (basis j)))
    (hamiltonNablaPTimeComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis)
    (hamilton_differentiated_P_identity_components_of_solution
      (I := I) S t x basis horth)
    (hamilton_gradient_P_identity_components_of_solution
      (I := I) S t x basis horth)
    (hamilton_contracted_curvature_derivative_components_of_solution
      (I := I) S (t : Real) x basis horth)
    (hamilton_rm_components_symm_of_solution (I := I) S t x basis)
    (hamilton_ricci_components_symm_of_solution
      (I := I) S (t : Real) x basis horth)
    (hamilton_nabla_ricci_components_symm_of_solution
      (I := I) S (t : Real) x basis)
    (hamilton_curvature_ricci_trace_components_of_solution
      (I := I) S t x basis horth)
    (fun d i j k l => hcore.2.1.2.1
      (basis d) (basis j) (basis i) (basis k) (basis l))
    (hamilton_curvature_second_derivative_commutator_components_of_solution
      (I := I) S t x basis horth)
    (hamilton_differentiated_curvature_divergence_components_of_solution
      (I := I) S (t : Real) x basis horth)
    (hamilton_nabla_P_components_skew_of_solution
      (I := I) S (t : Real) x basis)
    (hamiltonDivPComponentOfSolution_eq_hamiltonDivPAt_orthonormal
      (I := I) S (t : Real) x basis horth)
    (hamiltonNablaP_nablaHeat_components_of_solution
      (I := I) S t x basis horth) a b

theorem hamiltonDivP_evolution_of_ricci_flow
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonDivPHeatComponent
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField
          (I := I) (S.base.metric (t : Real)) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l => hamiltonNablaPTimeDerivativeField
          (I := I) (S.base.metric (t : Real)) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l m r => hamiltonNabla3PField
          (I := I) (S.base.metric (t : Real)) x
          (Fin.cons (basis i)
            (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
        a b =
      hamiltonDivPEvolutionComponent
        (fun i j k l => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField
          (I := I) (S.base.metric (t : Real)) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => hamiltonDivPAt (I := I) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j))) a b := by
  change hamiltonDivPHeatComponent
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaPTimeComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis) a b =
    hamiltonDivPEvolutionComponent
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
      (fun i j => hamiltonDivPAt (I := I) (S.base.metric (t : Real)) x
        (vec2 (I := I) (basis i) (basis j))) a b
  exact hamiltonDivP_evolution_components_of_solution
    (I := I) S t x basis horth a b

theorem hamiltonCurvatureRicci_evolution_of_ricci_flow
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (a b : Fin n) :
    hamiltonCurvatureRicciHeatComponent
        (fun i j k l => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b =
      hamiltonCurvatureRicciEvolutionComponent
        (fun i j k l => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b := by
  exact hamiltonCurvatureRicci_evolution
    (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
    (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis) a b

theorem hamiltonShiftedRicci_evolution_of_ricci_flow
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (a b : Fin n) :
    hamiltonShiftedRicciHeatComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j))) a b =
      hamiltonShiftedRicciEvolutionComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j))) a b := by
  exact hamiltonShiftedRicci_evolution clock
    (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
    (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
      (vec2 (I := I) (basis i) (basis j))) a b

theorem hamiltonP_evolution_covariantDerivative_of_ricci_flow
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    uhlenbeckNablaHeatPComponent
        (fun i j => metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l => hamiltonNablaPTimeDerivativeField
          (I := I) (S.base.metric (t : Real)) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l m r => hamiltonNabla3PField
          (I := I) (S.base.metric (t : Real)) x
          (Fin.cons (basis i)
            (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
        q a b c =
      hamiltonNablaPEvolutionReactionComponent
        (fun i j k l => S.base.rm04 (t : Real) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M) (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S (t : Real) x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric (t : Real)) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l m r => nablaKRm04Field (I := I) S (t : Real) 2 x
          (Fin.cons (basis i)
            (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
        (fun i j k l => hamiltonNablaPField (I := I) (S.base.metric (t : Real)) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) q a b c := by
  change uhlenbeckNablaHeatPComponent
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaPTimeComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis) q a b c =
    hamiltonNablaPEvolutionReactionComponent
      (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis) q a b c
  exact hamiltonNablaP_nablaHeat_components_of_solution
    (I := I) S t x basis horth q a b c


private theorem hamiltonM_evolution_components_of_solution
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonMHeatComponent clock
        (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNablaRmComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNablaPTimeComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNabla3PComponentOfSolution (I := I) S clock.time x basis) a b =
      hamiltonMEvolutionReactionComponent clock
        (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
        (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j))) a b := by
  have hcore := hamilton_bianchi_trace_components_of_solution
    (I := I) S clock.time x basis horth
  exact hamiltonM_evolution clock
    (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNablaRmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNabla2RmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
    (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
      (vec2 (I := I) (basis i) (basis j)))
    (hamiltonNablaPTimeComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNabla3PComponentOfSolution (I := I) S clock.time x basis)
    (hamilton_differentiated_P_identity_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth)
    (hamilton_gradient_P_identity_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth)
    (hamilton_contracted_curvature_derivative_components_of_solution
      (I := I) S clock.time x basis horth)
    (hamilton_rm_components_symm_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis)
    (hamilton_ricci_components_symm_of_solution
      (I := I) S clock.time x basis horth)
    (hamilton_nabla_ricci_components_symm_of_solution
      (I := I) S clock.time x basis)
    (hamilton_curvature_ricci_trace_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth)
    (fun d i j k l => hcore.2.1.2.1
      (basis d) (basis j) (basis i) (basis k) (basis l))
    (hamilton_curvature_second_derivative_commutator_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth)
    (hamilton_differentiated_curvature_divergence_components_of_solution
      (I := I) S clock.time x basis horth)
    (hamilton_nabla_P_components_skew_of_solution
      (I := I) S clock.time x basis)
    (hamiltonDivPComponentOfSolution_eq_hamiltonDivPAt_orthonormal
      (I := I) S clock.time x basis horth)
    (hamiltonNablaP_nablaHeat_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth) a b

theorem hamiltonM_evolution_of_ricci_flow
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonMHeatComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S clock.time x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField
          (I := I) (S.base.metric clock.time) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l => hamiltonNablaPTimeDerivativeField
          (I := I) (S.base.metric clock.time) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l m r => hamiltonNabla3PField
          (I := I) (S.base.metric clock.time) x
          (Fin.cons (basis i)
            (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis r))))
        a b =
      hamiltonMEvolutionReactionComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField
          (I := I) (S.base.metric clock.time) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j))) a b := by
  change hamiltonMHeatComponent clock
      (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaPTimeComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNabla3PComponentOfSolution (I := I) S clock.time x basis) a b =
    hamiltonMEvolutionReactionComponent clock
      (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
      (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
        (vec2 (I := I) (basis i) (basis j))) a b
  exact hamiltonM_evolution_components_of_solution
    (I := I) S clock ht x basis horth a b

theorem hamiltonMAt_hasDerivWithinAt_of_ricci_flow
    [I.Boundaryless] [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let R := fun i j k l => S.base.rm04 clock.time x
      (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))
    let Ric := fun i j => metricRicci (I := I) (M := M)
      (S.base.metric clock.time) x (vec2 (I := I) (basis i) (basis j))
    HasDerivWithinAt
      (fun s : Real =>
        hamiltonDivPAt (I := I) (S.base.metric s) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis a))
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis b))) +
          hamiltonCurvatureRicciAt (I := I) (S.base.metric s) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis a))
              (oneTimeUhlenbeckVector
                (I := I) (S.base.metric clock.time) clock.time s (basis b))) +
          (1 / (2 * (s - clock.origin))) *
            metricRicci (I := I) (M := M) (S.base.metric s) x
              (vec2 (I := I)
                (oneTimeUhlenbeckVector
                  (I := I) (S.base.metric clock.time) clock.time s (basis a))
                (oneTimeUhlenbeckVector
                  (I := I) (S.base.metric clock.time) clock.time s (basis b))))
      (hamiltonDivPRoughLaplacianField
            (I := I) (S.base.metric clock.time) x
              (vec2 (I := I) (basis a) (basis b)) +
          hamiltonCurvatureRicciRoughLaplacianField
            (I := I) (S.base.metric clock.time) x
              (vec2 (I := I) (basis a) (basis b)) +
          (1 / (2 * clock.elapsed)) *
            metricTraceFirstTwoField (I := I) (M := M)
              (S.base.metric clock.time)
              (metricNabla2Ric (I := I) (M := M)
                (S.base.metric clock.time)) x
                (vec2 (I := I) (basis a) (basis b)) +
        hamiltonMEvolutionReactionComponent clock R Ric
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j k l => hamiltonNablaPField
            (I := I) (S.base.metric clock.time) x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => hamiltonDivPAt
            (I := I) (S.base.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b)
      D.carrier clock.time := by
  dsimp only
  have h := hamiltonMAt_hasDerivWithinAt_oneTimeUhlenbeck_heat
    (I := I) S hS clock ht x basis horth a b
  dsimp only at h
  have hEvolution := hamiltonM_evolution_of_ricci_flow
    (I := I) S clock ht x basis horth a b
  change hamiltonMHeatComponent clock
      (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaRmComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaPTimeComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNabla3PComponentOfSolution (I := I) S clock.time x basis) a b =
    hamiltonMEvolutionReactionComponent clock
      (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
      (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
      (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
        (vec2 (I := I) (basis i) (basis j))) a b at hEvolution
  unfold hamiltonRmComponentOfSolution hamiltonRicciComponentOfSolution
    hamiltonNablaRicciComponentOfSolution hamiltonNablaPComponentOfSolution
    at hEvolution
  unfold hamiltonNablaRicciComponentOfSolution hamiltonNablaPComponentOfSolution at h
  refine h.congr_deriv ?_
  exact congrArg (fun z : Real =>
    hamiltonDivPRoughLaplacianField
          (I := I) (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) +
        hamiltonCurvatureRicciRoughLaplacianField
          (I := I) (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) +
        (1 / (2 * clock.elapsed)) *
          metricTraceFirstTwoField (I := I) (M := M)
            (S.base.metric clock.time)
            (metricNabla2Ric (I := I) (M := M)
              (S.base.metric clock.time)) x
              (vec2 (I := I) (basis a) (basis b)) + z) hEvolution

theorem hamiltonMOriginField_rough_laplacian_component
    [T2Space M]
    {n : Nat}
    (origin time : Real) (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let derivs := CanonicalSpatialDerivs0S.ofSmoothConnection
      (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (hamiltonMOriginField (I := I) origin time g)
    metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Fin n)) (derivs.nabla2A x)
        (vec2 (I := I) (basis a) (basis b)) =
      hamiltonDivPRoughLaplacianField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) +
        hamiltonCurvatureRicciRoughLaplacianField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) +
        (1 / (2 * (time - origin))) *
          metricTraceFirstTwoField (I := I) (M := M) g
            (metricNabla2Ric (I := I) (M := M) g) x
            (vec2 (I := I) (basis a) (basis b)) := by
  classical
  dsimp only
  let cov := metricCov (I := I) (M := M) g
  let P1 := hamiltonNablaPField (I := I) g
  let P2 := hamiltonNabla2PField (I := I) g
  let P3 := hamiltonNabla3PField (I := I) g
  let D0 := hamiltonDivPField (I := I) g
  let A1 := Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
    (traceNablaShuffle 2) P2
  let D1 := metricTraceFirstTwoField (I := I) (M := M) g A1
  let A2 := Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
    (frontExtendEquiv (traceNablaShuffle 2)) P3
  let D2 := metricTraceFirstTwoField (I := I) (M := M) g
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (traceNablaShuffle 3) A2)
  let C0 := hamiltonCurvatureRicciField (I := I) g
  let C1 := hamiltonNablaCurvatureRicciField (I := I) g
  let C2 := hamiltonNabla2CurvatureRicciField (I := I) g
  let R0 := metricRicci (I := I) (M := M) g
  let R1 := metricNablaRic (I := I) (M := M) g
  let R2 := metricNabla2Ric (I := I) (M := M) g
  let q : Real := 1 / (2 * (time - origin))
  let M0 := hamiltonMOriginField (I := I) origin time g
  let M1 := D1 + C1 + q • R1
  let M2 := D2 + C2 + q • R2
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) cov g := by
    simpa [cov, metricCov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) g
  have hP2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov P1 P2 := by
    simpa [cov, P1, P2, hamiltonNabla2PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov P1
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) P1))
  have hP3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 cov P2 P3 := by
    simpa [cov, P2, P3, hamiltonNabla3PField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5 cov P2
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) P2))
  have hD0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov D0 D1 := by
    simpa [D0, D1, A1, hamiltonDivPField, P1, P2] using
      nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
        (s := 2) cov g hmc P1 P2 hP2
  have hA1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 cov A1 A2 := by
    simpa [A1, A2] using totalNabla0SRealizes_domDomCongr
      (I := I) cov (traceNablaShuffle 2) P2 P3 hP3
  have hD1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov D1 D2 := by
    simpa [D1, D2] using nablaRealizes_metricTraceFirstTwo
      (I := I) (M := M) (s := 3) cov g hmc A1 A2 hA1
  have hC0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov C0 C1 := by
    simpa [cov, C0, C1] using
      hamiltonNablaCurvatureRicciField_realizes (I := I) g
  have hC1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov C1 C2 := by
    simpa [cov, C1, C2, hamiltonNabla2CurvatureRicciField] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov C1
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) C1))
  have hR0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov R0 R1 := by
    simpa [cov, R0, R1, metricNablaRic] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov R0
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) R0))
  have hR1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov R1 R2 := by
    simpa [cov, R1, R2, metricNabla2Ric] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov R1
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          3 cov (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) R1))
  have hM0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov M0 M1 := by
    simpa [M0, M1, q, hamiltonMOriginField, D0, C0, R0] using
      (hD0.add hC0).add (hR0.smul q)
  have hM1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov M1 M2 := by
    simpa [M1, M2] using (hD1.add hC1).add (hR1.smul q)
  let derivs := CanonicalSpatialDerivs0S.ofSmoothConnection cov
    (by simpa [cov] using metricCov_smooth (I := I) (M := M) g) M0
  have hfirst : derivs.nablaA = M1 :=
    totalNabla0SRealizes_unique derivs.first hM0
  have hM1' : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov derivs.nablaA M2 := by
    rw [hfirst]
    exact hM1
  have hsecond : derivs.nabla2A = M2 :=
    totalNabla0SRealizes_unique derivs.second hM1'
  have htrace (A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4) :
      metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n)) (A x)
          (vec2 (I := I) (basis a) (basis b)) =
        metricTraceFirstTwoField (I := I) (M := M) g A x
          (vec2 (I := I) (basis a) (basis b)) := by
    rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin n))
        (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth),
      metricTrace0S2TensorInBasis_apply]
  have hDrough :
      metricTraceFirstTwoField (I := I) (M := M) g D2 x
          (vec2 (I := I) (basis a) (basis b)) =
        hamiltonDivPRoughLaplacianField (I := I) g x
          (vec2 (I := I) (basis a) (basis b)) := by
    dsimp only [D2]
    rw [metricTraceFirstTwoField_apply_orthonormal_pre
      (I := I) g basis horth]
    simp_rw [metricTraceFirstTwoField_apply_orthonormal_pre
      (I := I) g basis horth]
    rw [hamiltonDivPRoughLaplacianField,
      metricTraceFirstTwoField_apply_orthonormal_pre
        (I := I) g basis horth]
    simp_rw [metricTraceFirstTwoField_apply_orthonormal_pre
      (I := I) g basis horth]
    have hshuffle (e c : Fin n) :
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
          (traceNablaShuffle 3) A2) x
          (metricTraceInput (I := I) (basis c) (basis c)
            (metricTraceInput (I := I) (basis e) (basis e)
              (vec2 (I := I) (basis a) (basis b)))) =
          P3 x (metricTraceInput (I := I) (basis e) (basis e)
            (metricTraceInput (I := I) (basis c) (basis c)
              (vec2 (I := I) (basis a) (basis b)))) := by
      simp only [Tensor0SField.domDomCongr_apply,
        Tensor0SSpace.domDomCongr_apply, A2, P3]
      apply congrArg (hamiltonNabla3PField (I := I) g x)
      funext i
      fin_cases i <;> rfl
    simp_rw [hshuffle]
    rw [Finset.sum_comm]
  have hsplit :
      metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n)) ((D2 + C2 + q • R2) x)
          (vec2 (I := I) (basis a) (basis b)) =
        metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin n)) (D2 x)
            (vec2 (I := I) (basis a) (basis b)) +
          metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin n)) (C2 x)
            (vec2 (I := I) (basis a) (basis b)) +
          q * metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin n)) (R2 x)
            (vec2 (I := I) (basis a) (basis b)) := by
    simp only [metricTrace0S2TensorInBasis_apply, metricTrace0S2InBasis,
      ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_left_comm]
  rw [show (CanonicalSpatialDerivs0S.ofSmoothConnection
      (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
      (hamiltonMOriginField (I := I) origin time g)).nabla2A = M2 by
        simpa [derivs, cov, M0] using hsecond]
  rw [show M2 = D2 + C2 + q • R2 by rfl, hsplit,
    htrace D2, htrace C2, htrace R2, hDrough]
  simp only [C2, hamiltonCurvatureRicciRoughLaplacianField,
    R2, q]

theorem hamiltonMComponent_eq_hamiltonMAt_orthonormal
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      (S.family.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Idx) :
    hamiltonMComponent clock
      (fun i j k l => metricRm04 (I := I) (M := M)
        (S.family.metric clock.time) x
        (vec4 (basis i) (basis j) (basis k) (basis l)))
      (fun i j => metricRicci (I := I) (M := M)
        (S.family.metric clock.time) x (vec2 (basis i) (basis j)))
      (fun i j => hamiltonDivPAt (I := I) (S.family.metric clock.time) x
        (vec2 (basis i) (basis j))) a b =
      hamiltonMAt (I := I) clock (S.family.metric clock.time) x
        (vec2 (basis a) (basis b)) := by
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (S.family.metric clock.time) basis horth
  rw [hamiltonMAt_apply (I := I) S hS clock ht x
      (basis a) (basis b)]
  unfold hamiltonMComponent hamiltonCurvatureRicciComponent
  dsimp
  have hcurv :
      (∑ c : Idx, ∑ d : Idx,
          metricRm04 (I := I) (M := M) (S.family.metric clock.time) x
              (vec4 (basis a) (basis c) (basis d) (basis b)) *
            metricRicci (I := I) (M := M) (S.family.metric clock.time) x
              (vec2 (basis c) (basis d))) =
        hamiltonCurvatureRicciAt (I := I) (S.family.metric clock.time) x
          (vec2 (basis a) (basis b)) := by
    rw [hamiltonCurvatureRicciAt_apply (I := I)
      (S.family.metric clock.time) basis
      (fun i j => if i = j then (1 : Real) else 0) hinv]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
  rw [hcurv]

theorem hamiltonBlock_coefficients_bound_of_curvature_derivative_bound
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (K S0 : Real) (hS0 : 0 <= S0)
    (helapsed : clock.elapsed <= S0)
    (hderiv : forall k : Nat, k <= 2 ->
      nablaKRm04NormSqIntrinsic (I := I) S k clock.time x <= K) :
    let A := Real.sqrt K
    let N : Real := n
    let B := A + N * A + N * A +
      S0 * (N ^ 2 * A + N ^ 3 * A ^ 2) + N * A / 2
    0 <= B ∧
      (forall a b c d,
        |S.base.rm04 clock.time x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))| <= B) ∧
      (forall a b c,
        |hamiltonPComponent
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric clock.time) x
            (vec3 (I := I) (basis i) (basis j) (basis k))) a b c| <= B) ∧
      (forall a b,
        |hamiltonMComponent clock
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M)
            (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i j => hamiltonDivPAt (I := I)
            (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j))) a b| <=
          B / clock.elapsed) ∧
      (forall a b,
        |metricRicci (I := I) (M := M) (S.base.metric clock.time) x
          (vec2 (I := I) (basis a) (basis b))| <= B) := by
  let A := Real.sqrt K
  let N : Real := n
  let B := A + N * A + N * A +
    S0 * (N ^ 2 * A + N ^ 3 * A ^ 2) + N * A / 2
  change 0 <= B ∧
    (forall a b c d,
      |S.base.rm04 clock.time x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))| <= B) ∧
    (forall a b c,
      |hamiltonPComponent
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec3 (I := I) (basis i) (basis j) (basis k))) a b c| <= B) ∧
    (forall a b,
      |hamiltonMComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j => hamiltonDivPAt (I := I)
          (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j))) a b| <=
        B / clock.elapsed) ∧
    (forall a b,
      |metricRicci (I := I) (M := M) (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b))| <= B)
  have hA : 0 <= A := by
    dsimp [A]
    exact Real.sqrt_nonneg K
  have hComponent : forall (k : Nat), k <= 2 ->
      forall v : Fin (4 + k) -> TangentSpace I x,
        (forall q, (S.base.metric clock.time).inner x (v q) (v q) = 1) ->
        |nablaKRm04Field (I := I) S clock.time k x v| <= A := by
    intro k hk v hv
    have hcomp := DifferentialGeometry.Tensor0SBundle.abs_apply_le_sqrt_normSq0S
      (I := I) (S.base.metric clock.time) x (4 + k) basis horth
      (nablaKRm04Field (I := I) S clock.time k x) v
    have hprod :
        (∏ q : Fin (4 + k),
          Real.sqrt ((S.base.metric clock.time).inner x (v q) (v q))) = 1 := by
      apply Finset.prod_eq_one
      intro q _
      rw [hv q]
      norm_num
    rw [hprod, mul_one] at hcomp
    exact hcomp.trans (Real.sqrt_le_sqrt (hderiv k hk))
  have hRBound : forall a b c d : Fin n,
      |hamiltonRmComponentOfSolution (I := I) S clock.time x basis a b c d| <= A := by
    intro a b c d
    have hcomp := hComponent 0 (by omega)
      (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) (by
        intro q
        fin_cases q <;> simp [vec4, horth])
    simpa only [hamiltonRmComponentOfSolution, nablaKRm04Field_zero] using hcomp
  have hNablaRBound : forall e a b c d : Fin n,
      |hamiltonNablaRmComponentOfSolution
        (I := I) S clock.time x basis e a b c d| <= A := by
    intro e a b c d
    have hcomp := hComponent 1 (by omega)
      (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)) (by
        intro q
        fin_cases q <;> simp [vec5, horth])
    simpa only [hamiltonNablaRmComponentOfSolution, nablaKRm04Field,
      nablaRm04Field] using hcomp
  have hNabla2RBound : forall e f a b c d : Fin n,
      |hamiltonNabla2RmComponentOfSolution
        (I := I) S clock.time x basis e f a b c d| <= A := by
    intro e f a b c d
    let slots : Fin 6 -> Fin n := fun q =>
      if q = 0 then e else if q = 1 then f else if q = 2 then a else
        if q = 3 then b else if q = 4 then c else d
    have hcomp := hComponent 2 (by omega) (fun q => basis (slots q)) (by
      intro q
      rw [horth (slots q) (slots q)]
      simp)
    have hv : (fun q => basis (slots q)) =
        Fin.cons (basis e)
          (vec5 (I := I) (basis f) (basis a) (basis b) (basis c) (basis d)) := by
      funext q
      fin_cases q <;> rfl
    rw [hv] at hcomp
    exact hcomp
  have hcoeff := hamiltonBlock_coefficient_bounds clock
    (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNablaRmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNabla2RmComponentOfSolution (I := I) S clock.time x basis)
    (hamiltonNablaPComponentOfSolution (I := I) S clock.time x basis)
    A A A S0 hA hA hA hS0 helapsed hRBound hNablaRBound hNabla2RBound
    (hamilton_nabla_ricci_components_symm_of_solution
      (I := I) S clock.time x basis)
    (hamilton_curvature_ricci_trace_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth)
    (hamilton_contracted_curvature_derivative_components_of_solution
      (I := I) S clock.time x basis horth)
    (hamilton_differentiated_curvature_divergence_components_of_solution
      (I := I) S clock.time x basis horth)
  simp only [Fintype.card_fin] at hcoeff
  refine ⟨hcoeff.1, ?_, ?_, ?_, ?_⟩
  · intro a b c d
    exact hcoeff.2.1 a b c d
  · intro a b c
    exact hcoeff.2.2.1 a b c
  · intro a b
    have hM := hcoeff.2.2.2.1 a b
    change
      |hamiltonMComponent clock
        (hamiltonRmComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonRicciComponentOfSolution (I := I) S clock.time x basis)
        (hamiltonDivPComponentOfSolution (I := I) S clock.time x basis) a b| <=
        B / clock.elapsed at hM
    unfold hamiltonMComponent hamiltonCurvatureRicciComponent at hM ⊢
    rw [hamiltonDivPComponentOfSolution_eq_hamiltonDivPAt_orthonormal
      (I := I) S clock.time x basis horth a b] at hM
    simpa only [hamiltonRmComponentOfSolution,
      hamiltonRicciComponentOfSolution] using hM
  · intro a b
    exact hcoeff.2.2.2.2 a b

theorem hamiltonPerturbedBlock_reaction_ge_of_curvature_derivative_bound
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (K S0 B C phi Lphi psi psi' : Real)
    (hS0 : 0 <= S0) (helapsed : clock.elapsed <= S0)
    (hderiv : forall k : Nat, k <= 2 ->
      nablaKRm04NormSqIntrinsic (I := I) S k clock.time x <= K)
    (hB : B = Real.sqrt K + (n : Real) * Real.sqrt K +
      (n : Real) * Real.sqrt K +
      S0 * ((n : Real) ^ 2 * Real.sqrt K +
        (n : Real) ^ 3 * (Real.sqrt K) ^ 2) +
      (n : Real) * Real.sqrt K / 2)
    (hCphi : 2 * (B + 1) * (n : Real) ^ 3 <= C)
    (hCpsiW : 2 * B * S0 * (n : Real) ^ 3 +
      4 * B * S0 ^ 2 * (n : Real) ^ 4 +
      B * S0 ^ 2 * (n : Real) ^ 2 +
      4 * B ^ 2 * S0 ^ 2 * (n : Real) ^ 2 +
      (n : Real) ^ 2 <= C)
    (hCpsiU : 4 * B * (n : Real) ^ 3 +
      (8 * B + 4) * (n : Real) ^ 4 + B * (n : Real) +
      2 * B * (n : Real) ^ 2 + 1 <= C)
    (U : Fin n -> Fin n -> Real) (W : Fin n -> Real)
    (hU : forall a b, U a b = -U b a)
    (hphi : 0 <= phi) (hpsi : 0 <= psi) (hpsi1 : psi <= 1) :
    let R : Fin n -> Fin n -> Fin n -> Fin n -> Real :=
      fun a b c d => S.base.rm04 clock.time x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))
    let Ric : Fin n -> Fin n -> Real := fun a b =>
      metricRicci (I := I) (M := M) (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b))
    let nablaR : Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
      fun e a b c d => nablaRm04Field (I := I) S clock.time x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))
    let nablaRic : Fin n -> Fin n -> Fin n -> Real := fun a b c =>
      metricNablaRic (I := I) (M := M) (S.base.metric clock.time) x
        (vec3 (I := I) (basis a) (basis b) (basis c))
    let nablaP : Fin n -> Fin n -> Fin n -> Fin n -> Real :=
      fun e a b c =>
        metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
            (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)) -
          metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
            (vec4 (I := I) (basis e) (basis b) (basis a) (basis c))
    hamiltonBlockHeatProduct
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => R a b d c) psi)
        (hamiltonPComponent nablaRic)
        (hamiltonPerturbedMBlock clock
          (hamiltonMComponent clock R Ric
            (fun a b => ∑ e, nablaP e e a b)) phi)
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => hamiltonRmReactionComponent R a b d c) psi')
        (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
        (hamiltonPerturbedMBlock clock
          (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
            (fun a b => ∑ e, nablaP e e a b))
          (Lphi - phi / clock.elapsed))
        (fun e a b c d => nablaR e a b d c) nablaP
        (fun _ _ _ => 0)
        (hamiltonTestJetDU clock Ric
          (fun a b => if a = b then 1 else 0) W)
        (fun _ => 0) (fun _ _ => 0)
        (fun a => (1 / clock.elapsed) * W a) U W >=
      hamiltonBlockJ
          (hamiltonPerturbedCurvatureBlock
            (fun a b c d => R a b d c) psi)
          (hamiltonPComponent nablaRic)
          (hamiltonPerturbedMBlock clock
            (hamiltonMComponent clock R Ric
              (fun a b => ∑ e, nablaP e e a b)) phi) U W +
        hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock
            (fun a b c d => R a b d c) psi)
          (hamiltonPComponent nablaRic) U W +
        (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
            C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) *
          (∑ a, (W a) ^ 2) +
        (psi' - C * psi) * (∑ a, ∑ b, (U a b) ^ 2) := by
  dsimp only
  let R := hamiltonRmComponentOfSolution (I := I) S clock.time x basis
  let Ric := hamiltonRicciComponentOfSolution (I := I) S clock.time x basis
  let nablaR :=
    hamiltonNablaRmComponentOfSolution (I := I) S clock.time x basis
  let nablaRic :=
    hamiltonNablaRicciComponentOfSolution (I := I) S clock.time x basis
  let nablaP : Fin n -> Fin n -> Fin n -> Fin n -> Real :=
    fun e a b c =>
      metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
          (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)) -
        metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
          (vec4 (I := I) (basis e) (basis b) (basis a) (basis c))
  change hamiltonBlockHeatProduct
      (hamiltonPerturbedCurvatureBlock (fun a b c d => R a b d c) psi)
      (hamiltonPComponent nablaRic)
      (hamiltonPerturbedMBlock clock
        (hamiltonMComponent clock R Ric
          (fun a b => ∑ e, nablaP e e a b)) phi)
      (hamiltonPerturbedCurvatureBlock
        (fun a b c d => hamiltonRmReactionComponent R a b d c) psi')
      (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
      (hamiltonPerturbedMBlock clock
        (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
          (fun a b => ∑ e, nablaP e e a b))
        (Lphi - phi / clock.elapsed))
      (fun e a b c d => nablaR e a b d c) nablaP (fun _ _ _ => 0)
      (hamiltonTestJetDU clock Ric
        (fun a b => if a = b then 1 else 0) W)
      (fun _ => 0) (fun _ _ => 0)
      (fun a => (1 / clock.elapsed) * W a) U W >= _
  have hcoeff := hamiltonBlock_coefficients_bound_of_curvature_derivative_bound
    (I := I) S clock ht x basis horth K S0 hS0 helapsed hderiv
  dsimp only at hcoeff
  rw [← hB] at hcoeff
  have hdiv : forall a b, (∑ e, nablaP e e a b) =
      hamiltonDivPAt (I := I) (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b)) := by
    intro a b
    simpa only [nablaP, hamiltonDivPComponentOfSolution,
      hamiltonNablaPComponentOfSolution, hamiltonNablaPField_apply] using
      hamiltonDivPComponentOfSolution_eq_hamiltonDivPAt_orthonormal
        (I := I) S clock.time x basis horth a b
  have hRmetric : R = fun a b c d =>
      metricRm04 (I := I) (M := M) (S.family.metric clock.time) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) := by
    rfl
  have hRicmetric : Ric = fun a b =>
      metricRicci (I := I) (M := M) (S.family.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b)) := by
    rfl
  have hDivmetric :
      (fun i j => hamiltonDivPAt (I := I) (S.base.metric clock.time) x
        (vec2 (I := I) (basis i) (basis j))) =
      fun i j => hamiltonDivPAt (I := I) (S.family.metric clock.time) x
        (vec2 (I := I) (basis i) (basis j)) := by
    rfl
  have hM : forall a b,
      hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b =
        hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) b a := by
    intro a b
    simp_rw [hdiv]
    rw [hRmetric, hRicmetric, hDivmetric,
      hamiltonMComponent_eq_hamiltonMAt_orthonormal
        (I := I) S hS clock ht x basis horth a b,
      hamiltonMComponent_eq_hamiltonMAt_orthonormal
        (I := I) S hS clock ht x basis horth b a]
    exact hamiltonMAt_symm (I := I) S clock ht x (basis a) (basis b)
  apply hamiltonPerturbedBlock_heat_product_ge clock R Ric nablaR nablaRic
    nablaP (fun _ _ _ => 0) phi Lphi psi psi' B S0 C U W
  · exact hamilton_rm_components_symm_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis
  · exact hamilton_nabla_rm_components_pair_symm_of_solution
      (I := I) S clock.time x basis horth
  · exact hamilton_ricci_components_symm_of_solution
      (I := I) S clock.time x basis horth
  · exact hamilton_nabla_ricci_components_symm_of_solution
      (I := I) S clock.time x basis
  · exact hamilton_curvature_ricci_trace_components_of_solution
      (I := I) S ⟨clock.time, ht⟩ x basis horth
  · exact hamilton_contracted_curvature_derivative_components_of_solution
      (I := I) S clock.time x basis horth
  · intro e a b c
    dsimp only [nablaP]
    ring
  · exact hM
  · exact hU
  · exact hcoeff.1
  · exact hphi
  · exact hpsi
  · exact hpsi1
  · exact helapsed
  · exact hcoeff.2.1
  · exact hcoeff.2.2.1
  · intro a b
    simp_rw [hdiv]
    exact hcoeff.2.2.2.1 a b
  · exact hcoeff.2.2.2.2
  · simpa using hCphi
  · simpa using hCpsiW
  · simpa using hCpsiU

end DifferentialGeometry.PDE.RicciFlow
