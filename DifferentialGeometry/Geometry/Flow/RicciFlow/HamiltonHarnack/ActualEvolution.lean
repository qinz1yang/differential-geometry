import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.ReactionBound
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.DifferentiatedSecondBianchi
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MIdentities
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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

private noncomputable def hamiltonNablaPField
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

private noncomputable def hamiltonNabla3PField
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

private theorem hamiltonNablaPField_apply
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

private noncomputable def hamiltonCurvatureRicciField
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

private noncomputable def hamiltonNablaPTimeDerivativeField
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
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (perm : Equiv.Perm (Fin 8))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) g
    (metricTraceFirstTwoField (I := I) (M := M) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) perm A))

private theorem metricTraceFirstTwoField_apply_orthonormal_pre
    [T2Space M]
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
    [T2Space M]
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
    [T2Space M]
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
    [T2Space M]
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

private theorem doubleTraceProductField_apply_orthonormal
    [T2Space M]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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

def hamiltonRmComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l => S.base.rm04 t x
    (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))

noncomputable def hamiltonRicciComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Real :=
  fun i j => metricRicci (I := I) (M := M) (S.base.metric t) x
    (vec2 (I := I) (basis i) (basis j))

noncomputable def hamiltonNablaRmComponentOfSolution
    [CompleteSpace E] [T2Space M] [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l m => nablaRm04Field (I := I) S t x
    (vec5 (I := I) (basis i) (basis j) (basis k) (basis l) (basis m))

noncomputable def hamiltonNablaRicciComponentOfSolution
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

noncomputable def hamiltonNablaPTimeComponentOfSolution
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

noncomputable def hamiltonNabla2RmComponentOfSolution
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l m p => nablaKRm04Field (I := I) S t 2 x
    (Fin.cons (basis i)
      (vec5 (I := I) (basis j) (basis k) (basis l) (basis m) (basis p)))

noncomputable def hamiltonNablaPComponentOfSolution
    [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Fin n -> Fin n -> Fin n -> Fin n -> Real :=
  fun i j k l => hamiltonNablaPField (I := I) (S.base.metric t) x
    (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))

noncomputable def hamiltonNabla3PComponentOfSolution
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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

private theorem hamilton_curvature_ricci_trace_components_of_solution
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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

private theorem uhlenbeckHeatNablaPComponent_eq_hamiltonNablaPHeatField_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    uhlenbeckHeatNablaPComponent
        (fun i j => metricRicci (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M) g x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j k l => hamiltonNablaPTimeDerivativeField (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) +
          ∑ r : Fin 3, ∑ d : Fin n,
            ricciFlowConnectionVariationField (I := I) g x
              (vec3 (I := I) (basis i)
                (basis (if r = 0 then j else if r = 1 then k else l))
                (basis d)) *
              hamiltonPField (I := I) g x
                (vec3 (I := I)
                  (basis (if 0 = r then d else j))
                  (basis (if 1 = r then d else k))
                  (basis (if 2 = r then d else l))))
        (fun i j k l m r => hamiltonNabla3PField (I := I) g x
          (Fin.cons (basis i)
            (Fin.cons (basis j)
              (Fin.cons (basis k)
                (Fin.cons (basis l)
                  (Fin.cons (basis m) (fun _ : Fin 1 => basis r))))))) q a b c =
      hamiltonNablaPHeatField (I := I) g x
        (vec4 (I := I) (basis q) (basis a) (basis b) (basis c)) := by
  rw [uhlenbeckHeatNablaPComponent,
    hamiltonNablaPHeatField_apply_orthonormal (I := I) g basis horth]
  simp only [uhlenbeckTimeDerivativeOfCovariantDerivative,
    roughLaplacianCovariantDerivativeComponents,
    covariantTensorNablaRicciSlotAction, covariantTensorRicciSlotAction]
  rw [nablaRicPActionField_apply_orthonormal (I := I) g basis horth,
    ricciNablaPActionField_apply_orthonormal (I := I) g basis horth]
  simp [hamiltonPComponent, Function.update_apply,
    ricciFlowConnectionVariationField_apply]
  simp only [Fin.sum_univ_three]
  ring

private theorem hamiltonNablaPHeatField_eq_reaction_add_curvatureAction_of_orthonormal
    [T2Space M]
    {n : Nat}
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (q a b c : Fin n) :
    hamiltonNablaPHeatField (I := I) g x
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
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) q a b c +
      curvatureSlotActionContraction
        (fun i j k l => metricRm04 (I := I) (M := M) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun e (slots : Fin 3 -> Fin n) => hamiltonNablaPField (I := I) g x
          (vec4 (I := I) (basis e) (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)))) q
        (fun r : Fin 3 => if r = 0 then a else if r = 1 then b else c) := by
  rw [hamiltonNablaPHeatField_apply_orthonormal (I := I) g basis horth,
    hamiltonNablaPEvolutionReactionField_apply_orthonormal (I := I) g basis horth]
  simp only [curvatureSlotActionContraction, hamiltonNablaPEvolutionReactionComponent,
    hamiltonPComponent, Function.update_apply]
  simp only [Fin.sum_univ_three]
  ring

private theorem hamiltonNablaP_nablaHeat_components_of_solution
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
        (fun i j k l => hamiltonNablaPTimeComponentOfSolution
            (I := I) S (t : Real) x basis i j k l +
          ∑ r : Fin 3, ∑ d : Fin n,
            ricciFlowConnectionVariationField (I := I) (S.base.metric (t : Real)) x
              (vec3 (I := I) (basis i)
                (basis (if r = 0 then j else if r = 1 then k else l))
                (basis d)) *
              hamiltonPField (I := I) (S.base.metric (t : Real)) x
                (vec3 (I := I)
                  (basis (if 0 = r then d else j))
                  (basis (if 1 = r then d else k))
                  (basis (if 2 = r then d else l))))
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
  let R := hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis
  let Ric := hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis
  let nablaR := hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis
  let nablaRic := hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis
  let nabla2R := hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis
  let nablaP := hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis
  let nabla3P := hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis
  let slots : Fin 3 -> Fin n := fun r => if r = 0 then a else if r = 1 then b else c
  let nablaDtP : Fin n -> Fin n -> Fin n -> Fin n -> Real := fun i j k l =>
    hamiltonNablaPTimeComponentOfSolution (I := I) S (t : Real) x basis i j k l +
      ∑ r : Fin 3, ∑ d : Fin n,
        ricciFlowConnectionVariationField (I := I) g x
          (vec3 (I := I) (basis i)
            (basis (if r = 0 then j else if r = 1 then k else l)) (basis d)) *
          hamiltonPField (I := I) g x
            (vec3 (I := I) (basis (if 0 = r then d else j))
              (basis (if 1 = r then d else k)) (basis (if 2 = r then d else l)))
  have hHeat := uhlenbeckHeatNablaPComponent_eq_hamiltonNablaPHeatField_of_orthonormal
    (I := I) g (x := x) basis horth q a b c
  have hReaction := hamiltonNablaPHeatField_eq_reaction_add_curvatureAction_of_orthonormal
    (I := I) g (x := x) basis horth q a b c
  have hHeat' :
      uhlenbeckHeatNablaPComponent Ric nablaRic nablaP nablaDtP nabla3P q a b c =
        hamiltonNablaPEvolutionReactionComponent R Ric nablaR nablaRic nabla2R nablaP q a b c +
          curvatureSlotActionContraction R
            (fun e (s : Fin 3 -> Fin n) => nablaP e (s 0) (s 1) (s 2)) q slots := by
    simpa [g, R, Ric, nablaR, nablaRic, nabla2R, nablaP, nabla3P, nablaDtP,
      slots, hamiltonNablaPTimeComponentOfSolution,
      hamiltonNablaPComponentOfSolution, hamiltonNabla3PComponentOfSolution] using
      hHeat.trans hReaction
  have hComm := uhlenbeck_heat_covariantDerivative_commutator
    R nablaR Ric nablaRic
    (fun s : Fin 3 -> Fin n => hamiltonPComponent nablaRic (s 0) (s 1) (s 2))
    (fun e (s : Fin 3 -> Fin n) => nablaP e (s 0) (s 1) (s 2))
    (fun e (s : Fin 3 -> Fin n) => nablaDtP e (s 0) (s 1) (s 2))
    (fun e f d (s : Fin 3 -> Fin n) => nabla3P e f d (s 0) (s 1) (s 2))
    (hamilton_differentiated_P_identity_components_of_solution (I := I) S t x basis horth)
    (hamilton_gradient_P_identity_components_of_solution (I := I) S t x basis horth)
    (hamilton_contracted_curvature_derivative_components_of_solution
      (I := I) S t x basis horth)
    (hamilton_rm_components_symm_of_solution (I := I) S t x basis).swap12
    (hamilton_rm_components_symm_of_solution (I := I) S t x basis).swap34
    (hamilton_curvature_ricci_trace_components_of_solution (I := I) S t x basis horth)
    q slots
  change
    (uhlenbeckHeatNablaPComponent Ric nablaRic nablaP nablaDtP nabla3P q a b c -
      uhlenbeckNablaHeatPComponent Ric nablaRic nablaP nablaDtP nabla3P q a b c) =
      curvatureSlotActionContraction R
        (fun e (s : Fin 3 -> Fin n) => nablaP e (s 0) (s 1) (s 2)) q slots at hComm
  rw [hHeat'] at hComm
  linarith

theorem hamilton_nablaP_evolution_of_ricci_flow
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
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
        (fun i j k l => hamiltonNablaPTimeComponentOfSolution
            (I := I) S (t : Real) x basis i j k l +
          ∑ r : Fin 3, ∑ d : Fin n,
            ricciFlowConnectionVariationOrthonormal
              (fun p r s => hamiltonNablaRicciComponentOfSolution
                (I := I) S (t : Real) x basis p r s) i
              (if r = 0 then j else if r = 1 then k else l) d *
              hamiltonPComponent
                (hamiltonNablaRicciComponentOfSolution
                  (I := I) S (t : Real) x basis)
                (if 0 = r then d else j) (if 1 = r then d else k)
                (if 2 = r then d else l))
        (hamiltonNabla3PComponentOfSolution (I := I) S (t : Real) x basis)
        q a b c =
      hamiltonNablaPEvolutionReactionComponent
        (hamiltonRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaRicciComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNabla2RmComponentOfSolution (I := I) S (t : Real) x basis)
        (hamiltonNablaPComponentOfSolution (I := I) S (t : Real) x basis) q a b c := by
  have h := hamiltonNablaP_nablaHeat_components_of_solution
    (I := I) S t x basis horth q a b c
  simpa [ricciFlowConnectionVariationField_apply, hamiltonPField_apply,
    hamiltonPComponent] using h

end DifferentialGeometry.PDE.RicciFlow
