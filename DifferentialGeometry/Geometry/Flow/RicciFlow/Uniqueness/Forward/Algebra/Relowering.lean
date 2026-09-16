import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Relowering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.AlgebraicBridge
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

section ReLower

private theorem sum_comm4 {Idx : Type*} [Fintype Idx] (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F a b i j) =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F a b i j := by
  classical
  calc (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F a b i j)
      = ∑ a : Idx, ∑ i : Idx, ∑ b : Idx, ∑ j : Idx, F a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Idx, ∑ a : Idx, ∑ b : Idx, ∑ j : Idx, F a b i j := Finset.sum_comm
    _ = ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

omit [SigmaCompactSpace M] in
theorem reLower_rm04 (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) (hRm : Rm2 x = metricRm04At (I := I) g₂ x)
    (X Y Z W : TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ Rm2 x)
        (vec4 (I := I) X Y Z W) =
      g₁.inner x (riemannOp (metricCov (I := I) g₂) x X Y Z) W := by
  classical
  have hlast : (vec4 (I := I) X Y Z W) (Fin.last 3) = W := by
    simp [vec4]
  have hupd : Function.update (vec4 (I := I) X Y Z W) (Fin.last 3)
      (sharpFlat (I := I) g₁ g₂ x W) =
      vec4 (I := I) X Y Z (sharpFlat (I := I) g₁ g₂ x W) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [reLower_apply (I := I) g₁ g₂ Rm2 x, hlast, hupd, hRm]
  exact mixLow_eq_rm04 (I := I) g₁ g₂ x X Y Z W

end ReLower

section Defect

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem metricCov_one (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) g) (1 : WithTop ℕ∞) := by
  simpa [metricCov] using
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g)

end Defect

section Payoff

def reLowerOp (g₁ g₂ : SmoothRiemannianMetric I M) :
    ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k
  | 0 => id
  | (_ + 1) => fun T => reLower (I := I) g₁ g₂ T

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
@[simp] theorem reLowerOp_succ (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    reLowerOp (I := I) g₁ g₂ (k + 1) T = reLower (I := I) g₁ g₂ T := rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommFlux_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommFlux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      reLowerPair (I := I) g₂ T
        (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  rw [lapCommFlux, reLowerOp_succ, reLowerOp_succ, nabla_reLower]
  abel

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T := by
  have h := lapComm_eq_div_flux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T
  rw [lapCommFlux_reLower (I := I) g₁ g₂ T] at h
  simpa using h

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem traceInput_last {k : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (k + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (Fin.last (k + 2)) = tail (Fin.last k) := by
  have hv : ((Fin.last (k + 2) : Fin (k + 1 + 2)) : ℕ) = k + 2 := rfl
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(k + 2 = 0)), dif_neg (by omega : ¬(k + 2 = 1))]
  exact congrArg tail (Fin.ext (by simp))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem traceInput_update_last {k : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (k + 1) -> TangentSpace I x) (v : TangentSpace I x) :
    Function.update (metricTraceInput (I := I) a b tail) (Fin.last (k + 2)) v =
      metricTraceInput (I := I) a b (Function.update tail (Fin.last k) v) := by
  classical
  funext p
  have hp : (p : ℕ) < k + 1 + 2 := p.isLt
  by_cases hlast : p = Fin.last (k + 2)
  · subst hlast
    rw [Function.update_self, traceInput_last, Function.update_self]
  · have hpv : (p : ℕ) ≠ k + 2 := fun hc => hlast (Fin.ext (by rw [hc]; rfl))
    rw [Function.update_of_ne hlast, metricTraceInput_apply, metricTraceInput_apply]
    split_ifs with h0 h1
    · rfl
    · rfl
    · have hne : (⟨(p : ℕ) - 2, by omega⟩ : Fin (k + 1)) ≠ Fin.last k := by
        intro hc
        have hval : (p : ℕ) - 2 = k := congrArg Fin.val hc
        omega
      exact (Function.update_of_ne hne v tail).symm

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem trace_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 2 + 1)) :
    metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ (reLower (I := I) g₁ g₂ A) =
      reLower (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  apply tensor0SSpace_ext (I := I) (k + 1) x
  intro tail
  change Tensor0SSpace.eval
      (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLower (I := I) g₁ g₂ A) x) tail =
    Tensor0SSpace.eval
      (reLower (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) x) tail
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_isInverse (I := I) g₂ x basis
  with_unfolding_all
    rw [traceField_eq_sum (I := I) g₂ (reLower (I := I) g₁ g₂ A) basis gInv hinv tail,
      reLower_eval (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) basis gInv hinv tail]
  have hL : ∀ a b : Fin (Module.finrank Real (TangentSpace I x)),
      gInv a b * Tensor0SSpace.eval ((reLower (I := I) g₁ g₂ A) x)
          (metricTraceInput (I := I) (basis a) (basis b) tail) =
        ∑ i, ∑ j, gInv a b * gInv i j *
          (Tensor0SSpace.eval (A x) (metricTraceInput (I := I) (basis a) (basis b)
              (Function.update tail (Fin.last k) (basis i))) *
            g₁.inner x (basis j) (tail (Fin.last k))) := by
    intro a b
    rw [reLower_eval (I := I) g₁ g₂ A basis gInv hinv
      (metricTraceInput (I := I) (basis a) (basis b) tail), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [traceInput_update_last, traceInput_last]
    ring
  have hR : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      gInv i j * (Tensor0SSpace.eval
          ((metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) x)
            (Function.update tail (Fin.last k) (basis i)) *
          g₁.inner x (basis j) (tail (Fin.last k))) =
        ∑ a, ∑ b, gInv a b * gInv i j *
          (Tensor0SSpace.eval (A x) (metricTraceInput (I := I) (basis a) (basis b)
              (Function.update tail (Fin.last k) (basis i))) *
            g₁.inner x (basis j) (tail (Fin.last k))) := by
    intro i j
    rw [traceField_eq_sum (I := I) g₂ A basis gInv hinv
      (Function.update tail (Fin.last k) (basis i)), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [hL, hR]
  exact sum_comm4 _

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommRem_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapCommRem, reLowerOp_succ, reLowerOp_succ, covDiv0SField, covDiv0SField,
    nabla_reLower, metricTraceFirstTwoField_add, trace_reLower]
  abel

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_eq (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower (I := I) g₁ g₂ T, lapCommRem_reLower (I := I) g₁ g₂ T]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower_eq (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

end Payoff

end DifferentialGeometry.PDE.RicciFlow

end
