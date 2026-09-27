import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Relowering

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


end DifferentialGeometry.PDE.RicciFlow
