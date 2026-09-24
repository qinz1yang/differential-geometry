import DifferentialGeometry.Geometry.Connection.MetricTrace.Higher
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section Trace

variable {s : ℕ}

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceNormSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    normSq0S (I := I) g x s (metricTraceFirstTwo0STensor (I := I) g V) ≤
      (Module.finrank Real E : Real) ^ (s + 2) * normSq0S (I := I) g x (s + 2) V := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  set NV := Real.sqrt (normSq0S (I := I) g x (s + 2) V) with hNV
  have hNVnn : 0 ≤ NV := Real.sqrt_nonneg _
  set B : Real := (Module.finrank Real E : Real) * NV with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hcomp : ∀ φ : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis (metricTraceFirstTwo0STensor (I := I) g V) φ| ≤ B := by
    intro φ
    rw [component0S_apply, metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv]
    have hcollapse :
        metricTrace0S2InBasis (I := I) basis
            (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) V
            (fun a : Fin s => basis (φ a)) =
          ∑ i, V (metricTraceInput (I := I) (basis i) (basis i)
            (fun a : Fin s => basis (φ a))) := by
      unfold metricTrace0S2InBasis
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro k _ hk
        rw [show identityInvMetric
              (Idx := Fin (Module.finrank Real (TangentSpace I x))) i k = 0 from
          diagonalInvMetric_eq_zero_of_ne (Ne.symm hk), zero_mul]
      · intro hni; exact absurd (Finset.mem_univ i) hni
    rw [hcollapse]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i, |V (metricTraceInput (I := I) (basis i) (basis i)
        (fun a : Fin s => basis (φ a)))| ≤ NV := by
      intro i
      have hb : ∀ b : Fin (s + 2), ∃ j,
          metricTraceInput (I := I) (basis i) (basis i) (fun a : Fin s => basis (φ a)) b = basis j := by
        intro b
        refine Fin.cases ?_ ?_ b
        · exact ⟨i, rfl⟩
        · intro c
          refine Fin.cases ?_ ?_ c
          · exact ⟨i, rfl⟩
          · intro d; exact ⟨φ d, rfl⟩
      have hbound := abs_apply_le_sqrt_normSq0S (I := I) g x (s + 2) basis hON V
        (metricTraceInput (I := I) (basis i) (basis i) (fun a : Fin s => basis (φ a)))
      have hprod : (∏ b : Fin (s + 2), Real.sqrt (g.inner x
          (metricTraceInput (I := I) (basis i) (basis i) (fun a : Fin s => basis (φ a)) b)
          (metricTraceInput (I := I) (basis i) (basis i) (fun a : Fin s => basis (φ a)) b))) = 1 := by
        refine Finset.prod_eq_one fun b _ => ?_
        obtain ⟨j, hj⟩ := hb b
        rw [hj, hON j j]
        simp
      simpa only [hprod, mul_one] using hbound
    calc (∑ i, |V (metricTraceInput (I := I) (basis i) (basis i)
              (fun a : Fin s => basis (φ a)))|)
        ≤ ∑ _i : Fin (Module.finrank Real (TangentSpace I x)), NV :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hB]
          simp only [nsmul_eq_mul]
          rw [show (Module.finrank Real (TangentSpace I x) : Real) = (Module.finrank Real E : Real) from rfl]
  have hcard := normSq0S_le_card_of_component_bound (I := I) g x s basis hinv
    (metricTraceFirstTwo0STensor (I := I) g V) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin s -> Fin (Module.finrank Real (TangentSpace I x))) : Real)
        = (Module.finrank Real E : Real) ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  rw [hcard_eq] at hcard
  refine hcard.trans (le_of_eq ?_)
  rw [hB]
  have hV2 : NV ^ 2 = normSq0S (I := I) g x (s + 2) V :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x (s + 2) _)
  rw [show ((Module.finrank Real E : Real) * NV) ^ 2
      = (Module.finrank Real E : Real) ^ 2 * NV ^ 2 by ring, hV2]
  rw [pow_add]
  ring

end Trace


end DifferentialGeometry.PDE.RicciFlow
