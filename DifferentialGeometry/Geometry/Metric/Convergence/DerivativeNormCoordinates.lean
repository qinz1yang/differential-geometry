import DifferentialGeometry.Geometry.Metric.Convergence.GoodFrame
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeBounds

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv

open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_le_compSq_uniform
    [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ∃ (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (u' : Set M) (Cu : Real),
      IsOpen u' ∧ x ∈ u' ∧
      u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧ 1 ≤ Cu ∧
      ∀ (gk gInf : SmoothRiemannianMetric I M),
      ∀ z ∈ u', ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
        metricDerivNorm (I := I) a gk gInf gRef z ≤
          Cu * Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            (Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _)
                  x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gk gRef a z) I0
              - Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _)
                  x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
  classical
  obtain ⟨basisE, u', ε, hopen, hxu', hsub, hε0, hnε, hgram, hONx, hfwd, hrev⟩ :=
    exists_goodFrame_compBound (I := I) gRef x
  refine ⟨basisE, u', ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^
    (a + 2),
    hopen, hxu', hsub, ?_, fun gk gInf z hzu' hz => ?_⟩
  · have hcard : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) :=
      Nat.cast_nonneg _
    exact one_le_pow₀ (by nlinarith)
  · set bz := (((trivializationAt E (TangentSpace I : M → Type _)
    x).isLocalFrameOn_localFrame_baseSet
        I 1 basisE).toBasisAt hz) with hbz
    have hcomp : ∀ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
        Tensor0SBundle.component0S (I := I) bz
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0
          = Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
            - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0 :=
      fun I0 => rfl
    have hsumeq : (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          Tensor0SBundle.component0S (I := I) bz
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2)
        = ∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          (Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
            - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0) ^
              2 := by
      refine Finset.sum_congr rfl fun I0 _ => ?_
      rw [hcomp I0]
    have hb := hrev z hz hzu' (a + 2) (metricDiffCovDerivAt (I := I) a gk gInf gRef z)
    have hCge1 : (1 : Real) ≤ (3 / 2) *
      ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1) := by
      have : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) := Nat.cast_nonneg _
      nlinarith
    have hCpow1 : (1 : Real) ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1))
      ^ (a + 2) :=
      one_le_pow₀ hCge1
    have hsqrtle : Real.sqrt
      (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2))
        ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) := by
      have h2 : ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)
          ≤ (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)) ^
            2 := by
        nlinarith [hCpow1]
      calc Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^
        (a + 2))
          ≤ Real.sqrt ((((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^
            (a + 2)) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) :=
            Real.sqrt_sq (by positivity)
    rw [metricDerivNorm]
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
            (metricDiffCovDerivAt (I := I) a gk gInf gRef z))
        ≤ Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2)
          *
            ∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^
        (a + 2)) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) :=
          Real.sqrt_mul (by positivity) _
      _ ≤ ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I) bz
                (metricDiffCovDerivAt (I := I) a gk gInf gRef z) I0 ^ 2) :=
          mul_le_mul_of_nonneg_right hsqrtle (Real.sqrt_nonneg _)
      _ = ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) *
            Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              (Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gk gRef a z) I0
                - Tensor0SBundle.component0S (I := I) bz (metricCovDeriv (I := I) gInf gRef a z) I0)
                  ^ 2) := by
          rw [hsumeq]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_le_compSq
    [FiniteDimensional Real E]
    (gRef gk gInf : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ∃ (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (u' : Set M) (Cu : Real),
      IsOpen u' ∧ x ∈ u' ∧
      u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧ 1 ≤ Cu ∧
      ∀ z ∈ u', ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
        metricDerivNorm (I := I) a gk gInf gRef z ≤
          Cu * Real.sqrt (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            (Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _)
                  x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gk gRef a z) I0
              - Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _)
                  x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) (metricCovDeriv (I := I) gInf gRef a z) I0) ^ 2) := by
  obtain ⟨basisE, u', Cu, hopen, hxu', hsub, hCu, h⟩ :=
    metricDerivNorm_le_compSq_uniform (I := I) gRef a x
  exact ⟨basisE, u', Cu, hopen, hxu', hsub, hCu, fun z hzu' hz => h gk gInf z hzu' hz⟩

end HCGCompactness
end DifferentialGeometry
