import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.NormHeatEquation

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem Rm04NormHeatEquationOn.exists_hasDerivAt_le_of_reaction_bound
    {D : RealTimeInterval} {u lap nabla reaction : ℝ → M → ℝ} {C : ℝ}
    (hheat : Rm04NormHeatEquationOn (D := D) u lap nabla reaction)
    (hnabla : ∀ t : D.RegularTime, ∀ x : M, 0 ≤ nabla (t : ℝ) x)
    (hreaction : ∀ t : D.RegularTime, ∀ x : M, reaction (t : ℝ) x ≤ C * u (t : ℝ) x) :
    ∀ t : D.RegularTime, ∀ x : M, ∃ d : ℝ,
      HasDerivAt (fun s : ℝ => u s x) d (t : ℝ) ∧
        d ≤ lap (t : ℝ) x + C * u (t : ℝ) x := by
  intro t x
  refine ⟨lap (t : ℝ) x + (-2 * nabla (t : ℝ) x + reaction (t : ℝ) x),
    (hheat t x).hasDerivAt (D.regular_mem_nhds t.2), ?_⟩
  linarith [hnabla t x, hreaction t x]

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem Rm04NormHeatEquationOn.exists_hasDerivAt_le_of_rpow_reaction_bound
    {D : RealTimeInterval} {u lap nabla reaction : ℝ → M → ℝ} {C K : ℝ}
    (hC : 0 ≤ C)
    (hheat : Rm04NormHeatEquationOn (D := D) u lap nabla reaction)
    (hu : ∀ t : D.RegularTime, ∀ x : M, 0 ≤ u (t : ℝ) x)
    (hub : ∀ t : D.RegularTime, ∀ x : M, u (t : ℝ) x ≤ K)
    (hnabla : ∀ t : D.RegularTime, ∀ x : M, 0 ≤ nabla (t : ℝ) x)
    (hreaction : ∀ t : D.RegularTime, ∀ x : M,
      reaction (t : ℝ) x ≤ C * (u (t : ℝ) x) ^ (3 / 2 : ℝ)) :
    ∀ t : D.RegularTime, ∀ x : M, ∃ d : ℝ,
      HasDerivAt (fun s : ℝ => u s x) d (t : ℝ) ∧
        d ≤ lap (t : ℝ) x + (C * Real.sqrt K) * u (t : ℝ) x := by
  refine Rm04NormHeatEquationOn.exists_hasDerivAt_le_of_reaction_bound hheat hnabla ?_
  intro t x
  have hu0 : 0 ≤ u (t : ℝ) x := hu t x
  have hrpow : (u (t : ℝ) x) ^ (3 / 2 : ℝ) ≤ u (t : ℝ) x * Real.sqrt K := by
    rw [rpow_three_halves_eq_mul_sqrt hu0]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hub t x)) hu0
  calc reaction (t : ℝ) x ≤ C * (u (t : ℝ) x) ^ (3 / 2 : ℝ) := hreaction t x
    _ ≤ C * (u (t : ℝ) x * Real.sqrt K) := mul_le_mul_of_nonneg_left hrpow hC
    _ = (C * Real.sqrt K) * u (t : ℝ) x := by ring

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormHeatEquationOn_of_solution.exists_hasDerivAt_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (gInv : ℝ → InverseMetricComponents M Idx)
    (frame : Idx → (x : M) → TangentSpace I x)
    (rm04Dt : ℝ → M → Idx → Idx → Idx → Idx → ℝ)
    (rmNormLap roughLapInner nablaRmNormSq : ℝ → M → ℝ)
    (h_raw : Rm04NormRawDerivativeEquationOn (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame (I := I) S Rm04 gInv frame
      rm04Dt roughLapInner (rmReactionInFrame (I := I) Rm04 gInv frame))
    (h_lap : Rm04NormLaplacianComponentsOn rmNormLap roughLapInner nablaRmNormSq)
    (horth : ∀ t : D.RegularTime, ∀ x : M,
      InverseMetricOrthonormalAt (M := M) gInv (t : ℝ) x)
    (hnabla : ∀ t : D.RegularTime, ∀ x : M, 0 ≤ nablaRmNormSq (t : ℝ) x)
    {K : ℝ}
    (hub : ∀ t : D.RegularTime, ∀ x : M,
      rm04NormSqInFrame (I := I) Rm04 gInv frame (t : ℝ) x ≤ K) :
    ∀ t : D.RegularTime, ∀ x : M, ∃ d : ℝ,
      HasDerivAt (fun s : ℝ => rm04NormSqInFrame (I := I) Rm04 gInv frame s x) d (t : ℝ) ∧
        d ≤ rmNormLap (t : ℝ) x +
          (16 * (Fintype.card Idx : ℝ) ^ 6 * Real.sqrt K) *
            rm04NormSqInFrame (I := I) Rm04 gInv frame (t : ℝ) x := by
  have hC : (0 : ℝ) ≤ 16 * (Fintype.card Idx : ℝ) ^ 6 := by positivity
  refine Rm04NormHeatEquationOn.exists_hasDerivAt_le_of_rpow_reaction_bound hC
    (rm04NormHeatEquationOn_of_solution (I := I) S Rm04 gInv frame rm04Dt
      rmNormLap roughLapInner nablaRmNormSq h_raw h_simplify h_lap)
    ?_ hub hnabla ?_
  · intro t x
    rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) Rm04 gInv frame (t : ℝ) x (horth t x)]
    exact compNormSq4_nonneg _
  · intro t x
    exact (le_abs_self (rmReactionInFrame (I := I) Rm04 gInv frame (t : ℝ) x)).trans
      (abs_rmReactionInFrame_le (I := I) Rm04 gInv frame (t : ℝ) x (horth t x))

end DifferentialGeometry.PDE.RicciFlow
