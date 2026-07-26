import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

/-!
# Three-dimensional low-regularity metric realization

The spectral `H3` ball used by the low-regularity maximal-regularity solver
lies in a fixed fibre-small metric ball.  This is the dimension-three
replacement for the deliberately lossy high-order realization bound.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology
open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

/-- In dimension three, a positive spectral `H2` radius directly supplies
the fibre-smallness needed to realize every smooth perturbation in the state
ball as a metric. -/
theorem lowreg_realize_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧
      p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
      ∀ (T : SmoothCcTensor g 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) p.2 := by
  obtain ⟨C, hC, hOp⟩ := hs2_op_bound (I := I) (M := M) hDim g
  let θ : ℝ := deTurckArmContractionThreshold'' (Module.finrank ℝ E)
  have hθ : 0 < θ := deTurckArmContractionThreshold''_pos (Module.finrank ℝ E)
  refine ⟨(θ / C, θ), div_pos hθ hC, le_rfl, ?_⟩
  intro T hT
  have htwo : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T :=
    tensorHs.ext (funext (fun _ ↦ rfl))
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ θ / C := by
    simpa only [htwo] using hT
  have hdelta : C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ θ := by
    calc
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ C * (θ / C) := mul_le_mul_of_nonneg_left hT' hC.le
      _ = θ := by field_simp
  have hsmall := hOp T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- In dimension three, a positive spectral `H3` radius gives the exact
realizability witness used by the Sobolev Ricci--DeTurck nonlinearity. -/
theorem lowreg_realize
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧
      p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
      ∀ (T : SmoothCcTensor g 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) p.2 := by
  obtain ⟨C, hC, hOp⟩ := hs2_op_bound (I := I) (M := M) hDim g
  let θ : ℝ := deTurckArmContractionThreshold'' (Module.finrank ℝ E)
  have hθ : 0 < θ := deTurckArmContractionThreshold''_pos (Module.finrank ℝ E)
  refine ⟨(θ / C, θ), div_pos hθ hC, le_rfl, ?_⟩
  intro T hT
  have htwo : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T :=
    tensorHs.ext (funext (fun _ ↦ rfl))
  have hthree : ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) T :=
    tensorHs.ext (funext (fun _ ↦ rfl))
  have hmono :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ :=
    ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ θ / C := by
    simpa only [hthree] using hT
  have hdelta :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ θ := by
    calc
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ :=
        mul_le_mul_of_nonneg_left hmono hC.le
      _ ≤ C * (θ / C) := mul_le_mul_of_nonneg_left hT' hC.le
      _ = θ := by field_simp
  have hsmall := hOp T
  intro x v w
  refine (hsmall x v w).trans ?_
  have hsv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta hsv) hsw

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
