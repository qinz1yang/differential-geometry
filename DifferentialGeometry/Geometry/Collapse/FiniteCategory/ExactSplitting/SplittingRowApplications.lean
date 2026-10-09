import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingRow
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameExamples

/-!
# Consumers of the LFR11 row

* `exactSplitting_curvature_and_product`: the (Ψ)-metric and (sec) clauses read off the row
  for a nonnegatively curved exact splitting;
* `realFrame_exactSplitting_regularity`: the whole row for the actual real-line splitting
  `ℝ ≃ᵢ ℓ²(ℝ × PUnit)` of the tier-T3 examples, with no geometric input.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section General

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

/-- A nonnegatively curved exact splitting: the actual product diffeomorphism pulls `g` back to
`du² + h`, and `h` is nonnegatively curved. -/
theorem exactSplitting_curvature_and_product
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y))
    (hsec : ∀ (x : M) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    (∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      g.inner (splittingProductDiffeomorph g hr hnorm e p)
        (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p v)
        (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric g hr hnorm e).inner p.2 v.2 w.2) ∧
    ∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
      0 ≤ (inducedMetric g hr hnorm e).sectionalCurvature z v w := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hmet, -, hnn⟩ :=
    exactSplitting_regularity g hr hnorm e
  exact ⟨hmet, hnn hsec⟩

end General

section RealLine

local instance nezero_finrank_real_row_F7LFR11b : NeZero (Module.finrank ℝ ℝ) :=
  ⟨by rw [Module.finrank_self]; decide⟩

private theorem realFrame_enorm_row_F7LFR11b : ∀ (x : ℝ) (w : TangentSpace 𝓘(ℝ, ℝ) x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner x w w)) := by
  intro x w
  change ‖(w : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (w : ℝ) w))
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

/-- The LFR11 row for the actual real-line splitting `ℝ ≃ᵢ ℓ²(ℝ × PUnit)`: its zero factor is
complete, and the product map is a `C⁴` diffeomorphism with the stated value. -/
theorem realFrame_exactSplitting_regularity :
    letI := splittingFactorChartedSpace (r := 2) realFrameMetric le_rfl
      realFrame_enorm_row_F7LFR11b realFrameSplitting.{0}
    letI := splittingFactor_isManifold_one (r := 2) realFrameMetric le_rfl
      realFrame_enorm_row_F7LFR11b realFrameSplitting.{0}
    CompleteSpace {x : ℝ // (realFrameSplitting.{0} x).fst = 0} ∧
      ∀ p : ℝ × {x : ℝ // (realFrameSplitting.{0} x).fst = 0},
        splittingProductDiffeomorph (r := 2) realFrameMetric le_rfl realFrame_enorm_row_F7LFR11b
            realFrameSplitting.{0} p =
          realFrameSplitting.{0}.symm (toLp 2 (p.1, (realFrameSplitting.{0} p.2.val).snd)) := by
  obtain ⟨-, -, -, -, -, -, -, hc, -, -, -, -, hval, -⟩ :=
    exactSplitting_regularity (r := 2) realFrameMetric le_rfl realFrame_enorm_row_F7LFR11b
      realFrameSplitting.{0}
  exact ⟨hc, hval⟩

end RealLine

end DifferentialGeometry.Geometry.ExactSplitting
