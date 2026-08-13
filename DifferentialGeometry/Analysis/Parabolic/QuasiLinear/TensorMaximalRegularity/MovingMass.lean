import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperator
import Mathlib.Topology.MetricSpace.Contracting
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a T : ℝ}
private abbrev Ha (a : ℝ) := tensorHs (I := I) (M := M) g r s a
private abbrev ET (a T : ℝ) :=
  MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := r) (s := s) a T
noncomputable def massForce
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (u : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T) :
    timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T :=
  f + timeOp B hB C hC
    (timeH1.timeDeriv
      (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T u)

noncomputable def massDuh
    (hT : 0 < T) (hT1 : T ≤ 1)
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (u : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T) :
    ET (I := I) (M := M) (g := g) (r := r) (s := s) a T :=
  maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀
    (massForce B hB C hC f u)

omit [NeZero (Module.finrank ℝ E)] in
theorem massForce_sub
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (u v : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T) :
    massForce B hB C hC f u - massForce B hB C hC f v =
      timeOp B hB C hC
        (timeH1.timeDeriv
          (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T (u - v)) := by
  simp only [massForce, map_sub]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem massForce_bound
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (u v : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T) :
    ‖massForce B hB C hC f u - massForce B hB C hC f v‖ ≤
      (C : ℝ) * ‖u - v‖ := by
  rw [massForce_sub]
  calc
    ‖timeOp B hB C hC
        (timeH1.timeDeriv
          (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T (u - v))‖
        ≤ ‖timeOp B hB C hC‖ *
            ‖timeH1.timeDeriv
              (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T (u - v)‖ :=
      (timeOp B hB C hC).le_opNorm _
    _ ≤ (C : ℝ) *
          ‖timeH1.timeDeriv
            (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T (u - v)‖ := by
      gcongr
      exact timeOp_norm_le B hB C hC
    _ ≤ (C : ℝ) * ‖u - v‖ := by
      exact mul_le_mul_of_nonneg_left
        (timeH1.norm_deriv_le (u - v)) C.coe_nonneg

omit [NeZero (Module.finrank ℝ E)] in
theorem massDuh_diff
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (u v : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T) :
    ‖massDuh hT hT1 B hB C hC u₀ f u -
        massDuh hT hT1 B hB C hC u₀ f v‖ ≤
      (2 * (C : ℝ)) * ‖u - v‖ := by
  calc
    ‖massDuh hT hT1 B hB C hC u₀ f u -
        massDuh hT hT1 B hB C hC u₀ f v‖
        ≤ 2 * ‖massForce B hB C hC f u - massForce B hB C hC f v‖ := by
      exact maxRegDuhamelMap_dist_le (I := I) (M := M)
        (h_compact := h_compact) (a := a) hT hT1 u₀ _ _
    _ ≤ 2 * ((C : ℝ) * ‖u - v‖) := by
      gcongr
      exact massForce_bound B hB C hC f u v
    _ = (2 * (C : ℝ)) * ‖u - v‖ := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem massDuh_contract
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (hsmall : 2 * (C : ℝ) < 1) :
    ContractingWith (2 * C)
      (massDuh hT hT1 B hB C hC u₀ f) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using hsmall
  · intro u v
    rw [dist_eq_norm, dist_eq_norm]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      massDuh_diff h_compact hT hT1 B hB C hC u₀ f u v

omit [NeZero (Module.finrank ℝ E)] in
theorem massDuh_exists
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (hsmall : 2 * (C : ℝ) < 1) :
    ∃! u : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T,
      massDuh hT hT1 B hB C hC u₀ f u = u := by
  let Φ := massDuh hT hT1 B hB C hC u₀ f
  have hcontr : ContractingWith (2 * C) Φ :=
    massDuh_contract h_compact hT hT1 B hB C hC u₀ f hsmall
  let uStar := ContractingWith.fixedPoint Φ hcontr
  refine ⟨uStar, ContractingWith.fixedPoint_isFixedPt hcontr, ?_⟩
  intro v hv
  exact ContractingWith.fixedPoint_unique hcontr hv

omit [NeZero (Module.finrank ℝ E)] in
theorem massDuh_trace
    (hT : 0 < T) (hT1 : T ≤ 1)
    (B : ℝ → Ha (I := I) (M := M) (g := g) (r := r) (s := s) a →L[ℝ]
      Ha (I := I) (M := M) (g := g) (r := r) (s := s) a)
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (C : ℝ≥0) (hC : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (C : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T)
    (u : ET (I := I) (M := M) (g := g) (r := r) (s := s) a T)
    (hu : massDuh hT hT1 B hB C hC u₀ f u = u) :
    timeH1.trace0
        (Ha (I := I) (M := M) (g := g) (r := r) (s := s) a) T u =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) u₀ := by
  rw [← hu]
  exact maxRegDuhamelMap_trace0 (I := I) (M := M)
    (a := a) hT hT1 u₀ (massForce B hB C hC f u)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
