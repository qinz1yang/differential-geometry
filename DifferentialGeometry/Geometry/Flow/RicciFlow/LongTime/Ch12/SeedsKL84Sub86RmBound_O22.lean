import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum

/-!
# CH12-O22 G2 (b3): Hamilton–Ivey pinching and a scalar upper bound control `|Rm|`

Pointwise and at metric level (KL Sub86.3, step "HI ⇒ |Rm|"): in dimension three the scalar
curvature is twice the sum of the ordered sectional curvatures (the curvature operator
eigenvalues `k₀ ≥ k₁ ≥ k₂`); a lower bound `k₂ ≥ -L` and `R ≤ Rb` give `|kᵢ| ≤ Rb/2 + 2L`, hence
`|Rm| ≤ 2√3 (Rb/2 + 2L)`.  With an admissible pinching function `Phi` and `R ≤ M`, `M ≥ 1`, one
has `Phi R ≤ Phi M ≤ Phi 1 · M`, so `|Rm| ≤ √3 (1 + 4 Phi 1) M`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [T2Space M]

/-- Metric-level form of `R = 2 Σ kᵢ` (ordered sectional curvatures in an orthonormal basis). -/
theorem metricScalarAt_eq_two_mul_sum_orderedSectional_O22
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis) :
    metricScalarAt (I := I) (M := M) g x =
      2 * ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis
        (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) i := by
  rw [← traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt g x basis horth,
    traceNormalizedMetricCurvatureOperatorMatrixAt,
    traceNormalizedCurvatureOperatorMatrixAt_trace_eq_twice_sectionalSum,
    ← curvatureOperatorMatrixAt_trace_eq_sectionalSum,
    curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt]

/-- (b3), linear form: curvature operator `≥ -L` and `R ≤ Rb` give `|Rm| ≤ 2√3 (Rb/2 + 2L)`. -/
theorem sqrt_normSq_le_of_lowerBound_O22
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {L Rb : ℝ} (hL : 0 ≤ L) (hRb : 0 ≤ Rb)
    (hlow : curvatureOperatorLowerBoundAt (I := I) g x
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) L)
    (hR : metricScalarAt (I := I) (M := M) g x ≤ Rb) :
    Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) (M := M) g x)) ≤
      2 * Real.sqrt 3 * (Rb / 2 + 2 * L) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdim
  set A := metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x with hA
  have hmin := (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I) g basis horth
    (A := A) (K := L)).mp hlow
  have hanti := orderedSectionalCurvaturesAt_antitone (I := I) x basis A
  have hscal := metricScalarAt_eq_two_mul_sum_orderedSectional_O22 g x basis horth
  rw [Fin.sum_univ_three] at hscal
  have h01 := hanti (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := hanti (show (1 : Fin 3) ≤ 2 by decide)
  have hub : ∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis A i| ≤ Rb / 2 + 2 * L := by
    intro i
    have hi2 := hanti (show i ≤ (2 : Fin 3) by fin_cases i <;> decide)
    have hi0 := hanti (Fin.zero_le i)
    rw [abs_le]
    constructor <;> linarith
  exact sqrt_normSq0S_le_of_abs_orderedSectionalCurvaturesAt_le (I := I) g x basis horth A hub

/-- (b3), pinching form: admissible `Phi`, curvature operator `≥ -Phi R`, `R ≤ M`, `1 ≤ M`
give `|Rm| ≤ √3 (1 + 4 Phi 1) M`. -/
theorem sqrt_normSq_le_of_pinching_O22 {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {Mb : ℝ} (hM : 1 ≤ Mb)
    (hlow : curvatureOperatorLowerBoundAt (I := I) g x
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x)
      (Phi (metricScalarAt (I := I) (M := M) g x)))
    (hR : metricScalarAt (I := I) (M := M) g x ≤ Mb) :
    Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) (M := M) g x)) ≤
      Real.sqrt 3 * (1 + 4 * Phi 1) * Mb := by
  have hMpos : 0 < Mb := lt_of_lt_of_le one_pos hM
  have hq : Phi Mb / Mb ≤ Phi 1 / 1 :=
    hPhi.quotientAntitoneOn (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr hMpos) hM
  have hPM : Phi Mb ≤ Phi 1 * Mb := by
    rw [div_one, div_le_iff₀ hMpos] at hq
    exact hq
  have hPR : Phi (metricScalarAt (I := I) (M := M) g x) ≤ Phi 1 * Mb :=
    (hPhi.mono hR).trans hPM
  have hlow' : curvatureOperatorLowerBoundAt (I := I) g x
      (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) (Phi 1 * Mb) := by
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdim
    rw [curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I) g basis horth] at hlow ⊢
    linarith
  have h := sqrt_normSq_le_of_lowerBound_O22 g x hdim
    (by have := hPhi.pos 1; positivity) hMpos.le hlow' hR
  have h3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  calc Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) (M := M) g x))
      ≤ 2 * Real.sqrt 3 * (Mb / 2 + 2 * (Phi 1 * Mb)) := h
    _ = Real.sqrt 3 * (1 + 4 * Phi 1) * Mb := by ring

end GC.LongTime.Ch12
