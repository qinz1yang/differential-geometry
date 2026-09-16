import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearResponse
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.SubcriticalSmallTime
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.StrongBackwardIdentification
import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap
import DifferentialGeometry.Analysis.Integration.Lp.PiLp
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.FiniteProduct

section

open scoped BigOperators ENNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]
variable {X Y : ι → Type*} [∀ i, SeminormedAddCommGroup (X i)] [∀ i, SeminormedAddCommGroup (Y i)]

private theorem piLp_two_dist_le_of_componentwise {C : ℝ} (hC : 0 ≤ C)
    (Φ : PiLp 2 X → PiLp 2 Y) {x x' : PiLp 2 X}
    (hΦ : ∀ i, dist (Φ x i) (Φ x' i) ≤ C * dist (x i) (x' i)) :
    dist (Φ x) (Φ x') ≤ C * dist x x' := by
  rw [PiLp.dist_eq_of_L2 (β := Y) (Φ x) (Φ x'), PiLp.dist_eq_of_L2 (β := X) x x']
  have hsum : (∑ i, dist (Φ x i) (Φ x' i) ^ 2) ≤
      C ^ 2 * (∑ i, dist (x i) (x' i) ^ 2) := by
    calc
      (∑ i, dist (Φ x i) (Φ x' i) ^ 2) ≤
          ∑ i, (C * dist (x i) (x' i)) ^ 2 :=
        Finset.sum_le_sum (fun i _ => by
          have hi := hΦ i
          nlinarith [(show 0 ≤ dist (Φ x i) (Φ x' i) from dist_nonneg),
            (show 0 ≤ dist (x i) (x' i) from dist_nonneg)])
      _ = C ^ 2 * (∑ i, dist (x i) (x' i) ^ 2) := by
        rw [Finset.mul_sum]
        simp_rw [mul_pow]
  have hleft : 0 ≤ Real.sqrt (∑ i, dist (Φ x i) (Φ x' i) ^ 2) := Real.sqrt_nonneg _
  have hright : 0 ≤ C * Real.sqrt (∑ i, dist (x i) (x' i) ^ 2) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (∑ i, dist (Φ x i) (Φ x' i) ^ 2) ^ 2 ≤
      (C * Real.sqrt (∑ i, dist (x i) (x' i) ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    exact hsum
  nlinarith

end DifferentialGeometry.Analysis

end

noncomputable section

open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def maximalRegularityDuhamelSolutionFieldPi (hT : 0 < T)
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T) :=
  WithLp.toLp 2 (fun i => maximalRegularityDuhamelSolutionField a hT (u₀ i) (F i))

def maximalRegularityDuhamelSolutionFieldHa1Pi (hT : 0 < T)
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T) :=
  WithLp.toLp 2 (fun i => maximalRegularityDuhamelSolutionFieldHa1 a hT (u₀ i) (F i))

theorem maximalRegularityDuhamelSolutionFieldPi_dist_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F F' : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    dist (maximalRegularityDuhamelSolutionFieldPi hT u₀ F)
        (maximalRegularityDuhamelSolutionFieldPi hT u₀ F') ≤ (1 + T) * dist F F' := by
  apply piLp_two_dist_le_of_componentwise (by linarith : 0 ≤ 1 + T)
  intro i
  change dist (maximalRegularityDuhamelSolutionField a hT (u₀ i) (F i))
      (maximalRegularityDuhamelSolutionField a hT (u₀ i) (F' i)) ≤ _
  simpa only [dist_eq_norm] using
    maximalRegularityDuhamelSolutionField_dist_le hT h_compact (u₀ i) (F i) (F' i)

theorem maximalRegularityDuhamelSolutionFieldHa1Pi_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F F' : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    dist (maximalRegularityDuhamelSolutionFieldHa1Pi hT u₀ F)
        (maximalRegularityDuhamelSolutionFieldHa1Pi hT u₀ F') ≤
      (2 * Real.sqrt T) * dist F F' := by
  apply piLp_two_dist_le_of_componentwise (by positivity : 0 ≤ 2 * Real.sqrt T)
  intro i
  change dist (maximalRegularityDuhamelSolutionFieldHa1 a hT (u₀ i) (F i))
      (maximalRegularityDuhamelSolutionFieldHa1 a hT (u₀ i) (F' i)) ≤ _
  simpa only [dist_eq_norm] using
    maximalRegularityDuhamelSolutionFieldHa1_dist_le hT hT1 h_compact (u₀ i) (F i) (F' i)

def maximalRegularityDuhamelMapPi (hT : 0 < T)
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    PiLp 2 (fun _ : ι => MaximalRegularitySolutionSpace (I := I) (M := M)
      (g := g) (r := r) (s := s) a T) :=
  WithLp.toLp 2 (fun i => maximalRegularityDuhamelMap a hT (u₀ i) (F i))

omit [Fintype ι] in
theorem maximalRegularityDuhamelMapPi_trace (hT : 0 < T)
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) (i : ι) :
    timeH1.trace0 _ T (maximalRegularityDuhamelMapPi hT u₀ F i) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (u₀ i) :=
  maximalRegularityDuhamelMap_trace0 hT (u₀ i) (F i)

omit [Fintype ι] in
theorem maximalRegularityDuhamelMapPi_timeDeriv (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) (i : ι) :
    timeH1.timeDeriv _ T (maximalRegularityDuhamelMapPi hT u₀ F i) =
      timeScaleLaplacian a (maximalRegularityDuhamelSolutionFieldPi hT u₀ F i) + F i :=
  maximalRegularityDuhamelMap_timeDeriv_eq hT h_compact (u₀ i) (F i)

theorem maximalRegularityDuhamelMapPi_dist_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F F' : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    dist (maximalRegularityDuhamelMapPi hT u₀ F)
        (maximalRegularityDuhamelMapPi hT u₀ F') ≤ 2 * dist F F' := by
  apply piLp_two_dist_le_of_componentwise (by norm_num : (0 : ℝ) ≤ 2)
  intro i
  change dist (maximalRegularityDuhamelMap a hT (u₀ i) (F i))
      (maximalRegularityDuhamelMap a hT (u₀ i) (F' i)) ≤ _
  simpa only [dist_eq_norm] using
    maximalRegularityDuhamelMap_dist_le hT h_compact (u₀ i) (F i) (F' i)

omit [Fintype ι] in
theorem timeL2Inclusion_maximalRegularityDuhamelSolutionFieldPi
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith))
      (maximalRegularityDuhamelSolutionFieldPi hT u₀ F) =
        maximalRegularityDuhamelSolutionFieldHa1Pi hT u₀ F := by
  apply PiLp.ext
  intro i
  exact timeL2Inclusion_maximalRegularityDuhamelSolutionField hT hT1 (u₀ i) (F i)

omit [Fintype ι] in
theorem maximalRegularityDuhamelSolutionFieldPi_zero_zero
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T) :
    maximalRegularityDuhamelSolutionFieldPi (I := I) (M := M) (g := g)
      (r := r) (s := s) (a := a) (ι := ι) hT (fun _ => 0) 0 = 0 := by
  apply PiLp.ext
  intro i
  exact maximalRegularityDuhamelSolutionField_zero_zero hT

omit [Fintype ι] in
theorem maximalRegularityDuhamelSolutionFieldPi_sub (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs (I := I) (M := M) g r s (a + 2))
    (F F' : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    maximalRegularityDuhamelSolutionFieldPi hT u₀ F -
      maximalRegularityDuhamelSolutionFieldPi hT u₀ F' =
    maximalRegularityDuhamelSolutionFieldPi hT (fun _ => 0) (F - F') := by
  apply PiLp.ext
  intro i
  change maximalRegularityDuhamelSolutionField a hT (u₀ i) (F i) -
    maximalRegularityDuhamelSolutionField a hT (u₀ i) (F' i) =
    maximalRegularityDuhamelSolutionField a hT 0 (F i - F' i)
  rw [maximalRegularityDuhamelSolutionField_sub hT h_compact,
    maximalRegularityDuhamelSolutionField]
  have hz : maximalRegularityHomogeneousSolutionField a T
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) = 0 := by
    apply norm_le_zero_iff.mp
    simpa only [norm_zero, mul_zero] using
      maximalRegularityHomogeneousSolutionField_norm_le
        (I := I) (M := M) h_compact
        (0 : TensorHs (I := I) (M := M) g r s (a + 2)) hT.le
  rw [hz, zero_add]

theorem maximalRegularityDuhamelSolutionFieldPi_inclusion_Ha1_ae_pointwise_le
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T)
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs (I := I) (M := M) g r s a) T)) :
    ∀ᵐ t ∂(timeMeasure T),
      ‖WithLp.toLp 2 (fun i : ι =>
        (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)
          (maximalRegularityDuhamelSolutionField a hT 0 (F i))) t)‖ ≤
        Real.sqrt (1 + T) * ‖F‖ := by
  have hall : ∀ᵐ t ∂(timeMeasure T), ∀ i : ι,
      ‖(timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField a hT 0 (F i))) t‖ ≤
          Real.sqrt (1 + T) * ‖F i‖ := by
    apply (MeasureTheory.ae_all_iff).mpr
    intro i
    exact maximalRegularityDuhamelSolutionField_inclusion_Ha1_ae_pointwise_le hT (F i)
  filter_upwards [hall] with t ht
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (pow_le_pow_left₀ (norm_nonneg _) (ht i) 2).trans_eq (mul_pow _ _ _)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section

open scoped Manifold ContDiff ENNReal NNReal
open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def maximalRegularityDuhamelVectorField (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) T :=
  (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
    (maximalRegularityDuhamelSolutionFieldPi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F))

def maximalRegularityDuhamelVectorFieldHa1 (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) T :=
  (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
    (maximalRegularityDuhamelSolutionFieldHa1Pi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F))

def maximalRegularityDuhamelVectorMap (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T :=
  timeH1.piLpEquiv.symm
    (maximalRegularityDuhamelMapPi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F))

theorem maximalRegularityDuhamelVectorMap_trace0 (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    timeH1.trace0 _ T (maximalRegularityDuhamelVectorMap hT u₀ F) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith)) u₀ := by
  apply PiLp.ext
  intro i
  exact maximalRegularityDuhamelMapPi_trace hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i

theorem maximalRegularityDuhamelVectorField_dist_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F F' : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    dist (maximalRegularityDuhamelVectorField hT u₀ F)
        (maximalRegularityDuhamelVectorField hT u₀ F') ≤ (1 + T) * dist F F' := by
  simpa only [maximalRegularityDuhamelVectorField, LinearIsometryEquiv.dist_map] using
    maximalRegularityDuhamelSolutionFieldPi_dist_le hT h_compact u₀
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F')

theorem maximalRegularityDuhamelVectorFieldHa1_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F F' : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    dist (maximalRegularityDuhamelVectorFieldHa1 hT u₀ F)
        (maximalRegularityDuhamelVectorFieldHa1 hT u₀ F') ≤
          (2 * Real.sqrt T) * dist F F' := by
  simpa only [maximalRegularityDuhamelVectorFieldHa1, LinearIsometryEquiv.dist_map] using
    maximalRegularityDuhamelSolutionFieldHa1Pi_dist_le hT hT1 h_compact u₀
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F')

theorem maximalRegularityDuhamelVectorField_ae (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    (maximalRegularityDuhamelVectorField hT u₀ F : ℝ → _) =ᵐ[timeMeasure T]
      fun t => WithLp.toLp 2 (fun i => maximalRegularityDuhamelSolutionField a hT
        (u₀ i) ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i) t) :=
  Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) _

theorem maximalRegularityDuhamelVectorField_zero_zero
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T) :
    maximalRegularityDuhamelVectorField (I := I) (M := M) (g := g)
      (r := r) (s := s) (a := a) (ι := ι) hT 0 0 = 0 := by
  simp only [maximalRegularityDuhamelVectorField, map_zero]
  change (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm (maximalRegularityDuhamelSolutionFieldPi hT (fun _ : ι => 0) 0) = 0
  rw [maximalRegularityDuhamelSolutionFieldPi_zero_zero hT, map_zero]

theorem maximalRegularityDuhamelVectorField_sub (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F F' : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    maximalRegularityDuhamelVectorField hT u₀ F -
      maximalRegularityDuhamelVectorField hT u₀ F' =
        maximalRegularityDuhamelVectorField hT 0 (F - F') := by
  simp only [maximalRegularityDuhamelVectorField, map_sub]
  rw [← map_sub, maximalRegularityDuhamelSolutionFieldPi_sub hT h_compact]
  congr 2

theorem norm_maximalRegularityDuhamelVectorField_zero_le
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    ‖maximalRegularityDuhamelVectorField hT
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) F‖ ≤
        (1 + T) * ‖F‖ := by
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := I) (M := M) g r s
  have h := maximalRegularityDuhamelVectorField_dist_le hT hc
    (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) F 0
  simpa only [maximalRegularityDuhamelVectorField_zero_zero, dist_zero_right] using h

theorem maximalRegularityDuhamelVectorMap_timeDeriv_eq (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    timeH1.timeDeriv _ T (maximalRegularityDuhamelVectorMap hT u₀ F) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F) + F := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [map_add, Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  change Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)
    ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
      (WithLp.toLp 2 (fun i =>
        (maximalRegularityDuhamelMapPi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i).deriv))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  unfold maximalRegularityDuhamelVectorField
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact maximalRegularityDuhamelMapPi_timeDeriv hT h_compact u₀
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i

theorem maximalRegularityDuhamelVectorMap_dist_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F F' : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    dist (maximalRegularityDuhamelVectorMap hT u₀ F)
        (maximalRegularityDuhamelVectorMap hT u₀ F') ≤ 2 * dist F F' := by
  simpa only [maximalRegularityDuhamelVectorMap, LinearIsometryEquiv.dist_map] using
    maximalRegularityDuhamelMapPi_dist_le hT h_compact u₀
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F')

theorem timeL2Inclusion_maximalRegularityDuhamelVectorField
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T)
          (maximalRegularityDuhamelVectorField hT u₀ F) =
        maximalRegularityDuhamelVectorFieldHa1 hT u₀ F := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  simp only [maximalRegularityDuhamelVectorField, maximalRegularityDuhamelVectorFieldHa1,
    LinearIsometryEquiv.apply_symm_apply]
  exact timeL2Inclusion_maximalRegularityDuhamelSolutionFieldPi hT hT1 u₀
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F)

theorem maximalRegularityDuhamelVectorField_Ha1_ae_pointwise_le
    [NeZero (Module.finrank ℝ E)] (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    ∀ᵐ t ∂(timeMeasure T),
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith))
        (maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) F t)‖ ≤
        Real.sqrt (1 + T) * ‖F‖ := by
  let G := Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F
  let J := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show a + 1 ≤ a + 2 by linarith)
  have hcoord : ∀ᵐ t ∂(timeMeasure T), ∀ i : ι,
      (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField a hT 0 (G i))) t =
      J (maximalRegularityDuhamelSolutionField a hT 0 (G i) t) := by
    apply ae_all_iff.mpr
    intro i
    exact J.coeFn_compLpL (maximalRegularityDuhamelSolutionField a hT 0 (G i))
  have hfield := maximalRegularityDuhamelVectorField_ae hT
    (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) F
  have hbound := maximalRegularityDuhamelSolutionFieldPi_inclusion_Ha1_ae_pointwise_le hT G
  filter_upwards [hfield, hcoord, hbound] with t hft ht hb
  rw [hft]
  have heq : ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
      (WithLp.toLp 2 (fun i : ι => maximalRegularityDuhamelSolutionField a hT 0 (G i) t)) =
    WithLp.toLp 2 (fun i : ι =>
      (timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField a hT 0 (G i))) t) := by
    apply PiLp.ext
    intro i
    exact (ht i).symm
  change ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (WithLp.toLp 2 (fun i : ι => maximalRegularityDuhamelSolutionField a hT 0 (G i) t))‖ ≤ _
  rw [heq]
  simpa only [G, LinearIsometryEquiv.norm_map] using hb

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def maximalRegularityVectorFieldL (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T →L[ℝ]
      timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) T :=
  (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => maximalRegularitySolutionFieldL a hT)).comp
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem maximalRegularityVectorFieldL_eq_duhamel (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    maximalRegularityVectorFieldL a hT.le F = maximalRegularityDuhamelVectorField hT
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) F := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  change Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)
    ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => maximalRegularitySolutionFieldL a hT.le)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F))) =
    Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
      (maximalRegularityDuhamelSolutionFieldPi hT (fun _ : ι => 0)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F)))
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact maximalRegularitySolutionFieldL_eq_duhamel hT _

theorem maximalRegularityVectorFieldL_norm_le (hT : 0 < T) :
    ‖maximalRegularityVectorFieldL (I := I) (M := M) (g := g)
      (r := r) (s := s) (ι := ι) a hT.le‖ ≤ 1 + T := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro F
  rw [maximalRegularityVectorFieldL_eq_duhamel hT]
  exact norm_maximalRegularityDuhamelVectorField_zero_le hT F

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem maximalRegularityDuhamelVectorField_toFunL2 (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T)
          (maximalRegularityDuhamelVectorField hT u₀ F) =
        (maximalRegularityDuhamelVectorMap hT u₀ F).toFunL2 := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  simp only [maximalRegularityDuhamelVectorField, maximalRegularityDuhamelVectorMap,
    timeH1.piLpEquiv_symm_toFunL2, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact duhamelField_pin hT h_compact (u₀ i) (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_eq_duhamel_vector (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) T)
    (htrace : timeH1.trace0 _ T u =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)) u₀)
    (hlink : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
          2 (timeMeasure T) field = u.toFunL2)
    (heq : timeH1.timeDeriv _ T u =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T) field + F) :
    field = maximalRegularityDuhamelVectorField hT u₀ F ∧
      u = maximalRegularityDuhamelVectorMap hT u₀ F := by
  have hcomponent (i : ι) := strongPair_eq_duhamel hT hc (u₀ i)
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i) (timeH1.piLpEquiv u i)
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) field i)
  have hparts (i : ι) :
      Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) field i =
        maximalRegularityDuhamelSolutionField a hT (u₀ i)
          (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i) ∧
      timeH1.piLpEquiv u i = maximalRegularityDuhamelMap a hT (u₀ i)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i) := by
    apply hcomponent i
    · exact congrArg (fun x => x i) htrace
    · have h := congrArg (fun x => Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) x i) hlink
      rw [Lp.piLpEquiv_compLpL] at h
      simpa only [ContinuousLinearMap.piLpMap_apply, timeH1.toTimeL2_apply,
        timeH1.piLpEquiv_toFunL2, timeL2Inclusion] using h
    · have h := congrArg (fun x => Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) x i) heq
      rw [map_add, Lp.piLpEquiv_compLpL] at h
      exact h
  constructor
  · apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
    change _ = (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T))
      ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm _)
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact PiLp.ext fun i => (hparts i).1
  · apply timeH1.piLpEquiv.injective
    change _ = timeH1.piLpEquiv (timeH1.piLpEquiv.symm _)
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact PiLp.ext fun i => (hparts i).2

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
