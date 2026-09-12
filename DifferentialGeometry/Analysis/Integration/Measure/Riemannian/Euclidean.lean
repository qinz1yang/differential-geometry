import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

set_option autoImplicit false

namespace DifferentialGeometry
namespace Integral
namespace Measure

open MeasureTheory Set Module
open scoped Manifold ContDiff ENNReal Matrix

section MeasureReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianMeasure_eq_sum_support
    (g : SmoothRiemannianMetric I M) (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : {α : M | (Function.support (ρ α)).Nonempty} =>
        (chartLocalMeasure (I := I) g α.val).withDensity
          (fun x => ENNReal.ofReal (ρ α.val x))) := by
  rw [riemannianMeasure_def]
  set s : Set M := {α : M | (Function.support (ρ α)).Nonempty} with hs
  have h := Measure.sum_add_sum_compl s
    (fun α : M => (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x)))
  rw [← h]
  have hzero : Measure.sum (fun i : ↥sᶜ =>
      (chartLocalMeasure (I := I) g i.val).withDensity
        (fun x : M => ENNReal.ofReal (ρ i.val x))) = 0 := by
    rw [Measure.sum_eq_zero]
    intro i
    have hρ : ∀ x : M, ρ i.val x = 0 := by
      intro x
      by_contra hne
      exact i.2 (Set.nonempty_iff_ne_empty.mpr (fun hempty => by
        have : x ∈ Function.support (ρ i.val) := hne
        rw [hempty] at this
        exact this.elim))
    have hfun : (fun x : M => ENNReal.ofReal (ρ i.val x)) = 0 := by
      funext x; rw [hρ x, ENNReal.ofReal_zero]; rfl
    rw [hfun, withDensity_zero]
  rw [hzero, add_zero]

end MeasureReduction

section EuclideanVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

open Tensor.Coordinates

omit [FiniteDimensional ℝ E] in
theorem extChartAt_modelWithCornersSelf (x₀ : E) :
    extChartAt 𝓘(ℝ, E) x₀ = PartialEquiv.refl E := by
  ext x <;> simp [chartAt_self_eq]

theorem chartBasisVecFiber_modelWithCornersSelf (x₀ x : E) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := 𝓘(ℝ, E)) x₀ i x = chartModelBasis E i := by
  rw [chartBasisVecFiber, TangentBundle.symmL_model_space]
  rfl

theorem chartDensity_euclideanMetric (x₀ x : E) :
    chartDensity (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) x₀ x =
      Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (chartModelBasis E i)
        (chartModelBasis E j))) := by
  have hgram : chartGramMatrix (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) x₀ x =
      Matrix.of (fun i j => inner ℝ (chartModelBasis E i) (chartModelBasis E j)) := by
    ext i j
    rw [chartGramMatrix_apply, euclideanMetric_inner,
      chartBasisVecFiber_modelWithCornersSelf x₀ x i,
      chartBasisVecFiber_modelWithCornersSelf x₀ x j]
    rfl
  rw [chartDensity, hgram]

theorem addHaar_withDensity_sqrt_det_gramMatrix_eq_volume
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    b.addHaar.withDensity (fun _ => ENNReal.ofReal (Real.sqrt
      (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j))))) =
      (volume : Measure E) := by
  classical
  have hu : (stdOrthonormalBasis ℝ E).toBasis.addHaar = (volume : Measure E) :=
    (stdOrthonormalBasis ℝ E).addHaar_eq_volume
  have hterm : ∀ (k i : Fin (Module.finrank ℝ E)),
      ((stdOrthonormalBasis ℝ E).toBasis.repr (b i)) k =
        inner ℝ (b i) ((stdOrthonormalBasis ℝ E) k) := by
    intro k i
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      real_inner_comm]
  have hgram : (Matrix.of fun i j => inner ℝ (b i) (b j)) =
      ((stdOrthonormalBasis ℝ E).toBasis.toMatrix b)ᵀ *
        ((stdOrthonormalBasis ℝ E).toBasis.toMatrix b) := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Basis.toMatrix_apply, hterm]
    rw [← OrthonormalBasis.sum_inner_mul_inner (stdOrthonormalBasis ℝ E) (b i) (b j)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_comm (b j) ((stdOrthonormalBasis ℝ E) k)]
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)) =
      ((stdOrthonormalBasis ℝ E).toBasis.det b) ^ 2 := by
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, sq]
    rw [Basis.det_apply]
  have hc : ENNReal.ofReal (Real.sqrt
      (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)))) =
      ENNReal.ofReal |((stdOrthonormalBasis ℝ E).toBasis.det b)| := by
    rw [hdet, Real.sqrt_sq_eq_abs]
  have hvol : (volume : Measure E) (b.parallelepiped : Set E) =
      ENNReal.ofReal |((stdOrthonormalBasis ℝ E).toBasis.det b)| := by
    rw [← hu]
    exact Measure.addHaar_parallelepiped (stdOrthonormalBasis ℝ E).toBasis b
  have huniq : (volume : Measure E) =
      ENNReal.ofReal |((stdOrthonormalBasis ℝ E).toBasis.det b)| • b.addHaar := by
    rw [Basis.addHaar_def, Measure.addHaarMeasure_unique (volume : Measure E) b.parallelepiped,
      hvol]
  rw [withDensity_const, hc, huniq]

theorem chartLocalMeasure_euclideanMetric (x₀ : E) :
    chartLocalMeasure (I := 𝓘(ℝ, E)) (M := E) (euclideanMetric (E := E)) x₀ =
      (volume : Measure E) := by
  rw [chartLocalMeasure_def, extChartAt_modelWithCornersSelf x₀]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_target, PartialEquiv.refl_coe,
    Measure.restrict_univ, Measure.map_id, id_eq]
  have hdens : (fun y : E => ENNReal.ofReal
      (chartDensity (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) x₀ y)) =
      (fun _ : E => ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j =>
        inner ℝ (chartModelBasis E i) (chartModelBasis E j))))) := by
    funext y
    rw [chartDensity_euclideanMetric]
  rw [hdens, modelHaar]
  exact addHaar_withDensity_sqrt_det_gramMatrix_eq_volume (chartModelBasis E)

end EuclideanVolume

section ModelSpaceVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem riemannianVolumeMeasure_euclideanMetric
    [T2Space E] [SigmaCompactSpace E] :
    riemannianVolumeMeasure (I := 𝓘(ℝ, E)) (M := E) (euclideanMetric (E := E)) =
      (volume : Measure E) := by
  classical
  set ρ : SmoothPartitionOfUnity E 𝓘(ℝ, E) E univ := chartAtlasPOU 𝓘(ℝ, E) E with hρ
  set T : Set E := {α : E | (Function.support (ρ α)).Nonempty} with hT
  have hC : Countable T :=
    (countable_nonempty_support_of_pou (I := 𝓘(ℝ, E)) ρ).to_subtype
  rw [riemannianVolumeMeasure_def, riemannianMeasure_eq_sum_support (I := 𝓘(ℝ, E)) _ ρ]
  have hp : (fun α : T => (chartLocalMeasure (I := 𝓘(ℝ, E)) (M := E)
        (euclideanMetric (E := E)) α.val).withDensity
        (fun x => ENNReal.ofReal (ρ α.val x))) =
      (fun α : T => (volume : Measure E).withDensity
        (fun x => ENNReal.ofReal (ρ α.val x))) :=
    funext fun α => by rw [chartLocalMeasure_euclideanMetric]
  rw [hp, ← @withDensity_tsum E _ (volume : Measure E) T hC
    (fun α : T => fun x : E => ENNReal.ofReal (ρ α.val x))
    (fun α => measurable_ofReal_pou_weight (I := 𝓘(ℝ, E)) ρ α.val)]
  have hsum : (∑' α : T, (fun x : E => ENNReal.ofReal (ρ α.val x))) = 1 := by
    funext x
    rw [tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)]
    have hsupp : Function.support (fun α : E => ENNReal.ofReal (ρ α x)) ⊆ T := by
      intro α hα
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hα
      refine Set.nonempty_iff_ne_empty.mpr ?_
      intro hempty
      have hzero : ρ α x = 0 := by
        by_contra hne
        have : x ∈ Function.support (ρ α) := hne
        rw [hempty] at this
        exact this.elim
      linarith
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    exact tsum_ofReal_pou_eq_one (I := 𝓘(ℝ, E)) ρ x
  rw [hsum, withDensity_one]

end ModelSpaceVolume

end Measure
end Integral
end DifferentialGeometry
