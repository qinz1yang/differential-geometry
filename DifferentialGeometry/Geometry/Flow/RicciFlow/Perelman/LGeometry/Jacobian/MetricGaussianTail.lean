import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.GaussianTail
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory
open scoped ContDiff ENNReal Manifold

open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Integral.Measure

universe u uH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private theorem metricGram_eq_gramMatrixAt {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] (g : SmoothRiemannianMetric I X) (x : X) :
    (Matrix.of fun i k : Fin (Module.finrank ℝ E) =>
        g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)) =
      DifferentialGeometry.TensorMetric.gramMatrixAt (I := I) (M := X) g x := by
  ext i j
  simp only [Matrix.of_apply, DifferentialGeometry.TensorMetric.gramMatrixAt_apply,
    DifferentialGeometry.TensorMetric.modelInnerAt_apply]
  with_unfolding_all
    simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply]

private theorem metricGram_quadraticForm {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] (g : SmoothRiemannianMetric I X) (x : X) (Z : E) :
    inner ℝ (toEuclidean Z)
        (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ)
          (Matrix.of fun i k : Fin (Module.finrank ℝ E) =>
            g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k))
          (toEuclidean Z)) =
      g.inner x Z Z := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let v := toEuclidean Z
  have hw : Z = ∑ i, v i • b i := by
    have hvsum : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      let e := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
      simpa [e, EuclideanSpace.basisFun_apply] using (e.sum_repr v).symm
    calc
      Z = (toEuclidean (E := E)).symm v := ((toEuclidean (E := E)).symm_apply_apply Z).symm
      _ = (toEuclidean (E := E)).symm (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) :=
        congrArg _ hvsum
      _ = ∑ i, v i • b i := by
        rw [map_sum]
        simp only [b, map_smul, DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply]
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  change inner ℝ v (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ)
      (Matrix.of fun i k => B (b i) (b k)) v) = B Z Z
  rw [Matrix.inner_toEuclideanCLM, hw]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_uniform_tail_gaussian_metric_of_finrank_eq {n : ℕ}
    (hn : Module.finrank ℝ E = n) (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
      (g : SmoothRiemannianMetric I X) (x : X),
      ∫⁻ Z : E in {Z | R < Real.sqrt (g.inner x Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((n : ℝ) / 2))⁻¹ *
          Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ E) =>
            g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)).det *
          Real.exp (-g.inner x Z Z)) ∂(modelHaar (E := E)) ≤ eps := by
  classical
  subst hn
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    refine ⟨0, le_rfl, fun g x => ?_⟩
    have hempty : {Z : E | 0 < Real.sqrt (g.inner x Z Z)} = ∅ := by
      ext Z
      rw [Subsingleton.elim Z 0]
      change 0 < Real.sqrt ((g.inner x : E →L[ℝ] E →L[ℝ] ℝ) 0 0) ↔ False
      simp
    simpa only [hempty, Measure.restrict_empty, lintegral_zero_measure] using heps.le
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hdim⟩⟩
  obtain ⟨R, hR, htail⟩ := gaussianPosDef_uniform_tail
    (n := Fin (Module.finrank ℝ E)) eps heps
  refine ⟨R, hR, fun {H} _ {I} {X} _ _ _ g x => ?_⟩
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i k => g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
  have hA : A.PosDef := by
    rw [show A = _ from metricGram_eq_gramMatrixAt g x]
    exact DifferentialGeometry.TensorMetric.gramMatrixAt_posDef (I := I) (M := X) g x
  let e := toEuclidean (E := E)
  let sE : Set E := {Z | R < Real.sqrt (g.inner x Z Z)}
  let sU : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    {y | R < Real.sqrt (inner ℝ y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y))}
  let dens : E → ℝ≥0∞ := fun Z => ENNReal.ofReal ((Real.pi ^
    ((Module.finrank ℝ E : ℝ) / 2))⁻¹ * Real.sqrt A.det * Real.exp (-g.inner x Z Z))
  let G : E → ℝ≥0∞ := sE.indicator dens
  have hsE : MeasurableSet sE := by
    change MeasurableSet {Z : E | R < Real.sqrt ((g.inner x : E →L[ℝ] E →L[ℝ] ℝ) Z Z)}
    exact measurableSet_lt measurable_const (by fun_prop)
  have hsU : MeasurableSet sU :=
    measurableSet_lt measurable_const (by fun_prop)
  have hquad : ∀ y, g.inner x (e.symm y) (e.symm y) =
      inner ℝ y (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y) := by
    intro y
    have h := metricGram_quadraticForm g x (e.symm y)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hpoint : ∀ y, G (e.symm y) =
      sU.indicator (fun z => ENNReal.ofReal
        ((Real.pi ^ ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) / 2))⁻¹ *
          Real.sqrt A.det * Real.exp (-inner ℝ z
            (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A z)))) y := by
    intro y
    have hmem : e.symm y ∈ sE ↔ y ∈ sU := by
      change R < Real.sqrt (g.inner x (e.symm y) (e.symm y)) ↔ _
      rw [hquad]
      rfl
    by_cases hy : y ∈ sU
    · simp only [G, Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy, dens, hquad,
        Fintype.card_fin]
    · simp only [G, Set.indicator_of_notMem (fun h => hy (hmem.1 h)),
        Set.indicator_of_notMem hy]
  calc
    ∫⁻ Z : E in sE, dens Z ∂(modelHaar (E := E)) = ∫⁻ Z : E, G Z ∂(modelHaar (E := E)) := by
      rw [← lintegral_indicator hsE]
    _ = ∫⁻ y, G (e.symm y) ∂(Measure.map e (modelHaar (E := E))) := by
      symm
      refine (e.toHomeomorph.measurableEmbedding.lintegral_map _).trans ?_
      refine lintegral_congr fun Z => ?_
      change G (e.symm (e Z)) = G Z
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫⁻ y, G (e.symm y)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ∫⁻ y in sU, ENNReal.ofReal
          ((Real.pi ^ ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) / 2))⁻¹ *
            Real.sqrt A.det * Real.exp (-inner ℝ y
              (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y))) ∂volume := by
      rw [← lintegral_indicator hsU]
      exact lintegral_congr hpoint
    _ ≤ eps := htail A hA

theorem exists_uniform_tail_gaussian_metric (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {X : Type u} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
      [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ X]
      (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) X) (x : X),
      ∫⁻ Z : EuclideanSpace ℝ (Fin 3) in {Z | R < Real.sqrt (g.inner x Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
          Real.sqrt (Matrix.of fun i k :
              Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) =>
            g.inner x
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis
                (EuclideanSpace ℝ (Fin 3)) i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis
                (EuclideanSpace ℝ (Fin 3)) k)).det *
          Real.exp (-g.inner x Z Z)) ∂(modelHaar (E := EuclideanSpace ℝ (Fin 3))) ≤ eps := by
  obtain ⟨R, hR, htail⟩ := exists_uniform_tail_gaussian_metric_of_finrank_eq.{u, 0}
    (E := EuclideanSpace ℝ (Fin 3)) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)) eps heps
  exact ⟨R, hR, fun g x => by exact_mod_cast htail g x⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
