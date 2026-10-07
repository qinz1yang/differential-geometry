import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal
namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}

/-- A map that is locally distance non-increasing (for the length distances of two smooth
Riemannian metrics on three-manifolds) at every point of a measurable set `A` does not increase
Riemannian volume: `vol_h (f '' A) ≤ vol_g A`.  Route: `ℋ³ = vol` on both sides
(`lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure`), a countable
disjointed cover of `A`, and `normalizedHausdorffMeasure_image_le`. -/
theorem riemannianVolumeMeasure_image_le_of_local_edist_le_S14
    (hE : Module.finrank ℝ E = 3) (hF : Module.finrank ℝ F = 3)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T3Space X]
    [SigmaCompactSpace X] [SecondCountableTopology X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y] [T3Space Y]
    [SigmaCompactSpace Y]
    (g : SmoothRiemannianMetric I X) (h : SmoothRiemannianMetric J Y) (f : X → Y)
    {A : Set X} (hA : MeasurableSet[borel X] A)
    (hloc : ∀ x ∈ A, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ riemannianEDistOf g y z) :
    riemannianVolumeMeasure J Y h (f '' A) ≤ riemannianVolumeMeasure I X g A := by
  classical
  let : EMetricSpace X := inducedEMetricSpace g
  let : EMetricSpace Y := inducedEMetricSpace h
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  have hX : (normalizedHausdorffMeasure 3 : Measure X) = riemannianVolumeMeasure I X g :=
    lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure (I := I) (M := X) g hE
  have hY : (normalizedHausdorffMeasure 3 : Measure Y) = riemannianVolumeMeasure J Y h :=
    lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure (I := J) (M := Y) h hF
  rw [← hX, ← hY]
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  choose! U hU hUle using hloc
  obtain ⟨t, htA, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := A)
    (f := fun x => interior (U x))
    (fun x hx => mem_nhdsWithin_of_mem_nhds (interior_mem_nhds.mpr (hU x hx)))
  obtain ⟨x0, hx0A⟩ := hne
  have htne : t.Nonempty := by
    have := hcov hx0A
    simp only [mem_iUnion] at this
    obtain ⟨x, hx, _⟩ := this
    exact ⟨x, hx⟩
  obtain ⟨c, hc⟩ := htc.exists_eq_range htne
  let S : ℕ → Set X := fun n => A ∩ interior (U (c n))
  have hcA : ∀ n, c n ∈ A := fun n => htA (hc ▸ mem_range_self n)
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
    hA.inter isOpen_interior.measurableSet
  have hAS : A = ⋃ n, S n := by
    ext x
    constructor
    · intro hx
      have := hcov hx
      simp only [mem_iUnion] at this
      obtain ⟨y, hy, hxy⟩ := this
      rw [hc] at hy
      obtain ⟨n, rfl⟩ := hy
      exact mem_iUnion.mpr ⟨n, hx, hxy⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.1
  let B : ℕ → Set X := disjointed S
  have hBmeas : ∀ n, MeasurableSet (B n) := MeasurableSet.disjointed hSmeas
  have hBdisj : Pairwise (Function.onFun Disjoint B) := disjoint_disjointed S
  have hAB : A = ⋃ n, B n := by rw [iUnion_disjointed, ← hAS]
  have hlip : ∀ n, LipschitzOnWith 1 f (B n) := by
    intro n
    intro y hy z hz
    rw [ENNReal.coe_one, one_mul]
    have hyU : y ∈ U (c n) := interior_subset (disjointed_subset S n hy).2
    have hzU : z ∈ U (c n) := interior_subset (disjointed_subset S n hz).2
    exact hUle (c n) (hcA n) y hyU z hzU
  calc (normalizedHausdorffMeasure 3 : Measure Y) (f '' A)
      = (normalizedHausdorffMeasure 3 : Measure Y) (⋃ n, f '' B n) := by
        rw [hAB, image_iUnion]
    _ ≤ ∑' n, (normalizedHausdorffMeasure 3 : Measure Y) (f '' B n) := measure_iUnion_le _
    _ ≤ ∑' n, (normalizedHausdorffMeasure 3 : Measure X) (B n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        have := normalizedHausdorffMeasure_image_le (hlip n) 3
        simpa using this
    _ = (normalizedHausdorffMeasure 3 : Measure X) (⋃ n, B n) :=
        (measure_iUnion hBdisj hBmeas).symm
    _ = (normalizedHausdorffMeasure 3 : Measure X) A := by rw [← hAB]

end GC.LongTime.Ch12
