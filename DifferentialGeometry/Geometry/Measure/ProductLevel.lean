import DifferentialGeometry.Geometry.Measure.ChartVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory TopologicalSpace
open scoped Manifold Topology ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Measure
open DifferentialGeometry DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance : MeasurableSpace (E × ℝ) := borel (E × ℝ)
private local instance : BorelSpace (E × ℝ) := ⟨rfl⟩
private local instance (U : Opens (M × ℝ)) : MeasurableSpace U := borel U
private local instance (U : Opens (M × ℝ)) : BorelSpace U := ⟨rfl⟩

private theorem modelHaar_snd_fiber_eq_zero (c : ℝ) :
    modelHaar (E := E × ℝ) {x | x.2 = c} = 0 := by
  let K : Submodule ℝ (E × ℝ) := (LinearMap.snd ℝ E ℝ).ker
  have hproper : K ≠ ⊤ := by
    intro h
    have hm : ((0 : E), (1 : ℝ)) ∈ K := by rw [h]; trivial
    simp [K] at hm
  have hzero := MeasureTheory.Measure.addHaar_submodule (modelHaar (E := E × ℝ)) K hproper
  have hset : {x : E × ℝ | x.2 = c} =
      (fun x : E × ℝ => x + (0, -c)) ⁻¹' (K : Set (E × ℝ)) := by
    ext x
    simp [K, ← sub_eq_add_neg, sub_eq_zero]
  rw [hset, measure_preimage_add_right, hzero]

theorem riemannianVolumeMeasure_snd_fiber_eq_zero
    [T2Space M] (U : Opens (M × ℝ)) [SigmaCompactSpace U]
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U) (c : ℝ) :
    riemannianVolumeMeasure (I.prod 𝓘(ℝ)) U g {x | x.val.2 = c} = 0 := by
  apply riemannianVolumeMeasure_eq_zero_of_chart_preimages g
    ((isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const).measurableSet)
  intro α
  apply measure_mono_null _ (modelHaar_snd_fiber_eq_zero (E := E) c)
  rintro u ⟨hu, ht⟩
  have heq := congrArg Prod.snd ((extChartAt (I.prod 𝓘(ℝ)) α).right_inv ht)
  change ((extChartAt (I.prod 𝓘(ℝ)) α).symm u).val.2 = u.2 at heq
  change u.2 = c
  exact heq.symm.trans hu
end DifferentialGeometry.Geometry.Measure
