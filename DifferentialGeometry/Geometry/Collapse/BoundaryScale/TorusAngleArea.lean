import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The area of the torus in angle coordinates (statement V.1, step 2)

The angle map `torusAngleParam u = (exp u₁, exp u₂) : E₂ → T² = Circle × Circle`, with source the
model vector space `E₂ = ℝ¹ × ℝ¹` of `torusModel` (the area formula needs source = model space), is
smooth,
injective on the half-open fundamental domain `torusAngleDomain = (-π, π]²` and maps it onto `T²`.
By the injective `C¹` area formula (`riemannianVolumeMeasure_image_eq`), for every Riemannian
metric `g_T` on the torus and every Borel set `B`:
`vol_{g_T}(B) = ∫⁻_{φ⁻¹B ∩ (-π, π]²} ρ_T dmodelHaar` with `ρ_T = paramDensity g_T φ`
(`riemannianVolumeMeasure_torus_eq_setLIntegral`), i.e. `vol_{g_T}` is the push-forward of
`ρ_T · modelHaar|_{(-π, π]²}` (`riemannianVolumeMeasure_torus_eq_map`).

`E₂` carries `borel E₂` (the σ-algebra of `modelHaar`), the torus `borel Torus` (that of
`riemannianVolumeMeasure`); both are local instances of this file.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open DifferentialGeometry.Integral.Measure GC.Endpoint
open scoped Manifold ContDiff ENNReal Real

namespace DifferentialGeometry.Geometry.Collapse

local notation "E₂" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

private local instance instMeasE₂ : MeasurableSpace E₂ := borel E₂
private local instance instBorelE₂ : BorelSpace E₂ := ⟨rfl⟩
private local instance instMeasTorus : MeasurableSpace Torus := borel Torus
private local instance instBorelTorus : BorelSpace Torus := ⟨rfl⟩

/-- The angle parametrisation of the torus from its model vector space, `u ↦ (exp u₁, exp u₂)`. -/
def torusAngleParam (u : E₂) : Torus := (Circle.exp (u.1 0), Circle.exp (u.2 0))

/-- The half-open fundamental domain `(-π, π]²` of the angle parametrisation. -/
def torusAngleDomain : Set E₂ := {u | u.1 0 ∈ Ioc (-π) π ∧ u.2 0 ∈ Ioc (-π) π}

theorem contMDiff_torusAngleParam : ContMDiff 𝓘(ℝ, E₂) torusModel ∞ torusAngleParam := by
  have h1 : ContMDiff 𝓘(ℝ, E₂) 𝓘(ℝ, ℝ) ∞ (fun u : E₂ => u.1 0) :=
    ((EuclideanSpace.proj (0 : Fin 1)).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))).contDiff.contMDiff
  have h2 : ContMDiff 𝓘(ℝ, E₂) 𝓘(ℝ, ℝ) ∞ (fun u : E₂ => u.2 0) :=
    ((EuclideanSpace.proj (0 : Fin 1)).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))).contDiff.contMDiff
  exact (contMDiff_circleExp.comp h1).prodMk (contMDiff_circleExp.comp h2)

theorem continuous_torusAngleParam : Continuous torusAngleParam :=
  contMDiff_torusAngleParam.continuous

theorem euclideanSpace_fin_one_ext {x y : EuclideanSpace ℝ (Fin 1)} (h : x 0 = y 0) : x = y := by
  ext i
  rw [Subsingleton.elim i 0]
  exact h

theorem injOn_torusAngleParam : InjOn torusAngleParam torusAngleDomain := by
  intro u hu u' hu' h
  simp only [torusAngleParam, Prod.mk.injEq] at h
  have hπ : π - -π ≤ 2 * π := by linarith
  exact Prod.ext (euclideanSpace_fin_one_ext (Circle.exp_injOn_Ioc hπ hu.1 hu'.1 h.1))
    (euclideanSpace_fin_one_ext (Circle.exp_injOn_Ioc hπ hu.2 hu'.2 h.2))

theorem exists_mem_torusAngleDomain_eq (t : Torus) :
    ∃ u ∈ torusAngleDomain, torusAngleParam u = t := by
  obtain ⟨a, ha, hat⟩ := Circle.surjOn_exp_neg_pi_pi (mem_univ t.1)
  obtain ⟨b, hb, hbt⟩ := Circle.surjOn_exp_neg_pi_pi (mem_univ t.2)
  exact ⟨(WithLp.toLp 2 (fun _ => a), WithLp.toLp 2 (fun _ => b)), ⟨ha, hb⟩, Prod.ext hat hbt⟩

theorem measurableSet_torusAngleDomain : MeasurableSet[borel E₂] torusAngleDomain := by
  have h1 : Continuous (fun u : E₂ => u.1 0) := by fun_prop
  have h2 : Continuous (fun u : E₂ => u.2 0) := by fun_prop
  exact (h1.measurable measurableSet_Ioc).inter (h2.measurable measurableSet_Ioc)

theorem measurable_torusAngleParam :
    @Measurable E₂ Torus (borel E₂) (borel Torus) torusAngleParam :=
  continuous_torusAngleParam.measurable

/-- `torusAngleParam` maps `φ⁻¹ B ∩ (-π, π]²` onto `B`. -/
theorem image_preimage_inter_torusAngleDomain (B : Set Torus) :
    torusAngleParam '' (torusAngleParam ⁻¹' B ∩ torusAngleDomain) = B := by
  ext t
  constructor
  · rintro ⟨u, ⟨huB, -⟩, rfl⟩
    exact huB
  · intro ht
    obtain ⟨u, hu, rfl⟩ := exists_mem_torusAngleDomain_eq t
    exact ⟨u, ⟨ht, hu⟩, rfl⟩

theorem contMDiffOn_one_torusAngleParam :
    ContMDiffOn 𝓘(ℝ, E₂) torusModel 1 torusAngleParam univ :=
  (contMDiff_torusAngleParam.of_le (by exact_mod_cast le_top)).contMDiffOn

/-- **Torus area in angle coordinates.** For every Riemannian metric on the torus and every Borel
set `B`, `vol(B) = ∫⁻_{φ⁻¹B ∩ (-π, π]²} paramDensity g_T φ dmodelHaar`. -/
theorem riemannianVolumeMeasure_torus_eq_setLIntegral (gT : SmoothRiemannianMetric torusModel Torus)
    {B : Set Torus} (hB : MeasurableSet[borel Torus] B) :
    riemannianVolumeMeasure torusModel Torus gT B =
      ∫⁻ u in torusAngleParam ⁻¹' B ∩ torusAngleDomain,
        ENNReal.ofReal (paramDensity gT torusAngleParam u) ∂(modelHaar (E := E₂)) := by
  have hmeas : MeasurableSet (torusAngleParam ⁻¹' B ∩ torusAngleDomain) :=
    (measurable_torusAngleParam hB).inter measurableSet_torusAngleDomain
  conv_lhs => rw [← image_preimage_inter_torusAngleDomain B]
  exact riemannianVolumeMeasure_image_eq gT isOpen_univ hmeas (subset_univ _)
    contMDiffOn_one_torusAngleParam (injOn_torusAngleParam.mono inter_subset_right)

theorem continuous_paramDensity_torusAngleParam (gT : SmoothRiemannianMetric torusModel Torus) :
    Continuous (paramDensity gT torusAngleParam) :=
  continuousOn_univ.mp (continuousOn_paramDensity gT isOpen_univ contMDiffOn_one_torusAngleParam)

/-- **The torus volume is the push-forward of the angle density.** -/
theorem riemannianVolumeMeasure_torus_eq_map (gT : SmoothRiemannianMetric torusModel Torus) :
    riemannianVolumeMeasure torusModel Torus gT =
      @Measure.map E₂ Torus (borel E₂) (borel Torus) torusAngleParam
        (((modelHaar (E := E₂)).restrict torusAngleDomain).withDensity
          fun u => ENNReal.ofReal (paramDensity gT torusAngleParam u)) := by
  ext B hB
  rw [Measure.map_apply measurable_torusAngleParam hB,
    withDensity_apply _ (measurable_torusAngleParam hB),
    Measure.restrict_restrict (measurable_torusAngleParam hB)]
  exact riemannianVolumeMeasure_torus_eq_setLIntegral gT hB

end DifferentialGeometry.Geometry.Collapse
