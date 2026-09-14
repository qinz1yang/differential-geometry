import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerModelMasses

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance alternativesTopology : TopologicalSpace L.M := L.topology
local instance alternativesCharted : ChartedSpace H L.M := L.charted
local instance alternativesSmooth : IsManifold I ∞ L.M := L.smooth
local instance alternativesT2 : T2Space L.M := L.t2
local instance alternativesSigma : SigmaCompactSpace L.M := L.sigmaCompact

private abbrev shrinkerSpherePoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨PiLp.single 2 (0 : Fin 4) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩

theorem exists_pointed_compact_normalized_nonflat_three_shrinker_round :
    ∃ L' : PointedRiemannianManifold.{0, 0, 0} (I := 𝓡 3),
      CompactSpace L'.M ∧
        (∀ x : L'.M, metricScalarAt (I := 𝓡 3) L'.metric x = (3 : ℝ) / 2) ∧
        ∀ x : L'.M, ∀ v : TangentSpace (𝓡 3) x,
          ricciTensor (I := 𝓡 3) L'.metric x v v =
            ((3 : ℝ) / 2 / 3) * L'.metric.inner x v v := by
  let L0 : PointedRiemannianManifold.{0, 0, 0} (I := 𝓡 3) :=
    { M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
      basepoint := shrinkerSpherePoint
      metric := roundThreeSphereShrinkerMetric }
  refine ⟨L0, inferInstance, ?_, ?_⟩
  · intro x
    simpa only [L0] using roundThreeSphereShrinkerMetric_scalarCurvature x
  · intro x v
    have h := roundSphereShrinkerMetric_ricciTensor
      (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide) x v v
    rw [show (3 : ℝ) / 2 / 3 = 1 / 2 by norm_num]
    simpa only [L0, roundThreeSphereShrinkerMetric] using h

private abbrev lineOffsetPotential : ℝ → ℝ := fun t => t ^ 2 / 4

private abbrev planeGaussianPotential : ℝ × ℝ → ℝ := fun z => z.1 ^ 2 / 4 + z.2 ^ 2 / 4

private theorem measurable_planeGaussianPotential_uncurried :
    Measurable (fun z : ℝ × ℝ => z.1 ^ 2 / 4 + z.2 ^ 2 / 4) := by
  fun_prop

private theorem measurable_planeGaussianPotential :
    @Measurable (ℝ × ℝ) ℝ (borel (ℝ × ℝ)) Real.measurableSpace
      planeGaussianPotential := by
  rw [show (borel (ℝ × ℝ)) = Prod.instMeasurableSpace from
    (BorelSpace.measurable_eq (α := ℝ × ℝ)).symm]
  exact measurable_planeGaussianPotential_uncurried

private abbrev gaussianProductPotential : (ℝ × ℝ) × ℝ → ℝ :=
  fun z => z.1.1 ^ 2 / 4 + z.1.2 ^ 2 / 4 + z.2 ^ 2 / 4

private abbrev planeEuclideanMetric :
    SmoothRiemannianMetric ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (ℝ × ℝ) :=
  (euclideanMetric (E := ℝ)).prod (euclideanMetric (E := ℝ))

private abbrev productEuclideanMetric :
    SmoothRiemannianMetric (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      ((ℝ × ℝ) × ℝ) :=
  (((euclideanMetric (E := ℝ)).prod (euclideanMetric (E := ℝ))).prod
    (euclideanMetric (E := ℝ)))

theorem lintegral_exp_neg_sq_div_four_volume :
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-(t ^ 2 / 4))) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal (2 * Real.sqrt Real.pi) :=
  lintegral_exp_neg_sq_div_four

private theorem lintegral_exp_neg_planeGaussianPotential :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (Real.exp (-planeGaussianPotential z))
      ∂riemannianVolumeMeasure (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (M := ℝ × ℝ)
        planeEuclideanMetric) =
      ENNReal.ofReal (2 * Real.sqrt Real.pi) * ENNReal.ofReal (2 * Real.sqrt Real.pi) := by
  have h1 := normalizedShrinkerMass_eq_const_mul_lintegral
    (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (M := ℝ × ℝ) planeEuclideanMetric
      planeGaussianPotential
  have h2 := normalizedShrinkerMass_prod_real (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (euclideanMetric (E := ℝ)) (f := lineOffsetPotential) (φ := lineOffsetPotential)
      (by fun_prop) (by fun_prop)
  rw [riemannianVolumeMeasure_euclideanMetric, lintegral_exp_neg_sq_div_four_volume] at h2
  have h2' : normalizedShrinkerMass (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (M := ℝ × ℝ)
        planeEuclideanMetric planeGaussianPotential =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(Module.finrank ℝ (ℝ × ℝ) : ℝ) / 2)) *
        (ENNReal.ofReal (2 * Real.sqrt Real.pi) * ENNReal.ofReal (2 * Real.sqrt Real.pi)) := by
    simpa only [planeEuclideanMetric, planeGaussianPotential, lineOffsetPotential] using h2
  have hc0 :
      ENNReal.ofReal ((4 * Real.pi) ^ (-(Module.finrank ℝ (ℝ × ℝ) : ℝ) / 2)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (by positivity) _)
  exact (ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top).mp (h1.symm.trans h2')

theorem normalizedShrinkerMass_flatGaussianProduct_eq_one :
    normalizedShrinkerMass (I := ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (M := (ℝ × ℝ) × ℝ) productEuclideanMetric gaussianProductPotential = 1 := by
  have h3 := normalizedShrinkerMass_prod_real (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
    (M := ℝ × ℝ) planeEuclideanMetric (f := planeGaussianPotential)
      (φ := lineOffsetPotential) measurable_planeGaussianPotential (by fun_prop)
  change normalizedShrinkerMass (I := ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
    (M := (ℝ × ℝ) × ℝ) productEuclideanMetric
    (fun z : (ℝ × ℝ) × ℝ => planeGaussianPotential z.1 + lineOffsetPotential z.2) = 1
  rw [h3, lintegral_exp_neg_planeGaussianPotential, lintegral_exp_neg_sq_div_four_volume,
    show Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 by simp [Module.finrank_prod]]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
    ← ENNReal.ofReal_one]
  congr 1
  have ha : (0 : ℝ) < 4 * Real.pi := by positivity
  have hX : (2 * Real.sqrt Real.pi) = (4 * Real.pi) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt (4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num]
  have hcube : (2 * Real.sqrt Real.pi) * (2 * Real.sqrt Real.pi) * (2 * Real.sqrt Real.pi) =
      (4 * Real.pi) ^ ((3 : ℝ) / 2) := by
    rw [show (2 * Real.sqrt Real.pi) * (2 * Real.sqrt Real.pi) * (2 * Real.sqrt Real.pi) =
        (2 * Real.sqrt Real.pi) ^ 3 by ring, hX, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    rw [show (1 : ℝ) / 2 * ((3 : ℕ) : ℝ) = (3 : ℝ) / 2 by norm_num]
  rw [hcube, ← Real.rpow_add ha,
    show -((3 : ℕ) : ℝ) / 2 + (3 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
