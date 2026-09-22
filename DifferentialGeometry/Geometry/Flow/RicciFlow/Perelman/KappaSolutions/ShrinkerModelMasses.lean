import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalQuotientVolume
import DifferentialGeometry.Geometry.Metric.ProjectiveSpace
import DifferentialGeometry.Geometry.Metric.Sphere.Round.TotalArea
import DifferentialGeometry.Topology.ProjectiveSpace.Manifold
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff ENNReal

local notation "CylI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance modelMassMeasurableS2 : MeasurableSpace S2 := borel S2
private local instance modelMassBorelS2 : BorelSpace S2 := ⟨rfl⟩
private local instance modelMassMeasurableRP : MeasurableSpace RealProjectivePlane :=
  borel RealProjectivePlane
private local instance modelMassBorelRP : BorelSpace RealProjectivePlane := ⟨rfl⟩
private local instance modelMassMeasurableCyl : MeasurableSpace (S2 × ℝ) := borel (S2 × ℝ)
private local instance modelMassBorelCyl : BorelSpace (S2 × ℝ) := ⟨rfl⟩
private local instance modelMassMeasurableDQ : MeasurableSpace CylinderDiagonalQuotient :=
  borel CylinderDiagonalQuotient
private local instance modelMassBorelDQ : BorelSpace CylinderDiagonalQuotient := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance modelMassMeasurableM : MeasurableSpace M := borel M
private local instance modelMassBorelM : BorelSpace M := ⟨rfl⟩

private theorem lintegral_cast_measurableSpace {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (μ : @Measure X m₁) (f : X → ℝ≥0∞) :
    ∫⁻ x, f x ∂(cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ) =
      ∫⁻ x, f x ∂μ := by
  cases hm
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_riemannianVolumeMeasure_prod_real
    (h : SmoothRiemannianMetric I M) {A : M → ℝ≥0∞} {B : ℝ → ℝ≥0∞}
    (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ z, A z.1 * B z.2 ∂(riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × ℝ) (h.prod (euclideanMetric (E := ℝ)))) =
      (∫⁻ x, A x ∂riemannianVolumeMeasure (I := I) (M := M) h) *
        ∫⁻ t, B t ∂(volume : Measure ℝ) := by
  have hproduct (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ) :
      (h.prod (euclideanMetric (E := ℝ))).inner (y, s) (v, a) (w, c) =
        h.inner y v w + a * c := by
    rw [SmoothRiemannianMetric.prod_inner, euclideanMetric_inner]
    rw [show inner ℝ a c = c * a from rfl]
    ring_nf
  rw [riemannianVolumeMeasure_product_real_of_inner_eq (I := I) (M := M) h _
    hproduct]
  rw [lintegral_cast_measurableSpace (BorelSpace.measurable_eq (α := M × ℝ))]
  rw [lintegral_prod]
  · rw [lintegral_congr (fun x => lintegral_const_mul'' (A x) hB.aemeasurable)]
    rw [lintegral_mul_const'' _ hA.aemeasurable]
  · exact ((hA.comp measurable_fst).mul (hB.comp measurable_snd)).aemeasurable

theorem normalizedShrinkerMass_prod_real
    (h : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : Measurable f)
    {φ : ℝ → ℝ} (hφ : Measurable φ) :
    normalizedShrinkerMass (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ)
        (h.prod (euclideanMetric (E := ℝ))) (fun z => f z.1 + φ z.2) =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(Module.finrank ℝ (E × ℝ) : ℝ) / 2)) *
        ((∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) ∂riemannianVolumeMeasure (I := I) (M := M) h) *
          ∫⁻ t, ENNReal.ofReal (Real.exp (-φ t)) ∂(volume : Measure ℝ)) := by
  rw [normalizedShrinkerMass_eq_const_mul_lintegral]
  have hsplit : (fun z : M × ℝ => ENNReal.ofReal (Real.exp (-(f z.1 + φ z.2))))
      = fun z : M × ℝ =>
          ENNReal.ofReal (Real.exp (-f z.1)) * ENNReal.ofReal (Real.exp (-φ z.2)) := by
    funext z
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    ring_nf
  rw [hsplit, lintegral_riemannianVolumeMeasure_prod_real (h := h)
      (A := fun x => ENNReal.ofReal (Real.exp (-f x)))
      (B := fun t => ENNReal.ofReal (Real.exp (-φ t)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf.neg))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hφ.neg))]

theorem lintegral_exp_eq_inv_two_mul_of_map_eq_two_smul
    {N M' : Type*} [MeasurableSpace N] [MeasurableSpace M']
    (ν : Measure N) (μ : Measure M') (φ : N → M') (hφ : Measurable φ)
    {f : N → ℝ} {g : M' → ℝ}
    (hg : Measurable fun y => ENNReal.ofReal (Real.exp (-g y)))
    (hmap : Measure.map φ ν = (2 : ENNReal) • μ)
    (hgf : ∀ x, g (φ x) = f x) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ =
      (2 : ENNReal)⁻¹ * ∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) ∂ν := by
  have h2 : (2 : ENNReal) * (∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ)
      = ∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) ∂ν := by
    calc (2 : ENNReal) * (∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ)
        = ∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂((2 : ENNReal) • μ) :=
          (lintegral_smul_measure (2 : ENNReal) _).symm
      _ = ∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂(Measure.map φ ν) := by rw [← hmap]
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-g (φ x))) ∂ν := lintegral_map hg hφ
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) ∂ν :=
          lintegral_congr (fun x => by rw [hgf x])
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ
      = 1 * (∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ) := (one_mul _).symm
    _ = ((2 : ENNReal)⁻¹ * 2) * (∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ) := by
          rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    _ = (2 : ENNReal)⁻¹ *
          ((2 : ENNReal) * (∫⁻ y, ENNReal.ofReal (Real.exp (-g y)) ∂μ)) := by
          rw [mul_assoc]
    _ = (2 : ENNReal)⁻¹ * ∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) ∂ν := by rw [h2]

theorem riemannianVolumeMeasure_roundTwoSphereShrinkerMetric_univ_eq :
    riemannianVolumeMeasure (I := 𝓡 2) (M := S2) roundTwoSphereShrinkerMetric Set.univ =
      ENNReal.ofReal (8 * Real.pi) := by
  rw [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
    volume_scaleMetric (I := 𝓡 2) (M := S2)
      (roundSphereShrinkerRadius 2 ^ 2)
      (sq_pos_of_pos (roundSphereShrinkerRadius_pos (by decide : 2 ≤ 2)))
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)),
    finrank_euclideanSpace_fin, Measure.smul_apply, smul_eq_mul,
    riemannianVolumeMeasure_roundMetric_sphere_univ_eq,
    show Real.sqrt (roundSphereShrinkerRadius 2 ^ 2) = Real.sqrt 2 by
      rw [roundSphereShrinkerRadius_two]
      exact Real.sqrt_sq (Real.sqrt_nonneg 2),
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg 2) 2, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring_nf

theorem lintegral_exp_neg_sq_div_four :
    ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-(t ^ 2 / 4))) ∂(volume : Measure ℝ) =
      ENNReal.ofReal (2 * Real.sqrt Real.pi) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun t : ℝ => Real.exp (-(t ^ 2 / 4)))]
  · rw [show (∫ t : ℝ, Real.exp (-(t ^ 2 / 4))) = 2 * Real.sqrt Real.pi by
      rw [show (∫ t : ℝ, Real.exp (-(t ^ 2 / 4))) =
          ∫ t : ℝ, Real.exp (-(1 / 4) * t ^ 2) by
        apply integral_congr_ae
        filter_upwards with t
        rw [show -(t ^ 2 / 4) = -(1 / 4) * t ^ 2 by ring]]
      rw [integral_gaussian]
      rw [show Real.pi / (1 / 4) = 4 * Real.pi by ring]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num]]
  · exact (integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).congr
      (Filter.Eventually.of_forall (fun t => congrArg Real.exp (by ring)))
  · exact Filter.Eventually.of_forall (fun t => Real.exp_nonneg _)

private local instance rpTwoFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem encard_realProjectivePlaneQuotientMap_fiber (y : RealProjectivePlane) :
    {x : S2 | realProjectivePlaneQuotientMap x = y}.encard = (2 : ℕ∞) := by
  classical
  revert y
  refine Quotient.ind (motive := fun y : RealProjectivePlane =>
    {x : S2 | realProjectivePlaneQuotientMap x = y}.encard = (2 : ℕ∞)) fun x₀ => ?_
  have hfix : x₀ ≠ realProjectivePlaneAntipodalHomeomorph x₀ :=
    fun h => realProjectivePlaneAntipodalHomeomorph_fixed_point_free x₀ h.symm
  have hset : {x : S2 | realProjectivePlaneQuotientMap x =
      realProjectivePlaneQuotientMap x₀} =
      {x₀, realProjectivePlaneAntipodalHomeomorph x₀} := by
    ext x
    rw [Set.mem_ofPred_eq, realProjectivePlaneQuotientMap_eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr (Subtype.ext ?_)
        rw [realProjectivePlaneAntipodalHomeomorph_coe]
        exact h
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ?_
        rw [h, realProjectivePlaneAntipodalHomeomorph_coe]
  change {x : S2 | realProjectivePlaneQuotientMap x =
    realProjectivePlaneQuotientMap x₀}.encard = (2 : ℕ∞)
  rw [hset, Set.encard_insert_of_notMem (by simpa using hfix), Set.encard_singleton]
  norm_num

theorem map_realProjectivePlaneQuotientMap_riemannianVolumeMeasure :
    Measure.map realProjectivePlaneQuotientMap
        (riemannianVolumeMeasure (I := 𝓡 2) (M := S2)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) =
      (2 : ENNReal) • riemannianVolumeMeasure (I := 𝓡 2) (M := RealProjectivePlane)
        (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) :=
  riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    (I := 𝓡 2) (M := S2) (N := RealProjectivePlane)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    (localPullMetric_roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) 2
    encard_realProjectivePlaneQuotientMap_fiber

theorem riemannianVolumeMeasure_roundProjectiveMetric_univ_eq :
    riemannianVolumeMeasure (I := 𝓡 2) (M := RealProjectivePlane)
      (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) Set.univ =
      ENNReal.ofReal (2 * Real.pi) := by
  have hqmeas : Measurable realProjectivePlaneQuotientMap :=
    (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (E := EuclideanSpace ℝ (Fin 3))
      (n := 2)).contMDiff.continuous.measurable
  have hmapuniv : Measure.map realProjectivePlaneQuotientMap
        (riemannianVolumeMeasure (I := 𝓡 2) (M := S2)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) Set.univ =
      riemannianVolumeMeasure (I := 𝓡 2) (M := S2)
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) Set.univ := by
    rw [Measure.map_apply (f := realProjectivePlaneQuotientMap) hqmeas MeasurableSet.univ,
      Set.preimage_univ]
  have h := congrArg (fun m : Measure RealProjectivePlane => m Set.univ)
    map_realProjectivePlaneQuotientMap_riemannianVolumeMeasure
  rw [Measure.smul_apply, smul_eq_mul, hmapuniv,
    riemannianVolumeMeasure_roundMetric_sphere_univ_eq] at h
  have hnum : ENNReal.ofReal (4 * Real.pi) =
      (2 : ENNReal) * ENNReal.ofReal (2 * Real.pi) := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hnum] at h
  rw [mul_comm (2 : ENNReal) (ENNReal.ofReal (2 * Real.pi)),
    mul_comm (2 : ENNReal)
      (riemannianVolumeMeasure (I := 𝓡 2) (M := RealProjectivePlane)
        (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) Set.univ)] at h
  exact ((ENNReal.mul_left_inj (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)).mp h).symm

theorem riemannianVolumeMeasure_scaleTwoRoundProjectiveMetric_univ_eq :
    riemannianVolumeMeasure (I := 𝓡 2) (M := RealProjectivePlane)
      (scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) Set.univ =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [volume_scaleMetric (I := 𝓡 2) (M := RealProjectivePlane) 2 (by norm_num)
      (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)),
    finrank_euclideanSpace_fin, Measure.smul_apply, smul_eq_mul,
    riemannianVolumeMeasure_roundProjectiveMetric_univ_eq,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg 2) 2, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring_nf

theorem normalizedShrinkerMass_roundThreeCylinderShrinker :
    normalizedShrinkerMass (I := CylI) (M := S2 × ℝ)
      roundThreeCylinderShrinkerMetric
      (fun x : S2 × ℝ => roundThreeCylinderShrinkerPotential x) =
    ENNReal.ofReal (2 * Real.exp (-1)) := by
  have hpot : (fun z : S2 × ℝ => roundTwoSphereShrinkerPotential z.1 + gaussianPotential z.2) =
      fun z : S2 × ℝ => roundThreeCylinderShrinkerPotential z := by
    funext z
    rw [roundThreeCylinderShrinkerPotential_apply, roundTwoSphereShrinkerPotential_apply,
      gaussianPotential_apply, Real.norm_eq_abs, sq_abs]
  rw [← hpot, roundThreeCylinderShrinkerMetric,
    normalizedShrinkerMass_prod_real (h := roundTwoSphereShrinkerMetric)
      (f := fun x => roundTwoSphereShrinkerPotential x) (φ := gaussianPotential)
      (by fun_prop) (by fun_prop)]
  rw [lintegral_congr (fun x => by rw [roundTwoSphereShrinkerPotential_apply]),
    lintegral_const, riemannianVolumeMeasure_roundTwoSphereShrinkerMetric_univ_eq,
    lintegral_congr (fun t => by rw [gaussianPotential_apply, Real.norm_eq_abs, sq_abs]),
    lintegral_exp_neg_sq_div_four]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 by
    simp [Module.finrank_prod]]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-1)),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg (-1)) (by positivity : (0:ℝ) ≤ 8 * Real.pi)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi) _)]
  congr 1
  have ha : (0 : ℝ) < 4 * Real.pi := by positivity
  have h32 : (4 * Real.pi) ^ ((3 : ℝ) / 2) = 8 * Real.pi * Real.sqrt Real.pi := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ha, Real.rpow_one,
      ← Real.sqrt_eq_rpow (4 * Real.pi), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num]
    ring
  rw [neg_div, Real.rpow_neg ha.le]
  rw [show (4 * Real.pi) ^ ((↑(3:ℕ) : ℝ) / 2) = 8 * Real.pi * Real.sqrt Real.pi by
    simpa only [Nat.cast_ofNat] using h32]
  have hs : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

theorem normalizedShrinkerMass_realProjectivePlaneProduct :
    normalizedShrinkerMass (I := CylI) (M := RealProjectivePlane × ℝ)
      ((scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := ℝ)))
      (fun x : RealProjectivePlane × ℝ => 1 + x.2 ^ 2 / 4) =
    ENNReal.ofReal (Real.exp (-1)) := by
  rw [show (fun x : RealProjectivePlane × ℝ => 1 + x.2 ^ 2 / 4) =
      fun z : RealProjectivePlane × ℝ =>
        (fun _ : RealProjectivePlane => (1 : ℝ)) z.1 + (fun t : ℝ => t ^ 2 / 4) z.2 from rfl]
  rw [normalizedShrinkerMass_prod_real
      (h := scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))
      (f := fun _ : RealProjectivePlane => (1 : ℝ))
      (φ := fun t : ℝ => t ^ 2 / 4) measurable_const (by fun_prop)]
  rw [lintegral_congr (fun x => by rfl), lintegral_const,
    riemannianVolumeMeasure_scaleTwoRoundProjectiveMetric_univ_eq,
    lintegral_exp_neg_sq_div_four]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 by
    simp [Module.finrank_prod]]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-1)),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg (-1)) (by positivity : (0:ℝ) ≤ 4 * Real.pi)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi) _)]
  congr 1
  have ha : (0 : ℝ) < 4 * Real.pi := by positivity
  have h32 : (4 * Real.pi) ^ ((3 : ℝ) / 2) = 8 * Real.pi * Real.sqrt Real.pi := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ha, Real.rpow_one,
      ← Real.sqrt_eq_rpow (4 * Real.pi), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num]
    ring
  rw [neg_div, Real.rpow_neg ha.le,
    show (4 * Real.pi) ^ ((↑(3:ℕ) : ℝ) / 2) = 8 * Real.pi * Real.sqrt Real.pi by
      simpa only [Nat.cast_ofNat] using h32]
  have hs : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp
  ring

theorem normalizedShrinkerMass_cylinderDiagonalQuotient :
    normalizedShrinkerMass (I := CylI) (M := CylinderDiagonalQuotient)
      cylinderDiagonalQuotientMetric
      (fun x : CylinderDiagonalQuotient => cylinderDiagonalQuotientPotential x) =
    ENNReal.ofReal (Real.exp (-1)) := by
  have hφ : Measurable cylinderDiagonalQuotientMap :=
    cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous.measurable
  have hg : Measurable (fun y : CylinderDiagonalQuotient =>
      ENNReal.ofReal (Real.exp (-cylinderDiagonalQuotientPotential y))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      cylinderDiagonalQuotientPotential_continuous.measurable.neg)
  have hintegral := lintegral_exp_eq_inv_two_mul_of_map_eq_two_smul
    (riemannianVolumeMeasure (I := CylI) (M := S2 × ℝ) roundThreeCylinderShrinkerMetric)
    (riemannianVolumeMeasure (I := CylI) (M := CylinderDiagonalQuotient)
      cylinderDiagonalQuotientMetric)
    cylinderDiagonalQuotientMap hφ
    (f := fun x => roundThreeCylinderShrinkerPotential x)
    (g := fun y => cylinderDiagonalQuotientPotential y) hg
    map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure
    (fun x => by rw [cylinderDiagonalQuotientPotential_apply])
  rw [normalizedShrinkerMass_eq_const_mul_lintegral, hintegral]
  rw [← mul_assoc, mul_comm (ENNReal.ofReal _) (2 : ENNReal)⁻¹, mul_assoc]
  rw [← normalizedShrinkerMass_eq_const_mul_lintegral
      (g := roundThreeCylinderShrinkerMetric)
      (f := fun x => roundThreeCylinderShrinkerPotential x),
    normalizedShrinkerMass_roundThreeCylinderShrinker]
  rw [show ENNReal.ofReal (2 * Real.exp (-1)) =
      (2 : ENNReal) * ENNReal.ofReal (Real.exp (-1)) by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem noncompactShrinkerModelMasses : NoncompactShrinkerModelMasses :=
  ⟨normalizedShrinkerMass_roundThreeCylinderShrinker,
    normalizedShrinkerMass_realProjectivePlaneProduct,
    normalizedShrinkerMass_cylinderDiagonalQuotient⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
