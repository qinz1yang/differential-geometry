/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.RadialCone
import DifferentialGeometry.Geometry.Measure.Area.ManifoldComposition
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.Metric.ConvexProjection
import DifferentialGeometry.Geometry.Metric.CurveLength

/-! # Metric area of the literal periodic cone in a coordinate ball

Both metric comparisons apply to the supplied map and the supplied metric on
the original coordinate ball. The conclusion keeps the same parametrized cone.
-/

noncomputable section

open Set Metric MeasureTheory Filter Bundle Manifold
open DifferentialGeometry.Topology
open scoped NNReal ENNReal Topology ContDiff Manifold Bundle

namespace DifferentialGeometry.Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem periodicLoopCone_mapsTo_convex
    (p : F) {a : ℝ → F} (ha : Function.Periodic a 1)
    {S : Set F} (hS : Convex ℝ S) (hp : p ∈ S) (hmap : ∀ t, a t ∈ S) :
    MapsTo (periodicLoopCone p ha) (closedBall (0 : ℂ) 1) S := by
  have hb (z : Circle) : periodicCircleMap ha z ∈ S := by
    let ξ : loopCircle := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z +
      ((1 / 2 : ℝ) : loopCircle)
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective ξ
    change ha.lift ξ ∈ S
    rw [← ht, Function.Periodic.lift_coe]
    exact hmap t
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  change p + ‖z‖ • (periodicCircleMap ha (radialDirection z) - p) ∈ S
  have he : p + ‖z‖ • (periodicCircleMap ha (radialDirection z) - p) =
      (1 - ‖z‖) • p + ‖z‖ • periodicCircleMap ha (radialDirection z) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  exact hS hp (hb (radialDirection z)) (sub_nonneg.mpr hz1) (norm_nonneg z) (by ring)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem coordinate_edist_le_of_pullback_norm_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {φ : F → M} {U S : Set F} {L : ℝ≥0}
    (hU : IsOpen U) (hφ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 φ U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hbound : ∀ x ∈ S, ∀ v : F, Real.sqrt (g.inner (φ x)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v)) ≤ L * ‖v‖)
    {x y : F} (hx : x ∈ S) (hy : y ∈ S) :
    riemannianEDistOf g (φ x) (φ y) ≤ (L : ℝ≥0∞) * edist x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hspeed : ∀ w ∈ S, ∀ v : F,
      ‖mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, E) φ U w v‖ₑ ≤ ENNReal.ofReal ((L : ℝ) * ‖v‖) := by
    intro w hw v
    rw [mfderivWithin_of_mem_nhds (hU.mem_nhds (hSU hw)),
      ← ofReal_norm, norm_eq_sqrt_real_inner]
    exact ENNReal.ofReal_le_ofReal (hbound w hw v)
  have hdist := DifferentialGeometry.riemannianEDist_le_of_mfderivWithin_le
    hφ hSU hspeed (hS.segment_subset hx hy)
  change Manifold.riemannianEDist 𝓘(ℝ, E) (φ x) (φ y) ≤ _
  convert hdist using 1
  rw [ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal, edist_dist]

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [T3Space M]

private theorem sqrt_mul_integral_norm_deriv_le_curveLength
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {φ : F → M} {U : Set F}
    (hU : IsOpen U) (hφ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 φ U)
    {a : ℝ → F} {K C : ℝ≥0} (hLip : LipschitzWith K a) (haU : ∀ t, a t ∈ U)
    {m : ℝ} (hm : 0 ≤ m)
    (hlower : ∀ t, ∀ v : F, m * ‖v‖ ^ 2 ≤ g.inner (φ (a t))
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ (a t) v) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ (a t) v))
    (hcurve : ∀ x y, riemannianEDistOf g ((φ ∘ a) x) ((φ ∘ a) y) ≤
      (C : ℝ≥0∞) * edist x y) :
    Real.sqrt m * (∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖) ≤
      riemannianCurveLength g (φ ∘ a) 0 1 := by
  borelize F
  have hi : IntegrableOn (fun t => ‖deriv a t‖) (Icc (0 : ℝ) 1) := by
    apply Integrable.of_bound (measurable_deriv a).norm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun t => by
      simpa only [norm_norm] using
        (show ‖deriv a t‖ ≤ (K : ℝ) from norm_deriv_le_of_lipschitz hLip)
  have hnonneg (t : ℝ) : 0 ≤ Real.sqrt m * ‖deriv a t‖ :=
    mul_nonneg (Real.sqrt_nonneg m) (norm_nonneg _)
  have hspeed : ∀ᵐ t ∂volume,
      Real.sqrt m * ‖deriv a t‖ ≤ riemannianCurveSpeed g (φ ∘ a) t := by
    filter_upwards [hLip.ae_differentiableAt_real] with t ht
    have hφt := ((hφ (a t) (haU t)).contMDiffAt (hU.mem_nhds (haU t))).mdifferentiableAt
      one_ne_zero
    rw [riemannianCurveSpeed_comp g hφt ht]
    have h := Real.sqrt_le_sqrt (hlower t (deriv a t))
    rw [Real.sqrt_mul hm, Real.sqrt_sq_eq_abs, abs_norm] at h
    exact h
  have he : ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, Real.sqrt m * ‖deriv a t‖) ≤
      riemannianCurveELength g (φ ∘ a) 0 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi.const_mul (Real.sqrt m))
      (Eventually.of_forall hnonneg)]
    apply lintegral_mono_ae
    exact (ae_restrict_of_ae hspeed).mono fun _ ht => ENNReal.ofReal_le_ofReal ht
  have hreal := ENNReal.toReal_mono (riemannianCurveELength_ne_top_of_lipschitz g hcurve 0 1) he
  rw [ENNReal.toReal_ofReal (integral_nonneg hnonneg), integral_const_mul] at hreal
  exact hreal

/-- Explicit bounds for the actual pulled-back metric transfer the literal cone
area estimate to the length of its original coordinate-parametrized curve. -/
theorem riemannianDiskArea_periodicLoopCone_le_radius_mul_length
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (φ : F → M) {U : Set F}
    (hU : IsOpen U) (hφ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 φ U)
    (p c : F) {a : ℝ → F} {K : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith K a)
    {R ρ m A : ℝ} (hBU : closedBall c ρ ⊆ U)
    (hp : p ∈ closedBall c ρ) (haBall : ∀ t, a t ∈ closedBall c ρ)
    (hR : ∀ t, ‖a t - p‖ ≤ R) (hm : 0 < m) (hmA : m ≤ A)
    (hmetric : ∀ x ∈ closedBall c ρ, ∀ v : F,
      m * ‖v‖ ^ 2 ≤ g.inner (φ x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) ∧
      g.inner (φ x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) ≤ A * ‖v‖ ^ 2) :
    riemannianDiskArea g (fun z : closedDisk => φ (periodicLoopCone p ha z)) ≤
      (A / (2 * Real.sqrt m)) * R * riemannianCurveLength g (φ ∘ a) 0 1 := by
  have hA : 0 ≤ A := hm.le.trans hmA
  have hR0 : 0 ≤ R := (norm_nonneg (a 0 - p)).trans (hR 0)
  let L : ℝ≥0 := ⟨Real.sqrt A, Real.sqrt_nonneg A⟩
  have hLsq : (L : ℝ) ^ 2 = A := Real.sq_sqrt hA
  have hbound (x : F) (hx : x ∈ closedBall c ρ) (v : F) :
      Real.sqrt (g.inner (φ x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v)) ≤ L * ‖v‖ := by
    have h := Real.sqrt_le_sqrt (hmetric x hx v).2
    rw [Real.sqrt_mul hA, Real.sqrt_sq_eq_abs, abs_norm] at h
    exact h
  have hφLip (x : F) (hx : x ∈ closedBall c ρ) (y : F) (hy : y ∈ closedBall c ρ) :
      riemannianEDistOf g (φ x) (φ y) ≤ (L : ℝ≥0∞) * edist x y :=
    coordinate_edist_le_of_pullback_norm_bound g hU hφ hBU (convex_closedBall c ρ) hbound hx hy
  have hne : (closedBall c ρ).Nonempty := ⟨p, hp⟩
  have hcomplete : IsComplete (closedBall c ρ) := isClosed_closedBall.isComplete
  let P : F → closedBall c ρ := convexProjection hne hcomplete (convex_closedBall c ρ)
  have hP : LipschitzWith 1 P := convexProjection_lipschitz hne hcomplete (convex_closedBall c ρ)
  have hPeq (x : F) (hx : x ∈ closedBall c ρ) : (P x : F) = x :=
    congrArg Subtype.val (convexProjection_of_mem hne hcomplete (convex_closedBall c ρ) ⟨x, hx⟩)
  let f : F → M := fun x => φ (P x)
  have hfeq (x : F) (hx : x ∈ closedBall c ρ) : f x = φ x := congrArg φ (hPeq x hx)
  have hf (x y : F) : riemannianEDistOf g (f x) (f y) ≤ (L : ℝ≥0∞) * edist x y := by
    calc
      _ ≤ (L : ℝ≥0∞) * edist (P x) (P y) := hφLip _ (P x).property _ (P y).property
      _ ≤ (L : ℝ≥0∞) * ((1 : ℝ≥0∞) * edist x y) := mul_le_mul_of_nonneg_left (hP x y) (show (0 : ℝ≥0∞) ≤ (L : ℝ≥0∞) from zero_le)
      _ = _ := by rw [one_mul]
  have hcurve (x y : ℝ) : riemannianEDistOf g ((φ ∘ a) x) ((φ ∘ a) y) ≤
      (↑(L * K) : ℝ≥0∞) * edist x y := by
    calc
      _ ≤ (L : ℝ≥0∞) * edist (a x) (a y) := hφLip _ (haBall x) _ (haBall y)
      _ ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * edist x y) := mul_le_mul_of_nonneg_left (hLip x y) (show (0 : ℝ≥0∞) ≤ (L : ℝ≥0∞) from zero_le)
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
  have hlength := sqrt_mul_integral_norm_deriv_le_curveLength g hU hφ hLip
    (fun t => hBU (haBall t)) hm.le (fun t v => (hmetric (a t) (haBall t) v).1) hcurve
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hlength' : (∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖) ≤
      riemannianCurveLength g (φ ∘ a) 0 1 / Real.sqrt m := by
    apply (le_div_iff₀ hsqrt).mpr
    simpa only [mul_comm] using hlength
  have hcone := periodicLoopCone_mapsTo_convex p ha (convex_closedBall c ρ) hp haBall
  obtain ⟨C, hC⟩ := exists_lipschitzWith_periodicLoopCone p ha hLip
  have hu (x y : closedDisk) : riemannianEDistOf (standardEuclideanMetric F)
      (periodicLoopCone p ha x) (periodicLoopCone p ha y) ≤ (C : ℝ≥0∞) * edist x y := by
    rw [riemannianEDistOf_standardEuclideanMetric]
    exact hC (x : ℂ) (y : ℂ)
  have hfstd (x y : F) : riemannianEDistOf g (f x) (f y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (standardEuclideanMetric F) x y := by
    rw [riemannianEDistOf_standardEuclideanMetric]
    exact hf x y
  have harea := riemannianDiskArea_comp_le (standardEuclideanMetric F) g
    (u := fun z : closedDisk => periodicLoopCone p ha z) (f := f) hu hfstd
  have hcomp : (f ∘ fun z : closedDisk => periodicLoopCone p ha z) =
      (fun z : closedDisk => φ (periodicLoopCone p ha z)) := by
    funext z
    exact hfeq _ (hcone z.property)
  rw [hcomp, riemannianDiskArea_standardEuclideanMetric, hLsq] at harea
  have hEuclidean : euclideanDiskArea (fun z : closedDisk => periodicLoopCone p ha z) ≤
      (R / 2) * (∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖) := by
    rw [euclideanDiskArea_eq_of_extension _ (periodicLoopCone p ha) (fun _ => rfl)]
    exact euclideanArea_periodicLoopCone_le_radius_mul_length p ha hLip hR
  calc
    _ ≤ A * euclideanDiskArea (fun z : closedDisk => periodicLoopCone p ha z) := harea
    _ ≤ A * ((R / 2) * (∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖)) :=
      mul_le_mul_of_nonneg_left hEuclidean hA
    _ ≤ A * ((R / 2) * (riemannianCurveLength g (φ ∘ a) 0 1 / Real.sqrt m)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlength' (div_nonneg hR0 (by norm_num))) hA
    _ = _ := by field_simp [hsqrt.ne']

end DifferentialGeometry.Geometry
