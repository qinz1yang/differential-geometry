import DifferentialGeometry.Analysis.Complex.RadialVariation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialVariation
import DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Complex
import DifferentialGeometry.Tensor.LinearAlgebra.PlanarBilinear
import DifferentialGeometry.Analysis.Integration.Integral.WeightedDerivativePairing
import DifferentialGeometry.Geometry.Metric.Pullback.Continuity
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import Mathlib.Analysis.Calculus.Rademacher
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakPullback
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence

noncomputable section

open Manifold MeasureTheory Set Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem integral_diskMapPartial_pair_eq_pullback
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {U : ℂ → M} {R : ℝ}
    (hdiff : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) R),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (weight : ℂ → ℝ) (i j : Fin 2) :
    (∫ z in Metric.closedBall (0 : ℂ) R, weight z *
      g.inner (U z) (diskMapPartial U z (Complex.orthonormalBasisOneI i))
        (diskMapPartial U z (Complex.orthonormalBasisOneI j))) =
      ∫ x in Metric.ball (0 : V) R, weight (Complex.orthonormalBasisOneI.repr.symm x) *
        pullbackMetricCoefficients g r (Φ (U (Complex.orthonormalBasisOneI.repr.symm x)))
          (fderiv ℝ (fun y => Φ (U (Complex.orthonormalBasisOneI.repr.symm y))) x
            (EuclideanSpace.single i 1))
          (fderiv ℝ (fun y => Φ (U (Complex.orthonormalBasisOneI.repr.symm y))) x
            (EuclideanSpace.single j 1)) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  let f := Φ ∘ U
  let A := pullbackMetricCoefficients g r
  have hpair : (fun z => weight z *
      g.inner (U z) (diskMapPartial U z (Complex.orthonormalBasisOneI i))
        (diskMapPartial U z (Complex.orthonormalBasisOneI j))) =ᵐ[
      volume.restrict (Metric.ball (0 : ℂ) R)] (fun z => weight z *
        A (f z) (fderiv ℝ f z (Complex.orthonormalBasisOneI i))
          (fderiv ℝ f z (Complex.orthonormalBasisOneI j))) := by
    filter_upwards [hdiff] with z hz
    congr 1
    exact (pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
      (hΦ.mdifferentiableAt one_ne_zero)
      ((hr.contMDiffAt (hN.mem_nhds (hΦN (mem_range_self (U z))))).mdifferentiableAt
        one_ne_zero) hleft hz _ _).symm
  have hpre : e ⁻¹' Metric.ball (0 : ℂ) R = Metric.ball (0 : V) R := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  have hd (k : Fin 2) (x : V) :
      fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single k 1) =
        fderiv ℝ f (e x) (Complex.orthonormalBasisOneI k) := by
    rw [show (fun y => f (e y)) = f ∘ e.toContinuousLinearEquiv by rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    change fderiv ℝ f (e x) (e (EuclideanSpace.single k 1)) = _
    congr 1
    exact Complex.orthonormalBasisOneI.repr_symm_single k
  rw [← DifferentialGeometry.Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex R, integral_congr_ae hpair]
  change _ = ∫ x in Metric.ball (0 : V) R, weight (e x) * A (f (e x))
    (fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single i 1))
    (fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1))
  simp_rw [hd]
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => weight z *
      A (f z) (fderiv ℝ f z (Complex.orthonormalBasisOneI i))
        (fderiv ℝ f z (Complex.orthonormalBasisOneI j))) (Metric.ball (0 : ℂ) R)
  rw [hpre] at h
  exact h.symm

theorem radialDiskEnergyFirstVariation_eq_sum_integral_pullback
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (u : closedDisk → M)
    (hdiff : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)
    (hpair : ∀ i j : Fin 2, IntegrableOn (fun z =>
      pullbackMetricCoefficients g r (Φ (diskExtension u z))
        (fderiv ℝ (Φ ∘ diskExtension u) z (Complex.orthonormalBasisOneI i))
        (fderiv ℝ (Φ ∘ diskExtension u) z (Complex.orthonormalBasisOneI j)))
      (Metric.ball (0 : ℂ) 1))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    radialDiskEnergyFirstVariation g u ψ =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        radialDiskStressCoefficient ψ (Complex.orthonormalBasisOneI.repr.symm x) i j *
          pullbackMetricCoefficients g r (Φ (diskExtension u
            (Complex.orthonormalBasisOneI.repr.symm x)))
            (fderiv ℝ (fun y => Φ (diskExtension u
              (Complex.orthonormalBasisOneI.repr.symm y))) x (EuclideanSpace.single i 1))
            (fderiv ℝ (fun y => Φ (diskExtension u
              (Complex.orthonormalBasisOneI.repr.symm y))) x (EuclideanSpace.single j 1)) := by
  let U := diskExtension u
  let P (i j : Fin 2) (z : ℂ) := g.inner (U z)
    (diskMapPartial U z (Complex.orthonormalBasisOneI i))
    (diskMapPartial U z (Complex.orthonormalBasisOneI j))
  have hP (i j : Fin 2) : IntegrableOn (P i j) (Metric.closedBall (0 : ℂ) 1) := by
    rw [IntegrableOn, ← DifferentialGeometry.Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex (1 : ℝ)]
    apply (hpair i j).congr
    filter_upwards [hdiff] with z hz
    exact pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
      (hΦ.mdifferentiableAt one_ne_zero)
      ((hr.contMDiffAt (hN.mem_nhds (hΦN (mem_range_self (U z))))).mdifferentiableAt
        one_ne_zero) hleft hz _ _
  have hint (i j : Fin 2) : IntegrableOn
      (fun z => radialDiskStressCoefficient ψ z i j * P i j z)
      (Metric.closedBall (0 : ℂ) 1) :=
    (hP i j).bdd_mul (measurable_radialDiskStressCoefficient ψ i j).aestronglyMeasurable
      (Eventually.of_forall fun z => norm_radialDiskStressCoefficient_le hψ z i j)
  have heq (z : ℂ) : deriv ψ (Complex.arg z / (2 * Real.pi)) *
      (diskMapDirectionalEnergyDensity g U (fun z => radialDirection z) z -
        diskMapDirectionalEnergyDensity g U (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2 =
      ∑ i : Fin 2, ∑ j : Fin 2, radialDiskStressCoefficient ψ z i j * P i j z :=
    radial_quadratic_variation_eq_sum ψ z
      ((g.inner (U z)).bilinearComp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
  unfold radialDiskEnergyFirstVariation
  change (∫ z in Metric.closedBall (0 : ℂ) 1, deriv ψ (Complex.arg z / (2 * Real.pi)) *
    (diskMapDirectionalEnergyDensity g U (fun z => radialDirection z) z -
      diskMapDirectionalEnergyDensity g U (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2) = _
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_diskMapPartial_pair_eq_pullback g hΦ hN hr hΦN hleft hdiff
    (fun z => radialDiskStressCoefficient ψ z i j) i j

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold MeasureTheory Set Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem radialDiskEnergyFirstVariation_eq_sum_integral_pullback_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (u : closedDisk → M) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    radialDiskEnergyFirstVariation g u ψ =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        radialDiskStressCoefficient ψ (Complex.orthonormalBasisOneI.repr.symm x) i j *
          pullbackMetricCoefficients g r (Φ (diskExtension u
            (Complex.orthonormalBasisOneI.repr.symm x)))
            (fderiv ℝ (fun y => Φ (diskExtension u
              (Complex.orthonormalBasisOneI.repr.symm y))) x (EuclideanSpace.single i 1))
            (fderiv ℝ (fun y => Φ (diskExtension u
              (Complex.orthonormalBasisOneI.repr.symm y))) x (EuclideanSpace.single j 1)) := by
  obtain ⟨B, _, hB⟩ := exists_riemannian_lipschitz_of_contMDiff g hΦ
  have hf : LipschitzWith (B * L) (Φ ∘ diskExtension u) := by
    apply diskExtension_lipschitz (u := fun z : closedDisk => Φ (u z))
    intro z w
    calc
      edist (Φ (u z)) (Φ (u w)) ≤
          (B : ℝ≥0∞) * riemannianEDistOf g (u z) (u w) := hB _ _
      _ ≤ (B : ℝ≥0∞) * ((L : ℝ≥0∞) * edist z w) :=
        mul_le_mul_of_nonneg_left (hu z w) (by positivity)
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
  have hdiff : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z := by
    filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt] with z hz
    have hrz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (Φ (diskExtension u z)) :=
      ((hr.contMDiffAt (hN.mem_nhds (hΦN (mem_range_self _)))).mdifferentiableAt
        one_ne_zero)
    have hh := hrz.comp z hz.mdifferentiableAt
    rw [show r ∘ (Φ ∘ diskExtension u) = diskExtension u from
      funext fun y => hleft _] at hh
    exact hh
  have hpair (i j : Fin 2) : IntegrableOn (fun z =>
      pullbackMetricCoefficients g r (Φ (diskExtension u z))
        (fderiv ℝ (Φ ∘ diskExtension u) z (Complex.orthonormalBasisOneI i))
        (fderiv ℝ (Φ ∘ diskExtension u) z (Complex.orthonormalBasisOneI j)))
      (Metric.ball (0 : ℂ) 1) := by
    apply integrableOn_bilinear_fderiv_of_lipschitz hf Metric.isOpen_ball.measurableSet
      measure_ball_lt_top.ne (isCompact_range hΦ.continuous)
      (fun z _ => mem_range_self _) (pullbackMetricCoefficients g r)
      ((continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hN hr).mono hΦN)
  exact radialDiskEnergyFirstVariation_eq_sum_integral_pullback
    g hΦ hN hr hΦN hleft u hdiff hpair hψ

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold MeasureTheory Set Filter
open DifferentialGeometry.Topology DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem radialDiskEnergyFirstVariation_eq_sum_integral_weak_pullback
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (q : C(closedDisk, M)) (w : V → F)
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (v : V → F)
    (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    radialDiskEnergyFirstVariation g q ψ =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        radialDiskStressCoefficient ψ (Complex.orthonormalBasisOneI.repr.symm x) i j *
          pullbackMetricCoefficients g r (w x)
            (WithLp.toLp 2 (fun k => (hw k).weakGrad x i))
            (WithLp.toLp 2 (fun k => (hw k).weakGrad x j)) := by
  let e := Complex.orthonormalBasisOneI.repr
  let f : ℂ → F := Φ ∘ diskExtension q
  let A := pullbackMetricCoefficients g r
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun a : F => a i) hx)
  let G (j : Fin 2) (x : V) : F := WithLp.toLp 2 fun i => (hv i).weakGrad x j
  have heBall {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      e z ∈ Metric.ball (0 : V) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz
  have heSymmBall {x : V} (hx : x ∈ Metric.ball (0 : V) 1) :
      e.symm x ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, e.symm.norm_map] using hx
  have hpre : e ⁻¹' Metric.ball (0 : V) 1 = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hmp : MeasurePreserving e (volume.restrict (Metric.ball (0 : ℂ) 1))
      (volume.restrict (Metric.ball (0 : V) 1)) := by
    have h := e.measurePreserving.restrict_preimage (s := Metric.ball (0 : V) 1)
      Metric.isOpen_ball.measurableSet
    rwa [hpre] at h
  have hfe : EqOn (fun x => f (e.symm x)) v (Metric.ball (0 : V) 1) := by
    intro x hx
    change Φ (diskExtension q (e.symm x)) = v x
    rw [hq _ (heSymmBall hx), e.apply_symm_apply]
    obtain ⟨p, hp⟩ := hvK hx
    rw [← hp, hleft]
  have hf : EqOn f (v ∘ e) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [e.symm_apply_apply, Function.comp_apply] using hfe (heBall hz)
  have hdiff : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    have hdv : DifferentiableAt ℝ v (e z) :=
      (hvc.contDiffAt (Metric.isOpen_ball.mem_nhds (heBall hz))).differentiableAt one_ne_zero
    have hdr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (v (e z)) :=
      (hr.contMDiffAt (hN.mem_nhds (hΦN (hvK (heBall hz))))).mdifferentiableAt one_ne_zero
    have hgerm : diskExtension q =ᶠ[𝓝 z] r ∘ (v ∘ e) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact hq y hy
    exact (hdr.comp z (hdv.comp z e.differentiableAt).mdifferentiableAt).congr_of_eventuallyEq
      hgerm
  have hgradient (i : ι) : (hv i).weakGrad =ᵐ[volume.restrict (Metric.ball (0 : V) 1)]
      DeGiorgi.smoothGradField (fun x => v x i) :=
    (hv i).weakGrad_ae_eq_smoothGradField (by norm_num) Metric.isOpen_ball
      ((contDiff_piLp_apply (p := 2) (i := i)).comp_contDiffOn hvc)
  have hcols : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), ∀ j,
      G j x = fderiv ℝ v x (EuclideanSpace.single j 1) := by
    filter_upwards [ae_all_iff.mpr hgradient, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hxB
    intro j
    ext i
    have hd : DifferentiableAt ℝ v x :=
      (hvc.contDiffAt (Metric.isOpen_ball.mem_nhds hxB)).differentiableAt one_ne_zero
    let L : F →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) i
    have hh := L.hasFDerivAt.comp x hd.hasFDerivAt
    change (hv i).weakGrad x j = (fderiv ℝ v x (EuclideanSpace.single j 1)) i
    rw [hx i]
    change fderiv ℝ (L ∘ v) x (EuclideanSpace.single j 1) = _
    rw [hh.fderiv]
    rfl
  have hA : ContinuousOn A (range Φ) :=
    (continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hN hr).mono hΦN
  have hAv : ContinuousOn (fun x => A (v x)) (Metric.ball (0 : V) 1) :=
    hA.comp hvc.continuousOn hvK
  have hnorm : ContinuousOn (fun y => ‖A y‖) (range Φ) :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨D, hD⟩ := (isCompact_range hΦ.continuous).bddAbove_image hnorm
  have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), ‖A (v x)‖ ≤ D :=
    (ae_restrict_mem Metric.isOpen_ball.measurableSet).mono
      fun x hx => hD (mem_image_of_mem _ (hvK hx))
  have hG (j : Fin 2) : MemLp (G j) 2 (volume.restrict (Metric.ball (0 : V) 1)) :=
    MemLp.of_eval_piLp fun i => (hv i).weakGrad_component_memLp j
  have hAm : AEStronglyMeasurable (fun x => A (v x))
      (volume.restrict (Metric.ball (0 : V) 1)) :=
    hAv.aestronglyMeasurable Metric.isOpen_ball.measurableSet
  have hI (i j : Fin 2) :
      IntegrableOn (fun x => A (v x) (G i x) (G j x)) (Metric.ball (0 : V) 1) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (v x))
      (fun a b => (hAm.apply_continuousLinearMap a).apply_continuousLinearMap b)
      hbound (hG i) (hG j)
  have hfcol : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1), ∀ j,
      fderiv ℝ f z (Complex.orthonormalBasisOneI j) = G j (e z) := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hcols,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzB
    intro j
    have heq : f =ᶠ[𝓝 z] v ∘ e := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzB] with y hy
      exact hf hy
    have hdv : DifferentiableAt ℝ v (e z) :=
      (hvc.contDiffAt (Metric.isOpen_ball.mem_nhds (heBall hzB))).differentiableAt one_ne_zero
    rw [heq.fderiv_eq, fderiv_comp z hdv e.differentiableAt, e.hasFDerivAt.fderiv]
    change fderiv ℝ v (e z) (e (Complex.orthonormalBasisOneI j)) = _
    rw [Complex.orthonormalBasisOneI.repr_self, hz j]
  have hpair (i j : Fin 2) : IntegrableOn (fun z =>
      A (f z) (fderiv ℝ f z (Complex.orthonormalBasisOneI i))
        (fderiv ℝ f z (Complex.orthonormalBasisOneI j))) (Metric.ball (0 : ℂ) 1) := by
    apply (hmp.integrable_comp_of_integrable (hI i j)).congr
    filter_upwards [hfcol, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzB
    rw [hf hzB, Function.comp_apply, hz i, hz j]
    rfl
  rw [radialDiskEnergyFirstVariation_eq_sum_integral_pullback
    g hΦ hN hr hΦN hleft q hdiff hpair hψ]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [hcols, hvw, ae_restrict_mem Metric.isOpen_ball.measurableSet]
    with x hx hvwx hxB
  have heq : (fun y => f (e.symm y)) =ᶠ[𝓝 x] v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxB] with y hy
    exact hfe hy
  have hvals : f (e.symm x) = w x := (hfe hxB).trans hvwx
  change radialDiskStressCoefficient ψ (e.symm x) i j *
      A (f (e.symm x))
        (fderiv ℝ (fun y => f (e.symm y)) x (EuclideanSpace.single i 1))
        (fderiv ℝ (fun y => f (e.symm y)) x (EuclideanSpace.single j 1)) = _
  rw [hvals, heq.fderiv_eq, ← hx i, ← hx j]
  rfl

end DifferentialGeometry.Geometry

end
