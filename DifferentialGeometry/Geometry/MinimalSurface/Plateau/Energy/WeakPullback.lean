import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Integrability
import DifferentialGeometry.Geometry.Metric.Pullback.Continuity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import DifferentialGeometry.Analysis.Integration.Integral.ComplexDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Complex
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence

noncomputable section
open Set Filter MeasureTheory Manifold
open scoped ENNReal Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_diskMapEnergyDensity_comp_eq_weak_pullback_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {U K : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U) {R : ℝ} {v : V → F}
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 R))
    (hvc : ContDiffOn ℝ 1 v (Metric.ball 0 R)) (hvK : MapsTo v (Metric.ball 0 R) K) :
    IntegrableOn (diskMapEnergyDensity g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))))
        (Metric.ball (0 : ℂ) R) ∧
      (∫ z in Metric.ball (0 : ℂ) R,
        diskMapEnergyDensity g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) z) =
        (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) R, pullbackMetricCoefficients g r (v x)
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) / 2 := by
  let e := Complex.orthonormalBasisOneI.repr
  let A := pullbackMetricCoefficients g r
  let G (j : Fin 2) (x : V) : F := WithLp.toLp 2 fun i => (hv i).weakGrad x j
  have hpre : e ⁻¹' Metric.ball (0 : V) R = Metric.ball (0 : ℂ) R := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have hmp : MeasurePreserving e (volume.restrict (Metric.ball (0 : ℂ) R))
      (volume.restrict (Metric.ball (0 : V) R)) := by
    have hh := e.measurePreserving.restrict_preimage (s := Metric.ball (0 : V) R)
      Metric.isOpen_ball.measurableSet
    rwa [hpre] at hh
  have hgrad (i : ι) : (hv i).weakGrad =ᵐ[volume.restrict (Metric.ball (0 : V) R)]
      DeGiorgi.smoothGradField (fun x => v x i) :=
    (hv i).weakGrad_ae_eq_smoothGradField (by norm_num) Metric.isOpen_ball
      ((contDiff_piLp_apply (p := 2) (i := i)).comp_contDiffOn hvc)
  have hcols : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) R), ∀ j,
      G j x = fderiv ℝ v x (EuclideanSpace.single j 1) := by
    filter_upwards [ae_all_iff.mpr hgrad, ae_restrict_mem Metric.isOpen_ball.measurableSet]
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
  have hA : ContinuousOn A K :=
    (continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hU hr).mono hKU
  have hAv : ContinuousOn (fun x => A (v x)) (Metric.ball (0 : V) R) :=
    hA.comp hvc.continuousOn hvK
  have hnorm : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) R), ‖A (v x)‖ ≤ C :=
    (ae_restrict_mem Metric.isOpen_ball.measurableSet).mono
      fun x hx => hC (mem_image_of_mem _ (hvK hx))
  have hG (j : Fin 2) : MemLp (G j) 2 (volume.restrict (Metric.ball (0 : V) R)) :=
    MemLp.of_eval_piLp fun i => (hv i).weakGrad_component_memLp j
  have hAm : AEStronglyMeasurable (fun x => A (v x))
      (volume.restrict (Metric.ball (0 : V) R)) :=
    hAv.aestronglyMeasurable Metric.isOpen_ball.measurableSet
  have hI (j : Fin 2) :
      IntegrableOn (fun x => A (v x) (G j x) (G j x)) (Metric.ball (0 : V) R) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (v x))
      (fun a b => (hAm.apply_continuousLinearMap a).apply_continuousLinearMap b)
      hbound (hG j) (hG j)
  let Q (x : V) := (∑ j : Fin 2, A (v x) (G j x) (G j x)) / 2
  have hQI : Integrable Q (volume.restrict (Metric.ball (0 : V) R)) :=
    (integrable_finsetSum _ fun j _ => hI j).div_const 2
  have hQcomp : Integrable (fun z => Q (e z)) (volume.restrict (Metric.ball (0 : ℂ) R)) :=
    hmp.integrable_comp_of_integrable hQI
  have heq : diskMapEnergyDensity g (fun z => r (v (e z))) =ᵐ[
      volume.restrict (Metric.ball (0 : ℂ) R)] (fun z => Q (e z)) := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hcols,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzB
    have hx : e z ∈ Metric.ball (0 : V) R := by
      simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hzB
    have hdv : DifferentiableAt ℝ v (e z) :=
      (hvc.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero
    have hdr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (v (e z)) :=
      (hr.contMDiffAt (hU.mem_nhds (hKU (hvK hx)))).mdifferentiableAt (by simp)
    have hd (j : Fin 2) : diskMapPartial (fun z => r (v (e z))) z (Complex.orthonormalBasisOneI j) =
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (v (e z)) (G j (e z)) := by
      have he : DifferentiableAt ℝ (v ∘ e) z := hdv.comp z e.differentiableAt
      change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (r ∘ (v ∘ e)) z (Complex.orthonormalBasisOneI j) = _
      have hchain := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, E))
        z hdr he.mdifferentiableAt
      have hvd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (v ∘ e) z (Complex.orthonormalBasisOneI j) =
          G j (e z) := by
        rw [mfderiv_eq_fderiv, fderiv_comp z hdv e.differentiableAt]
        change fderiv ℝ v (e z) (fderiv ℝ e z (Complex.orthonormalBasisOneI j)) = _
        rw [e.hasFDerivAt.fderiv]
        change fderiv ℝ v (e z) (e (Complex.orthonormalBasisOneI j)) = _
        rw [Complex.orthonormalBasisOneI.repr_self, hz j]
      exact (congrArg (fun L : ℂ →L[ℝ] E => L (Complex.orthonormalBasisOneI j)) hchain).trans
        (congrArg (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (v (e z))) hvd)
    have h0 := hd 0
    have h1 := hd 1
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    simp only [diskMapEnergyDensity, h0, h1, Q, Fin.sum_univ_two, A,
      pullbackMetricCoefficients_apply]
  refine ⟨hQcomp.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, hmp.integral_comp e.toMeasurableEquiv.measurableEmbedding Q]
  rw [show Q = fun x => (∑ j : Fin 2, A (v x) (G j x) (G j x)) / 2 from rfl,
    integral_div, integral_finsetSum _ (fun j _ => hI j)]

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem sum_integral_pullback_gradient_eq_two_mul_riemannianDiskEnergy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (u : closedDisk → M) {L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (L : ℝ≥0∞) * edist x y) :
    (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
      pullbackMetricCoefficients g r (Φ (diskExtension u (Complex.orthonormalBasisOneI.repr.symm x)))
        (fderiv ℝ (fun y => Φ (diskExtension u (Complex.orthonormalBasisOneI.repr.symm y)))
          x (EuclideanSpace.single j 1))
        (fderiv ℝ (fun y => Φ (diskExtension u (Complex.orthonormalBasisOneI.repr.symm y)))
          x (EuclideanSpace.single j 1))) = 2 * riemannianDiskEnergy g u := by
  obtain ⟨C, _, hC⟩ := exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le g hΦ
  have hf := (hC (diskExtension u) L (diskExtension_riemannian_lipschitz g hu)).1
  have hA := (continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hN hr).mono hΦN
  have h := sum_integral_target_energy_comp_complex_repr_symm hf
    (isCompact_range hΦ.continuous) (pullbackMetricCoefficients g r) hA
    (a := 1) (fun z _ => mem_range_self _)
  change _ = 2 * _ at h
  rw [restrict_ball_eq_restrict_closedBall_complex (1 : ℝ)] at h
  apply h.trans
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Metric.closedBall (0 : ℂ) 1)
    (ae_mdifferentiableAt_of_riemannian_lipschitz g (diskExtension_riemannian_lipschitz g hu))]
    with z hz
  have hp (a : ℂ) := pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
    (hΦ.mdifferentiableAt one_ne_zero)
    ((hr.contMDiffAt (hN.mem_nhds (hΦN (mem_range_self _)))).mdifferentiableAt one_ne_zero)
    hleft hz a a
  change _ = diskMapEnergyDensity g (diskExtension u) z
  simp only [Function.comp_apply]
  rw [hp 1, hp Complex.I]
  rfl

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

omit [CompactSpace M] in
theorem integrable_diskMapEnergyDensity_and_energy_eq_of_contDiffOn_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {N K : Set F}
    (hN : IsOpen N) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hK : IsCompact K) (hKN : K ⊆ N)
    (q : C(closedDisk, M)) (w : V → F)
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) K)
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z))) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension q)) (Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskEnergy g q =
        (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1, pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) / 2 := by
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun a : F => a i) hx)
  have hmain := integral_diskMapEnergyDensity_comp_eq_weak_pullback_energy
    g hN hr hK hKN hv hvc hvK
  have henergy : (∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
      pullbackMetricCoefficients g r (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in Metric.ball (0 : V) 1,
        pullbackMetricCoefficients g r (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hvw] with x hx
    rw [hx]
    rfl
  rw [henergy] at hmain
  have hμ := restrict_ball_eq_restrict_closedBall_complex (1 : ℝ)
  have hclosed : IntegrableOn
      (diskMapEnergyDensity g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))))
      (Metric.closedBall (0 : ℂ) 1) := by
    simpa only [IntegrableOn, ← hμ] using hmain.1
  have heq : diskMapEnergyDensity g (diskExtension q) =ᵐ[
      volume.restrict (Metric.closedBall (0 : ℂ) 1)]
      diskMapEnergyDensity g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) := by
    filter_upwards [ae_disk_interior] with z hz
    have hgerm : diskExtension q =ᶠ[𝓝 z]
        (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact hq y hy
    unfold diskMapEnergyDensity diskMapPartial
    rw [hgerm.mfderiv_eq, hgerm.self_of_nhds]
  refine ⟨hclosed.congr heq.symm, ?_⟩
  change (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension q) z) = _
  rw [integral_congr_ae heq, ← hμ]
  exact hmain.2

end DifferentialGeometry.Geometry

end
