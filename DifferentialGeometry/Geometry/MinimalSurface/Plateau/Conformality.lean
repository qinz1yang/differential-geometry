import DifferentialGeometry.Geometry.HarmonicMap.HopfDifferential
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.SmoothHarmonicMap
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.StressCoordinates
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticResidual
import DifferentialGeometry.Analysis.Complex.HolomorphicMoments
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Attainment
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.BoundaryRecovery
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RecoveryStationarity

section

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem differentiableOn_hopfDifferentialCoefficient_representative_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F)
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    : DifferentiableOn ℂ (hopfDifferentialCoefficient g
        (fun z => r (v (Complex.orthonormalBasisOneI.repr z)))) (Metric.ball (0 : ℂ) 1) := by
  let hv (i : Fin n) := (hw i).congr
    (hvw.symm.mono fun x hx => congrArg (fun y : F => y i) hx)
  let e := Complex.orthonormalBasisOneI.repr
  have hrv := (contMDiffOn_representative_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK).1
  have hW : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun z => r (v (e z))) (Metric.ball (0 : ℂ) 1) :=
    hrv.comp e.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn (fun z hz => by
      change e z ∈ Metric.ball (0 : V) 1
      simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz)
  exact differentiableOn_hopfDifferentialCoefficient g Metric.isOpen_ball hW
    (diskMapTension_representative_eq_zero_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK)

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem norm_hopfDifferentialCoefficient_le_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) :
    ‖hopfDifferentialCoefficient g U z‖ ≤ diskMapEnergyDensity g U z := by
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := (g.inner (U z)).bilinearComp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
  have hp : LinearMap.IsPosSemidef Q.toBilinForm :=
    pullbackMetricCoefficients_isPosSemidef g U z
  have hc := hp.abs_apply_le_mul_self_add_inv_mul_self (1 : ℂ) Complex.I
    (show (0 : ℝ) < 1 by norm_num)
  simp only [one_mul, inv_one] at hc
  have ha := metric_inner_self_nonneg g (U z) (diskMapPartial U z 1)
  have hb := metric_inner_self_nonneg g (U z) (diskMapPartial U z Complex.I)
  change 0 ≤ Q 1 1 at ha
  change 0 ≤ Q Complex.I Complex.I at hb
  change |Q 1 Complex.I| ≤ (Q 1 1 + Q Complex.I Complex.I) / 2 at hc
  have hab : |Q 1 1 - Q Complex.I Complex.I| ≤ Q 1 1 + Q Complex.I Complex.I :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (hopfDifferentialCoefficient g U z)
  change ‖hopfDifferentialCoefficient g U z‖ ≤ (Q 1 1 + Q Complex.I Complex.I) / 2
  apply hn.trans
  change |(Q 1 1 - Q Complex.I Complex.I) / 4| + |-Q 1 Complex.I / 2| ≤ _
  rw [abs_div, abs_div, abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem integrableOn_hopfDifferentialCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {Ω : Set ℂ}
    (hm : AEStronglyMeasurable (hopfDifferentialCoefficient g U) (volume.restrict Ω))
    (henergy : IntegrableOn (diskMapEnergyDensity g U) Ω) :
    IntegrableOn (hopfDifferentialCoefficient g U) Ω := by
  exact henergy.mono' hm (Eventually.of_forall fun z =>
    norm_hopfDifferentialCoefficient_le_diskMapEnergyDensity g U z)

theorem integrableOn_hopfDifferentialCoefficient_of_differentiableOn
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {Ω : Set ℂ}
    (hΩ : MeasurableSet Ω)
    (hhol : DifferentiableOn ℂ (hopfDifferentialCoefficient g U) Ω)
    (henergy : IntegrableOn (diskMapEnergyDensity g U) Ω) :
    IntegrableOn (hopfDifferentialCoefficient g U) Ω :=
  integrableOn_hopfDifferentialCoefficient g (hhol.continuousOn.aestronglyMeasurable hΩ) henergy

theorem radial_energy_difference_eq_re_hopf
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) :
    (diskMapDirectionalEnergyDensity g U (fun z => radialDirection z) z -
      diskMapDirectionalEnergyDensity g U (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2 =
      2 * (hopfDifferentialCoefficient g U z * (radialDirection z : ℂ) ^ 2).re := by
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := (g.inner (U z)).bilinearComp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
  have hs : Q Complex.I 1 = Q 1 Complex.I := g.symm _ _ _
  change (Q (radialDirection z) (radialDirection z) -
    Q (Complex.I * (radialDirection z : ℂ)) (Complex.I * (radialDirection z : ℂ))) / 2 = _
  rw [bilinear_quadratic_sub_quarter_turn, hs]
  simp only [hopfDifferentialCoefficient, pow_two, Complex.mul_re, Complex.mul_im]
  change _ = 2 * (((Q 1 1 - Q Complex.I Complex.I) / 4) * _ -
    (-Q 1 Complex.I / 2) * _)
  ring

theorem radialDiskEnergyFirstVariation_eq_re_hopf_integral
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : closedDisk → M) (ψ : ℝ → ℝ) :
    radialDiskEnergyFirstVariation g u ψ =
      2 * ∫ z in Metric.ball (0 : ℂ) 1,
        deriv ψ (Complex.arg z / (2 * Real.pi)) *
          (hopfDifferentialCoefficient g (diskExtension u) z *
            (Complex.exp ((Complex.arg z : ℂ) * Complex.I)) ^ 2).re := by
  unfold radialDiskEnergyFirstVariation
  rw [← restrict_ball_eq_restrict_closedBall_complex (1 : ℝ), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : ℂ))] with z hz
  have he : (radialDirection z : ℂ) = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
    have h := radialDirection_reconstruct z
    rw [Complex.real_smul] at h
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    exact mul_left_cancel₀ hn (h.trans (Complex.norm_mul_exp_arg_mul_I z).symm)
  have h := radial_energy_difference_eq_re_hopf g (diskExtension u) z
  rw [he] at h
  calc
    _ = deriv ψ (Complex.arg z / (2 * Real.pi)) *
        ((diskMapDirectionalEnergyDensity g (diskExtension u) (fun z => radialDirection z) z -
          diskMapDirectionalEnergyDensity g (diskExtension u)
            (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2) := by ring
    _ = _ := by rw [h]; ring

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapConformalAt_of_holomorphic_hopf_of_radial_variations
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : closedDisk → M)
    (hhol : DifferentiableOn ℂ (hopfDifferentialCoefficient g (diskExtension q))
      (Metric.ball (0 : ℂ) 1))
    (henergy : IntegrableOn (diskMapEnergyDensity g (diskExtension q))
      (Metric.ball (0 : ℂ) 1))
    (hstationary : ∀ ψ : ℝ → ℝ, Differentiable ℝ ψ →
      (∃ C : ℝ≥0, LipschitzWith C ψ) → Function.Periodic ψ 1 →
      radialDiskEnergyFirstVariation g q ψ = 0) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z := by
  have hi := integrableOn_hopfDifferentialCoefficient_of_differentiableOn g
    Metric.isOpen_ball.measurableSet hhol henergy
  have hzero := eq_zero_on_unit_disk_of_holomorphic_radial_variations hhol hi (fun ψ hψ hLip hper => by
    have h := hstationary ψ hψ hLip hper
    rw [radialDiskEnergyFirstVariation_eq_re_hopf_integral] at h
    linarith)
  intro z hz
  exact (hopfDifferentialCoefficient_eq_zero_iff g (diskExtension q) z).mp (hzero hz)

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "μ" => volume.restrict (Metric.ball (0 : V) 1)

theorem diskMapConformalAt_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun p : C(closedDisk, M) => riemannianDiskEnergy g p) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[μ]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 μ) atTop (𝓝 0))
    (hweak : ∀ i (z : Lp V 2 μ),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (v : V → F) (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[μ] w) (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    {KΓ : ℝ≥0} (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ)
    : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z := by
  let hv (i : Fin n) := (hw i).congr
    (hvw.symm.mono fun x hx => congrArg (fun y : F => y i) hx)
  have hvs := (contMDiffOn_representative_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK).2
  have hhopf := differentiableOn_hopfDifferentialCoefficient_representative_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak v hvc hvw hvK
  have hsame : EqOn (hopfDifferentialCoefficient g (diskExtension q))
      (hopfDifferentialCoefficient g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))))
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have heq : diskExtension q =ᶠ[𝓝 z]
        (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact hq y hy
    unfold hopfDifferentialCoefficient diskMapPartial
    rw [heq.mfderiv_eq, heq.self_of_nhds]
  have hhol := hhopf.congr hsame
  have henergy := (integrable_diskMapEnergyDensity_and_energy_eq_of_contDiffOn_representative
    g hN (hr.of_le (by simp)) (isCompact_range hΦ.continuous) hΦN
    q w hw v (hvs.of_le (by simp)) hvw hvK hq).1
  apply diskMapConformalAt_of_holomorphic_hopf_of_radial_variations g q hhol
    (henergy.mono_set Metric.ball_subset_closedBall)
  intro ψ hψ hLip hper
  obtain ⟨C, hC⟩ := hLip
  exact radialDiskEnergyFirstVariation_eq_zero_of_minimizing_sequence
    g hΦ hN hr hΦN hleft u hu hmin w hs hw hrep hweak hae
    v (hvs.of_le (by simp)) hvw hvK q hq hΓ τ hτ hτ0 hτ1 hτ2 htrace hψ hC hper

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [PreconnectedSpace M]

theorem diskMapConformalAt_of_harmonic_energy_minimizer
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => γ (t : loopCircle)))
    (q : C(closedDisk, M)) (hq : DiskSmoothInterior (E := E) q)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension q) z = 0)
    (hE : IntegrableOn (diskMapEnergyDensity g (diskExtension q))
      (Metric.closedBall (0 : ℂ) 1))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ)
    (hmin : riemannianDiskEnergy g q = sInf
      ((fun u : C(closedDisk, M) => riemannianDiskEnergy g u) ''
        weaklyMonotoneDiskCompetitors g γ)) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z := by
  have hhol := differentiableOn_hopfDifferentialCoefficient g Metric.isOpen_ball hq hharm
  obtain ⟨qn, τn, a, hqn, _, _, ha, halim, hcore, _, henergy, _⟩ :=
    exists_weakly_monotone_disks_tendsto_energy_of_contMDiffOn
      g γ hγ q (hq.of_le (by simp)) hE τ hτ hτ0 hτ1 hτ2 htrace
  apply diskMapConformalAt_of_holomorphic_hopf_of_radial_variations g q hhol
    (hE.mono_set Metric.ball_subset_closedBall)
  intro ψ hψ hLip hper
  obtain ⟨C, hC⟩ := hLip
  exact radialDiskEnergyFirstVariation_eq_zero_of_exhausting_recovery
    g q qn hqn (fun n => (ha n).2.le) halim hcore hE henergy hmin hψ hC hper

end DifferentialGeometry.Geometry

end

end
