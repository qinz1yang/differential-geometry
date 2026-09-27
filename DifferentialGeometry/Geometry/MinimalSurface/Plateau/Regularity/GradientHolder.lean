import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ChartEnergy
import DifferentialGeometry.Geometry.HarmonicMap.ChartCoercivity
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CampanatoGradient
import DifferentialGeometry.Analysis.Integration.Integral.MeanSquareDeviation
import DifferentialGeometry.Analysis.Asymptotics.PowerDecay

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_chart_gradient_excess_comparison_of_minimizing_sequence
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
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    : let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ σ A : ℝ, 0 < ρ ∧ 0 < σ ∧ 0 ≤ A ∧
      Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        (Metric.ball x₀ (2 * σ) ⊆ Metric.ball x₀ ρ) ∧
        ∀ b ∈ Metric.ball x₀ σ, ∀ R : ℝ, 0 < R → R ≤ σ → ∀ s : ℝ, 0 ≤ s → s ≤ R / 8 →
          (∑ k, ∫ x in Metric.ball b s,
            ‖(hz k).weakGrad x - ⨍ y in Metric.ball b s, (hz k).weakGrad y‖ ^ 2) ≤
            16384 * (s / R) ^ 4 *
              (∑ k, ∫ x in Metric.ball b R,
                ‖(hz k).weakGrad x - ⨍ y in Metric.ball b R, (hz k).weakGrad y‖ ^ 2) +
            A * R ^ ((9 : ℝ) / 4) := by
  classical
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let z₀ := χ (v x₀)
  let z : V → H := fun x => χ (v x) - z₀
  let Ψ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (y + z₀))
  let B := pullbackMetricCoefficients g Ψ
  obtain ⟨ρ, τ, hρ, hτ, hρB, hbox, hzc, hzbox, hz, hzgrad, hbase, hcomp⟩ :=
    exists_chart_harmonic_replacement_comparison_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  obtain ⟨lam, L, hlam, hcoerce, hBLip⟩ :=
    exists_centered_chart_metric_bounds_on_coordinate_box g p z₀ τ hbox
  obtain ⟨ρq, ηq, Kq, hρq, hηq, hηqρ, hKq, hρqB, hzqc, hzq, hzqgrad, hpower⟩ :=
    exists_chart_weak_gradient_power_bound_of_exponent_lt_two
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
      (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2)
  have hηρq : Metric.ball x₀ ηq ⊆ Metric.ball x₀ ρq := Metric.ball_subset_ball (by linarith)
  let hzη (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hηρq (hzq k)
  have hpCamp (b : DeGiorgi.CampanatoBall x₀ ηq) :
      (∑ k, ∫ x in Metric.ball b.center b.radius, ‖(hzη k).weakGrad x‖ ^ 2) ≤
        Kq * b.radius ^ (2 * ((3 : ℝ) / 4)) := by
    have hh := hpower b.center (b.subset_ball (Metric.mem_ball_self b.radius_pos))
      b.radius b.radius_pos b.radius_le
    norm_num at hh ⊢
    exact hh
  obtain ⟨Lz, hLz, hHolder⟩ := exists_holder_bound_of_continuous_weak_gradient_power_bound
    hηq (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) hzη
    (hzqc.mono (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith)))) hKq hpCamp
  have hxnorm : ‖x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx₀
  let σ := min (min (ρ / 4) (ηq / 4)) ((1 - ‖x₀‖) / 4)
  have hσ : 0 < σ := lt_min (lt_min (by positivity) (by positivity)) (by linarith)
  have hσρ : σ ≤ ρ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hση : σ ≤ ηq / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hσx : ‖x₀‖ + 2 * σ < 1 := by
    have hh := min_le_right (min (ρ / 4) (ηq / 4)) ((1 - ‖x₀‖) / 4)
    dsimp only [σ]
    linarith
  let Cerr := 2 * (L : ℝ) * (Module.finrank ℝ E + 1) * Lz / lam
  have hCerr : 0 ≤ Cerr := by dsimp only [Cerr]; positivity
  let A := 16386 * Cerr * Kq
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let K := {y : H | ∀ k, |y k| ≤ τ}
  have hK : IsCompact K := isCompact_coordinate_box (fun _ => τ)
  refine ⟨ρ, σ, A, hρ, hσ, hA, hρB, hz, hzgrad,
    Metric.ball_subset_ball (by linarith), ?_⟩
  intro b hb R hR hRσ s hs hsR
  have hbDist : dist b x₀ < σ := Metric.mem_ball.mp hb
  have hbNorm : ‖b‖ + R < 1 := by
    have hn : ‖b‖ ≤ dist b x₀ + ‖x₀‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (b - x₀) x₀
    linarith
  have hballρ : Metric.ball b R ⊆ Metric.ball x₀ ρ := by
    intro x hx
    exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx, dist_triangle x b x₀])
  have hballη : Metric.ball b R ⊆ Metric.ball x₀ (ηq / 2) := by
    intro x hx
    exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx, dist_triangle x b x₀])
  have hbη : b ∈ Metric.ball x₀ (ηq / 2) := Metric.mem_ball.mpr (by linarith)
  have hballq : Metric.ball b R ⊆ Metric.ball x₀ ρq := hballη.trans
    ((Metric.ball_subset_ball (by linarith)).trans hηρq)
  let hza (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hballρ (hz k)
  let hzqa (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hballq (hzq k)
  have hGq (k : Fin (Module.finrank ℝ E)) : (hza k).weakGrad =ᵐ[volume.restrict (Metric.ball b R)]
      (hzqa k).weakGrad := DeGiorgi.MemW1pWitness.ae_eq Metric.isOpen_ball (hza k) (hzqa k)
  have hEz : (∑ k, ∫ x in Metric.ball b R, ‖(hza k).weakGrad x‖ ^ 2) ≤ Kq * R ^ ((3 : ℝ) / 2) := by
    have heq : (∑ k, ∫ x in Metric.ball b R, ‖(hza k).weakGrad x‖ ^ 2) =
        ∑ k, ∫ x in Metric.ball b R, ‖(hzq k).weakGrad x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact integral_congr_ae ((hGq k).mono fun x hx => congrArg (fun a : V => ‖a‖ ^ 2) hx)
    rw [heq]
    exact hpower b (Metric.ball_subset_ball (by linarith) hbη) R hR (hRσ.trans (by linarith))
  obtain ⟨h, hh, htrace, hhK, hEuler, _, hmetric⟩ := hcomp b R hR hbNorm hballρ
  have hzK : ∀ᵐ x ∂volume.restrict (Metric.ball b R), z x ∈ K := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hzbox x (Metric.ball_subset_closedBall (hballρ hx))
  have hzb : z b ∈ K := hzbox b (Metric.ball_subset_closedBall (hballρ (Metric.mem_ball_self hR)))
  have hminz : (∑ j : Fin 2, ∫ x in Metric.ball b R, B (z x)
      (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))
      (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.ball b R, B (h x)
        (WithLp.toLp 2 (fun k => (hh k).weakGrad x j))
        (WithLp.toLp 2 (fun k => (hh k).weakGrad x j)) := by
    have heq : (∑ j : Fin 2, ∫ x in Metric.ball b R, B (z x)
        (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))
        (WithLp.toLp 2 (fun k => (hza k).weakGrad x j))) =
        ∑ j : Fin 2, ∫ x in Metric.ball b R, pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset hballρ hbase).mono
        fun x hx => (hx j).symm)
    exact heq.trans_le hmetric
  have herr := integral_weakGrad_difference_sq_le_of_holder_harmonic_comparison hR
    (by norm_num : (0 : ℝ) ≤ 3 / 4) hLz hza hh htrace hEuler B hK hzK hhK hzb hBLip
    (fun v₁ v₂ => g.symm _ _ _) hlam (hcoerce (z b) hzb)
    (fun x hx => hHolder x (hballη hx) b hbη) hminz
  have hD : (∑ k, ∫ x in Metric.ball b R, ‖(hza k).weakGrad x - (hh k).weakGrad x‖ ^ 2) ≤
      Cerr * Kq * R ^ ((9 : ℝ) / 4) := by
    have hc : (2 * (L : ℝ) * (Fintype.card (Fin (Module.finrank ℝ E)) + 1) * Lz / lam) = Cerr := by
      simp only [Fintype.card_fin, Cerr]
    rw [hc] at herr
    apply herr.trans
    have hp := mul_le_mul_of_nonneg_left hEz
      (mul_nonneg hCerr (Real.rpow_nonneg hR.le ((3 : ℝ) / 4)))
    have hid : Cerr * R ^ ((3 : ℝ) / 4) * (Kq * R ^ ((3 : ℝ) / 2)) =
        Cerr * Kq * R ^ ((9 : ℝ) / 4) := by
      rw [show (9 : ℝ) / 4 = 3 / 4 + 3 / 2 by norm_num, Real.rpow_add hR]
      ring
    exact hp.trans_eq hid
  have hexcess := integral_weakGrad_sub_average_sq_le_of_harmonic_comparison hR hs hsR hza hh hEuler
  have hratio : 0 ≤ s / R ∧ s / R ≤ 1 := ⟨div_nonneg hs hR.le, (div_le_one hR).mpr (by linarith)⟩
  have hpow : (s / R) ^ 4 ≤ 1 := pow_le_one₀ hratio.1 hratio.2
  have hcoef : 2 + 16384 * (s / R) ^ 4 ≤ 16386 := by linarith
  have hstep := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 2 + 16384 * (s / R) ^ 4)
  have hstep' := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (mul_nonneg hCerr hKq) (Real.rpow_nonneg hR.le ((9 : ℝ) / 4)))
  have hsum := add_le_add_right (hstep.trans hstep')
    (16384 * (s / R) ^ 4 * ∑ k, ∫ x in Metric.ball b R,
      ‖(hza k).weakGrad x - ⨍ y in Metric.ball b R, (hza k).weakGrad y‖ ^ 2)
  have ht := hexcess.trans hsum
  simpa only [A, hza, DeGiorgi.MemW1pWitness.restrict, mul_assoc] using ht

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_chart_gradient_excess_power_bound_of_minimizing_sequence
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
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    : let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ σ K : ℝ, 0 < ρ ∧ 0 < σ ∧ 0 ≤ K ∧
      Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        (Metric.ball x₀ (2 * σ) ⊆ Metric.ball x₀ ρ) ∧
        ∀ b ∈ Metric.ball x₀ σ, ∀ s : ℝ, 0 < s → s ≤ σ →
          (∑ k, ∫ x in Metric.ball b s,
            ‖(hz k).weakGrad x - ⨍ y in Metric.ball b s, (hz k).weakGrad y‖ ^ 2) ≤
            K * s ^ ((9 : ℝ) / 4) := by
  obtain ⟨ρ, σ, A, hρ, hσ, hA, hρB, hz, hzgrad, hσρ, hexcess⟩ :=
    exists_chart_gradient_excess_comparison_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  let M := ∑ k, ∫ x in Metric.ball x₀ ρ, ‖(hz k).weakGrad x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  obtain ⟨K, hK, hpower⟩ := exists_uniform_radius_power_bound_of_decay
    (M := M) (p := 4) (q := (9 : ℝ) / 4) hσ (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (0 : ℝ) ≤ 16384) hA hM (by norm_num) (by norm_num)
  refine ⟨ρ, σ, K, hρ, hσ, hK, hρB, hz, hzgrad, hσρ, ?_⟩
  intro b hb s hs hsσ
  have hball : Metric.ball b σ ⊆ Metric.ball x₀ ρ := by
    apply Set.Subset.trans _ hσρ
    intro x hx
    exact Metric.mem_ball.mpr (by
      linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hb, dist_triangle x b x₀])
  let : IsFiniteMeasure (volume.restrict (Metric.ball b σ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let Ex := fun a => ∑ k, ∫ x in Metric.ball b a,
    ‖(hz k).weakGrad x - ⨍ y in Metric.ball b a, (hz k).weakGrad y‖ ^ 2
  have hLp (k : Fin (Module.finrank ℝ E)) :
      MemLp (hz k).weakGrad 2 (volume.restrict (Metric.ball b σ)) :=
    (hz k).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume hball)
  have hmono : MonotoneOn Ex (Ioc (0 : ℝ) σ) := by
    intro a ha d hd had
    exact Finset.sum_le_sum fun k _ =>
      monotoneOn_integral_norm_sub_average_sq_ball (hLp k) ha hd had
  have hEx : 0 ≤ Ex σ := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hExM : Ex σ ≤ M := by
    apply Finset.sum_le_sum
    intro k hk
    have hh := integral_norm_sub_average_sq_le_integral_norm_sub_sq (hLp k) (0 : V)
    simp only [sub_zero] at hh
    exact hh.trans (setIntegral_mono_set (hz k).weakGrad_memLp.norm.integrable_sq
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hball))
  apply hpower Ex hmono hEx hExM _ s ⟨hs, hsσ⟩
  intro a ha d hd hda
  have hh := hexcess b hb a ha.1 ha.2 d hd.le (by linarith)
  simpa only [Ex, Real.rpow_ofNat] using hh

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_chart_holder_weak_gradient_of_minimizing_sequence
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
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    : let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧
      Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        (Metric.ball x₀ (2 * σ) ⊆ Metric.ball x₀ ρ) ∧
        ∃ (G : Fin (Module.finrank ℝ E) → V → V) (C : Fin (Module.finrank ℝ E) → ℝ),
          (∀ k, 0 ≤ C k) ∧
          (∀ k, G k =ᵐ[volume.restrict (Metric.ball x₀ σ)] (hz k).weakGrad) ∧
          (∀ k, ContinuousOn (G k) (Metric.ball x₀ (σ / 2))) ∧
          ∀ k, ∀ x ∈ Metric.ball x₀ (σ / 2), ∀ y ∈ Metric.ball x₀ (σ / 2),
            ‖G k x - G k y‖ ≤ C k * ‖x - y‖ ^ ((1 : ℝ) / 8) := by
  obtain ⟨ρ, σ, K, hρ, hσ, hK, hρB, hz, hzgrad, hσρ, hpower⟩ :=
    exists_chart_gradient_excess_power_bound_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  have hball : Metric.ball x₀ σ ⊆ Metric.ball x₀ ρ :=
    (Metric.ball_subset_ball (by linarith : σ ≤ 2 * σ)).trans hσρ
  refine ⟨ρ, σ, hρ, hσ, hρB, hz, hzgrad, hσρ, ?_⟩
  apply exists_holder_representative_of_gradient_excess_bound hσ
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1) hK
    (fun k => (hz k).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume hball))
  intro b
  have hh := hpower b.center (b.subset_ball (Metric.mem_ball_self b.radius_pos))
    b.radius b.radius_pos b.radius_le
  norm_num at hh ⊢
  exact hh

end DifferentialGeometry.Geometry

end
