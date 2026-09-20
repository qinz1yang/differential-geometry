import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.HarmonicComparison
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison
import DifferentialGeometry.Analysis.Asymptotics.GeometricDecay
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

theorem exists_chart_weak_energy_decay_of_exponent_lt_two
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
    {q : ℝ} (hq2 : q < 2) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ θ : ℝ, 0 < ρ ∧ 0 < θ ∧ θ < 1 / 4 ∧
      Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        ∀ (b : V) (R : ℝ), 0 < R → ‖b‖ + R < 1 → Metric.ball b R ⊆ Metric.ball x₀ ρ →
          ∀ n : ℕ,
            (∑ k, ∫ x in Metric.ball b (θ ^ n * R), ‖(hz k).weakGrad x‖ ^ 2) ≤
              (θ ^ q) ^ n * ∑ k, ∫ x in Metric.ball b R, ‖(hz k).weakGrad x‖ ^ 2 := by
  obtain ⟨θ, hθ, hθ4, hθsmall⟩ := Real.exists_pos_lt_mul_rpow_lt_mul_rpow
    (A := (512 : ℝ)) (p := (2 : ℝ)) (q := q) hq2
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 4)
  have hθ1 : θ < 1 := by linarith
  have hθq : 0 < θ ^ q := Real.rpow_pos_of_pos hθ q
  let δ := min 1 (θ ^ q / 4)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδq : 2 * δ ≤ θ ^ q / 2 := by
    have hh := min_le_right (1 : ℝ) (θ ^ q / 4)
    dsimp only [δ]
    linarith
  have hcontract : 256 * (1 + δ) * θ ^ 2 + 2 * δ ≤ θ ^ q := by
    rw [Real.rpow_two] at hθsmall
    have hh := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg θ)
    nlinarith
  obtain ⟨ρ, hρ, hρB, hzc, hz, hzgrad, happ⟩ :=
    exists_chart_harmonic_replacement_small_gradient_error_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀ hδ
  refine ⟨ρ, θ, hρ, hθ, hθ4, hρB, hzc, hz, hzgrad, ?_⟩
  intro b R hR hbR hball n
  let En := fun s => ∑ k, ∫ x in Metric.ball b s, ‖(hz k).weakGrad x‖ ^ 2
  have hstep (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) : En (θ * s) ≤ θ ^ q * En s := by
    have hsB : Metric.ball b s ⊆ Metric.ball x₀ ρ :=
      (Metric.ball_subset_ball hsR).trans hball
    obtain ⟨h, hh, _, hEuler, herr⟩ := happ b s hs (by linarith) hsB
    let hzs (k : Fin (Module.finrank ℝ E)) :=
      DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hsB (hz k)
    have hsmall : θ * s ≤ s / 4 := by nlinarith
    have hdec := integral_weakGrad_sq_le_of_harmonic_comparison_error hs (mul_nonneg hθ.le hs.le)
      hsmall hzs hh hEuler herr
    have hrati : θ * s / s = θ := by field_simp
    rw [hrati] at hdec
    have hE : 0 ≤ En s := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    exact hdec.trans (mul_le_mul_of_nonneg_right hcontract hE)
  have hnpos (k : ℕ) : 0 < θ ^ k * R := mul_pos (pow_pos hθ k) hR
  have hnle (k : ℕ) : θ ^ k * R ≤ R := mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le hθ1.le)
  have hh := le_geom (u := fun k => En (θ ^ k * R)) hθq.le n (fun k _ => by
    have ht := hstep (θ ^ k * R) (hnpos k) (hnle k)
    have heq : θ ^ (k + 1) * R = θ * (θ ^ k * R) := by rw [pow_succ]; ring
    rwa [heq])
  simpa only [pow_zero, one_mul] using hh

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

theorem exists_chart_weak_gradient_power_bound_of_exponent_lt_two
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
    {q : ℝ} (hq : 0 < q) (hq2 : q < 2) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ η K : ℝ, 0 < ρ ∧ 0 < η ∧ η ≤ ρ / 4 ∧ 0 ≤ K ∧
      Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        ∀ b ∈ Metric.ball x₀ η, ∀ a : ℝ, 0 < a → a ≤ η →
          (∑ k, ∫ x in Metric.ball b a, ‖(hz k).weakGrad x‖ ^ 2) ≤ K * a ^ q := by
  obtain ⟨ρ, θ, hρ, hθ, hθ4, hρB, hzc, hz, hzgrad, hdec⟩ :=
    exists_chart_weak_energy_decay_of_exponent_lt_two
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀ hq2
  have hxnorm : ‖x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx₀
  let η := min (ρ / 4) ((1 - ‖x₀‖) / 4)
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  have hηρ : η ≤ ρ / 4 := min_le_left _ _
  have hηx : ‖x₀‖ + 2 * η < 1 := by
    have hh := min_le_right (ρ / 4) ((1 - ‖x₀‖) / 4)
    dsimp only [η]
    linarith
  let M := ∑ k, ∫ x in Metric.ball x₀ ρ, ‖(hz k).weakGrad x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  let K := M / (θ * η) ^ q
  have hK : 0 ≤ K := div_nonneg hM (Real.rpow_nonneg (mul_nonneg hθ.le hη.le) q)
  refine ⟨ρ, η, K, hρ, hη, hηρ, hK, hρB, hzc, hz, hzgrad, ?_⟩
  intro b hb a ha haη
  have hbd : dist b x₀ < η := Metric.mem_ball.mp hb
  have hbn : ‖b‖ + η < 1 := by
    have hn : ‖b‖ ≤ dist b x₀ + ‖x₀‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (b - x₀) x₀
    linarith
  have hball : Metric.ball b η ⊆ Metric.ball x₀ ρ := by
    intro x hx
    exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx, dist_triangle x b x₀])
  let En := fun s => ∑ k, ∫ x in Metric.ball b s, ‖(hz k).weakGrad x‖ ^ 2
  have hI (k : Fin (Module.finrank ℝ E)) :
      IntegrableOn (fun x => ‖(hz k).weakGrad x‖ ^ 2) (Metric.ball x₀ ρ) :=
    (hz k).weakGrad_memLp.norm.integrable_sq
  have hmono : MonotoneOn En (Ioc (0 : ℝ) η) := by
    intro s hs t ht hst
    apply Finset.sum_le_sum
    intro k hk
    exact setIntegral_mono_set ((hI k).mono_set ((Metric.ball_subset_ball ht.2).trans hball))
      (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall (Metric.ball_subset_ball hst))
  have hEM : En η ≤ M := Finset.sum_le_sum fun k _ =>
    setIntegral_mono_set (hI k) (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall hball)
  have hd (n : ℕ) : En (θ ^ n * η) ≤ (θ ^ q) ^ n * M :=
    (hdec b η hη hbn hball n).trans
      (mul_le_mul_of_nonneg_left hEM (pow_nonneg (Real.rpow_nonneg hθ.le q) n))
  exact radius_power_bound_of_geometric_decay hθ (by linarith) hη hq.le hM hmono hd a ⟨ha, haη⟩

end DifferentialGeometry.Geometry

end
