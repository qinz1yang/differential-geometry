import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Scaling
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakReplacement
import DifferentialGeometry.Geometry.HarmonicMap.HoleFilling
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Integrability
import DifferentialGeometry.Analysis.Integration.Integral.SmallBalls
import DifferentialGeometry.Analysis.Asymptotics.GeometricDecay
import DifferentialGeometry.Geometry.HarmonicMap.WeakGradientBound

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weak_energy_hole_filling_factor_on_interior_balls_of_minimizing_sequence
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
    : ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 ≤ C / (1 + C) ∧ C / (1 + C) < 1 ∧
      ∀ (b : V) (R : ℝ), 0 < R → ‖b‖ + R < 1 →
      (∫ x in Metric.ball b R,
        ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) < ε →
      (∫ x in Metric.ball b (R / 2),
        ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
        C / (1 + C) * ∫ x in Metric.ball b R,
          ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
  obtain ⟨ε, C, hε, hC, hC0, hC1, hdecay⟩ :=
    exists_weak_energy_hole_filling_factor g hΦ hU hr hΦU hleft
  refine ⟨ε, C, hε, hC, hC0, hC1, ?_⟩
  intro b R hR hRb hsmall
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ range Φ :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  let c := (1 - ‖b‖ + R) / 2
  have hRc : R < c := by dsimp only [c]; linarith
  have hbc : ‖b‖ + c < 1 := by dsimp only [c]; linarith
  have hc : 0 < c := hR.trans hRc
  have hcne : c ≠ 0 := hc.ne'
  let S : V → V := fun x => b + c • x
  let Ω := S ⁻¹' Metric.ball (0 : V) 1
  let w' : V → F := fun x => w (S x)
  let hw' (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => w' x i) Ω :=
    (hw i).compAddSmul b hcne
  have hS : Continuous S := (continuous_const (y := b)).add (continuous_id.const_smul c)
  have hΩ : IsOpen Ω := Metric.isOpen_ball.preimage hS
  have hball : Metric.closedBall (0 : V) 1 ⊆ Ω := by
    intro x hx
    change b + c • x ∈ Metric.ball (0 : V) 1
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hn : ‖c • x‖ ≤ c := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_of_le_one_right hc.le hx'
    exact (norm_add_le b (c • x)).trans_lt (by linarith)
  have hw'K : ∀ᵐ x ∂volume.restrict Ω, w' x ∈ range Φ :=
    (quasiMeasurePreserving_add_smul_restrict volume b hcne _).ae hwK
  let A := pullbackMetricCoefficients g r
  have henergy (t : ℝ) :
      (∫ x in Metric.ball (0 : V) (t / c), ∑ j : Fin 2, A (w' x)
        (WithLp.toLp 2 (fun i => (hw' i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw' i).weakGrad x j))) =
      ∫ x in Metric.ball b t, ∑ j : Fin 2, A (w x)
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
    have hh := integral_sum_weak_metric_compAddSmul hw A b hcne (Metric.ball b t)
    have hpre : (fun x : V => b + c • x) ⁻¹' Metric.ball b t =
        Metric.ball (0 : V) (t / c) := by
      simpa only [smul_zero, add_zero] using preimage_add_smul_ball_plane b 0 hc t
    rw [hpre] at hh
    exact hh
  have hRscaled : 0 < R / c := div_pos hR hc
  have hRscaled1 : R / c < 1 := (div_lt_one hc).mpr hRc
  have hsmall' : (∫ x in Metric.ball (0 : V) (R / c), ∑ j : Fin 2, A (w' x)
      (WithLp.toLp 2 (fun i => (hw' i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hw' i).weakGrad x j))) < ε := by
    rw [henergy]
    exact hsmall
  have hmin' := weak_replacement_minimality_comp_add_smul_center hw A b hc
    (fun q hq hqK hqw =>
      weak_replacement_energy_le_on_interior_ball_of_disk_energy_minimizing_sequence
        g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak hR hRc hbc q hq hqK hqw)
  have hfinal := hdecay Ω hΩ w' hw' hw'K hball (R / c) hRscaled hRscaled1 hsmall' hmin'
  have hhalf : R / c / 2 = (R / 2) / c := by ring
  rw [hhalf, henergy, henergy] at hfinal
  exact hfinal

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_dyadic_weak_energy_decay_on_interior_balls_of_minimizing_sequence
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
    : ∃ δ θ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ θ ∧ θ < 1 ∧
      (∀ (b : V) (R : ℝ), 0 < R → R ≤ δ → ‖b‖ + R < 1 →
        (∫ x in Metric.ball b (R / 2),
          ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
          θ * ∫ x in Metric.ball b R,
            ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ∧
      ∀ b : V, ‖b‖ + δ < 1 → ∀ k : ℕ,
        (∫ x in Metric.ball b (δ / 2 ^ k),
          ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
          θ ^ k * ∫ x in Metric.ball b δ,
            ∑ j : Fin 2, pullbackMetricCoefficients g r (w x)
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
  obtain ⟨ε, C, hε, _, hθ0, hθ1, hdecay⟩ :=
    exists_weak_energy_hole_filling_factor_on_interior_balls_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  let A := pullbackMetricCoefficients g r
  let e := fun x => ∑ j : Fin 2, A (w x)
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ range Φ :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  have hA : ContinuousOn A (range Φ) :=
    (contDiffOn_pullback_metric_coefficients g hU hr).continuousOn.mono hΦU
  have hei : IntegrableOn e (Metric.ball (0 : V) 1) :=
    integrable_sum_quadratic_weakGrad hw hK A hA hwK
  obtain ⟨δ, hδ, hδ1, hδsmall⟩ := exists_pos_uniform_abs_integral_ball_lt hei hε
  have hstep (b : V) (R : ℝ) (hR : 0 < R) (hRδ : R ≤ δ) (hbR : ‖b‖ + R < 1) :
      (∫ x in Metric.ball b (R / 2), e x) ≤
        C / (1 + C) * ∫ x in Metric.ball b R, e x := by
    have hball : Metric.ball b R ⊆ Metric.ball (0 : V) 1 := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      have hx' : ‖x - b‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hn : ‖x‖ ≤ ‖x - b‖ + ‖b‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x - b) b
      linarith
    exact hdecay b R hR hbR
      ((le_abs_self _).trans_lt (hδsmall b R hR hRδ hball))
  refine ⟨δ, C / (1 + C), hδ, hδ1, hθ0, hθ1, hstep, ?_⟩
  intro b hb
  exact le_pow_mul_of_half_le (E := fun R => ∫ x in Metric.ball b R, e x)
    hδ hθ0 (fun R hR => hstep b R hR.1 hR.2 (by linarith [hR.2]))

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weak_gradient_power_bound_on_interior_balls_of_minimizing_sequence
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
    : ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < 1 →
      ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ K ∧
        ∀ b : V, ‖b‖ ≤ t → ∀ R : ℝ, 0 < R → R ≤ δ → ∀ i : ι,
          (∫ x in Metric.ball b R, ‖(hw i).weakGrad x‖ ^ 2) ≤ K * R ^ (2 * α) := by
  obtain ⟨δ₀, θ, hδ₀, hδ₀1, hθ, hθ1, hstep, _⟩ :=
    exists_dyadic_weak_energy_decay_on_interior_balls_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  obtain ⟨α, hα, hα1, hpower⟩ := exists_power_bound_of_half_contraction hθ hθ1
  obtain ⟨C, _, hcoercive⟩ :=
    exists_weak_gradient_norm_sq_le_pullback_metric_on_ball g hΦ hU hr hΦU hleft
  let A := pullbackMetricCoefficients g r
  let e := fun x => ∑ j : Fin 2, A (w x)
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), w x ∈ range Φ :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => mem_range_self _)
  have hA : ContinuousOn A (range Φ) :=
    (contDiffOn_pullback_metric_coefficients g hU hr).continuousOn.mono hΦU
  have hei : IntegrableOn e (Metric.ball (0 : V) 1) :=
    integrable_sum_quadratic_weakGrad hw hK A hA hwK
  have hepos (x : V) : 0 ≤ e x := Finset.sum_nonneg fun j _ =>
    metric_inner_self_nonneg g (r (w x)) _
  let M := ∫ x in Metric.ball (0 : V) 1, e x
  have hM : 0 ≤ M := integral_nonneg hepos
  refine ⟨α, hα, hα1, ?_⟩
  intro t ht ht1
  let δ := min δ₀ ((1 - t) / 2)
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt hδ₀1
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have htδ : t + δ < 1 := by
    have hm := min_le_right δ₀ ((1 - t) / 2)
    dsimp only [δ]
    linarith
  let B := (2 : ℝ) ^ (2 * α) * M / δ ^ (2 * α)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨δ, (C : ℝ) ^ 2 * B, hδ, hδ1, mul_nonneg (sq_nonneg _) hB, ?_⟩
  intro b hb R hR hRδ i
  have hball (s : ℝ) (hs : s ≤ δ) : Metric.closedBall b s ⊆ Metric.ball (0 : V) 1 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x - b‖ ≤ s := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hn : ‖x‖ ≤ ‖x - b‖ + ‖b‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - b) b
    linarith
  let E := fun s => ∫ x in Metric.ball b s, e x
  have hmono : MonotoneOn E (Ioc (0 : ℝ) δ) := by
    intro s hs t ht hst
    exact setIntegral_mono_set
      (hei.mono_set (Metric.ball_subset_closedBall.trans (hball t ht.2)))
      (Eventually.of_forall hepos) (Eventually.of_forall (Metric.ball_subset_ball hst))
  have hEM : E δ ≤ M := setIntegral_mono_set hei (Eventually.of_forall hepos)
    (Eventually.of_forall (Metric.ball_subset_closedBall.trans (hball δ le_rfl)))
  have hrec (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) δ) : E (s / 2) ≤ θ * E s :=
    hstep b s hs.1 (hs.2.trans hδδ₀) (by linarith [hs.2])
  have hEp : E R ≤ B * R ^ (2 * α) := hpower E δ M hδ hM hEM hmono hrec R ⟨hR, hRδ⟩
  have hcoer : ∀ᵐ x ∂volume.restrict (Metric.ball b R),
      ‖(hw i).weakGrad x‖ ^ 2 ≤ (C : ℝ) ^ 2 * e x := by
    have hall := ae_all_iff.mpr (fun j : Fin 2 =>
      hcoercive 2 (Metric.ball (0 : V) 1) Metric.isOpen_ball w hw hwK b R (hball R hRδ) j)
    filter_upwards [hall] with x hx
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ j : Fin 2, ‖(hw i).weakGrad x j‖ ^ 2) ≤
      (C : ℝ) ^ 2 * ∑ j : Fin 2, A (w x)
        (WithLp.toLp 2 (fun k => (hw k).weakGrad x j))
        (WithLp.toLp 2 (fun k => (hw k).weakGrad x j))
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcol : ‖(hw i).weakGrad x j‖ ≤
        ‖(WithLp.toLp 2 (fun k => (hw k).weakGrad x j) : F)‖ :=
      PiLp.norm_apply_le (WithLp.toLp 2 (fun k => (hw k).weakGrad x j) : F) i
    exact (pow_le_pow_left₀ (norm_nonneg _) hcol 2).trans (hx j)
  have hGi : IntegrableOn (fun x => ‖(hw i).weakGrad x‖ ^ 2) (Metric.ball b R) :=
    (show IntegrableOn (fun x => ‖(hw i).weakGrad x‖ ^ 2) (Metric.ball (0 : V) 1) volume from
      (hw i).weakGrad_memLp.norm.integrable_sq).mono_set
      (Metric.ball_subset_closedBall.trans (hball R hRδ))
  have hcompare : (∫ x in Metric.ball b R, ‖(hw i).weakGrad x‖ ^ 2) ≤ (C : ℝ) ^ 2 * E R := by
    rw [← integral_const_mul]
    exact integral_mono_ae hGi
      ((hei.mono_set (Metric.ball_subset_closedBall.trans (hball R hRδ))).const_mul _) hcoer
  have hfin := hcompare.trans (mul_le_mul_of_nonneg_left hEp (sq_nonneg (C : ℝ)))
  simpa only [mul_assoc] using hfin

end DifferentialGeometry.Geometry

end
