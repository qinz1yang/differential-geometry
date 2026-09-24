import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.FirstVariation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.CoordinateVariation
import DifferentialGeometry.Geometry.Metric.Pullback.Chart
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.WeakReplacement
import DifferentialGeometry.Geometry.HarmonicMap.WeakEquation

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_weak_chart_variational_equation_of_disk_energy_minimizing_sequence
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
    (hgrad : ∀ i, (hv i).weakGrad = (hw i).weakGrad)
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let Ψ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
    let z : V → H := χ ∘ v
    let B := pullbackMetricCoefficients g Ψ
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      MapsTo z (Metric.closedBall x₀ ρ) (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      (∀ x ∈ Metric.closedBall x₀ ρ, Ψ (z x) = r (v x)) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          DeGiorgi.weakGradientColumn hz x j =
            fderiv ℝ χ (v x) (DeGiorgi.weakGradientColumn hv x j)) ∧
        ∀ φ : V → H, ContDiff ℝ ∞ φ → tsupport φ ⊆ Metric.ball x₀ ρ →
          (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
            ((fderiv ℝ B (z x) (φ x)) (DeGiorgi.weakGradientColumn hz x j)
                (DeGiorgi.weakGradientColumn hz x j) +
              2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
                (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
  classical
  obtain ⟨r₀, hr₀, hball₀, hrmap, hzmap, hzc, hzback, hz₀, hzgrad⟩ :=
    exists_weak_chart_coordinates_of_continuousOn Metric.isOpen_ball hvc hv hU hr
      (fun x hx => hΦU (hvK hx)) hx₀
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let Ψ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
  let z : V → H := χ ∘ v
  let Uc := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  let β : H → F := Φ ∘ Ψ
  let A := pullbackMetricCoefficients g r
  let B := pullbackMetricCoefficients g Ψ
  have hUc : IsOpen Uc := chartTargetEuclid_isOpen p
  have hΨ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ Uc := contMDiffOn_chart_symm p
  have hβ : ContDiffOn ℝ ∞ β Uc := (hΦ.comp_contMDiffOn hΨ).contDiffOn
  have hB : ContDiffOn ℝ 1 B Uc :=
    (contDiffOn_pullback_metric_coefficients g hUc hΨ).of_le (by simp)
  have hxnorm : ‖x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx₀
  let R : ℝ := min (r₀ / 2) ((1 - ‖x₀‖) / 2)
  have hR : 0 < R := lt_min (half_pos hr₀) (by linarith)
  have hRr : R < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hRn : ‖x₀‖ + R < 1 := by
    have h := min_le_right (r₀ / 2) ((1 - ‖x₀‖) / 2)
    dsimp only [R]
    linarith
  have hRball : Metric.closedBall x₀ R ⊆ Metric.ball (0 : V) 1 :=
    (Metric.closedBall_subset_closedBall hRr.le).trans hball₀
  have hRrball : Metric.ball x₀ R ⊆ Metric.ball x₀ r₀ := Metric.ball_subset_ball hRr.le
  let hzR (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hRrball (hz₀ k)
  let hvR (i : Fin n) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hRball) (hv i)
  let K : Set H := z '' Metric.closedBall x₀ R
  have hK : IsCompact K := (isCompact_closedBall x₀ R).image_of_continuousOn
    (hzc.mono (Metric.closedBall_subset_closedBall hRr.le))
  have hKUc : K ⊆ Uc := by
    rintro y ⟨x, hx, rfl⟩
    exact hzmap (Metric.closedBall_subset_closedBall hRr.le hx)
  have hzK : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ R), z x ∈ K := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact mem_image_of_mem z (Metric.ball_subset_closedBall hx)
  let ρ := R / 4
  let c := R / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρc : ρ < c := by dsimp only [ρ, c]; linarith
  have hcR : c < R := half_lt_self hR
  have hρR : ρ < R := hρc.trans hcR
  have hsource : Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 :=
    (Metric.closedBall_subset_closedBall hρR.le).trans hRball
  let hzρ (k : Fin (Module.finrank ℝ E)) := DeGiorgi.MemW1pWitness.restrict
    Metric.isOpen_ball (Metric.ball_subset_ball hρR.le) (hzR k)
  refine ⟨ρ, hρ, hsource, ?_, ?_, ?_, hzρ, ?_, ?_⟩
  · exact hzmap.mono_left (Metric.closedBall_subset_closedBall (hρR.le.trans hRr.le))
  · exact hzc.mono (Metric.closedBall_subset_closedBall (hρR.le.trans hRr.le))
  · intro x hx
    exact hzback x (Metric.closedBall_subset_closedBall (hρR.le.trans hRr.le) hx)
  · intro x hx j
    exact hzgrad x (Metric.ball_subset_ball (hρR.le.trans hRr.le) hx) j
  · intro φ hφ hφρ
    have hβz : (fun x => β (z x)) =ᵐ[volume.restrict (Metric.ball x₀ R)] v := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      change Φ (Ψ (z x)) = v x
      have hzx : Ψ (z x) = r (v x) :=
        hzback x (Metric.closedBall_subset_closedBall hRr.le (Metric.ball_subset_closedBall hx))
      rw [hzx]
      obtain ⟨m, hm⟩ := hvK (hRball (Metric.ball_subset_closedBall hx))
      rw [← hm, hleft]
    have hmetric (y : H) (hy : y ∈ Uc) (u₁ u₂ : H) :
        A (β y) (fderiv ℝ β y u₁) (fderiv ℝ β y u₂) = B y u₁ u₂ :=
      pullbackMetricCoefficients_inverse_chart_of_leftInverse g p hΦ hU hr hΦU hleft
        (toEuclidean_symm_mem_target hy) u₁ u₂
    have hbase : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ R), ∀ j : Fin 2,
        A (v x) (DeGiorgi.weakGradientColumn hvR x j) (DeGiorgi.weakGradientColumn hvR x j) =
          B (z x) (DeGiorgi.weakGradientColumn hzR x j) (DeGiorgi.weakGradientColumn hzR x j) := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      intro j
      have hx₀ := hRball (Metric.ball_subset_closedBall hx)
      change A (v x) (DeGiorgi.weakGradientColumn hv x j) (DeGiorgi.weakGradientColumn hv x j) =
        B (z x) (WithLp.toLp 2 (fun k => (hz₀ k).weakGrad x j))
          (WithLp.toLp 2 (fun k => (hz₀ k).weakGrad x j))
      rw [hzgrad x (hRrball hx) j]
      exact (pullbackMetricCoefficients_chart_fderiv g p hU hr
        ⟨hΦU (hvK hx₀), hrmap (Metric.closedBall_subset_closedBall hRr.le
          (Metric.ball_subset_closedBall hx))⟩ _ _).symm
    apply integral_metric_energy_variation_eq_zero_of_coordinate_replacement
      Metric.isOpen_ball hρc (Metric.closedBall_subset_ball hcR) hzR hK hUc hKUc hzK β hβ hvR
      hβz A B hB (fun y _ u₁ u₂ => g.symm (Ψ y) _ _)
      (fun y _ => mem_range_self (Ψ y)) hmetric hbase
      (φ := φ) (hφ := hφ) (hφa := hφρ)
    intro qt hqt hqtK hqv
    have hcb : ‖x₀‖ + c < 1 := by dsimp only [c]; linarith
    have hsub : Metric.ball x₀ c \ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 :=
      sdiff_subset.trans ((Metric.ball_subset_ball hcR.le).trans
        (Metric.ball_subset_closedBall.trans hRball))
    have hqw := hqv.trans (ae_mono (Measure.restrict_mono_set volume hsub) hvw)
    have hm := weak_replacement_energy_le_on_interior_ball_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak hρ hρc hcb qt hqt hqtK hqw
    have heq (j : Fin 2) : (∫ x in Metric.closedBall x₀ ρ,
        A (v x) (DeGiorgi.weakGradientColumn hvR x j) (DeGiorgi.weakGradientColumn hvR x j)) =
        ∫ x in Metric.closedBall x₀ ρ,
          A (w x) (DeGiorgi.weakGradientColumn hw x j) (DeGiorgi.weakGradientColumn hw x j) := by
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono_set volume hsource) hvw] with x hx
      change A (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)) = _
      simp only [hx, hgrad, DeGiorgi.weakGradientColumn]
    simp_rw [heq]
    exact hm

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_weak_chart_harmonic_map_equation_of_disk_energy_minimizing_sequence
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
    (hgrad : ∀ i, (hv i).weakGrad = (hw i).weakGrad)
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1) :
    let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let Ψ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
    let z : V → H := χ ∘ v
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      MapsTo z (Metric.closedBall x₀ ρ) (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ∧
      ContinuousOn z (Metric.closedBall x₀ ρ) ∧
      (∀ x ∈ Metric.closedBall x₀ ρ, Ψ (z x) = r (v x)) ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          DeGiorgi.weakGradientColumn hz x j =
            fderiv ℝ χ (v x) (DeGiorgi.weakGradientColumn hv x j)) ∧
        (∀ k, IntegrableOn (fun x => ∑ j : Fin 2, ∑ a, ∑ b,
          chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
            (DeGiorgi.weakGradientColumn hz x j) a *
            (DeGiorgi.weakGradientColumn hz x j) b) (Metric.ball x₀ ρ)) ∧
        ∀ k (ζ : V → ℝ), ContDiff ℝ ∞ ζ → tsupport ζ ⊆ Metric.ball x₀ ρ →
          (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
            (DeGiorgi.weakGradientColumn hz x j) k *
              fderiv ℝ ζ x (EuclideanSpace.single j 1)) =
            ∫ x in Metric.ball x₀ ρ, ζ x * (∑ j : Fin 2, ∑ a, ∑ b,
              chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
                (DeGiorgi.weakGradientColumn hz x j) a *
                (DeGiorgi.weakGradientColumn hz x j) b) := by
  obtain ⟨ρ, hρ, hball, hzmap, hzc, hback, hz, hgradz, hEL⟩ :=
    exists_weak_chart_variational_equation_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hgrad hx₀
  refine ⟨ρ, hρ, hball, hzmap, hzc, hback, hz, hgradz, ?_, ?_⟩
  · exact fun k => integrable_christoffel_weakGradientColumn_sum g (r (v x₀)) hzc hzmap hz k
  · intro k ζ hζ hζsupp
    exact integral_weak_chart_gradient_test_eq_integral_christoffel
      g (r (v x₀)) hzc hzmap hz hEL k hζ hζsupp

theorem exists_continuous_weak_chart_harmonic_map_of_disk_energy_minimizing_sequence
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
    : ∃ (v : V → F)
      (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1)),
      ContinuousOn v (Metric.ball (0 : V) 1) ∧
      (v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w) ∧
      MapsTo v (Metric.ball (0 : V) 1) (range Φ) ∧
      (∀ i, (hv i).weakGrad = (hw i).weakGrad) ∧
      ∀ x₀ ∈ Metric.ball (0 : V) 1,
        let p := r (v x₀)
        let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
        let Ψ : H → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
        let z : V → H := χ ∘ v
        ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
          MapsTo z (Metric.closedBall x₀ ρ) (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ∧
          ContinuousOn z (Metric.closedBall x₀ ρ) ∧
          (∀ x ∈ Metric.closedBall x₀ ρ, Ψ (z x) = r (v x)) ∧
          ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
            (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
              DeGiorgi.weakGradientColumn hz x j =
                fderiv ℝ χ (v x) (DeGiorgi.weakGradientColumn hv x j)) ∧
            (∀ k, IntegrableOn (fun x => ∑ j : Fin 2, ∑ a, ∑ b,
              chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
                (DeGiorgi.weakGradientColumn hz x j) a *
                (DeGiorgi.weakGradientColumn hz x j) b) (Metric.ball x₀ ρ)) ∧
            ∀ k (ζ : V → ℝ), ContDiff ℝ ∞ ζ → tsupport ζ ⊆ Metric.ball x₀ ρ →
              (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
                (DeGiorgi.weakGradientColumn hz x j) k *
                  fderiv ℝ ζ x (EuclideanSpace.single j 1)) =
                ∫ x in Metric.ball x₀ ρ, ζ x * (∑ j : Fin 2, ∑ a, ∑ b,
                  chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
                    (DeGiorgi.weakGradientColumn hz x j) a *
                    (DeGiorgi.weakGradientColumn hz x j) b) := by
  obtain ⟨v, hv, hvc, hvw, hvK, hgrad, _⟩ :=
    exists_continuous_weak_representative_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  refine ⟨v, hv, hvc, hvw, hvK, hgrad, ?_⟩
  intro x₀ hx₀
  exact exists_weak_chart_harmonic_map_equation_of_disk_energy_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hgrad hx₀

end DifferentialGeometry.Geometry

end
