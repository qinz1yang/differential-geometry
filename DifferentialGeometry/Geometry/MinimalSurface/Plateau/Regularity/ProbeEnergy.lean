import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ProbeLowerSemicontinuity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ScalarProbes
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.IntrinsicEnergyDecay
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.BoundedProbes

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_weakGrad_comp_sq_le_of_local_energy_upper_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {P : M → ℝ}
    (hP : Continuous P) {D : ℝ} (hD : ∀ p, ‖P p‖ ≤ D) {K : ℝ≥0}
    (hPLip : ∀ p q, edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q)
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {B : ℝ}
    (hLip : ∀ n, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (L : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, riemannianDiskEnergy g (u n) ≤ B)
    (hw : DeGiorgi.MemW1pWitness 2
      (fun x => P (v (Complex.orthonormalBasisOneI.repr.symm x))) (ball 0 1))
    (b : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hball : ball b R ⊆ ball 0 1)
    {upper : ℕ → ℝ} {a : ℝ} (hlim : Tendsto upper atTop (𝓝 a))
    (hupper : ∀ᶠ n in atTop,
      (∫ z in ball (Complex.orthonormalBasisOneI.repr.symm b) R,
        diskMapEnergyDensity g (diskExtension (u n)) z) ≤ upper n) :
    (∫ x in ball b R, ‖hw.weakGrad x‖ ^ 2) ≤ 2 * (K : ℝ) ^ 2 * a := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ := fun n x => P (diskExtension (u n) (e x))
  let q : ℕ → ℝ := fun n => ∫ x in ball b R, ‖fderiv ℝ (f n) x‖ ^ 2
  have hLipe (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (f n) := by
    obtain ⟨L, hL⟩ := hLip n
    refine ⟨K * L, ?_⟩
    intro x y
    exact (hPLip _ _).trans ((mul_le_mul_right
      (diskExtension_riemannian_lipschitz g hL (e x) (e y)) (K : ℝ≥0∞)).trans_eq (by
        rw [e.isometry.edist_eq, ENNReal.coe_mul, mul_assoc]))
  have hpre : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
  have he := e.measurePreserving.restrict_preimage (s := ball (0 : ℂ) 1) measurableSet_ball
  rw [hpre] at he
  have haee := ae_restrict_of_ae_restrict_of_subset hball (he.quasiMeasurePreserving.ae hae)
  have hsource : ball (e b) R ⊆ closedBall (0 : ℂ) 1 := by
    intro z hz
    have hx : e.symm z ∈ ball b R := by
      rw [mem_ball, ← e.isometry.dist_eq]
      simpa only [e.apply_symm_apply, mem_ball] using hz
    have hu := hball hx
    rw [mem_ball_zero_iff, e.symm.norm_map] at hu
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using hu.le)
  have hlocal (n : ℕ) : q n ≤ 2 * (K : ℝ) ^ 2 *
      ∫ z in ball (e b) R, diskMapEnergyDensity g (diskExtension (u n)) z := by
    obtain ⟨L, hL⟩ := hLip n
    exact integral_norm_fderiv_sq_comp_plane_le_mul_disk_energy_on_ball g (u n) hL hPLip b R
  have hqB (n : ℕ) : q n ≤ 2 * (K : ℝ) ^ 2 * B := by
    obtain ⟨L, hL⟩ := hLip n
    have hmono := setIntegral_mono_set (integrable_diskMapEnergyDensity g hL)
      (Eventually.of_forall fun z => div_nonneg
        (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
          (by norm_num)) (Eventually.of_forall hsource)
    exact (hlocal n).trans (mul_le_mul_of_nonneg_left (hmono.trans (henergy n)) (by positivity))
  let : IsFiniteMeasure (volume.restrict (ball b R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hls := Analysis.Sobolev.Euclidean.integral_weakGrad_sq_le_liminf_comp_fderiv_on_subset
    isOpen_ball hball hP hD (fun n x => diskExtension (u n) (e x)) (fun x => v (e x))
    hLipe haee hqB hw
  have hq0 (n : ℕ) : 0 ≤ q n := integral_nonneg fun x => sq_nonneg _
  have hqlo : IsBoundedUnder (· ≥ ·) atTop q := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q n
    exact Eventually.of_forall hq0
  have hqhi : IsBoundedUnder (· ≤ ·) atTop q := by
    refine ⟨2 * (K : ℝ) ^ 2 * B, ?_⟩
    change ∀ᶠ n in atTop, q n ≤ 2 * (K : ℝ) ^ 2 * B
    exact Eventually.of_forall hqB
  have hup : Tendsto (fun n => 2 * (K : ℝ) ^ 2 * upper n) atTop
      (𝓝 (2 * (K : ℝ) ^ 2 * a)) := hlim.const_mul _
  have hle : q ≤ᶠ[atTop] (fun n => 2 * (K : ℝ) ^ 2 * upper n) := by
    filter_upwards [hupper] with n hn
    exact (hlocal n).trans (mul_le_mul_of_nonneg_left hn (by positivity))
  exact hls.trans ((liminf_le_limsup hqhi hqlo).trans
    ((limsup_le_limsup hle hqlo.isCoboundedUnder_le hup.isBoundedUnder_le).trans_eq hup.limsup_eq))

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_bounded_probe_dyadic_energy_bound_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M)) (v : ℂ → M)
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z))) :
    ∃ (N : ℕ) (B θ : ℝ), 0 < N ∧ 0 < B ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (P : M → ℝ) (D : ℝ) (K : ℝ≥0), Continuous P → (∀ p, ‖P p‖ ≤ D) →
        (∀ p q, edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q) →
          ∀ hw : DeGiorgi.MemW1pWitness 2
            (fun x => P (v (Complex.orthonormalBasisOneI.repr.symm x))) (ball 0 1),
            ∀ (b : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
              (∫ x in ball b (R / 2 ^ (N + k)), ‖hw.weakGrad x‖ ^ 2) ≤
                2 * (K : ℝ) ^ 2 * (θ ^ k * B) := by
  obtain ⟨N, B, θ, hN, hB, hθ, hθ1, hevent⟩ :=
    exists_eventually_dyadic_energy_bound_of_minimizing_sequence g hregular γ u hu hmin
  obtain ⟨B₀, hB₀⟩ := hmin.isBoundedUnder_le.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B₀ := hB₀ (mem_range_self n)
  refine ⟨N, B, θ, hN, hB, hθ, hθ1, ?_⟩
  intro P D K hP hD hPLip hw b R hR hbr k
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let r : ℝ := R / 2 ^ (N + k)
  have hr : 0 < r := div_pos hR (by positivity)
  have hrR : r ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hball : ball b r ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x hx
    have hn : ‖x‖ ≤ dist x b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - b) b
    have hd := mem_ball.mp hx
    exact mem_ball.mpr (by rw [dist_zero_right]; linarith)
  let infimum := sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
    weaklyMonotoneDiskCompetitors g γ)
  let upper : ℕ → ℝ := fun n => θ ^ k * B + (1 - θ ^ k) *
    (riemannianDiskEnergy g (u n) - infimum)
  have hδ : Tendsto (fun n => riemannianDiskEnergy g (u n) - infimum) atTop (𝓝 0) := by
    simpa only [infimum, sub_self] using hmin.sub_const infimum
  have hupp : Tendsto upper atTop (𝓝 (θ ^ k * B)) := by
    simpa only [upper, mul_zero, add_zero] using
      (hδ.const_mul (1 - θ ^ k)).const_add (θ ^ k * B)
  have hupper : ∀ᶠ n in atTop,
      (∫ z in ball (e b) r, diskMapEnergyDensity g (diskExtension (u n)) z) ≤ upper n := by
    filter_upwards [hevent] with n hn
    have h := hn (e b) R hR (by simpa only [e.norm_map] using hbr) k
    obtain ⟨L, hL⟩ := (hu n).2
    let : IsFiniteMeasure (volume.restrict (closedBall (e b) r)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (e b) r).measure_lt_top.ne
    have hi := integrableOn_diskMapEnergyDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g hL) (closedBall (e b) r) (μ := volume)
    have hmono := setIntegral_mono_set hi (Eventually.of_forall fun z => div_nonneg
      (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
        (by norm_num)) (Eventually.of_forall (ball_subset_closedBall :
          ball (e b) r ⊆ closedBall (e b) r))
    exact hmono.trans h
  exact integral_weakGrad_comp_sq_le_of_local_energy_upper_tendsto g hP hD hPLip
    u v (fun n => (hu n).2) hae htotal hw b hball hupp hupper

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_memW1pWitness_bounded_probe_dyadic_energy_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M)) (v : ℂ → M)
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z))) :
    ∃ (N : ℕ) (B θ : ℝ), 0 < N ∧ 0 < B ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (P : M → ℝ) (D : ℝ) (K : ℝ≥0), Continuous P → (∀ p, ‖P p‖ ≤ D) →
        (∀ p q, edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q) →
          ∃ hw : DeGiorgi.MemW1pWitness 2
            (fun x => P (v (Complex.orthonormalBasisOneI.repr.symm x))) (ball 0 1),
            ∀ (b : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
              (∫ x in ball b (R / 2 ^ (N + k)), ‖hw.weakGrad x‖ ^ 2) ≤
                2 * (K : ℝ) ^ 2 * (θ ^ k * B) := by
  obtain ⟨N, B, θ, hN, hB, hθ, hθ1, hbound⟩ :=
    exists_bounded_probe_dyadic_energy_bound_of_minimizing_sequence g hregular γ u v hu hmin hae
  obtain ⟨A, hA⟩ := hmin.isBoundedUnder_le.bddAbove_range
  refine ⟨N, B, θ, hN, hB, hθ, hθ1, ?_⟩
  intro P D K hP hD hPLip
  obtain ⟨hw, _, _, _⟩ := exists_memW1pWitness_bounded_intrinsic_probe_of_ae_tendsto
    g hP hD K hPLip u v (fun n => (hu n).2) hae (fun n => hA (mem_range_self n))
  exact ⟨hw, hbound P D K hP hD hPLip hw⟩

end DifferentialGeometry.Geometry

end

end
