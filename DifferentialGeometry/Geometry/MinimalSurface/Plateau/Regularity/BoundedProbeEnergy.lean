import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ScalarProbes
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.BoundedProbes
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.IntrinsicEnergyPower

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_bounded_probe_truncated_ball_power_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (v : ℂ → M)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z))) :
    ∃ p δ A : ℝ, 0 < p ∧ p ≤ 2 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ A ∧
      ∀ (P : M → ℝ) (D : ℝ) (K : ℝ≥0), Continuous P → (∀ p, ‖P p‖ ≤ D) →
        (∀ p q, edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q) →
        ∃ hw : DeGiorgi.MemW1pWitness 2
          (fun x => P (v (Complex.orthonormalBasisOneI.repr.symm x))) (ball 0 1),
          ∀ c ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
            (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ ball c s,
              ‖hw.weakGrad x‖ ^ 2) ≤ 2 * (K : ℝ) ^ 2 * (A * s ^ p) := by
  obtain ⟨p, δ, A, hp, hp2, hδ, hδ8, hA, hdec⟩ :=
    exists_uniform_intrinsic_truncated_ball_power_bound g hregular γ hγ u hu hmin
      ψ hψ htrace hthird htwothird
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have henergy (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (mem_range_self n)
  refine ⟨p, δ, A, hp, hp2, hδ, hδ8, hA, ?_⟩
  intro P D K hP hD hPLip
  obtain ⟨hw, _, _, _⟩ := exists_memW1pWitness_bounded_intrinsic_probe_of_ae_tendsto
    g hP hD K hPLip u v (fun n => (hu n).2) hae henergy
  refine ⟨hw, ?_⟩
  intro c hc s hs hsδ
  let e := Complex.orthonormalBasisOneI.repr.symm
  let S := ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ ball c s
  let T := ball (0 : ℂ) 1 ∩ closedBall (e c) s
  have hc' : e c ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, e.norm_map] using hc
  have hsub : e '' S ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    constructor
    · simpa only [mem_ball, dist_zero_right, e.norm_map] using hx.1
    · simpa only [mem_closedBall, e.isometry.dist_eq] using (mem_ball.mp hx.2).le
  have hTsub : T ⊆ closedBall (0 : ℂ) 1 := inter_subset_left.trans ball_subset_closedBall
  have hnonneg (n : ℕ) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension (u n)) z := by
    unfold diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  let a (n : ℕ) := ∫ z in e '' S, diskMapEnergyDensity g (diskExtension (u n)) z
  let b (n : ℕ) := ∫ z in T, diskMapEnergyDensity g (diskExtension (u n)) z
  have hab (n : ℕ) : a n ≤ b n := by
    obtain ⟨L, hL⟩ := (hu n).2
    exact setIntegral_mono_set ((integrable_diskMapEnergyDensity g hL).mono_set hTsub)
      (Eventually.of_forall (hnonneg n)) (Eventually.of_forall hsub)
  have ha0 : ∀ᶠ n in atTop, 0 ≤ a n := Eventually.of_forall fun n => integral_nonneg (hnonneg n)
  have hbB (n : ℕ) : b n ≤ B := by
    obtain ⟨L, hL⟩ := (hu n).2
    exact (setIntegral_mono_set (integrable_diskMapEnergyDensity g hL)
      (Eventually.of_forall (hnonneg n)) (Eventually.of_forall hTsub)).trans (henergy n)
  have hablim : limsup a atTop ≤ limsup b atTop :=
    limsup_le_limsup (Eventually.of_forall hab)
      (isBoundedUnder_of_eventually_ge ha0).isCoboundedUnder_le
      (isBoundedUnder_of_eventually_le (Eventually.of_forall hbB))
  have hbdec : limsup b atTop ≤ A * s ^ p := hdec (e c) hc' s hs hsδ
  have hlocal := integral_weakGrad_probe_sq_le_limsup_energy_on_subset g hP hD hPLip u v
    (fun n => (hu n).2) hae henergy hw (isOpen_ball.inter isOpen_ball) (show S ⊆ ball 0 1 from
      inter_subset_left)
  exact hlocal.trans (mul_le_mul_of_nonneg_left (hablim.trans hbdec) (by positivity))

end DifferentialGeometry.Geometry

end

end
