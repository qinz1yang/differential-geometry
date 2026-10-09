import DifferentialGeometry.Topology.LoopSpace.DiskAutomorphism
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ConformalReparametrization
import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Basic
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.Composition
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Boundary.Orientation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

noncomputable section

open Manifold MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

theorem differentiableAt_diskExtension_diskAutomorphism
    {a η z : ℂ} (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    DifferentiableAt ℂ
      (diskExtension (fun w => (Complex.diskAutomorphism a η ha hη w : ℂ))) z := by
  have hden := Complex.diskMoebius_denominator_ne_zero ha
    (by simpa using (Metric.ball_subset_closedBall hz))
  have hd := (Complex.hasDerivAt_const_mul_diskMoebius η hden).differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  change diskExtension (fun v => (Complex.diskAutomorphism a η ha hη v : ℂ)) w =
    η * Complex.diskMoebius a w
  rw [diskExtension_coe _ ⟨w, Metric.ball_subset_closedBall hw⟩,
    Complex.coe_diskAutomorphism_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

theorem integral_diskMapEnergyDensity_diskAutomorphism
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    ∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u ∘ Complex.diskAutomorphism a η ha hη)) z =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z :=
  integral_diskMapEnergyDensity_reparametrize g hu (Complex.diskAutomorphism a η ha hη)
    (Complex.lipschitz_diskAutomorphism a η ha hη)
    (Complex.lipschitz_diskAutomorphism_symm a η ha hη)
    (fun _ hz => differentiableAt_diskExtension_diskAutomorphism ha hη hz)

theorem exists_diskAutomorphism_three_point_normalized_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) (γ : freeLoop M) (σ : C(loopCircle, loopCircle))
    (f : CircleDeg1Lift) (hf : Continuous f)
    (hσ : ∀ t : ℝ, (f t : loopCircle) = σ (t : loopCircle))
    (htrace : diskTrace u = γ.comp σ) {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ∃ a η : ℂ, ∃ ha : ‖a‖ < 1, ∃ hη : ‖η‖ = 1,
      let φ := Complex.diskAutomorphism a η ha hη
      let δ := diskAutomorphismBoundary a η ha hη
      let τ := σ.comp ⟨δ, δ.continuous⟩
      let v := u.comp ⟨φ, φ.continuous⟩
      (∃ k : CircleDeg1Lift, Continuous k ∧ ∀ t : ℝ, (k t : loopCircle) = τ (t : loopCircle)) ∧
      diskTrace v = γ.comp τ ∧ τ 0 = 0 ∧ τ (p : loopCircle) = (p : loopCircle) ∧
      τ (q : loopCircle) = (q : loopCircle) ∧
      (∃ D : ℝ≥0, ∀ x y, riemannianEDistOf g (v x) (v y) ≤ (D : ℝ≥0∞) * edist x y) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension v) z) =
        ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  obtain ⟨a, η, ha, hη, h0, hp', hq'⟩ :=
    exists_diskAutomorphismBoundary_three_point_normalization σ f hf hσ hp hpq hq
  let φ := Complex.diskAutomorphism a η ha hη
  let δ := diskAutomorphismBoundary a η ha hη
  obtain ⟨h, hh, _, hδ⟩ := exists_continuous_circleDeg1Lift_diskAutomorphismBoundary a η ha hη
  have hτ := CircleDeg1Lift.exists_continuous_lift_comp
    (δ := ⟨δ, δ.continuous⟩) f h hf hh hσ hδ
  refine ⟨a, η, ha, hη, hτ, ?_, h0, hp', hq', ?_, ?_⟩
  · rw [diskTrace_comp_of_map_boundary u ⟨φ, φ.continuous⟩ ⟨δ, δ.continuous⟩
      (diskAutomorphism_diskBoundary a η ha hη), htrace]
    rfl
  · let K : ℝ≥0 := ⟨(1 + ‖a‖) / (1 - ‖a‖), by positivity⟩
    refine ⟨C * K, fun x y => ?_⟩
    calc
      riemannianEDistOf g (u (φ x)) (u (φ y)) ≤
          (C : ℝ≥0∞) * edist (φ x) (φ y) := hu _ _
      _ ≤ (C : ℝ≥0∞) * ((K : ℝ≥0∞) * edist x y) := by
        gcongr
        exact Complex.lipschitz_diskAutomorphism a η ha hη x y
      _ = (↑(C * K) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]
  · exact integral_diskMapEnergyDensity_diskAutomorphism g hu a η ha hη

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold MeasureTheory Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology ComplexConjugate
namespace DifferentialGeometry.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

theorem exists_diskAutomorphism_three_point_signed_normalized_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) (γ : freeLoop M)
    (htrace : DiskWeakJordanTrace γ u) {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ∃ a η : ℂ, ∃ ha : ‖a‖ < 1, ∃ hη : ‖η‖ = 1,
      let φ := Complex.diskAutomorphism a η ha hη
      let δ := diskAutomorphismBoundary a η ha hη
      ∃ v : C(closedDisk, M), ∃ σ : C(loopCircle, loopCircle), ∃ f : CircleDeg1Lift,
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      (∀ x y, riemannianEDistOf g (v x) (v y) ≤ (C : ℝ≥0∞) * edist x y) ∧
      Continuous f ∧ (∀ t : ℝ, (f t : loopCircle) = σ (t : loopCircle)) ∧
      diskTrace v = γ.comp σ ∧
      σ (δ 0) = 0 ∧ σ (δ (p : loopCircle)) = (p : loopCircle) ∧
      σ (δ (q : loopCircle)) = (q : loopCircle) ∧
      (∃ D : ℝ≥0, ∀ x y, riemannianEDistOf g (v.comp ⟨φ, φ.continuous⟩ x)
        (v.comp ⟨φ, φ.continuous⟩ y) ≤ (D : ℝ≥0∞) * edist x y) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension (v.comp ⟨φ, φ.continuous⟩)) z) =
        ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  obtain ⟨v, σ, f, hv, hf, hflift, htr⟩ := htrace.exists_positive_lift_trace
  have hvu : ∀ x y, riemannianEDistOf g (v x) (v y) ≤ (C : ℝ≥0∞) * edist x y := by
    rcases hv with rfl | rfl
    · exact hu
    · intro x y
      exact (hu _ _).trans (by
        gcongr
        simpa using (diskReflection_lipschitz x y))
  obtain ⟨a, η, ha, hη, hpos, htrpos, h0, hp', hq', hD, hE⟩ :=
    exists_diskAutomorphism_three_point_normalized_energy g v γ σ f hf hflift htr hvu hp hpq hq
  refine ⟨a, η, ha, hη, ?_⟩
  dsimp
  refine ⟨v, σ, f, hv, hvu, hf, hflift, htr, h0, hp', hq', hD, ?_⟩
  calc
    (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension (v.comp ⟨Complex.diskAutomorphism a η ha hη,
          (Complex.diskAutomorphism a η ha hη).continuous⟩)) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension v) z := hE
    _ = ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
      rcases hv with rfl | rfl
      · rfl
      · exact integral_diskMapEnergyDensity_diskReflection g
end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold MeasureTheory Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

theorem exists_three_point_normalized_disk_energy_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ∃ v : C(closedDisk, M), ∃ τ : C(loopCircle, loopCircle),
      v ∈ weaklyMonotoneDiskCompetitors g γ ∧ IsWeaklyMonotoneOnce τ ∧
      diskTrace v = γ.comp τ ∧ τ 0 = 0 ∧
      τ (p : loopCircle) = (p : loopCircle) ∧ τ (q : loopCircle) = (q : loopCircle) ∧
      riemannianDiskEnergy g v = riemannianDiskEnergy g u := by
  obtain ⟨htrace, C, hC⟩ := hu
  obtain ⟨a, η, ha, hη, v, σ, f, _, _, hf, hflift, htr, h0, hp', hq', hD, henergy⟩ :=
    exists_diskAutomorphism_three_point_signed_normalized_energy g u γ htrace hC hp hpq hq
  let φ := Complex.diskAutomorphism a η ha hη
  let δ := diskAutomorphismBoundary a η ha hη
  let τ := σ.comp ⟨δ, δ.continuous⟩
  let w := v.comp ⟨φ, φ.continuous⟩
  obtain ⟨h, hh, _, hδ⟩ := exists_continuous_circleDeg1Lift_diskAutomorphismBoundary a η ha hη
  obtain ⟨k, hk, hklift⟩ := CircleDeg1Lift.exists_continuous_lift_comp
    (δ := ⟨δ, δ.continuous⟩) f h hf hh hflift hδ
  have hτ : IsWeaklyMonotoneOnce τ :=
    ⟨k, hk, hklift, Or.inl ⟨k.monotone, k.map_add_one⟩⟩
  have hw : diskTrace w = γ.comp τ := by
    rw [diskTrace_comp_of_map_boundary v ⟨φ, φ.continuous⟩ ⟨δ, δ.continuous⟩
      (diskAutomorphism_diskBoundary a η ha hη), htr]
    rfl
  exact ⟨w, τ, ⟨⟨τ, hτ, hw⟩, hD⟩, hτ, hw, h0, hp', hq', henergy⟩

theorem exists_three_point_normalized_disk_sequence_energy_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ∃ v : ℕ → C(closedDisk, M), ∃ τ : ℕ → C(loopCircle, loopCircle),
      (∀ n, v n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      (∀ n, IsWeaklyMonotoneOnce (τ n)) ∧
      (∀ n, diskTrace (v n) = γ.comp (τ n)) ∧
      (∀ n, τ n 0 = 0) ∧
      (∀ n, τ n (p : loopCircle) = (p : loopCircle)) ∧
      (∀ n, τ n (q : loopCircle) = (q : loopCircle)) ∧
      ∀ n, riemannianDiskEnergy g (v n) = riemannianDiskEnergy g (u n) := by
  classical
  choose v τ hv hτ htrace h0 hp' hq' henergy using
    fun n => exists_three_point_normalized_disk_energy_eq g (hu n) hp hpq hq
  exact ⟨v, τ, hv, hτ, htrace, h0, hp', hq', henergy⟩

theorem exists_three_point_normalized_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hfinite : (weaklyMonotoneDiskCompetitors g γ).Nonempty)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ∃ u : ℕ → C(closedDisk, M), ∃ σ : ℕ → C(loopCircle, loopCircle),
      (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      (∀ n, IsWeaklyMonotoneOnce (σ n)) ∧
      (∀ n, diskTrace (u n) = γ.comp (σ n)) ∧
      (∀ n, σ n 0 = 0) ∧
      (∀ n, σ n (p : loopCircle) = (p : loopCircle)) ∧
      (∀ n, σ n (q : loopCircle) = (q : loopCircle)) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
        (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
          weaklyMonotoneDiskCompetitors g γ))) := by
  classical
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  obtain ⟨e, hanti, htendsto, he⟩ := exists_seq_tendsto_sInf
    (hfinite.image (fun v : C(closedDisk, M) => riemannianDiskEnergy g v)) hbound
  choose v hv hve using he
  obtain ⟨u, σ, hu, hσ, htrace, h0, hp', hq', henergy⟩ :=
    exists_three_point_normalized_disk_sequence_energy_eq g v hv hp hpq hq
  refine ⟨u, σ, hu, hσ, htrace, h0, hp', hq', ?_, ?_⟩
  · simpa only [henergy, hve] using hanti
  · simpa only [henergy, hve] using htendsto

end DifferentialGeometry.Geometry

end
