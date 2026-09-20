import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Retraction
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_embedded_minimizing_sequence_bounds
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ)))) :
    ∃ (Ku : ℕ → ℝ≥0) (τ : ℕ → C(loopCircle, loopCircle)) (B : ℝ),
      0 ≤ B ∧
      (∀ n, LipschitzWith (Ku n) (Φ ∘ diskExtension (u n))) ∧
      (∀ n, MapsTo (Φ ∘ diskExtension (u n))
        (Metric.closedBall (0 : ℂ) 1) (range Φ)) ∧
      (∀ n, IsWeaklyMonotoneOnce (τ n)) ∧
      (∀ n θ, Φ (diskExtension (u n) (diskBoundary θ)) = Φ (γ (τ n θ))) ∧
      (∀ n, IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension (u n)) z‖ ^ 2)
        (Metric.closedBall (0 : ℂ) 1)) ∧
      (∀ n, (∫ z in Metric.closedBall (0 : ℂ) 1,
        ‖fderiv ℝ (Φ ∘ diskExtension (u n)) z‖ ^ 2) ≤ B) ∧
      (∀ n, IntegrableOn (fun z =>
        (pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1)
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1) +
          pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)) / 2)
        (Metric.closedBall (0 : ℂ) 1)) ∧
      (∀ n, (∫ z in Metric.closedBall (0 : ℂ) 1,
        (pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1)
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1) +
          pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)) / 2) =
          riemannianDiskEnergy g (u n)) ∧
      Tendsto (fun n => ∫ z in Metric.closedBall (0 : ℂ) 1,
        (pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1)
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1) +
          pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)
            (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)) / 2) atTop
        (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
          weaklyMonotoneDiskCompetitors g γ))) := by
  have hLip (n : ℕ) : ∃ K : ℝ≥0, ∀ x y : closedDisk,
      riemannianEDistOf g (u n x) (u n y) ≤ (K : ℝ≥0∞) * edist x y := (hu n).2
  choose K hK using hLip
  have htrace (n : ℕ) : ∃ τ : C(loopCircle, loopCircle),
      IsWeaklyMonotoneOnce τ ∧ diskTrace (u n) = γ.comp τ := (hu n).1
  choose τ hτ ht using htrace
  obtain ⟨C, _, hC⟩ := exists_integral_norm_fderiv_comp_diskExtension_sq_le g hΦ
  have hglobal (n : ℕ) : LipschitzWith (C * K n) (Φ ∘ diskExtension (u n)) :=
    (hC (u n) (K n) (hK n)).1
  have hmaps (n : ℕ) : MapsTo (Φ ∘ diskExtension (u n))
      (Metric.closedBall (0 : ℂ) 1) (range Φ) := fun z _ => mem_range_self _
  have hboundary (n : ℕ) (θ : loopCircle) :
      Φ (diskExtension (u n) (diskBoundary θ)) = Φ (γ (τ n θ)) := by
    rw [diskExtension_coe]
    exact congrArg Φ (congrArg (fun f : freeLoop M => f θ) (ht n))
  obtain ⟨D, hD⟩ := hmin.isBoundedUnder_le.bddAbove_range
  have hD0 : 0 ≤ D := (riemannianDiskEnergy_nonneg g (u 0)).trans (hD (mem_range_self 0))
  have hbound (n : ℕ) : (∫ z in Metric.closedBall (0 : ℂ) 1,
      ‖fderiv ℝ (Φ ∘ diskExtension (u n)) z‖ ^ 2) ≤ 4 * (C : ℝ) ^ 2 * D := by
    exact ((hC (u n) (K n) (hK n)).2.2).trans
      (mul_le_mul_of_nonneg_left (hD (mem_range_self n)) (by positivity))
  obtain ⟨Cr, hCr⟩ := exists_riemannian_lipschitz_disk_of_lipschitz_retraction
    g hΦ.continuous hU hr hΦU hleft
  let e : ℕ → ℂ → ℝ := fun n z =>
    (pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
        (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1)
        (fderiv ℝ (Φ ∘ diskExtension (u n)) z 1) +
      pullbackMetricCoefficients g r (Φ (diskExtension (u n) z))
        (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)
        (fderiv ℝ (Φ ∘ diskExtension (u n)) z Complex.I)) / 2
  have hcoeff (n : ℕ) : IntegrableOn (e n) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, e n z) = riemannianDiskEnergy g (u n) := by
    obtain ⟨w, hw, _, _, _, _, hwe, heq⟩ :=
      hCr (Φ ∘ diskExtension (u n)) (C * K n) (hglobal n) (hmaps n) γ (τ n) (hboundary n)
    have hwu : w = u n := by
      ext x
      rw [hw x]
      change r (Φ (diskExtension (u n) x)) = u n x
      rw [hleft, diskExtension_coe]
    subst w
    exact ⟨hwe, heq.symm⟩
  refine ⟨fun n => C * K n, τ, 4 * (C : ℝ) ^ 2 * D, by positivity,
    hglobal, hmaps, hτ, hboundary, fun n => (hC (u n) (K n) (hK n)).2.1,
    hbound, fun n => (hcoeff n).1, fun n => (hcoeff n).2, ?_⟩
  simpa only [← (hcoeff _).2] using hmin

end DifferentialGeometry.Geometry
