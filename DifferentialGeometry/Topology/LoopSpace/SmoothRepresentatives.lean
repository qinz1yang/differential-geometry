import DifferentialGeometry.Topology.LoopSpace.ManifoldSmoothing
import DifferentialGeometry.Topology.LoopSpace.FiniteRegular









noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.Topology

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M] [Nonempty M]




theorem exists_smooth_loop_family (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Γ : C(K, freeLoop M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : C(K, freeLoop M))
      (hs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => S k (t : loopCircle)))
      (H : Γ.Homotopy S),
      (∀ (d : ℕ) (e : M → EuclideanSpace ℝ (Fin d))
        (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ e) (r : ℕ),
        Continuous[inferInstance, finiteRegularLoopTopology e he r]
          (fun k => (⟨S k, (hs k).of_le (by exact_mod_cast le_top)⟩ : finiteRegularLoop r E M))) ∧
      (∀ t k θ, riemannianEDistOf g (H (t, k) θ) (Γ k θ) < ENNReal.ofReal ε) ∧
      (∀ k q, Γ k = .const loopCircle q → ∀ t, H (t, k) = .const loopCircle q) ∧
      (∀ k, (Γ k).Nullhomotopic → ∀ t, (H (t, k)).Nullhomotopic) := by
  obtain ⟨δ, hδ, hδS⟩ := exists_uniform_smooth_loop_homotopy g Γ hε
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  obtain ⟨S, H, hs, hj, hclose, hconst, hnull⟩ := hδS φ (by dsimp [φ]; linarith)
  refine ⟨S, hs, H, ?_, hclose, hconst, hnull⟩
  intro d e he r
  apply (continuous_finiteRegularLoop_iff e he r _).mpr
  intro i
  exact hj d e he i.val

end DifferentialGeometry.Topology
