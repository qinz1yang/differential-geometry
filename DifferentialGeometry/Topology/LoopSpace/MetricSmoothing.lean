import DifferentialGeometry.Topology.LoopSpace.ManifoldSmoothing
import DifferentialGeometry.Topology.LoopSpace.SmoothingLipschitz
import DifferentialGeometry.Analysis.FiniteDimensional.CompactNeighborhood










noncomputable section

open Set Function ContinuousMap Manifold Metric DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal NNReal

universe u

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]





theorem exists_uniform_metric_loop_smoothing (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ C : ℝ≥0, ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K]
      (Γ : C(K, freeLoop M)) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
        ∃ (S : C(K, freeLoop M)) (H : Γ.Homotopy S),
          (∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => S k (t : loopCircle))) ∧
          (∀ (d : ℕ) (a : M → EuclideanSpace ℝ (Fin d)),
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a →
            ∀ j, Continuous (fun p : K × ℝ =>
              iteratedDeriv j (fun t : ℝ => a (S p.1 (t : loopCircle))) p.2)) ∧
          (∀ t k θ, riemannianEDistOf g (H (t, k) θ) (Γ k θ) < ENNReal.ofReal ε) ∧
          (∀ k q, Γ k = .const loopCircle q → ∀ t, H (t, k) = .const loopCircle q) ∧
          (∀ k, (Γ k).Nullhomotopic → ∀ t, (H (t, k)).Nullhomotopic) ∧
          (∀ V : ℝ≥0,
            (∀ k θ η, riemannianEDistOf g (Γ k θ) (Γ k η) ≤ (V : ℝ≥0∞) * edist θ η) →
            ∀ k θ η, riemannianEDistOf g (S k θ) (S k η) ≤
              ((C * V : ℝ≥0) : ℝ≥0∞) * edist θ η) := by
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction (E := E) (M := M)
  obtain ⟨ρ, hρ, hρK, hρU⟩ := DifferentialGeometry.Analysis.exists_compact_cthickening_subset
    (isCompact_range he.continuous) hU heU
  obtain ⟨C, hC⟩ := exists_smoothing_metric_lipschitz_constant g e
    (he.of_le (by exact_mod_cast le_top)) hU (hr.of_le (by exact_mod_cast le_top)) hρK hρU
  refine ⟨C, fun K _ _ Γ ε hε => ?_⟩
  obtain ⟨a, ha, haS⟩ := exists_uniform_retracted_loop_homotopy g e r U he hU heU hr hleft Γ hε
  let A : C(K, freeLoop (EuclideanSpace ℝ (Fin n))) :=
    (FreeLoop.postcompose ⟨e, he.continuous⟩).comp Γ
  obtain ⟨b, hb, hbA⟩ := smoothPeriodic_uniform_approximation A.uncurry.continuous hρ
  refine ⟨min a b, lt_min ha hb, fun φ hφ => ?_⟩
  obtain ⟨S, H, hs, hj, hclose, hconst, hnull, hformula, _⟩ :=
    haS φ (hφ.trans_le (min_le_left _ _))
  refine ⟨S, H, hs, hj, hclose, hconst, hnull, ?_⟩
  intro V hV k θ η
  rw [hformula, hformula]
  apply hC φ (Γ k) V (hV k)
  intro ξ
  apply mem_cthickening_of_dist_le _ (e (Γ k ξ)) ρ (range e) (mem_range_self _)
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  exact (hbA φ (hφ.trans_le (min_le_right _ _)) k t).le

end DifferentialGeometry.Topology
