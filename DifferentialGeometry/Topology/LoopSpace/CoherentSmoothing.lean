import DifferentialGeometry.Topology.LoopSpace.MetricSmoothing
import DifferentialGeometry.Topology.LoopSpace.SmoothingCoherence
import DifferentialGeometry.Topology.LoopSpace.FiniteRegular









noncomputable section

open Set Function ContinuousMap Manifold Metric DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal NNReal

universe u

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]




theorem exists_coherent_loop_smoothing (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n))
      (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e),
      _root_.Topology.IsEmbedding e ∧
      (∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p)) ∧
      ∃ C : ℝ≥0, ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K]
        (Γ : C(K, freeLoop M)) (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
          ∃ (S : C(K, freeLoop M))
            (hs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => S k (t : loopCircle)))
            (H : Γ.Homotopy S),
            (∀ (d : ℕ) (a : M → EuclideanSpace ℝ (Fin d))
              (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a) (j : ℕ),
              Continuous[inferInstance, finiteRegularLoopTopology a ha j]
                (fun k => (⟨S k, (hs k).of_le (by exact_mod_cast le_top)⟩ : finiteRegularLoop j E M))) ∧
            (∀ t k θ, riemannianEDistOf g (H (t, k) θ) (Γ k θ) < ENNReal.ofReal ε) ∧
            (∀ k q, Γ k = .const loopCircle q → ∀ t, H (t, k) = .const loopCircle q) ∧
            (∀ k, (Γ k).Nullhomotopic → ∀ t, (H (t, k)).Nullhomotopic) ∧
            (∀ V : ℝ≥0,
              (∀ k θ η, riemannianEDistOf g (Γ k θ) (Γ k η) ≤ (V : ℝ≥0∞) * edist θ η) →
              ∀ k θ η, riemannianEDistOf g (S k θ) (S k η) ≤
                ((C * V : ℝ≥0) : ℝ≥0∞) * edist θ η) ∧
            (∀ Γ₁ : K → regularLoop E M,
              Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ₁ →
              (∀ k, (Γ₁ k).val = Γ k) →
              ∃ R : unitInterval × K → regularLoop E M,
                Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] R ∧
                (∀ p, (R p).val = H p) ∧
                (∀ k, regularLoopDist e (he.of_le (by exact_mod_cast le_top)) (R (1, k)) (Γ₁ k) < ε)) := by
  obtain ⟨n, e, r, U, he, hemb, hi, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_compact_embedding_and_retraction (E := E) (M := M)
  obtain ⟨ρ, hρ, hρK, hρU⟩ := DifferentialGeometry.Analysis.exists_compact_cthickening_subset
    (isCompact_range he.continuous) hU heU
  obtain ⟨C, hC⟩ := exists_smoothing_metric_lipschitz_constant g e
    (he.of_le (by exact_mod_cast le_top)) hU (hr.of_le (by exact_mod_cast le_top)) hρK hρU
  refine ⟨n, e, he, hemb.isEmbedding, hi, C, fun K _ _ Γ ε hε => ?_⟩
  obtain ⟨a, ha, haS⟩ := exists_uniform_retracted_loop_homotopy g e r U he hU heU hr hleft Γ hε
  let A : C(K, freeLoop (EuclideanSpace ℝ (Fin n))) :=
    (FreeLoop.postcompose ⟨e, he.continuous⟩).comp Γ
  obtain ⟨b, hb, hbA⟩ := smoothPeriodic_uniform_approximation A.uncurry.continuous hρ
  obtain ⟨c, hc, hcR⟩ := exists_uniform_regular_smoothing_lift e he hemb.isEmbedding r U hU heU hr hleft Γ hε
  refine ⟨min (min a b) c, lt_min (lt_min ha hb) hc, fun φ hφ => ?_⟩
  have hφa := hφ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hφb := hφ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hφc := hφ.trans_le (min_le_right _ _)
  obtain ⟨S, H, hs, hj, hclose, hconst, hnull, hSformula, hHformula⟩ := haS φ hφa
  refine ⟨S, hs, H, ?_, hclose, hconst, hnull, ?_, hcR φ hφc H hHformula⟩
  · intro d a ha j
    apply (continuous_finiteRegularLoop_iff a ha j _).mpr
    intro i
    exact hj d a ha i.val
  · intro V hV k θ η
    rw [hSformula, hSformula]
    apply hC φ (Γ k) V (hV k)
    intro ξ
    apply mem_cthickening_of_dist_le _ (e (Γ k ξ)) ρ (range e) (mem_range_self _)
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective ξ
    exact (hbA φ hφb k t).le

end DifferentialGeometry.Topology
