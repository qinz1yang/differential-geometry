import DifferentialGeometry.Geometry.Measure.Area.ShortLoopFilling
import DifferentialGeometry.Topology.LoopSpace.RegularContractibleNearby
import DifferentialGeometry.Topology.LoopSpace.RegularDerivativeBounds








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold ENNReal NNReal

universe u

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M] [Nonempty M]




theorem exists_short_loop_and_family_filling (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ σ K : ℝ≥0, 0 < σ ∧ 0 < K ∧
      (∀ (γ : freeLoop M) (L : ℝ≥0),
        (∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * edist x y) →
        riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 < σ →
        ∃ u ∈ spanningDiskCompetitors g γ,
          riemannianDiskArea g u ≤ K * (riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1) ^ 2) ∧
      (∀ (X : Type u) [TopologicalSpace X] (Γ : X → regularLoop E M),
        Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ →
        (∀ k, riemannianCurveLength g (fun t => (Γ k).val (t : loopCircle)) 0 1 < σ) →
        ∃ R : unitInterval × X → regularLoop E M,
          Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] R ∧
          (∀ k, R (0, k) = Γ k) ∧
          (∀ k, R (1, k) = (regularContractibleLoopConst ((Γ k).val 0)).val) ∧
          (∀ p, (R p).val.Nullhomotopic) ∧
          (∀ k, Γ k = (regularContractibleLoopConst ((Γ k).val 0)).val → ∀ τ, R (τ, k) = Γ k)) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  obtain ⟨σ₀, K, hσ₀, hK, hfill⟩ := exists_short_loop_filling_bound g
  obtain ⟨ε, hε, hfamily⟩ := exists_regular_metric_nearby_homotopy_radius g e he hemb hi
  let σ : ℝ≥0 := min σ₀ ⟨ε, hε.le⟩
  have hσ : 0 < σ := lt_min hσ₀ (by exact_mod_cast hε)
  have hσσ₀ : (σ : ℝ) ≤ σ₀ := by exact_mod_cast min_le_left σ₀ (⟨ε, hε.le⟩ : ℝ≥0)
  have hσε : (σ : ℝ) ≤ ε := by exact_mod_cast min_le_right σ₀ (⟨ε, hε.le⟩ : ℝ≥0)
  refine ⟨σ, K, hσ, hK, fun γ L hγ hs => hfill γ L hγ (hs.trans_le hσσ₀), ?_⟩
  intro X _ Γ hΓ hshort
  let q : X → M := fun k => (Γ k).val 0
  have hq : Continuous q := FreeLoop.evaluation.continuous.comp
    ((continuous_regularLoop_inclusion e he₁ hemb).comp hΓ)
  let Δ : X → regularLoop E M := fun k => (regularContractibleLoopConst (q k)).val
  have hΔ : Continuous Δ :=
    ((continuous_regularContractibleLoop_iff e he₁ _).mp
      (continuous_regularContractibleLoopConst e he₁)).comp hq
  have hclose (k : X) (θ : loopCircle) :
      riemannianEDistOf g ((Δ k).val θ) ((Γ k).val θ) < ENNReal.ofReal ε := by
    obtain ⟨L, hL⟩ := regularLoop_riemannian_lipschitz g (Γ k)
    apply (loopPoint_edist_le_length g (Γ k).val hL θ).trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr ((hshort k).trans_le hσε)
  obtain ⟨R, hR, hR0, hR1, hfix⟩ := hfamily X Γ Δ hΓ hΔ hclose
  have hnull (k : X) : (Γ k).val.Nullhomotopic := by
    obtain ⟨L, hL⟩ := regularLoop_riemannian_lipschitz g (Γ k)
    obtain ⟨u, ⟨ht, _⟩, _⟩ := hfill (Γ k).val L hL ((hshort k).trans_le hσσ₀)
    rw [← ht]
    exact diskTrace_nullhomotopic u
  refine ⟨R, hR, hR0, hR1, ?_, hfix⟩
  exact regular_homotopy_nullhomotopic e he₁ hemb R hR (fun k => by rw [hR0]; exact hnull k)

end DifferentialGeometry.Topology
