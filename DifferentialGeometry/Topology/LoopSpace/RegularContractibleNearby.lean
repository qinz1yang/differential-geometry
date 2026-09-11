import DifferentialGeometry.Topology.LoopSpace.RegularContractible
import DifferentialGeometry.Topology.LoopSpace.RegularMetricNearby



noncomputable section

open Set Function ContinuousMap Manifold Metric DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



theorem regular_homotopy_nullhomotopic (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e)
    (R : unitInterval × K → regularLoop E M)
    (hc : Continuous[inferInstance, regularLoopTopology e he] R)
    (hn : ∀ k, (R (0, k)).val.Nullhomotopic) : ∀ p, (R p).val.Nullhomotopic := by
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he
  have hcont : Continuous (fun p : unitInterval × K => (R p).val) :=
    (continuous_regularLoop_inclusion e he hemb).comp hc
  rintro ⟨τ, k⟩
  have hp : Joined (0 : unitInterval) τ :=
    ⟨⟨⟨fun s => s * τ, continuous_id.mul continuous_const⟩, zero_mul τ, one_mul τ⟩⟩
  have hj : Joined (R (0, k)).val (R (τ, k)).val :=
    hp.map (hcont.comp (continuous_id.prodMk continuous_const))
  exact FreeLoop.nullhomotopic_of_homotopic ((FreeLoop.homotopic_iff_joined _ _).mpr hj) (hn k)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] [Nonempty M]



theorem exists_regular_contractible_nearby_homotopy_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    letI : TopologicalSpace (regularContractibleLoop E M) :=
      regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top));
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ Δ : C(K, regularContractibleLoop E M),
      (∀ k θ, riemannianEDistOf g ((Δ k).val.val θ) ((Γ k).val.val θ) < ENNReal.ofReal ε) →
      ∃ H : Γ.Homotopy Δ, ∀ k, Γ k = Δ k → ∀ τ, H (τ, k) = Γ k := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  obtain ⟨ε, hε, hR⟩ := exists_regular_metric_nearby_homotopy_radius g e he hemb hi
  refine ⟨ε, hε, fun Γ Δ hclose => ?_⟩
  obtain ⟨R, hc, hz, ho, hf⟩ := hR K (fun k => (Γ k).val) (fun k => (Δ k).val)
    ((continuous_regularContractibleLoop_iff e he₁ _).mp Γ.continuous)
    ((continuous_regularContractibleLoop_iff e he₁ _).mp Δ.continuous) hclose
  have hn : ∀ p, (R p).val.Nullhomotopic :=
    regular_homotopy_nullhomotopic e he₁ hemb R hc (fun k => by rw [hz]; exact (Γ k).property)
  have hcn : Continuous (fun p => (⟨R p, hn p⟩ : regularContractibleLoop E M)) :=
    (continuous_regularContractibleLoop_iff e he₁ _).mpr hc
  let H : Γ.Homotopy Δ :=
    ⟨⟨fun p => ⟨R p, hn p⟩, hcn⟩,
      fun k => Subtype.ext (hz k), fun k => Subtype.ext (ho k)⟩
  exact ⟨H, fun k hk τ => Subtype.ext (hf k (congrArg Subtype.val hk) τ)⟩

end DifferentialGeometry.Topology
