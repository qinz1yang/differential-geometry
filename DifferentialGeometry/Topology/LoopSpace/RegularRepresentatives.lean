import DifferentialGeometry.Topology.LoopSpace.RegularContractible
import DifferentialGeometry.Topology.LoopSpace.FiniteRegularOne
import DifferentialGeometry.Topology.LoopSpace.SmoothRepresentatives



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M] [Nonempty M]




theorem exists_regular_contractible_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e) (Γ : C(K, contractibleLoop M)) :
    letI : TopologicalSpace (regularContractibleLoop E M) :=
      regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top));
    ∃ (S : C(K, regularContractibleLoop E M))
      (H : Γ.Homotopy
        ((⟨regularContractibleLoopInclusion,
          continuous_regularContractibleLoopInclusion e (he.of_le (by exact_mod_cast le_top)) hemb⟩ :
          C(regularContractibleLoop E M, contractibleLoop M)).comp S)),
      (∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (S k).val.val (t : loopCircle))) ∧
      (∀ k q, Γ k = ContractibleLoop.constants q → ∀ t, H (t, k) = ContractibleLoop.constants q) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  obtain ⟨S₀, hs, H₀, hCr, _, hconst, hnull⟩ :=
    exists_smooth_loop_family g (ContractibleLoop.inclusion.comp Γ) zero_lt_one
  have hSn (k : K) : (S₀ k).Nullhomotopic := by
    simpa only [H₀.apply_one] using hnull k (Γ k).property 1
  let Sfun : K → regularContractibleLoop E M :=
    fun k => ⟨⟨S₀ k, (hs k).of_le (by exact_mod_cast le_top)⟩, hSn k⟩
  have hS : Continuous Sfun := by
    apply (continuous_regularContractibleLoop_iff e he₁ _).mpr
    rw [← finiteRegularLoopTopology_one e he]
    exact hCr n e he 1
  let S : C(K, regularContractibleLoop E M) := ⟨Sfun, hS⟩
  let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
    ⟨regularContractibleLoopInclusion, continuous_regularContractibleLoopInclusion e he₁ hemb⟩
  let H : Γ.Homotopy (inc.comp S) :=
    ⟨⟨fun p => ⟨H₀ p, hnull p.2 (Γ p.2).property p.1⟩,
      H₀.continuous.subtype_mk _⟩,
      fun k => Subtype.ext (H₀.apply_zero k), fun k => Subtype.ext (H₀.apply_one k)⟩
  refine ⟨S, H, hs, ?_⟩
  intro k q hk t
  apply Subtype.ext
  exact hconst k q (congrArg Subtype.val hk) t

end DifferentialGeometry.Topology
