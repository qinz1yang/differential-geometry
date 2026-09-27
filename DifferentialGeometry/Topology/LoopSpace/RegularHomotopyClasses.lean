import DifferentialGeometry.Topology.LoopSpace.RegularRepresentatives
import DifferentialGeometry.Topology.LoopSpace.RegularContractibleNearby



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.Topology

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M] [Nonempty M]





theorem regular_contractible_homotopicRel_of_continuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p)) :
    letI : TopologicalSpace (regularContractibleLoop E M) :=
      regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top));
    let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
      ⟨regularContractibleLoopInclusion,
        continuous_regularContractibleLoopInclusion e (he.of_le (by exact_mod_cast le_top)) hemb⟩;
    ∀ (Γ Δ : C(K, regularContractibleLoop E M)) (A : Set K),
      (∀ k ∈ A, ∃ q, Γ k = regularContractibleLoopConst q) →
      (inc.comp Γ).HomotopicRel (inc.comp Δ) A → Γ.HomotopicRel Δ A := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
    ⟨regularContractibleLoopInclusion, continuous_regularContractibleLoopInclusion e he₁ hemb⟩
  dsimp only
  intro Γ Δ A hA ⟨Hc⟩
  obtain ⟨ε, hε, hnear⟩ :=
    exists_regular_contractible_nearby_homotopy_radius (K := K) g e he hemb hi
  let Ψ : C(unitInterval × K, freeLoop M) := ContractibleLoop.inclusion.comp Hc.toContinuousMap
  obtain ⟨S₀, hs, F, hCr, hclose, hconst, hnull⟩ := exists_smooth_loop_family g Ψ hε
  have hSn (p : unitInterval × K) : (S₀ p).Nullhomotopic := by
    simpa only [F.apply_one] using hnull p (Hc p).property 1
  let Sfun : unitInterval × K → regularContractibleLoop E M :=
    fun p => ⟨⟨S₀ p, (hs p).of_le (by exact_mod_cast le_top)⟩, hSn p⟩
  have hS : Continuous Sfun := by
    apply (continuous_regularContractibleLoop_iff e he₁ _).mpr
    rw [← finiteRegularLoopTopology_one e he]
    exact hCr n e he 1
  let S : C(unitInterval × K, regularContractibleLoop E M) := ⟨Sfun, hS⟩
  let Szero : C(K, regularContractibleLoop E M) := ⟨fun k => S (0, k),
    S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let Sone : C(K, regularContractibleLoop E M) := ⟨fun k => S (1, k),
    S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hzclose (k : K) (θ : loopCircle) :
      riemannianEDistOf g ((Szero k).val.val θ) ((Γ k).val.val θ) < ENNReal.ofReal ε := by
    have h := hclose 1 (0, k) θ
    rw [F.apply_one] at h
    change riemannianEDistOf g (S₀ (0, k) θ) ((Hc (0, k)).val θ) < _ at h
    rw [Hc.apply_zero] at h
    exact h
  have hoclose (k : K) (θ : loopCircle) :
      riemannianEDistOf g ((Sone k).val.val θ) ((Δ k).val.val θ) < ENNReal.ofReal ε := by
    have h := hclose 1 (1, k) θ
    rw [F.apply_one] at h
    change riemannianEDistOf g (S₀ (1, k) θ) ((Hc (1, k)).val θ) < _ at h
    rw [Hc.apply_one] at h
    exact h
  obtain ⟨Jzero, hJzero⟩ := hnear Γ Szero hzclose
  obtain ⟨Jone, hJone⟩ := hnear Δ Sone hoclose
  have hfix (t : unitInterval) (k : K) (hk : k ∈ A) : S (t, k) = Γ k := by
    obtain ⟨q, hq⟩ := hA k hk
    have hΨ : Ψ (t, k) = .const loopCircle q := by
      change (Hc (t, k)).val = _
      rw [Hc.eq_fst t hk]
      change (Γ k).val.val = _
      rw [hq]
      rfl
    apply Subtype.ext
    apply Subtype.ext
    change S₀ (t, k) = (Γ k).val.val
    rw [hq]
    exact (F.apply_one (t, k)) ▸ hconst (t, k) q hΨ 1
  have hΓΔ (k : K) (hk : k ∈ A) : Γ k = Δ k := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun γ : contractibleLoop M => γ.val) (Hc.fst_eq_snd hk)
  let Jz : Γ.HomotopyRel Szero A :=
    ⟨Jzero, fun t k hk => hJzero k (hfix 0 k hk).symm t⟩
  let Jo : Δ.HomotopyRel Sone A :=
    ⟨Jone, fun t k hk => hJone k ((hΓΔ k hk).symm.trans (hfix 1 k hk).symm) t⟩
  let Jm : Szero.HomotopyRel Sone A :=
    ⟨⟨S, fun _ => rfl, fun _ => rfl⟩,
      fun t k hk => (hfix t k hk).trans (hfix 0 k hk).symm⟩
  exact ⟨Jz.trans (Jm.trans Jo.symm)⟩

end DifferentialGeometry.Topology
