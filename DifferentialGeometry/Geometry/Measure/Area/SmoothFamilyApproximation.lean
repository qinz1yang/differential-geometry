import DifferentialGeometry.Geometry.Measure.Area.RegularLeastArea
import DifferentialGeometry.Geometry.Metric.LoopLengthReparametrization
import DifferentialGeometry.Topology.LoopSpace.CoherentSmoothing
import DifferentialGeometry.Topology.LoopSpace.RegularRepresentatives








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]



theorem exists_smooth_family_leastArea_approximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (Γ : C(K, contractibleLoop M)) (V : ℝ≥0)
    (hV : ∀ k θ η, riemannianEDistOf g ((Γ k).val θ) ((Γ k).val η) ≤
      (V : ℝ≥0∞) * edist θ η) {ε : ℝ} (hε : 0 < ε) :
    letI : TopologicalSpace (regularContractibleLoop E M) :=
      regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top));
    ∃ (S : C(K, regularContractibleLoop E M))
      (hs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (S k).val.val (t : loopCircle)))
      (H : Γ.Homotopy
        ((⟨regularContractibleLoopInclusion,
          continuous_regularContractibleLoopInclusion e (he.of_le (by exact_mod_cast le_top)) hemb⟩ :
          C(regularContractibleLoop E M, contractibleLoop M)).comp S)),
      (∀ (d : ℕ) (a : M → EuclideanSpace ℝ (Fin d))
        (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a) (j : ℕ),
        Continuous[inferInstance, finiteRegularLoopTopology a ha j]
          (fun k => (⟨(S k).val.val, (hs k).of_le (by exact_mod_cast le_top)⟩ :
            finiteRegularLoop j E M))) ∧
      (∀ k, |regularLeastArea g (S k) - leastSpanningArea g ⟨Γ k, V, hV k⟩| < ε) ∧
      (∀ k q, Γ k = ContractibleLoop.constants q → ∀ t, H (t, k) = ContractibleLoop.constants q) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  obtain ⟨ρ, C, hρ, _, hann⟩ := exists_leastSpanningArea_annulus_bound g
  obtain ⟨_, _, _, _, _, Cs, hsm⟩ := exists_coherent_loop_smoothing g
  let B : ℝ := (C : ℝ) * ((Cs * V : ℝ≥0) + (V : ℝ))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let d : ℝ := min ((ρ : ℝ) / 2) (ε / (2 * (B + 1)))
  have hd : 0 < d := lt_min (half_pos (by exact_mod_cast hρ)) (by positivity)
  have hdρ : d < (ρ : ℝ) :=
    (min_le_left _ _).trans_lt (half_lt_self (by exact_mod_cast hρ))
  have hdB : B * d < ε := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp
      (min_le_right ((ρ : ℝ) / 2) (ε / (2 * (B + 1))))
    change d * (2 * (B + 1)) ≤ ε at h
    nlinarith
  obtain ⟨δ, hδ, hδS⟩ := hsm K (ContractibleLoop.inclusion.comp Γ) d hd
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  obtain ⟨S₀, hs, H₀, hCr, hclose, hconst, hnull, hLip, _⟩ := hδS φ (by dsimp [φ]; linarith)
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
    ⟨⟨fun p => ⟨H₀ p, hnull p.2 (Γ p.2).property p.1⟩, H₀.continuous.subtype_mk _⟩,
      fun k => Subtype.ext (H₀.apply_zero k), fun k => Subtype.ext (H₀.apply_one k)⟩
  refine ⟨S, hs, H, hCr, ?_, ?_⟩
  · intro k
    have hSlen := loop_arclength_le_of_riemannian_lipschitz g (hLip V hV k)
    have hΓlen := loop_arclength_le_of_riemannian_lipschitz g (hV k)
    let γ : lipschitzContractibleLoop g := ⟨Γ k, V, hV k⟩
    let σ := regularContractibleToLipschitz g (S k)
    have hdist : (riemannianLoopDistance g σ.val.val γ.val.val : ℝ) ≤ d := by
      have h := riemannianLoopDistance_le_of_pointwise g σ.val.val γ.val.val (B := ⟨d, hd.le⟩)
        (fun θ => by
          have hc := (hclose 1 k θ).le
          rw [ENNReal.ofReal_eq_coe_nnreal hd.le] at hc
          simpa only [H₀.apply_one] using! hc)
      exact_mod_cast h
    have hnear : riemannianLoopDistance g σ.val.val γ.val.val < ρ := by
      exact_mod_cast hdist.trans_lt hdρ
    have ha := hann σ γ hnear
    have hbound : (C : ℝ) * riemannianLoopDistance g σ.val.val γ.val.val *
        (riemannianCurveLength g (fun t => σ.val.val (t : loopCircle)) 0 1 +
          riemannianCurveLength g (fun t => γ.val.val (t : loopCircle)) 0 1) ≤ B * d := by
      calc
        _ ≤ (C : ℝ) * d * ((Cs * V : ℝ≥0) + (V : ℝ)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hdist C.coe_nonneg
          · exact add_le_add hSlen hΓlen
          · exact add_nonneg (riemannianCurveLength_nonneg g _ _ _)
              (riemannianCurveLength_nonneg g _ _ _)
          · positivity
        _ = B * d := by dsimp only [B]; ring
    exact (ha.trans hbound).trans_lt hdB
  · intro k q hk t
    apply Subtype.ext
    exact hconst k q (congrArg Subtype.val hk) t

end DifferentialGeometry.Geometry
