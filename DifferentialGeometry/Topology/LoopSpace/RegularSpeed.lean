import DifferentialGeometry.Topology.LoopSpace.RegularTopology
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]




theorem exists_regular_family_continuous_speed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ) :
    ∃ s : C(K × loopCircle, ℝ),
      (∀ k (t : ℝ), s (k, (t : loopCircle)) =
        riemannianCurveSpeed g (fun t : ℝ => (Γ k).val (t : loopCircle)) t) ∧
      ∃ C : ℝ≥0, ∀ p, s p ≤ C := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  obtain ⟨hcA, _⟩ := (continuous_regularLoop_iff e he₁ Γ).mp hΓ
  have hjet : Continuous (fun k => regularLoopJet e he₁ (Γ k)) := continuous_induced_rng.mp hΓ
  have hD : Continuous (fun p : K × loopCircle => regularLoopDerivative e he₁ (Γ p.1) p.2) :=
    (FreeLoop.continuous_family_iff _).mp hjet.snd
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    exists_smooth_neighborhood_retraction he hemb hi
  let hr₁ := hr.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let A : K × loopCircle → F × F := fun p =>
    (e ((Γ p.1).val p.2), regularLoopDerivative e he₁ (Γ p.1) p.2)
  have hA : Continuous A := hcA.prodMk hD
  let s : C(K × loopCircle, ℝ) :=
    ⟨fun p => Real.sqrt (g.inner (r (A p).1)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (A p).1 (A p).2)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (A p).1 (A p).2)),
      (continuousOn_metric_mfderiv_norm g hU hr₁).comp_continuous hA
        (fun p => ⟨heU (mem_range_self _), mem_univ _⟩)⟩
  refine ⟨s, ?_, ?_⟩
  · intro k t
    have hγeq : (fun t : ℝ => (Γ k).val (t : loopCircle)) =
        r ∘ (fun t : ℝ => e ((Γ k).val (t : loopCircle))) := by
      funext t
      exact (hleft _).symm
    rw [hγeq, riemannianCurveSpeed_comp g
      (((hr₁ _ (heU (mem_range_self _))).contMDiffAt
        (hU.mem_nhds (heU (mem_range_self _)))).mdifferentiableAt one_ne_zero)
      ((regularLoop_embedded_contDiff e he₁ (Γ k)).differentiable one_ne_zero t)]
    rfl
  · obtain ⟨B, hB⟩ := (isCompact_range s.continuous).isBounded.exists_norm_le
    refine ⟨⟨max B 0, le_max_right _ _⟩, fun p => ?_⟩
    have h := hB (s p) (mem_range_self p)
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ s p from Real.sqrt_nonneg _)] at h
    exact h.trans (le_max_left _ _)



theorem exists_regular_family_speed_length_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ) :
    ∃ C : ℝ≥0,
      (∀ k t, riemannianCurveSpeed g (fun t : ℝ => (Γ k).val (t : loopCircle)) t ≤ C) ∧
      (∀ k, riemannianCurveELength g (fun t : ℝ => (Γ k).val (t : loopCircle)) 0 1 ≤ (C : ℝ≥0∞)) := by
  obtain ⟨s, hs, C, hC⟩ := exists_regular_family_continuous_speed g e he hemb hi Γ hΓ
  have hbound (k : K) (t : ℝ) :
      riemannianCurveSpeed g (fun t : ℝ => (Γ k).val (t : loopCircle)) t ≤ C := by
    rw [← hs k t]
    exact hC _
  refine ⟨C, hbound, fun k => ?_⟩
  simpa only [sub_zero, ENNReal.ofReal_one, mul_one] using
    riemannianCurveELength_le g (a := 0) (b := 1) (fun t _ => hbound k t)

end DifferentialGeometry.Topology
