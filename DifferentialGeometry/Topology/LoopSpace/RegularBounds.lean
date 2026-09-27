import DifferentialGeometry.Topology.LoopSpace.RegularTopology
import DifferentialGeometry.Topology.LoopSpace.Lipschitz
import DifferentialGeometry.Geometry.Metric.CompactSourceCurves
import Mathlib.Analysis.Calculus.MeanValue



noncomputable section

open Set Function ContinuousMap Manifold Bundle DifferentialGeometry
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_regular_family_lipschitz_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ) :
    ∃ V : ℝ≥0, ∀ k θ η,
      riemannianEDistOf g ((Γ k).val θ) ((Γ k).val η) ≤ (V : ℝ≥0∞) * edist θ η := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  have hjet : Continuous (fun k => regularLoopJet e he₁ (Γ k)) := continuous_induced_rng.mp hΓ
  have hD : Continuous (fun p : K × loopCircle => regularLoopDerivative e he₁ (Γ p.1) p.2) :=
    (FreeLoop.continuous_family_iff _).mp hjet.snd
  obtain ⟨B, hB⟩ := (isCompact_range hD).isBounded.exists_norm_le
  let D : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hDbound (k : K) (t : ℝ) : ‖deriv (fun s : ℝ => e ((Γ k).val (s : loopCircle))) t‖ ≤ D :=
    (hB _ (mem_range_self (k, (t : loopCircle)))).trans (le_max_left _ _)
  have hLip (k : K) : LipschitzWith D (fun t : ℝ => e ((Γ k).val (t : loopCircle))) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((regularLoop_embedded_contDiff e he₁ (Γ k)).differentiable one_ne_zero)
    intro t
    exact_mod_cast hDbound k t
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨Cr, hCr⟩ := DifferentialGeometry.Geometry.exists_compact_source_curve_lipschitz g hU
    (hr.of_le (by exact_mod_cast le_top)) (isCompact_range he.continuous) heU
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  refine ⟨Cr * D, fun k θ η => ?_⟩
  have hLift : LipschitzWith (Cr * D) (fun t : ℝ => (Γ k).val (t : loopCircle)) := by
    intro x y
    have h := hCr D (fun t : ℝ => e ((Γ k).val (t : loopCircle)))
      (regularLoop_embedded_contDiff e he₁ (Γ k)) (hLip k) (fun t => mem_range_self _) x y
    simpa only [hleft] using! h
  exact (loop_lipschitz_of_lift (γ := (Γ k).val) hLift).edist_le_mul θ η

end DifferentialGeometry.Topology
