import DifferentialGeometry.Topology.LoopSpace.RegularTopology
import DifferentialGeometry.Geometry.Metric.SourceTangent



noncomputable section

open Set Function ContinuousMap Bundle Manifold
open DifferentialGeometry.Geometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]

set_option backward.isDefEq.respectTransparency false in


theorem exists_regular_family_tangent_velocity
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (Γ : K → regularLoop E M)
    (hΓ : Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ) :
    ∃ T : C(K × loopCircle, TangentBundle 𝓘(ℝ, E) M), ∀ k (t : ℝ),
      T (k, (t : loopCircle)) =
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => (Γ k).val (s : loopCircle))
          (TotalSpace.mk' ℝ t (1 : ℝ)) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  obtain ⟨hcA, _⟩ := (continuous_regularLoop_iff e he₁ Γ).mp hΓ
  have hjet : Continuous (fun k => regularLoopJet e he₁ (Γ k)) := continuous_induced_rng.mp hΓ
  have hD : Continuous (fun p : K × loopCircle => regularLoopDerivative e he₁ (Γ p.1) p.2) :=
    (FreeLoop.continuous_family_iff _).mp hjet.snd
  obtain ⟨r, U, hU, heU, hr, hleft⟩ := exists_smooth_neighborhood_retraction he hemb hi
  let hr₁ := hr.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let A : K × loopCircle → F × F := fun p =>
    (e ((Γ p.1).val p.2), regularLoopDerivative e he₁ (Γ p.1) p.2)
  have hA : Continuous A := hcA.prodMk hD
  let T : C(K × loopCircle, TangentBundle 𝓘(ℝ, E) M) :=
    ⟨fun p => TotalSpace.mk' E (r (A p).1)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (A p).1 (A p).2),
      (continuousOn_source_tangentMap hU hr₁).comp_continuous hA
        (fun p => ⟨heU (mem_range_self _), mem_univ _⟩)⟩
  refine ⟨T, fun k t => ?_⟩
  have hγeq : (fun s : ℝ => (Γ k).val (s : loopCircle)) =
      r ∘ (fun s : ℝ => e ((Γ k).val (s : loopCircle))) := by
    funext s
    exact (hleft _).symm
  rw [hγeq, tangent_velocity_comp
    (((hr₁ _ (heU (mem_range_self _))).contMDiffAt
      (hU.mem_nhds (heU (mem_range_self _)))).mdifferentiableAt one_ne_zero)
    ((regularLoop_embedded_contDiff e he₁ (Γ k)).differentiable one_ne_zero t)]
  rfl

end DifferentialGeometry.Topology
