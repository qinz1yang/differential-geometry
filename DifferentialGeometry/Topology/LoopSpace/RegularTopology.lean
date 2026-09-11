import DifferentialGeometry.Topology.LoopSpace.Regular
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families









noncomputable section

open Set Function ContinuousMap Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]



theorem continuous_regularLoopTopology_change (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (a : M → G) (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) 1 a) :
    Continuous[regularLoopTopology e (he.of_le (by exact_mod_cast le_top)),
      regularLoopTopology a ha] id := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨hv, hd⟩ := (continuous_regularLoop_iff e he₁ id).mp continuous_id
  have hreal : Continuous (fun p : regularLoop E M × ℝ => e (p.1.val (p.2 : loopCircle))) :=
    hv.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  have har : ContDiffOn ℝ 1 (a ∘ r) U :=
    (ha.comp_contMDiffOn (hr.of_le (by exact_mod_cast le_top))).contDiffOn
  have heq (γ : regularLoop E M) (θ : loopCircle) :
      a (γ.val θ) = (a ∘ r) (e (γ.val θ)) := by rw [comp_apply, hleft]
  apply (continuous_regularLoop_iff a ha id).mpr
  constructor
  · simp only [id_eq]
    simp_rw [heq]
    exact har.continuousOn.comp_continuous hv (fun p => heU (mem_range_self _))
  · simp only [id_eq]
    simp_rw [heq]
    exact DifferentialGeometry.Analysis.continuous_deriv_family_comp hU har
      (fun γ => (regularLoop_embedded_contDiff e he₁ γ).differentiable one_ne_zero)
      hreal hd (fun p => heU (mem_range_self _))



theorem regularLoopTopology_eq [FiniteDimensional ℝ G]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (a : M → G) (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ a)
    (hamb : _root_.Topology.IsEmbedding a)
    (hai : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) a p)) :
    regularLoopTopology e (he.of_le (by exact_mod_cast le_top)) =
      regularLoopTopology a (ha.of_le (by exact_mod_cast le_top)) := by
  apply le_antisymm
  · exact continuous_id_iff_le.mp
      (continuous_regularLoopTopology_change e he hemb hi a (ha.of_le (by exact_mod_cast le_top)))
  · exact continuous_id_iff_le.mp
      (continuous_regularLoopTopology_change a ha hamb hai e (he.of_le (by exact_mod_cast le_top)))

end DifferentialGeometry.Topology
