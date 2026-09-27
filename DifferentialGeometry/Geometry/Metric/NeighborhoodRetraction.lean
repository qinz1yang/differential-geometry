import DifferentialGeometry.Geometry.Metric.LocalCollapse
import DifferentialGeometry.Analysis.Calculus.Retraction.FiniteCover
import Mathlib.Geometry.Manifold.WhitneyEmbedding










noncomputable section

open Set Filter Function Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

section Boundaryless

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [Nonempty M]



theorem exists_smooth_neighborhood_retraction {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv I 𝓘(ℝ, F) e p)) :
    ∃ (r : F → M) (U : Set F), IsOpen U ∧ range e ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧ ∀ p, r (e p) = p := by
  classical
  choose Φ V hΦ hfix hV hpV hmap using
    (fun p => exists_smooth_local_collapse he hemb p (hi p))
  have hcover : range e ⊆ ⋃ p, V p := by
    rintro _ ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, hpV p⟩
  have hS : IsCompact (range e) := isCompact_range he.continuous
  obtain ⟨R, U, hR, hU, hSU, hRU, hRfix⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_of_local hS Φ V hΦ
      (fun i q ⟨p, hp⟩ => hp ▸ hfix i p) hV hmap hcover
  let r : F → M := fun z => if h : R z ∈ range e then Classical.choose h else Classical.arbitrary M
  have her (z : F) (hz : z ∈ U) : e (r z) = R z := by
    dsimp only [r]
    rw [dif_pos (hRU hz)]
    exact Classical.choose_spec (hRU hz)
  have hleft (p : M) : r (e p) = p := hemb.injective
    ((her (e p) (hSU (mem_range_self p))).trans (hRfix (e p) (mem_range_self p)))
  refine ⟨r, U, hU, hSU, ?_, hleft⟩
  intro z hz
  obtain ⟨r₀, W, hW, hpW, hr₀, hleft₀⟩ :=
    exists_local_retraction_of_embedding he hemb (r z) (hi (r z))
  have hRz : R z ∈ W := by rwa [her z hz] at hpW
  have hloc : r =ᶠ[𝓝 z] (r₀ ∘ R) := by
    filter_upwards [hU.mem_nhds hz, hR.continuous.continuousAt (hW.mem_nhds hRz)] with y hy hRy
    dsimp only [Function.comp_apply]
    rw [← her y hy]
    exact (hleft₀ (r y) (by rwa [her y hy])).symm
  have hsm : ContMDiffAt 𝓘(ℝ, F) I ∞ (r₀ ∘ R) z :=
    ((hr₀ (R z) hRz).contMDiffAt (hW.mem_nhds hRz)).comp z hR.contMDiff.contMDiffAt
  exact (hsm.congr_of_eventuallyEq hloc).contMDiffWithinAt

end Boundaryless

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
theorem exists_compact_smooth_embedding [T2Space M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      _root_.Topology.IsClosedEmbedding e ∧
      ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p) :=
  exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)



theorem exists_compact_embedding_and_retraction [T2Space M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n))
      (r : EuclideanSpace ℝ (Fin n) → M) (U : Set (EuclideanSpace ℝ (Fin n))),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      _root_.Topology.IsClosedEmbedding e ∧
      (∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p)) ∧
      IsOpen U ∧ range e ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ r U ∧
      ∀ p, r (e p) = p := by
  obtain ⟨n, e, he, hemb, hi⟩ := exists_compact_smooth_embedding (E := E) (M := M)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ := exists_smooth_neighborhood_retraction he hemb.isEmbedding hi
  exact ⟨n, e, r, U, he, hemb, hi, hU, heU, hr, hleft⟩

end DifferentialGeometry.Geometry
