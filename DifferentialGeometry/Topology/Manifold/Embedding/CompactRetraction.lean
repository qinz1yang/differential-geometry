import DifferentialGeometry.Analysis.Calculus.Retraction.Compact
import DifferentialGeometry.Geometry.Metric.LocalCollapse
import DifferentialGeometry.Topology.Manifold.Embedding.CompactNeighborhood
import DifferentialGeometry.Topology.Manifold.OpenSubtype

section

noncomputable section

open Set Filter Function Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Nonempty M]

theorem exists_smooth_neighborhood_retraction_of_isCompact {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv I 𝓘(ℝ, F) e p)) {K : Set M} (hK : IsCompact K) :
    ∃ (r : F → M) (U : Set F), IsOpen U ∧ e '' K ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, F) I ∞ r U ∧ ∀ p, e p ∈ U → r (e p) = p := by
  classical
  choose Φ V hΦ hfix hV hpV hmap using
    (fun p => exists_smooth_local_collapse he hemb p (hi p))
  have hcover : e '' K ⊆ ⋃ p, V p := by
    rintro _ ⟨p, _, rfl⟩
    exact mem_iUnion.mpr ⟨p, hpV p⟩
  obtain ⟨R, U, hR, hU, hKU, hRU, hRfix⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_neighborhood_retraction_near_compact
      (hK.image he.continuous) (image_subset_range e K) Φ V hΦ
      (fun i q ⟨p, hp⟩ => hp ▸ hfix i p) hV hmap hcover
  let r : F → M := fun z => if h : R z ∈ range e then Classical.choose h else Classical.arbitrary M
  have her (z : F) (hz : z ∈ U) : e (r z) = R z := by
    dsimp only [r]
    rw [dite_eq_left (hRU hz)]
    exact Classical.choose_spec (hRU hz)
  have hleft (p : M) (hp : e p ∈ U) : r (e p) = p := hemb.injective
    ((her (e p) hp).trans (hRfix (e p) (mem_range_self p)))
  refine ⟨r, U, hU, hKU, ?_, hleft⟩
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

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter Function Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_contMDiff_embedding_retraction_near_isCompact {K : Set M}
    (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ (N : TopologicalSpace.Opens M) (n : ℕ)
      (e : M → EuclideanSpace ℝ (Fin n)) (r : EuclideanSpace ℝ (Fin n) → M)
      (U : Set (EuclideanSpace ℝ (Fin n))),
      K ⊆ N ∧ ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      HasCompactSupport e ∧ _root_.Topology.IsEmbedding (fun x : N => e x) ∧
      (∀ x ∈ N, Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) ∧
      IsOpen U ∧ e '' (N : Set M) ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U ∧
      ∀ p ∈ N, r (e p) = p := by
  obtain ⟨N, n, e, hKN, he, hsupport, hemb, hi⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_embedding_on_nhds_of_isCompact (I := I) hK
  obtain ⟨p, hp⟩ := hKne
  let : Nonempty N := ⟨⟨p, hKN hp⟩⟩
  let eN : N → EuclideanSpace ℝ (Fin n) := fun x => e x
  have heN : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ eN :=
    he.comp contMDiff_subtype_val
  have hiN (x : N) : Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) eN x) := by
    rw [DifferentialGeometry.mfderiv_restrict_open e N x]
    exact hi x x.property
  have hKNc : IsCompact ((Subtype.val : N → M) ⁻¹' K) :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKN hx⟩, rfl⟩)
  obtain ⟨rN, U, hU, hKU, hrN, hleft⟩ :=
    exists_smooth_neighborhood_retraction_of_isCompact heN hemb hiN hKNc
  let N' : TopologicalSpace.Opens M := ⟨(N : Set M) ∩ e ⁻¹' U,
    N.isOpen.inter (hU.preimage he.continuous)⟩
  have hN'N : (N' : Set M) ⊆ N := inter_subset_left
  have hKN' : K ⊆ N' := by
    intro x hx
    exact ⟨hKN hx, hKU ⟨⟨x, hKN hx⟩, hx, rfl⟩⟩
  refine ⟨N', n, e, Subtype.val ∘ rN, U, hKN', he, hsupport,
    hemb.comp (_root_.Topology.IsEmbedding.inclusion hN'N),
    (fun x hx => hi x hx.1), hU, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · exact contMDiff_subtype_val.comp_contMDiffOn hrN
  · intro x hx
    exact congrArg Subtype.val (hleft ⟨x, hx.1⟩ hx.2)

end DifferentialGeometry.Geometry

end

end
