import DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]

theorem exists_smooth_neighborhood_retraction_prod_of_compact :
    ∃ (n : ℕ) (e : M × F → EuclideanSpace ℝ (Fin n))
      (r : EuclideanSpace ℝ (Fin n) → M × F) (U : Set (EuclideanSpace ℝ (Fin n))),
      ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      IsOpen U ∧ range e ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (I.prod 𝓘(ℝ, F)) ∞ r U ∧
      ∀ p, r (e p) = p := by
  obtain ⟨n, e₀, he₀, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨r₀, U₀, hU₀, heU₀, hr₀, hleft⟩ :=
    Geometry.exists_smooth_neighborhood_retraction_of_isCompact
      he₀ hemb.isEmbedding hi (isCompact_univ : IsCompact (univ : Set M))
  have heU : range e₀ ⊆ U₀ := by simpa only [image_univ] using heU₀
  let V := EuclideanSpace ℝ (Fin n) × F
  let N := Module.finrank ℝ V
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e : M × F → EuclideanSpace ℝ (Fin N) := fun p => L (e₀ p.1, p.2)
  let r : EuclideanSpace ℝ (Fin N) → M × F := fun q =>
    (r₀ (L.symm q).1, (L.symm q).2)
  let U : Set (EuclideanSpace ℝ (Fin N)) :=
    (fun q => (L.symm q).1) ⁻¹' U₀
  have hL : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 𝓘(ℝ, V) ∞ L.symm :=
    L.symm.toDiffeomorph.contMDiff
  have hfirst : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun q => (L.symm q).1) :=
    contDiff_fst.contMDiff.comp hL
  have hsecond : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      𝓘(ℝ, F) ∞ (fun q => (L.symm q).2) :=
    contDiff_snd.contMDiff.comp hL
  refine ⟨N, e, r, U, ?_, ?_, ?_, ?_, ?_⟩
  · exact L.toDiffeomorph.contMDiff.comp
      ((he₀.comp contMDiff_fst).prodMk_space contMDiff_snd)
  · exact hU₀.preimage hfirst.continuous
  · rintro _ ⟨p, rfl⟩
    change (L.symm (L (e₀ p.1, p.2))).1 ∈ U₀
    rw [L.symm_apply_apply]
    exact heU (mem_range_self _)
  · exact (hr₀.comp hfirst.contMDiffOn (fun _ hq => hq)).prodMk hsecond.contMDiffOn
  · intro p
    change (r₀ (L.symm (L (e₀ p.1, p.2))).1,
      (L.symm (L (e₀ p.1, p.2))).2) = p
    rw [L.symm_apply_apply, hleft p.1 (heU (mem_range_self _))]

end DifferentialGeometry.Topology
