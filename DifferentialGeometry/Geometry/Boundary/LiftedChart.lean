import DifferentialGeometry.Geometry.Boundary.OpenEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.DiffeomorphRestriction

noncomputable section
open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_lifted_chart_of_interior_range
    {E H W F G M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {K : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N]
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (O : TopologicalSpace.Opens N) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮K, J⟯ V) :
    ∃ U : TopologicalSpace.Opens N, ∃ hUO : U ≤ O,
      ∃ Z : TopologicalSpace.Opens W, ∃ Ψ : U ≃ₘ⟮K, I⟯ Z,
        (∀ x : O, (x : N) ∈ U ↔ (Φ x : M) ∈ interior (range ι)) ∧
        ((Z : Set W) = ι ⁻¹' ((V : Set M) ∩ interior (range ι))) ∧
        ∀ x : U, ι (Ψ x : W) = (Φ (TopologicalSpace.Opens.inclusion hUO x) : M) := by
  let R : TopologicalSpace.Opens M := ⟨(V : Set M) ∩ interior (range ι),
    V.isOpen.inter isOpen_interior⟩
  have hRV : R ≤ V := inter_subset_left
  have hRι : (R : Set M) ⊆ range ι := inter_subset_right.trans interior_subset
  obtain ⟨U, hUO, e, hU, he⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_restriction_to_open O V R Φ hRV
  let Z := TopologicalSpace.Opens.comap ⟨ι, hι.continuous⟩ R
  let d : Z ≃ₘ⟮I, J⟯ R := diffeomorphOfOpenSubsetRange ι hι hemb hinj hdim R hRι
  refine ⟨U, hUO, Z, e.trans d.symm, ?_, rfl, ?_⟩
  · intro x
    rw [hU]
    exact and_iff_right (Φ x).property
  · intro x
    change ι (d.symm (e x) : W) = _
    exact (diffeomorphOfOpenSubsetRange_symm_apply_coe ι hι hemb hinj hdim R hRι
      (e x)).trans (he x)

end DifferentialGeometry.Geometry.Boundary
