import DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem closure_image_interior_eq_closure_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] {M : Set X} [ChartedSpace H M] [IsManifold I 1 M] :
    closure ((Subtype.val : M → X) '' I.interior M) = closure M := by
  refine Subset.antisymm (closure_mono ?_) ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · have hdense : Dense (I.interior M) := ModelWithCorners.dense_interior I
    have hrange : (Subtype.val : M → X) '' univ = M := by
      rw [Set.image_univ, Subtype.range_coe]
    refine closure_minimal ?_ isClosed_closure
    calc M = (Subtype.val : M → X) '' closure (I.interior M) := by
          rw [hdense.closure_eq, hrange]
      _ ⊆ closure ((Subtype.val : M → X) '' I.interior M) :=
          image_closure_subset_closure_image continuous_subtype_val

theorem isOpen_image_interior_of_isImmersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    {f : M → N} (hf : IsImmersion I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') :
    IsOpen (f '' I.interior M) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  exact immersion_image_mem_nhds (hf.isImmersionAt x) hdim hx
    ((I.isOpen_interior (n := ∞) (by norm_num)).mem_nhds hx)

end DifferentialGeometry.Topology.Manifold
