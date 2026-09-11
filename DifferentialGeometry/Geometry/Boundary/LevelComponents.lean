import DifferentialGeometry.Geometry.Boundary.Metric.Induced
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import Mathlib.Geometry.Manifold.ContMDiff.Basic

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem isClopen_boundary_level_of_two_values {u : M → ℝ} {a b : ℝ}
    (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    IsClopen {x : BoundaryManifold I M | u x.1 = a} := by
  have hc : Continuous (fun x : BoundaryManifold I M ↦ u x.1) := hu.comp continuous_subtype_val
  have heq : {x : BoundaryManifold I M | u x.1 = a}ᶜ =
      {x : BoundaryManifold I M | u x.1 = b} := by
    ext x
    change u x.1 ≠ a ↔ u x.1 = b
    constructor
    · intro hx
      exact (hboundary x.1 x.2).resolve_left hx
    · intro hx hxa
      exact hab (hxa.symm.trans hx)
  refine ⟨isClosed_eq hc continuous_const, ?_⟩
  have hh : IsClosed {x : BoundaryManifold I M | u x.1 = b} := isClosed_eq hc continuous_const
  rw [← heq] at hh
  exact isClosed_compl_iff.mp hh

def boundaryLevel (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    TopologicalSpace.Opens (BoundaryManifold I M) :=
  ⟨{x | u x.1 = a}, (isClopen_boundary_level_of_two_values hab hu hboundary).isOpen⟩

variable [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem boundaryLevel_isManifold (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    IsManifold hI.boundaryI ∞ (boundaryLevel u a b hab hu hboundary) := inferInstance

theorem contMDiff_boundaryLevelInclusion (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    ContMDiff hI.boundaryI I ∞
      (fun x : boundaryLevel u a b hab hu hboundary ↦ x.1.1) :=
  boundaryInclusion_contMDiff.comp contMDiff_subtype_val

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_boundaryLevelInclusion (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (x : boundaryLevel u a b hab hu hboundary) :
    mfderiv hI.boundaryI I (fun y : boundaryLevel u a b hab hu hboundary ↦ y.1.1) x =
      boundaryInclusionMfderiv x.1 := by
  change mfderiv hI.boundaryI I (boundaryInclusion I M ∘ Subtype.val) x = _
  rw [mfderiv_comp x (boundaryInclusion_contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)), DifferentialGeometry.mfderiv_subtype_val]
  rfl

theorem injective_mfderiv_boundaryLevelInclusion (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (x : boundaryLevel u a b hab hu hboundary) :
    Injective (mfderiv hI.boundaryI I
      (fun y : boundaryLevel u a b hab hu hboundary ↦ y.1.1) x) := by
  rw [mfderiv_boundaryLevelInclusion]
  exact dincl_injective x.1

omit hI in
theorem boundaryLevel_compactSpace [CompactSpace M]
    (u : M → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    CompactSpace (boundaryLevel u a b hab hu hboundary) := by
  let : CompactSpace (BoundaryManifold I M) :=
    isCompact_iff_compactSpace.mp ((I.isClosed_boundary (M := M) (n := ∞) (by simp)).isCompact)
  exact isCompact_iff_compactSpace.mp
    (isClopen_boundary_level_of_two_values hab hu hboundary).isClosed.isCompact

omit hI [IsManifold I ∞ M] in
theorem range_boundaryLevelInclusion_lower [CompactSpace M]
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : Continuous u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    range (fun x : boundaryLevel u a b hab.ne hu hboundary ↦ x.1.1) = u ⁻¹' {a} := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact x.2
  · intro x hx
    have hmin : IsLocalMin u x := Eventually.of_forall (fun y ↦ by
      have hh := (range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self y)).1
      simpa only [show u x = a from hx] using hh)
    exact ⟨⟨⟨x, isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero hmin (hreg x)⟩, hx⟩, rfl⟩

omit hI [IsManifold I ∞ M] in
theorem range_boundaryLevelInclusion_upper [CompactSpace M]
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : Continuous u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    range (fun x : boundaryLevel u b a hab.ne.symm hu (fun x hx ↦ (hboundary x hx).symm) ↦ x.1.1) =
      u ⁻¹' {b} := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact x.2
  · intro x hx
    have hmax : IsLocalMax u x := Eventually.of_forall (fun y ↦ by
      have hh := (range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self y)).2
      simpa only [show u x = b from hx] using hh)
    exact ⟨⟨⟨x, isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero hmax (hreg x)⟩, hx⟩, rfl⟩

end DifferentialGeometry.Geometry.Boundary
