import DifferentialGeometry.Topology.Homology.BoundaryEuler
import DifferentialGeometry.Topology.Homology.BoundaryPartition

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.Homology

private def boundarySubsetHomeomorph {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    (A : Set (BoundaryManifold (𝓡∂ (n + 1)) M)) :
    A ≃ₜ (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' A) := by
  let f : A → M := fun p => p.val.val
  have hf : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hr : range f = ((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' A := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hr)

theorem relativeEulerChar_boundary_complement
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    (K : Type) [Field K]
    (A : Set (BoundaryManifold (𝓡∂ (n + 1)) M)) (hA : IsClopen A) :
    relativeEulerChar (TopCat.of M)
        (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' A) K =
      (-1 : ℤ) ^ (n + 1) * relativeEulerChar (TopCat.of M)
        (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' Aᶜ) K := by
  let eA := boundarySubsetHomeomorph A
  let eC := boundarySubsetHomeomorph Aᶜ
  have hfA := (finiteHomologyType_iff_of_homeomorph K
    (X := TopCat.of A) (Y := TopCat.of (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' A)) eA).mp
    (finiteHomologyType_of_isClopen_boundary (𝓡∂ (n + 1)) K A hA)
  have hfC := (finiteHomologyType_iff_of_homeomorph K
    (X := TopCat.of (Aᶜ : Set _)) (Y := TopCat.of (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' Aᶜ)) eC).mp
    (finiteHomologyType_of_isClopen_boundary (𝓡∂ (n + 1)) K Aᶜ hA.compl)
  have hfM := finiteHomologyType_of_compact_manifold_withBoundary (n := n + 1) (M := M) K
  have hAχ := eulerChar_eq_of_homeomorph K
    (X := TopCat.of A) (Y := TopCat.of (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' A)) eA
  have hCχ := eulerChar_eq_of_homeomorph K
    (X := TopCat.of (Aᶜ : Set _)) (Y := TopCat.of (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' Aᶜ)) eC
  have hrelA : relativeEulerChar (TopCat.of M)
      (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' A) K =
      eulerChar K (TopCat.of M) - eulerChar K (TopCat.of A) :=
    (relativeEulerChar_eq_sub (TopCat.of M) _ K hfA hfM).trans
      (congrArg (fun z => eulerChar K (TopCat.of M) - z) hAχ.symm)
  have hrelC : relativeEulerChar (TopCat.of M)
      (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) '' Aᶜ) K =
      eulerChar K (TopCat.of M) - eulerChar K (TopCat.of (Aᶜ : Set _)) :=
    (relativeEulerChar_eq_sub (TopCat.of M) _ K hfC hfM).trans
      (congrArg (fun z => eulerChar K (TopCat.of M) - z) hCχ.symm)
  rw [hrelA, hrelC]
  have hsum := eulerChar_boundary_partition (n := n) (M := M) K A hA
  have hboundary := eulerChar_intrinsicBoundary (n := n) (M := M) K
  have htotal := hboundary.symm.trans hsum
  have hpar := eulerChar_boundary_component_parity (n := n) (M := M) K Aᶜ hA.compl
  have hsign : (-1 : ℤ) ^ (n + 1) * eulerChar K (TopCat.of (Aᶜ : Set _)) =
      -eulerChar K (TopCat.of (Aᶜ : Set _)) := by
    rw [pow_succ]
    calc
      (-1 : ℤ) ^ n * -1 * eulerChar K (TopCat.of (Aᶜ : Set _)) =
        -((-1 : ℤ) ^ n * eulerChar K (TopCat.of (Aᶜ : Set _))) := by ring
      _ = _ := congrArg Neg.neg hpar.symm
  rw [mul_sub, hsign]
  linarith

end Poincare.Homology
