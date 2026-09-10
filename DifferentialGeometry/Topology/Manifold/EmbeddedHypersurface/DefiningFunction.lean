import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.CompactDefining
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.RegularDefiningNeighborhood
import DifferentialGeometry.Topology.Manifold.OpenSubtype

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_regular_definingFunction {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e))
    (V : ∀ s, TangentSpace J (e s))
    (hV : Continuous (fun s => (⟨e s, V s⟩ : TangentBundle J M)))
    (htrans : ∀ s, V s ∉ (mfderiv I J e s).range) :
    ∃ U : TopologicalSpace.Opens M, range e ⊆ U ∧
      ∃ f : U → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ f ∧
        (∀ y, f y = 0 ↔ (y : M) ∈ range e) ∧
        IsCompact {y | f y = 0} ∧
        ∀ y, f y = 0 → mfderiv J 𝓘(ℝ, ℝ) f y ≠ 0 := by
  obtain ⟨g, hg, _, hgz, hgpos⟩ :=
    exists_smooth_function_regular_on_compact_hypersurface I J he hK V hV htrans
  have hgr (s : S) : mfderiv J 𝓘(ℝ, ℝ) g (e s) ≠ 0 := by
    intro hzero
    have hp := hgpos s
    erw [hzero] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  choose W hW hxW hzero using (fun s =>
    exists_defining_neighborhood_of_regular_vanishing I J
      (he.isImmersion.isImmersionAt s) hg hgz (hgr s))
  let U : TopologicalSpace.Opens M := ⟨⋃ s, W s, isOpen_iUnion hW⟩
  have hKU : range e ⊆ U := by
    rintro _ ⟨s, rfl⟩
    exact mem_iUnion.mpr ⟨s, hxW s⟩
  let f : U → ℝ := fun y => g y
  have hf : ContMDiff J 𝓘(ℝ, ℝ) ∞ f := hg.comp contMDiff_subtype_val
  have hfzero (y : U) : f y = 0 ↔ (y : M) ∈ range e := by
    obtain ⟨s, hs⟩ := mem_iUnion.mp y.2
    exact hzero s y hs
  have himage : (Subtype.val : U → M) '' {y | f y = 0} = range e := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hfzero z).mp hz
    · intro hy
      exact ⟨⟨y, hKU hy⟩, (hfzero ⟨y, hKU hy⟩).mpr hy, rfl⟩
  have hfK : IsCompact {y | f y = 0} :=
    Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (himage.symm ▸ hK)
  refine ⟨U, hKU, f, hf, hfzero, hfK, ?_⟩
  intro y hy hzero
  obtain ⟨s, hs⟩ := (hfzero y).mp hy
  have hh := mfderiv_comp y ((hg y.val).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := J) (U := U) (n := ∞) y).mdifferentiableAt (by simp))
  change mfderiv J 𝓘(ℝ, ℝ) f y =
    (mfderiv J 𝓘(ℝ, ℝ) g y.val).comp (mfderiv J J (Subtype.val : U → M) y) at hh
  erw [DifferentialGeometry.mfderiv_subtype_val, ContinuousLinearMap.comp_id] at hh
  have hz' : mfderiv J 𝓘(ℝ, ℝ) g y.val = 0 := hh.symm.trans hzero
  rw [← hs] at hz'
  exact hgr s hz'

end Poincare.Manifold.EmbeddedHypersurface
