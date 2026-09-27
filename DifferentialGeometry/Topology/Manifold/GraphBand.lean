import DifferentialGeometry.Topology.GraphBand
import Mathlib.Geometry.Manifold.Algebra.Structures
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Order.DenselyOrdered

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
variable {n : WithTop ℕ∞}

def graphBandDiffeomorph (a b : N → ℝ)
    (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p ≠ b p) :
    Diffeomorph (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (N × ℝ) (N × ℝ) n where
  toEquiv := (graphBandHomeomorph a b ha.continuous hb.continuous hab).toEquiv
  contMDiff_toFun := contMDiff_fst.prodMk
    ((((hb.sub ha).comp contMDiff_fst).mul contMDiff_snd).add
      (ha.comp contMDiff_fst))
  contMDiff_invFun := contMDiff_fst.prodMk
    ((contMDiff_snd.sub (ha.comp contMDiff_fst)).div₀
      ((hb.sub ha).comp contMDiff_fst)
      (fun p ↦ sub_ne_zero.mpr (hab p.1).symm))

@[simp] theorem graphBandDiffeomorph_apply (a b : N → ℝ)
    (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p ≠ b p) (p : N × ℝ) :
    graphBandDiffeomorph a b ha hb hab p =
      (p.1, a p.1 + (b p.1 - a p.1) * p.2) :=
  graphBandHomeomorph_apply a b ha.continuous hb.continuous hab p

@[simp] theorem graphBandDiffeomorph_symm_apply (a b : N → ℝ)
    (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p ≠ b p) (p : N × ℝ) :
    (graphBandDiffeomorph a b ha hb hab).symm p =
      (p.1, (p.2 - a p.1) / (b p.1 - a p.1)) := rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

theorem exists_graphBand_partialDiffeomorph [CompactSpace N] [T2Space M]
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M n)
    (a b : N → ℝ) (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p ≠ b p)
    (hband : {z : N × ℝ | z.2 ∈ uIcc (a z.1) (b z.1)} ⊆ Φ.source) :
    ∃ Ψ : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M n,
      (univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source) ∧
      (∀ z, Ψ z = Φ (z.1, a z.1 + (b z.1 - a z.1) * z.2)) ∧
      (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) =
        Φ '' {z : N × ℝ | z.2 ∈ uIcc (a z.1) (b z.1)}) ∧
      IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun p ↦ Φ (p, a p)) ∪ range (fun p ↦ Φ (p, b p)) := by
  let A := graphBandDiffeomorph a b ha hb hab
  let Ψ := A.toPartialDiffeomorph.trans Φ
  have hval (z : N × ℝ) : Ψ z = Φ (z.1, a z.1 + (b z.1 - a z.1) * z.2) := by
    change Φ (A z) = _
    rw [graphBandDiffeomorph_apply]
  have hAimage : A '' (univ ×ˢ Icc (0 : ℝ) 1) =
      {z : N × ℝ | z.2 ∈ uIcc (a z.1) (b z.1)} :=
    graphBandHomeomorph_image_closed_strip a b ha.continuous hb.continuous hab
  have himage : Ψ '' (univ ×ˢ Icc (0 : ℝ) 1) =
      Φ '' {z : N × ℝ | z.2 ∈ uIcc (a z.1) (b z.1)} := by
    rw [← hAimage, image_image]
    rfl
  have hsource : univ ×ˢ Icc (0 : ℝ) 1 ⊆ Ψ.source := by
    intro z hz
    change z ∈ (A.toPartialDiffeomorph.toOpenPartialHomeomorph.trans
      Φ.toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_univ _, ?_⟩
    change A z ∈ Φ.source
    apply hband
    rw [← hAimage]
    exact mem_image_of_mem A hz
  have hcompact : IsCompact (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (Ψ.contMDiffOn_toFun.continuousOn.mono hsource)
  refine ⟨Ψ, hsource, hval, himage, hcompact, ?_⟩
  have hfront : Ψ '' frontier (univ ×ˢ Icc (0 : ℝ) 1) =
      frontier (Ψ '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    Ψ.toOpenPartialHomeomorph.image_frontier_of_subset_source hsource
      (isClosed_univ.prod isClosed_Icc) hcompact.isClosed
  rw [← hfront, frontier_univ_prod_eq, frontier_Icc zero_le_one]
  ext y
  constructor
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, rfl⟩
    rcases ht with rfl | ht
    · exact Or.inl ⟨p, by simp [hval]⟩
    · have ht1 : t = 1 := ht
      subst t
      exact Or.inr ⟨p, by simp [hval]⟩
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨(p, 0), ⟨mem_univ _, by simp⟩, by simp [hval]⟩
    · exact ⟨(p, 1), ⟨mem_univ _, by simp⟩, by simp [hval]⟩


end DifferentialGeometry.Topology
