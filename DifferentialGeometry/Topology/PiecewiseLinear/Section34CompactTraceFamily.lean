/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_finite_labelled_compact_trace_circles
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) :
    ∃ (ι : Type) (_ : Finite ι) (label : ι → Section34CompactSimplexIndex K 3) (J : ι → Set E3),
      (∀ i, IsPLSphere 1 (J i) ∧ J i ⊆ fblBd (label i) ∩
        frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      ∀ s, fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) =
        ⋃ i ∈ {i | label i = s}, J i := by
  classical
  have := finite_section34CompactSimplexIndex hcut.2.1 3
  have hlocal : ∀ s : Section34CompactSimplexIndex K 3,
      ∃ (n : ℕ) (F : Fin n → Set E3), (∀ i, IsPLSphere 1 (F i)) ∧
        (Pairwise fun i j => Disjoint (F i) (F j)) ∧
        fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) = ⋃ i, F i := by
    intro s
    obtain ⟨ι, hι, F, hF, hdis, htrace, -⟩ :=
      exists_finite_trace_circles_of_crossings hcut hf₁ hinv s
    have : Finite ι := hι
    let _ := Fintype.ofFinite ι
    let e := Fintype.equivFin ι
    have hU : (⋃ i : Fin (Fintype.card ι), F (e.symm i)) = ⋃ i, F i :=
      e.symm.surjective.iUnion_comp F
    exact ⟨Fintype.card ι, fun i => F (e.symm i), fun i => hF _,
      fun i j hij => hdis (fun heq => hij (e.symm.injective heq)), htrace.trans hU.symm⟩
  choose r F hF hdis htrace using hlocal
  let I := Σ s : Section34CompactSimplexIndex K 3, Fin (r s)
  let label : I → Section34CompactSimplexIndex K 3 := Sigma.fst
  let J : I → Set E3 := fun i => F i.1 i.2
  have hdata : ∀ i, IsPLSphere 1 (J i) ∧ J i ⊆ fblBd (label i) ∩
      frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    intro i
    exact ⟨hF i.1 i.2, fun x hx => (htrace i.1).symm.subset (mem_iUnion.mpr ⟨i.2, hx⟩)⟩
  refine ⟨I, inferInstance, label, J, hdata, ?_, ?_⟩
  · rintro ⟨s, i⟩ ⟨t, j⟩ hne
    by_cases hst : s = t
    · subst t
      exact hdis s (fun hij => hne (by cases hij; rfl))
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact ((hdata ⟨s, i⟩).2 hxi).2.2
        (hinv.2.2.2.1 s t hst
          ⟨(hinv.1 s).boundary_subset ((hdata ⟨s, i⟩).2 hxi).1,
            (hinv.1 t).boundary_subset ((hdata ⟨t, j⟩).2 hxj).1⟩)
  · intro s
    rw [htrace]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨⟨s, i⟩, rfl, hxi⟩
    · intro hx
      obtain ⟨⟨t, i⟩, ht, hxi⟩ := mem_iUnion₂.mp hx
      change t = s at ht
      subst t
      exact mem_iUnion.mpr ⟨i, hxi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
