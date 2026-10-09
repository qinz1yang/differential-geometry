/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.TorusTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_positive_finite_compact_trace_circles
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3) :
    ∃ (n : ℕ) (J : Fin n → Set E3), 0 < n ∧ (∀ i, IsPLSphere 1 (J i)) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) = ⋃ i, J i ∧
      fblBd s ∩ frontier
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) = ⋃ i, J i ∧
      CarriesFirstHomologyOnto (⋃ i, J i)
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∧
      ∃ i, IsPreconnected
          (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) \ J i) ∧
        CarriesFirstHomologyOnto (J i)
          (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  classical
  obtain ⟨-, hf₁, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨ι, hι, J, hJ, hdisj, hJN, hJT⟩ :=
    exists_finite_trace_circles_of_crossings hcut hf₁ hinv s
  let T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  have hJΘ : ∀ i, J i ⊆ frontier T := by
    intro i x hx
    exact (hJT.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)).2
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  obtain ⟨-, -, -, -, -, -, hcarry, -⟩ := id hinv
  have hcarryJ : CarriesFirstHomologyOnto (⋃ i, J i) T := by
    have hc := hcarry s
    change CarriesFirstHomologyOnto (fblBd s ∩ frontier T) T at hc
    rwa [hJT] at hc
  obtain ⟨k, hk, hkc⟩ := exists_surjective_trace_circle hT hJ hJΘ hdisj hcarryJ
  let _ := Fintype.ofFinite ι
  have : Nonempty ι := ⟨k⟩
  let e := Fintype.equivFin ι
  have hU : (⋃ i : Fin (Fintype.card ι), J (e.symm i)) = ⋃ i, J i :=
    e.symm.surjective.iUnion_comp J
  refine ⟨Fintype.card ι, fun i => J (e.symm i), Fintype.card_pos, fun i => hJ _,
    fun i j hij => hdisj (fun heq => hij (e.symm.injective heq)),
    hJN.trans hU.symm, hJT.trans hU.symm, ?_, e k, ?_, ?_⟩
  · rwa [hU]
  · simpa only [e.symm_apply_apply] using hk
  · simpa only [e.symm_apply_apply] using hkc

end DifferentialGeometry.Topology.PiecewiseLinear
