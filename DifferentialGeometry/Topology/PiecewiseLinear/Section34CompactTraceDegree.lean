/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceNonseparating
import DifferentialGeometry.Topology.PiecewiseLinear.TorusTracePrimitiveHomology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

namespace Section34CompactFaceBallInvariants

theorem trace_circle_carriesFirstHomologyOnto_of_no_operation
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) :
    CarriesFirstHomologyOnto J
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  have hnonsep :=
    hinv.trace_circle_nonseparating_of_subset_of_no_operation hcut hgraph hnc hnb s hJ hJT
  obtain ⟨n, F, -, hF, hdis, hFN, hFΘ, hcarry, -⟩ :=
    exists_positive_finite_compact_trace_circles hcut hgraph hinv s
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hdis (fun hij => hne (congrArg F hij))
  have hJrange : J ∈ range F :=
    (setOf_isPLSphere_one_subset_sUnion_eq (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact hF i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJT.trans hFN.subset⟩
  obtain ⟨i, rfl⟩ := hJrange
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  have hFsub : ∀ k, F k ⊆
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
    intro k x hx
    exact (hFΘ.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)).2
  exact carriesFirstHomologyOnto_trace_circle_of_isPreconnected
    hT hF hFsub hdis hcarry i hnonsep

theorem trace_circle_exists_primitive_homology_coordinates_of_no_operation
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) :
    ∃ (hsub : J ⊆ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)
      (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
      (eT : integralSingularHomology 1
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ≃ₗ[ℤ] ℤ),
      eT (integralSingularHomologyMap 1
          (⟨inclusion hsub, continuous_inclusion hsub⟩ :
            C(J, section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
          (eJ.symm 1)) = 1 ∨
        eT (integralSingularHomologyMap 1
          (⟨inclusion hsub, continuous_inclusion hsub⟩ :
            C(J, section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
          (eJ.symm 1)) = -1 := by
  have hcarry :=
    hinv.trace_circle_carriesFirstHomologyOnto_of_no_operation hcut hgraph hnc hnb s hJ hJT
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  obtain ⟨eJ, eT, hdegree⟩ := hJ.exists_primitive_homology_coordinates hT.1 hcarry
  exact ⟨hcarry.1, eJ, eT, hdegree⟩

end Section34CompactFaceBallInvariants

end DifferentialGeometry.Topology.PiecewiseLinear
