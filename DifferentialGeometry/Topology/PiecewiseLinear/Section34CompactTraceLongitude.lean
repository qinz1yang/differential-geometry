/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMeridianSystem
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceDegree
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridianLongitude

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

namespace Section34CompactFaceBallInvariants

theorem exists_primitive_marked_meridian_coordinates_of_no_operation
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
    ∃ (M Q : Set E3) (f : E3 × E3 → E3)
      (hf : IsPLHomeomorphOn f (M ×ˢ Q)
        (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)))
      (p : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1} → Q)
      (hJΘ : J ⊆ frontier
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
      (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
      (eQ : integralSingularHomology 1 Q ≃ₗ[ℤ] ℤ),
      IsPLSphere 1 M ∧ IsPLSphere 1 Q ∧ Function.Injective p ∧
        (∀ e, section34CompactSplitDiskImage srcBd f₁ e.1 =
          f '' (M ×ˢ {(p e : E3)})) ∧
        let φ := (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
        let ρ := ContinuousMap.snd.comp ((φ.symm : C(_, M × Q)).comp
          (⟨inclusion hJΘ, continuous_inclusion hJΘ⟩ : C(J, _)))
        (∀ x : J, Function.Surjective (FundamentalGroup.map ρ x)) ∧
          (eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = 1 ∨
            eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = -1) := by
  obtain ⟨M, Q, f, p, hM, hQ, hf, hp, hpinj, hmarked, hdisks⟩ :=
    split_disks_form_marked_meridian_system hcut hgraph s
  let T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  have hJΘ : J ⊆ frontier T := by
    intro x hx
    exact ((hinv.inter_frontier_faceTorus_eq hcut hgraph.2.1 s).symm.subset (hJT hx)).2
  let φ : (M × Q) ≃ₜ frontier T :=
    (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
  let p' : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1} → Q :=
    fun e => ⟨p e, hp e⟩
  have hp'inj : Function.Injective p' := by
    intro a b hab
    exact hpinj (congrArg Subtype.val hab)
  obtain ⟨n, v, -, hv, -⟩ := exists_cycle_order_compact_face_vertex_balls hcut hgraph.2.1 s
  have hv0 := (hv (v 0)).mpr ⟨0, rfl⟩
  obtain ⟨e, _, _, he, _, _⟩ :=
    exists_section34CompactEdgeIndex_pair_of_incident hcut.2.2.2.2.1 hcut.2.2.1 s (v 0) hv0
  let i : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1} := ⟨e, he⟩
  let D := section34CompactSplitDiskImage src f₁ e
  have hcell := hcut.isPLCellOn_splitDiskImage hgraph.2.1 e
  obtain ⟨r, hr, -⟩ := hcell.exists_isPLHomeomorphOn_stdSimplex
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hDT : D ⊆ T := (hdisks i).1
  have hfiber : ∀ m : M, (φ (m, p' i) : E3) ∈ D := by
    intro m
    apply hcell.boundary_subset
    rw [hmarked i]
    exact ⟨((m : E3), p i), ⟨m.property, rfl⟩, rfl⟩
  have hcarry :=
    hinv.trace_circle_carriesFirstHomologyOnto_of_no_operation hcut hgraph hnc hnb s hJ hJT
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  obtain ⟨eJ, eQ, hdegree⟩ := exists_primitive_longitude_coordinates_of_meridian_disk
    hT.1 hJ hQ φ hJΘ hcarry hD hDT (p' i) hfiber
  refine ⟨M, Q, f, hf, p', hJΘ, eJ, eQ, hM, hQ, hp'inj, hmarked, ?_⟩
  exact ⟨fun x => surjective_longitude_fundamentalGroup_of_meridian_disk
    hT.1 hJ hQ φ hJΘ hcarry hD hDT (p' i) hfiber x, hdegree⟩

end Section34CompactFaceBallInvariants

end DifferentialGeometry.Topology.PiecewiseLinear
