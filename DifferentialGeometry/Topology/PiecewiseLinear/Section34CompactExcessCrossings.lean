/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMeridianReturn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceLongitude
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridianReturn

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_admissible_bigon_of_excess_meridian_crossings
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
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hmore : ∃ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 ∧
      (J ∩ section34CompactSplitDiskImage srcBd f₁ e).Nontrivial) :
    ∃ t : Section34CompactSimplexIndex K 3,
      Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fblBd t := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 2
  obtain ⟨M, Q, f, hf, p, hJΘ, eJ, eQ, -, hQ, -, hmarked, honto, -⟩ :=
    hinv.exists_primitive_marked_meridian_coordinates_of_no_operation
      hcut hgraph hnc hnb s hJ hJT
  let φ := (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
  have hfiber (i : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1}) :
      range (fun m : M => (φ (m, p i) : E3)) =
        section34CompactSplitDiskImage srcBd f₁ i.1 := by
    rw [hmarked i]
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨((m : E3), (p i : E3)), ⟨m.property, rfl⟩, rfl⟩
    · rintro ⟨⟨m, q⟩, ⟨hm, hq⟩, rfl⟩
      have hq' : q = (p i : E3) := mem_singleton_iff.mp hq
      subst q
      exact ⟨⟨m, hm⟩, rfl⟩
  have hcross : ∀ i, ∀ x ∈ J ∩ range (fun m : M => (φ (m, p i) : E3)),
      HasPLCurveCrossingOnAt
        (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
        J (range (fun m : M => (φ (m, p i) : E3))) x := by
    intro i x hx
    rw [hfiber i] at hx ⊢
    exact hinv.curve_crossing_on_face_torus hcut hgraph.2.1 s hJ hJT i.1 hx
  have hmore' : ∃ i, (J ∩ range (fun m : M => (φ (m, p i) : E3))).Nontrivial := by
    obtain ⟨e, he, h⟩ := hmore
    exact ⟨⟨e, he⟩, by rwa [hfiber]⟩
  obtain ⟨i, B, η, hη, hBJ, hends, hmeet⟩ :=
    exists_returning_arc_of_primitive_longitude hJ hQ φ hJΘ p hcross honto hmore'
  rw [hfiber i] at hends
  simp_rw [hfiber] at hmeet
  exact exists_admissible_bigon_of_returning_meridian_arc hinv hcut hgraph hnc s i hη
    (hBJ.trans hJT) hends hmeet

end DifferentialGeometry.Topology.PiecewiseLinear
