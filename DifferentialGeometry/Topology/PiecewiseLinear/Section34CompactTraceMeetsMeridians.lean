/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCircleSurjectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceLongitude

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactFaceBallInvariants.trace_circle_inter_splitDiskBoundary_nonempty
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
    (e : Section34CompactEdgeIndex K K') (he : Section34Incident e.1 s.1) :
    (J ∩ section34CompactSplitDiskImage srcBd f₁ e).Nonempty := by
  obtain ⟨M, Q, f, hf, p, hJΘ, eJ, eQ, -, hQ, -, hmarked, honto, -⟩ :=
    hinv.exists_primitive_marked_meridian_coordinates_of_no_operation
      hcut hgraph hnc hnb s hJ hJT
  let φ := (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
  let ρ := ContinuousMap.snd.comp ((φ.symm : C(_, M × Q)).comp
    (⟨inclusion hJΘ, continuous_inclusion hJΘ⟩ : C(J, _)))
  obtain ⟨a, ha⟩ := hJ.nonempty
  have hρ : Function.Surjective ρ :=
    hQ.surjective_of_fundamentalGroup_map_surjective ρ ⟨a, ha⟩ (honto ⟨a, ha⟩)
  obtain ⟨x, hx⟩ := hρ (p ⟨e, he⟩)
  refine ⟨x, x.property, ?_⟩
  rw [hmarked ⟨e, he⟩]
  let z := (⟨(x : E3), hJΘ x.property⟩ : frontier
    (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
  have hx' : (φ.symm z).2 = p ⟨e, he⟩ := hx
  refine ⟨((φ.symm z).1, p ⟨e, he⟩), ⟨(φ.symm z).1.property, rfl⟩, ?_⟩
  change (φ ((φ.symm z).1, p ⟨e, he⟩) : E3) = (x : E3)
  rw [← hx', Prod.mk.eta, φ.apply_symm_apply]

end DifferentialGeometry.Topology.PiecewiseLinear
