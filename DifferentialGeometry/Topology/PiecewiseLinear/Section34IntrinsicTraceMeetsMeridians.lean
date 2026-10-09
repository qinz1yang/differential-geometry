/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCircleSurjectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceLongitude

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem intrinsic_trace_circle_inter_splitDiskBoundary_nonempty
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hJ : IsPLSphere 1 J) (hJΘ : J ⊆ frontier P)
    (hcarry : CarriesFirstHomologyOnto (u '' J)
      (section34FaceTorus (section34VertexBallImage src f₁) s))
    (e : Section34EdgeIndex 𝒦 𝒦') (he : Section34Incident e.1 s.1) :
    ((u '' J) ∩ section34SplitDiskImage srcBd f₁ e).Nonempty := by
  obtain ⟨M, Q, f, hf, p, eJ, eQ, -, hQ, -, hmarked, honto, -⟩ :=
    exists_primitive_intrinsic_marked_meridian_coordinates hcut hf₁ s hP hu hUP hJ hJΘ hcarry
  let φ := (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
  let ρ := ContinuousMap.snd.comp ((φ.symm : C(_, M × Q)).comp
    (⟨inclusion hJΘ, continuous_inclusion hJΘ⟩ : C(J, _)))
  obtain ⟨a, ha⟩ := hJ.nonempty
  have hρ : Function.Surjective ρ :=
    hQ.surjective_of_fundamentalGroup_map_surjective ρ ⟨a, ha⟩ (honto ⟨a, ha⟩)
  obtain ⟨x, hx⟩ := hρ (p ⟨e, he⟩)
  have hxg : (x : E3) ∈ Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e := by
    rw [hmarked ⟨e, he⟩]
    let z := (⟨(x : E3), hJΘ x.property⟩ : frontier P)
    have hx' : (φ.symm z).2 = p ⟨e, he⟩ := hx
    refine ⟨((φ.symm z).1, p ⟨e, he⟩), ⟨(φ.symm z).1.property, rfl⟩, ?_⟩
    change (φ ((φ.symm z).1, p ⟨e, he⟩) : E3) = (x : E3)
    rw [← hx', Prod.mk.eta, φ.apply_symm_apply]
  obtain ⟨y, hy, hyx⟩ := hxg
  have hyP : y ∈ u '' P := by
    rw [hUP]
    exact hcut.splitDiskImage_subset_faceTorus hf₁ s e he
      ((hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset hy)
  refine ⟨u x, mem_image_of_mem u x.property, ?_⟩
  rw [← hyx, hu.injOn.bijOn_image.invOn_invFunOn.2 hyP]
  exact hy

end DifferentialGeometry.Topology.PiecewiseLinear
