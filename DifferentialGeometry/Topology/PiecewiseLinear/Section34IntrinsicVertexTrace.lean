/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicSeamCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U W : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {η : M₁ → ℝ} {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem Section34FaceBallInvariants.disjoint_splitDiskImage_of_circle_subset_vertexBall
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34VertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (e : Section34EdgeIndex 𝒦 𝒦') :
    Disjoint J (section34SplitDiskImage src f₁ e) := by
  apply disjoint_left.mpr
  intro x hxJ hxE
  have hxγ : x ∈ section34SplitDiskImage srcBd f₁ e := by
    by_contra hnot
    exact (hJN hxJ).2
      (hcut.splitDiskImage_sdiff_subset_interior_vertexBallImages hgraph.2.2.1 e ⟨hxE, hnot⟩)
  obtain ⟨c, -, hxc, hc⟩ := hinv.curve_crossing_trace_circle_in_chart hcut hgraph s hJ
    (subset_inter hJP hJN) e ⟨hxJ, hxγ⟩
  exact hcut.not_subset_vertexBall_of_splitDiskBoundary_crossing hgraph.2.2.1 w e c hxc hc hJV

end DifferentialGeometry.Topology.PiecewiseLinear
