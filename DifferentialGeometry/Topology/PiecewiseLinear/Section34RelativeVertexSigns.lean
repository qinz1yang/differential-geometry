/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellRelativeOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexIncidentEdge

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_relative_vertex_signs [FiniteDimensional ℝ Ea]
    {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
    {Sd : Section34SimplexIndex 𝒦 3 → Set E3}
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hsep : ∀ w w', w ≠ w' →
      Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w'))
    (hDvsub : ∀ w, Dv w ⊆ G w '' Cp w)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦))
    {R : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
    (hR : ∀ w, IsPLHomeomorphInto 3 (R w) (src (.vertexBall w)))
    (hRim : ∀ w, R w '' src (.vertexBall w) = Dv w) :
    ∃ (H F : Section34VertexIndex 𝒦 𝒦' → OpenPartialHomeomorph M₁ M₂)
      (σ : Section34VertexIndex 𝒦 𝒦' → ZMod 2),
      (∀ w, (H w).source = interior (src (.vertexBall w))) ∧
      (∀ w, (F w).source = interior (src (.vertexBall w))) ∧
      (∀ w, (H w).target = h '' interior (src (.vertexBall w))) ∧
      (∀ w, (F w).target = R w '' interior (src (.vertexBall w))) ∧
      (∀ w x, H w x = h x) ∧ (∀ w x, F w x = R w x) ∧
      ∀ w (c : OpenPartialHomeomorph M₂ E3), Q w ⊆ c.source →
        ∀ x (hxH : x ∈ (H w).source) (hxF : x ∈ (F w).source)
          (hxc : H w x ∈ c.source) (hxfc : F w x ∈ c.source),
          chartOrientationParity (H w ≫ₕ c) (F w ≫ₕ c) x ⟨hxH, hxc⟩ ⟨hxF, hxfc⟩ = σ w := by
  obtain ⟨-, -, -, hcell, -, -, -, -, hcover, -⟩ := id hframe
  have hsrcU (w : Section34VertexIndex 𝒦 𝒦') : src (.vertexBall w) ⊆ U :=
    (subset_iUnion src (.vertexBall w)).trans hcover.subset
  have hhcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhinj : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show U.domRestrict h ⟨x, hx⟩ =
      U.domRestrict h ⟨y, hy⟩ from hxy))
  have hcarrier := section34_vertex_carrier_connected
    hU hh hframe hprep hsep hDvsub hDv hDvQ hQlf hDnbhd
  choose b hb hbQ using exists_section34_vertex_chart hframe htor
  have hHA (w : Section34VertexIndex 𝒦 𝒦') :
      MapsTo h (interior (src (.vertexBall w))) (h '' src (.vertexBall w) ∪ Dv w) :=
    fun x hx => Or.inl ⟨x, interior_subset hx, rfl⟩
  have hRA (w : Section34VertexIndex 𝒦 𝒦') :
      MapsTo (R w) (interior (src (.vertexBall w))) (h '' src (.vertexBall w) ∪ Dv w) := by
    intro x hx
    apply Or.inr
    rw [← hRim w]
    exact ⟨x, interior_subset hx, rfl⟩
  choose H F σ hHs hFs hHt hFt hH hF hsign using fun w =>
    exists_relative_orientation_sign_of_cell (hcell (.vertexBall w))
      (hhcont.mono (hsrcU w)) (hhinj.mono (hsrcU w)) (hR w).continuousOn (hR w).injOn
      (hcarrier w).1.isPreconnected (hHA w) (hRA w) (b w) ((hcarrier w).2.trans (hbQ w))
  exact ⟨H, F, σ, hHs, hFs, hHt, hFt, hH, hF,
    fun w c hc => hsign w c ((hcarrier w).2.trans hc)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
