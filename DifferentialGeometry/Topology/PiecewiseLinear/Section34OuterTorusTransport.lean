/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTopologicalSolidTorus.image_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {S : Set X}
    (hS : IsTopologicalSolidTorus S) (hf : IsEmbedding (S.domRestrict f)) :
    IsTopologicalSolidTorus (f '' S) := by
  obtain ⟨e⟩ := hS
  let ef := hf.toHomeomorph.trans (Homeomorph.setCongr (Set.range_domRestrict f S))
  exact ⟨ef.symm.trans e⟩

theorem IsSpine.image_of_isEmbedding {f : E3 → E3} {S J : Set E3}
    (hJ : IsSpine S J) (hf : IsEmbedding (S.domRestrict f)) :
    IsSpine (f '' S) (f '' J) := by
  obtain ⟨e, p, hp, hJ⟩ := hJ
  let ef := hf.toHomeomorph.trans (Homeomorph.setCongr (Set.range_domRestrict f S))
  refine ⟨e.trans ef, p, hp, ?_⟩
  rw [hJ]
  simp only [image_image]
  rfl

theorem IsSpine.isTopologicalSolidTorus {S J : Set E3} (hJ : IsSpine S J) :
    IsTopologicalSolidTorus S := by
  obtain ⟨e, -, -, -⟩ := hJ
  exact ⟨e.symm⟩

theorem IsSpine.subset {S J : Set E3} (hJ : IsSpine S J) : J ⊆ S := by
  obtain ⟨e, -, -, rfl⟩ := hJ
  exact Subtype.coe_image_subset S _

theorem IsSpine.nonempty {S J : Set E3} (hJ : IsSpine S J) : J.Nonempty := by
  obtain ⟨e, p, hp, rfl⟩ := hJ
  obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 2))) |>.mpr
    (zero_le_one : (0 : ℝ) ≤ 1)
  exact ⟨e (⟨p, interior_subset hp⟩, ⟨z, hz⟩),
    ⟨e (⟨p, interior_subset hp⟩, ⟨z, hz⟩), ⟨_, rfl, rfl⟩, rfl⟩⟩

theorem IsSpine.carriesFundamentalGroupOnto {S J : Set E3} (hJ : IsSpine S J) :
    CarriesFundamentalGroupOnto J S :=
  ⟨hJ.subset, fun hJS x => (fundamentalGroup_map_inclusion_bijective_of_isSpine hJ hJS x).2⟩

theorem IsSpine.not_subset_of_isPLBall {S J D : Set E3} {d : ℕ}
    (hJ : IsSpine S J) (hD : IsPLBall d D) (hDS : D ⊆ S) : ¬ J ⊆ D := by
  intro hJD
  exact hJ.isTopologicalSolidTorus.not_carriesFundamentalGroupOnto_of_subset_isPLBall
    hD hDS hJ.nonempty hJD hJ.carriesFundamentalGroupOnto

theorem IsPLCellOn.not_subset_of_isSpine_image_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {d : ℕ} {D B A : Set M} {S : Set E3} (hD : IsPLCellOn d D B)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    (hAc : A ⊆ c.source) (hAS : c '' A ⊆ S) (hspine : IsSpine S (c '' B)) :
    ¬ D ⊆ A := by
  intro hDA
  obtain ⟨q, hq, -⟩ := hD.exists_isPLHomeomorphOn_image_chart hc (hDA.trans hAc)
  exact hspine.not_subset_of_isPLBall ⟨q, hq⟩ ((image_mono hDA).trans hAS)
    (image_mono hD.boundary_subset)

theorem section34OuterTorus_of_isSpine
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
    [MetricSpace M₂] [ChartedSpace E3 M₂]
    {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {h : M₁ → M₂}
    {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
    {Sd : Section34SimplexIndex 𝒦 3 → Set E3}
    (hchart : ∀ s : Section34SimplexIndex 𝒦 3,
      ct s ∈ (plGroupoid 3).maximalAtlas M₂ ∧
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w) ⊆
        (ct s).source)
    (hrim : ∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
      ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w)
    (hspine : ∀ s : Section34SimplexIndex 𝒦 3,
      IsSpine (Sd s) (ct s '' (h '' simplexRim 𝒦 s.1)))
    (hbuffer : ∀ s : Section34SimplexIndex 𝒦 3,
      ct s '' (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w) ⊆
        interior (Sd s)) :
    Section34OuterTorus 𝒦 𝒦' h Q ct Sd := by
  refine ⟨hchart, hrim, fun s => ⟨(hspine s).isTopologicalSolidTorus, hspine s⟩,
    hbuffer, ?_⟩
  intro s D B hD hB
  apply hD.not_subset_of_isSpine_image_chart (hchart s).1 (hchart s).2
    ((hbuffer s).trans interior_subset)
  rw [hB]
  exact hspine s

end DifferentialGeometry.Topology.PiecewiseLinear
