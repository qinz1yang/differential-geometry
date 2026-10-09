/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactRimCoreBuffer
import DifferentialGeometry.Topology.OpenEmbeddingFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem exists_compactRimNeighborhoods
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space) {V : Set E3} (hV : IsOpen V)
    (hMV : M.space ⊆ V) {h : E3 → E3} (hh : ContinuousOn h V) (hinj : InjOn h V) :
    let L := restrict K (section34CompactGraphSkeleton K)
    ∃ P : Section34CompactSimplexIndex K 3 → Set E3,
      (∀ s, P s ⊆ interior M.space) ∧
      (∀ s, (⋃ v ∈ (s.1 : Set E3), (graphDualCell M L v).space) ⊆ interior (P s)) ∧
      ∃ Φ : ∀ s, (Metric.closedBall (0 : E2) 1 × Metric.sphere (0 : E2) 1) ≃ₜ P s,
        (∀ s, section34CompactSimplexRim s.1 =
          Subtype.val '' (Φ s '' {q | (q.1 : E2) = 0})) ∧
        ∃ W : E3 → Set E3, (∀ v, IsOpen (W v)) ∧
          (∀ v ∈ K.vertices, h '' (graphDualCell M L v).space ⊆ W v) ∧
          ∀ (s : Section34CompactSimplexIndex K 3) v, v ∈ s.1 →
            W v ⊆ interior (h '' P s) := by
  classical
  let : DecidableEq E3 := Classical.decEq E3
  dsimp only
  let L := restrict K (section34CompactGraphSkeleton K)
  let _ : Finite (Section34CompactSimplexIndex K 3) :=
    finite_section34CompactSimplexIndex ((Set.toFinite M.faces).subset hKM) 3
  choose P hPM hNP Φ hΦ using fun s => exists_compactRimCoreBuffer hM hKM hKint s
  have hPV (s : Section34CompactSimplexIndex K 3) : P s ⊆ V :=
    (hPM s).trans (interior_subset.trans hMV)
  let W (v : E3) := ⋂ (s : Section34CompactSimplexIndex K 3) (_ : v ∈ s.1),
    interior (h '' P s)
  refine ⟨P, hPM, hNP, Φ, hΦ, W, fun v => isOpen_iInter_of_finite fun s =>
    isOpen_iInter_of_finite fun _ => isOpen_interior, ?_, ?_⟩
  · intro v _
    refine subset_iInter fun s => subset_iInter fun hvs => ?_
    rw [interior_image_eq_image_interior hV hh hinj (hPV s)]
    exact image_mono fun x hx => hNP s (mem_iUnion₂.mpr ⟨v, hvs, hx⟩)
  · intro s v hvs
    exact iInter_subset_of_subset s (iInter_subset_of_subset hvs subset_rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
