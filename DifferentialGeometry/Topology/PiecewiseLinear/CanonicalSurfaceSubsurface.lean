/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentSubsurfaceEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalComponentSeamDisks

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalNullSplit.preserves_subsurface_embeddings [DecidableEq E3]
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (hY : IsCanonicalSurface Y (fun j => φ '' S j) T'' I P' a b)
    (hstep : IsCanonicalNullSplit (fun j => φ '' S j) T'' i X Y)
    (hmodel : ∀ j, HasEssentialBoundaryPLEmbeddings (X j) (T'' (2 * j + 1))) :
    ∀ j, HasEssentialBoundaryPLEmbeddings (Y j) (T'' (2 * j + 1)) := by
  let _ (j : ℤ) : Finite (X j).faces := (hX.finiteFaces j).to_subtype
  let _ (j : ℤ) : Finite (Y j).faces := (hY.finiteFaces j).to_subtype
  have hBleft : (boundaryComplex 2 (X (i - 1))).space =
      (X (i - 1)).space ∩ (T'' (2 * (i - 1)) ∪ T'' (2 * i)) := by
    simpa only [sub_add_cancel] using hX.boundary (i - 1)
  intro j
  by_cases hj : j = i - 1
  · subst j
    rcases hstep.capping with ⟨hcap, f, hf, hfix⟩ | ⟨⟨f, hf, hfix⟩, hcap⟩
    · apply HasEssentialBoundaryPLEmbeddings.of_circle_capping (X (i - 1)) (Y (i - 1))
        (hX.manifold _) (hY.manifold _) (htw.boundary_isPLTorus _) (hmodel (i - 1))
        (by rw [hBleft]; exact hcap)
      intro c G hG hnull
      have hiff : boundsDiskIn G (T'' (2 * i)) ↔
          boundsDiskIn G (T'' (2 * (i - 1) + 1)) := by
        simpa only [sub_add_cancel] using hX.upper_component_boundsDiskIn_iff htw h314 (i - 1) c
          (by simpa only [sub_add_cancel] using hG)
      exact hiff.mp hnull
    · exact HasEssentialBoundaryPLEmbeddings.of_isPLHomeomorphOn (X (i - 1)) (Y (i - 1))
        (hX.manifold _) (hmodel (i - 1)) hf (by rw [hBleft]; exact hfix)
  · by_cases hji : j = i
    · subst j
      rcases hstep.capping with ⟨hcap, f, hf, hfix⟩ | ⟨⟨f, hf, hfix⟩, hcap⟩
      · exact HasEssentialBoundaryPLEmbeddings.of_isPLHomeomorphOn (X i) (Y i)
          (hX.manifold _) (hmodel i) hf (by rw [hX.boundary i]; exact hfix)
      · apply HasEssentialBoundaryPLEmbeddings.of_circle_capping (X i) (Y i)
          (hX.manifold _) (hY.manifold _) (htw.boundary_isPLTorus _) (hmodel i)
          (by rw [hX.boundary i]; exact hcap)
        intro c G hG hnull
        exact (hX.lower_component_boundsDiskIn_iff htw h314 i c hG).mp hnull
    · rw [hstep.unchanged j hj hji]
      exact hmodel j

theorem IsCanonicalTower.subsurface_embeddings_of_null_splits [DecidableEq E3]
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} (window : Finset ℤ)
    (hmodel : ∀ j, HasEssentialBoundaryPLEmbeddings (X j) (T'' (2 * j + 1)))
    (hpath : Relation.ReflTransGen (fun U V =>
      IsCanonicalSurface U (fun j => φ '' S j) T'' I P' a b ∧
      IsCanonicalSurface V (fun j => φ '' S j) T'' I P' a b ∧
      ∃ i ∈ window, IsCanonicalNullSplit (fun j => φ '' S j) T'' i U V) X Y) :
    ∀ j, HasEssentialBoundaryPLEmbeddings (Y j) (T'' (2 * j + 1)) := by
  induction hpath with
  | refl => exact hmodel
  | tail hpath hlast ih =>
    obtain ⟨hU, hV, i, -, hstep⟩ := hlast
    exact hstep.preserves_subsurface_embeddings htw h314 hU hV ih

end DifferentialGeometry.Topology.PiecewiseLinear
