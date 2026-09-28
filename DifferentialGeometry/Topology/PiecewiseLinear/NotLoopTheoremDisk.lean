/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcStep
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskLevelSet

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Descent

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_disjoint_of_decomposition
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h8 : ∀ v₁ ∈ K.vertices, ∀ e₁ ∈ K.faces, e₁.card = 2 →
      ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → Δ ⊆ Cpp v₁ ∩ interior N' →
        Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2 →
        (∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
            DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint) →
        (∀ e ∈ K.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) →
        (Δ ∩ h '' K.space).Nonempty)
    (n : ℕ) {Δ : Set E3} (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    {Cs : Set (Set E3)} (hfin : Cs.Finite) (hn : Cs.ncard = n) (hdisj : Cs.PairwiseDisjoint id)
    (hA : Δ ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs)
    (hCs : ∀ S ∈ Cs, (IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)) ∨
      ∃ q : (Fin 2 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) S ∧
        q '' stdSimplexBoundary 1 = S ∩ frontier XK.space) :
    ∃ Δ' : Set E3, IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧
      Disjoint Δ' (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) := by
  induction n using Nat.strong_induction_on generalizing Δ Cs with
  | _ n ih =>
    rcases Cs.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨Δ, hΔ, Set.disjoint_iff_inter_eq_empty.mpr ?_⟩
      rw [hA, hCe, sUnion_empty]
    · have hstep : ∃ (Δ' : Set E3) (Cs' : Set (Set E3)),
          IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧ Cs' ⊆ Cs ∧ Cs' ≠ Cs ∧
            Δ' ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs' := by
        by_cases hcirc : ∃ S ∈ Cs, IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)
        · exact h2.exists_isLoopTheoremDisk_circleStep hd h34 h8 hΔ hfin hdisj hA hCs hcirc
        · refine h2.exists_isLoopTheoremDisk_arcStep hd h34 hΔ hfin hdisj hA (fun S hS => ?_)
            hCne
          exact (hCs S hS).resolve_left fun hS' => hcirc ⟨S, hS, hS'⟩
      obtain ⟨Δ', Cs', hΔ', hsub, hne, hA'⟩ := hstep
      have hlt : Cs'.ncard < n :=
        hn ▸ Set.ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩) hfin
      exact ih _ hlt hΔ' (hfin.subset hsub) rfl (hdisj.subset hsub) hA'
        (fun S hS => hCs S (hsub hS))

end Descent

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem section33_not_isLoopTheoremDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h7 : HasNoHandleLoopTheoremDisk K h N' Cpp XK.space)
    (h8 : ∀ v₁ ∈ K.vertices, ∀ e₁ ∈ K.faces, e₁.card = 2 →
      ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → Δ ⊆ Cpp v₁ ∩ interior N' →
        Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2 →
        (∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
            DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint) →
        (∀ e ∈ K.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) →
        (Δ ∩ h '' K.space).Nonempty) :
    ∀ Δ : Set (EuclideanSpace ℝ (Fin 3)),
      ¬ IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ := by
  intro Δ hΔ
  obtain ⟨Δ₁, Cs, hΔ₁, hfin, hdisj, hA, hCs⟩ := h2.exists_isLoopTheoremDisk_levelSet hd hΔ
  obtain ⟨Δ₂, hΔ₂, hdis⟩ := h2.exists_isLoopTheoremDisk_disjoint_of_decomposition hd h34 h8
    Cs.ncard hΔ₁ hfin rfl hdisj hA hCs
  obtain ⟨y, hyΔ, hyA⟩ := h7.inter_pseudoCells_nonempty hd hΔ₂
  exact Set.disjoint_left.mp hdis hyΔ hyA

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
