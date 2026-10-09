/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalCompletionRows
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeSequenceStability
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalStableEvenAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalDisplayedSeparators
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.exists_annular_chain_sequence [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices) (hv : v ∈ K.vertices)
    (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (h303 : Moise303) (h286 : Moise286) (h314 : Moise314)
    {Y : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hY : IsCanonicalSurface Y (fun i => φ '' S i) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (hmodel : ∀ i, HasEssentialBoundaryPLEmbeddings (Y i) (T'' (2 * i + 1)))
    (hwitness : HasCanonicalBridgeWitnesses Y T'') :
    ∃ (H B Jlo Jhi : ℤ → Set E3) (M : ℕ → Set E3),
      IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P' ∧
      M 0 = towerSurface T'' (fun i => (Y i).space) P' ∧
      (∀ n, IsSeparatorIn (interior (h '' C u ∪ h '' C v)) (M n) {h u} {h v}) ∧
      (∀ n, P' ∈ M n) ∧
      IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' annularChain H B P') ∧
      ∀ x ∈ interior (h '' C u ∪ h '' C v), x ≠ P' →
        ∃ U ∈ 𝓝 x, ∃ N : ℕ, ∀ n ≥ N, M n ∩ U = annularChain H B P' ∩ U := by
  obtain ⟨X, hzero, hstep⟩ := hY.exists_bridge_normalization_sequence ht hu hv huv he htw
    havoid h303 h286 h314 hmodel hwitness (fun n => {-(n : ℤ), (n : ℤ)})
  let B : ℤ → Set E3 := fun i => (X (i.natAbs + 1) i).space
  have hX (n : ℕ) := (hstep n).source
  have hstable (i : ℤ) (n : ℕ) (hn : i.natAbs + 1 ≤ n) : (X n i).space = B i :=
    congrArg Geometry.SimplicialComplex.space (htw.row_eq_of_bridge_normalizations hstep i hn)
  have hevent (i : ℤ) : ∃ N, ∀ n, N ≤ n → (X n i).space = B i :=
    ⟨i.natAbs + 1, hstable i⟩
  obtain ⟨Jlo, Jhi, hrow⟩ := htw.exists_marked_annuli_of_bridge_normalizations h314 hstep
  have hB (i : ℤ) : IsPLAnnulusWithEnds (B i) (Jlo i) (Jhi i) := (hrow i).1
  have hlo (i : ℤ) : B i ∩ T'' (2 * i) = Jlo i := (hrow i).2.1
  have hhi (i : ℤ) : B i ∩ T'' (2 * (i + 1)) = Jhi i := (hrow i).2.2.1
  obtain ⟨H, H', hhalf⟩ := htw.exists_complementary_even_annuli_of_eventually_stable_rows
    X hX B Jlo Jhi hevent hB hlo hhi
    (fun i => (hrow i).2.2.2.1) (fun i => (hrow i).2.2.2.2.1)
  have hchain := htw.isAnnularChain_of_eventually_stable_rows X hX H B Jlo Jhi hevent
    (fun i => (hhalf i).1) (fun i => subset_union_left.trans (hhalf i).2.2.1.subset)
    hB hlo hhi (fun i => (hrow i).2.2.2.2.2.1) (fun i => (hrow i).2.2.2.2.2.2)
  obtain ⟨M, hM₀, hM, hMP, hlocal⟩ := htw.exists_displayed_separators_of_stable_rows
    isOpen_interior havoid hX H H' B Jlo Jhi hstable hhalf hlo hhi
  refine ⟨H, B, Jlo, Jhi, M, hchain, ?_, hM, hMP,
    IsAnnularChain.isClosed_preimage_annularChain htw hchain, hlocal⟩
  simpa only [hzero] using hM₀

end DifferentialGeometry.Topology.PiecewiseLinear
