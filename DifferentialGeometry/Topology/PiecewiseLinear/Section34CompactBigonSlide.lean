/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ChartBigonRemoval
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonModelUpdate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactBigonSlide (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (s : Section34CompactSimplexIndex K 3)
    (hop : Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s =
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s + 2 =
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  let _ := hcar
  classical
  obtain ⟨w, v, e, B, B', Bb, Dj, Jd, O, k, hB, hBf, hBw, hBbe, hBsplit,
    hB', hB'e, hBB', hD, hDS, hJ, hclean, hwv, hewv, hwi, hvi, hei, hinter, hY,
    hDball, hDF, hEfront, hO, hDO, hOV, hOT, hOf, hOrim, hOE, hOH, hforeign,
    hDk, hkO, hk, hki, hSf, hVu, hT, hEz⟩ :=
    exists_section34CompactBigonChart hcut hgraph hinv s hop
  obtain ⟨-, -, -, -, -, -, -, hfinite, -⟩ := id hinv
  obtain ⟨-, hf₁, -, -, hmarkers, -⟩ := id hgraph
  have hDSg : Dj ⊆ frontier (⋃ z, section34CompactVertexBallImage src f₁ z) :=
    fun x hx => (hDS hx).2
  have hDB := compactBigon_inter_faceBall_boundary hinv hB hBf hB' hB'e hBB' hD
    hDSg hJ (hclean s)
  have hDB' := compactBigon_inter_splitDisk_boundary hcut hgraph
    hBsplit hB' hB'e hD hDS hJ
  have hEs : ∀ x ∈ section34CompactSplitDiskImage srcBd f₁ e ∩ k.source,
      x ∈ frontier (⋃ z, section34CompactVertexBallImage src f₁ z) :=
    fun x hx => (hSf x hx.2).mpr (hEz x hx.2 hx.1)
  obtain ⟨Q, A, C, α, β, p, q, hQ, hDQ, -, hα, hβ, hαc, hβc,
    hpq, hAC, hp, hq, hcp, hcq, hBb, hlocal⟩ :=
    exists_compactBigonCrosscutNeighborhood hcut hgraph hinv s hB hB' hD
      hDB hDB' hBB' hDSg k hk hki hDk hSf hEs isOpen_univ (subset_univ _)
  let S := frontier (⋃ z, section34CompactVertexBallImage src f₁ z)
  let T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  let E := ⋃ e', section34CompactSplitDiskImage srcBd f₁ e'
  have hQtarget : Q ×ˢ {(0 : ℝ)} ⊆ k.target := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rcases ht with rfl
    exact (hlocal z hz).1
  have hEmem : ∀ x ∈ k.source,
      x ∈ E ↔ x ∈ section34CompactSplitDiskImage srcBd f₁ e := by
    intro x hx
    constructor
    · intro hxE
      obtain ⟨e', hxe'⟩ := mem_iUnion.mp hxE
      have he' : e' = e := by
        by_contra hne
        exact disjoint_left.mp (hOE e' hne) (hkO hx)
          ((hcut.isPLCellOn_splitDiskImage hf₁ e').boundary_subset hxe')
      exact he' ▸ hxe'
    · exact fun hxe => mem_iUnion.mpr ⟨e, hxe⟩
  have hPmodel : ∀ z ∈ Q, k.symm (z, 0) ∈ fblBd s ↔ z ∈ A := by
    intro z hz
    have hzt := (hlocal z hz).1
    have hsz : k.symm (z, 0) ∈ S :=
      (hSf _ (k.map_target hzt)).mpr (by rw [k.right_inv hzt])
    exact (show k.symm (z, 0) ∈ fblBd s ↔ k.symm (z, 0) ∈ fblBd s ∩ S from
      ⟨fun hx => ⟨hx, hsz⟩, fun hx => hx.1⟩).trans (hlocal z hz).2.1
  have hEmodel : ∀ z ∈ Q, k.symm (z, 0) ∈ E ↔ z ∈ C := by
    intro z hz
    exact (hEmem _ (k.map_target (hlocal z hz).1)).trans (hlocal z hz).2.2
  have hEflat : ∀ z ∈ k.target, k.symm z ∈ E → z.2 = 0 := by
    intro z hz hzE
    have hflat := hEz _ (k.map_target hz) ((hEmem _ (k.map_target hz)).mp hzE)
    rwa [k.right_inv hz] at hflat
  obtain ⟨L, Φ, hL, hLk, hΦ, hfix, -, hΦT, hdelete, hdrop,
    G, hG, hG0, hG1, -, -, hGT⟩ :=
    exists_chart_bigon_removal k hk hki hQ hQtarget hαc hβc hAC hpq hp hq hcp hcq
      (S := S) (Y := T) hSf hT hPmodel hEmodel hEflat (hfinite s)
  exact exists_compactBigonSlide_of_model_move hinv
    (fun z => (hmarkers z).trans interior_subset) s hwi hvi hOV hOT
    hOH hOf hOrim hforeign Φ hΦ hL (hLk.trans hkO) hfix hΦT
    G hG hG0 hG1 hGT hdelete hdrop

end DifferentialGeometry.Topology.PiecewiseLinear
