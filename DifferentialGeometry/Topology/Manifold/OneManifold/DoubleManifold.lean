import DifferentialGeometry.Topology.Manifold.OneManifold.Double

/-!
# The double is a compact smooth one-manifold without boundary

All coordinate changes of the atlas of `Double M` are smooth (`contDiffOn_fold_fold`,
`contDiffOn_fold_sheet`, `contDiffOn_sheet_fold`, `contDiffOn_sheet_sheet`), so `Double M` is a
smooth manifold modelled on `𝓘(ℝ, ℝ)`; it is compact.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M] [CompactSpace M] [T2Space M]

theorem contDiffOn_fold_fold (p p' : Bdry M) :
    ContDiffOn ℝ ∞ ((foldChart p).symm ≫ₕ foldChart p')
      ((foldChart p).symm ≫ₕ foldChart p').source := by
  refine contDiffOn_id.congr ?_
  rintro s ⟨hs, -⟩
  exact foldInv_snd p hs

theorem contDiffOn_fold_sheet (p : Bdry M) {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) (s₀ : ℝ) :
    ContDiffOn ℝ ∞ ((foldChart p).symm ≫ₕ sheetChart e he s₀)
      ((foldChart p).symm ≫ₕ sheetChart e he s₀).source := by
  have hG := contDiffOn_coord_transition (chart_mem_atlas (EuclideanHalfSpace 1) p.1) he
  have hlin : ContDiff ℝ ∞ (fun s : ℝ => bdryRadius p * (sgn s₀ * s)) :=
    contDiff_const.mul (contDiff_const.mul contDiff_id)
  have hkey : ∀ s ∈ ((foldChart p).symm ≫ₕ sheetChart e he s₀).source,
      sgn s₀ * s = |s| := by
    rintro s ⟨hs, hs'⟩
    have h2 : 0 < sgn s₀ * (foldInv p s).1.2 := hs'.2
    rw [foldInv_snd p hs] at h2
    exact mul_eq_abs_of_pos (abs_sgn s₀) h2
  refine (hG.comp hlin.contDiffOn ?_).congr ?_
  · intro s hsrc
    obtain ⟨hs, hs'⟩ := hsrc
    have h2 : 0 < sgn s₀ * (foldInv p s).1.2 := hs'.2
    rw [foldInv_snd p hs] at h2
    refine ⟨mul_pos (bdryRadius_pos p) h2, ?_, ?_⟩
    · change halfPt (bdryRadius p * (sgn s₀ * s)) ∈ _
      rw [hkey s ⟨hs, hs'⟩]
      exact hs.1
    · change (chartAt (EuclideanHalfSpace 1) p.1).symm
        (halfPt (bdryRadius p * (sgn s₀ * s))) ∈ e.source
      rw [hkey s ⟨hs, hs'⟩]
      exact hs'.1
  · intro s hsrc
    change (e ((chartAt (EuclideanHalfSpace 1) p.1).symm (halfPt (bdryRadius p * |s|)))).val 0 =
      (e ((chartAt (EuclideanHalfSpace 1) p.1).symm
        (halfPt (bdryRadius p * (sgn s₀ * s))))).val 0
    rw [hkey s hsrc]

theorem contDiffOn_sheet_fold {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) (s₀ : ℝ) (p : Bdry M) :
    ContDiffOn ℝ ∞ ((sheetChart e he s₀).symm ≫ₕ foldChart p)
      ((sheetChart e he s₀).symm ≫ₕ foldChart p).source := by
  have hG := contDiffOn_coord_transition he (chart_mem_atlas (EuclideanHalfSpace 1) p.1)
  refine (((contDiffOn_const (c := sgn s₀)).mul (hG.div_const (bdryRadius p))).mono ?_).congr ?_
  · rintro t ⟨ht, ht'⟩
    have hmem : e.symm (halfPt t) ∈ bdryNbhd p := ht'
    exact ⟨ht.1, ht.2, bdryNbhd_subset_source p hmem⟩
  · rintro t ⟨-, ht'⟩
    change sgn s₀ * bdryFn (e.symm (halfPt t)) =
      sgn s₀ * ((chartAt (EuclideanHalfSpace 1) p.1 (e.symm (halfPt t))).val 0 / bdryRadius p)
    have hmem : e.symm (halfPt t) ∈ bdryNbhd p := ht'
    rw [bdryFn_eq_on_bdryNbhd p hmem]
    rfl

theorem contDiffOn_sheet_sheet {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) (he' : e' ∈ atlas (EuclideanHalfSpace 1) M)
    (s₀ s₁ : ℝ) :
    ContDiffOn ℝ ∞ ((sheetChart e he s₀).symm ≫ₕ sheetChart e' he' s₁)
      ((sheetChart e he s₀).symm ≫ₕ sheetChart e' he' s₁).source := by
  refine ((contDiffOn_coord_transition he he').mono ?_).congr ?_
  · rintro t ⟨ht, ht'⟩
    exact ⟨ht.1, ht.2, ht'.1⟩
  · intro t _
    rfl

instance : IsManifold 𝓘(ℝ, ℝ) ∞ (Double M) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨q, rfl⟩ ⟨q', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, preimage_id, range_id, inter_univ]
  change ContDiffOn ℝ ∞ ((doubleChartAt q).symm ≫ₕ doubleChartAt q')
    ((doubleChartAt q).symm ≫ₕ doubleChartAt q').source
  unfold doubleChartAt
  split_ifs
  · exact contDiffOn_fold_fold _ _
  · exact contDiffOn_fold_sheet _ _ _
  · exact contDiffOn_sheet_fold _ _ _
  · exact contDiffOn_sheet_sheet _ _ _ _

instance : CompactSpace (Double M) := by
  have hS : IsCompact {q : M × ℝ | |q.2| = bdryFn q.1} := by
    apply (isCompact_univ.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
    · exact isClosed_eq (continuous_abs.comp continuous_snd) (continuous_bdryFn.comp continuous_fst)
    · intro q hq
      refine ⟨mem_univ _, ?_⟩
      have h1 := bdryFn_le_one q.1
      rw [← show |q.2| = bdryFn q.1 from hq] at h1
      exact abs_le.mp h1
  exact isCompact_iff_compactSpace.mp hS

end DifferentialGeometry.Topology.Manifold.OneManifold
