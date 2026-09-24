import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCirclePair
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedAnnulusRecognition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_lateral_complement_of_rim_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {W : Set (E × ℝ)} {ρ : (E × ℝ) × ℝ → E × ℝ}
    (hρ : IsPLHomeomorphOn ρ (((r '' stdSimplexBoundary 2) ×ˢ {a}) ×ˢ Icc c d) W)
    (hzero : ∀ z ∈ (r '' stdSimplexBoundary 2) ×ˢ {a}, ρ (z, c) = z)
    (hWA : W ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)
    (hWtop : Disjoint W ((r '' stdSimplexBoundary 2) ×ˢ {b})) :
    ∃ η : (Fin 3 → ℝ) × ℝ → E × ℝ,
      IsPLHomeomorphOn η (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (closure (((r '' stdSimplexBoundary 2) ×ˢ Icc a b) \ W)) ∧
      η '' (stdSimplexBoundary 2 ×ˢ {0}) =
        ρ '' (((r '' stdSimplexBoundary 2) ×ˢ {a}) ×ˢ {d}) ∧
      η '' (stdSimplexBoundary 2 ×ˢ {1}) = (r '' stdSimplexBoundary 2) ×ˢ {b} ∧
      closure (((r '' stdSimplexBoundary 2) ×ˢ Icc a b) \ W) ∩ W =
        ρ '' (((r '' stdSimplexBoundary 2) ×ˢ {a}) ×ˢ {d}) ∧
      W ∪ closure (((r '' stdSimplexBoundary 2) ×ˢ Icc a b) \ W) =
        (r '' stdSimplexBoundary 2) ×ˢ Icc a b := by
  let J := r '' stdSimplexBoundary 2
  let A := J ×ˢ Icc a b
  let D₀ := P ×ˢ {a}
  let D₁ := P ×ˢ {b}
  let J₀ := J ×ˢ {a}
  let J₁ := J ×ˢ {b}
  let L := ρ '' (J₀ ×ˢ {d})
  let S := P ×ˢ {a, b} ∪ A
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hJP : J ⊆ P := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hS : IsPLSphere 2 S := hr.isPLSphere_prism_boundary hab
  have hr₀ := hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hr₁ := hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const b)
  have hb₀ : ((fun x : E => (x, a)) ∘ r) '' stdSimplexBoundary 2 = J₀ := by
    rw [image_comp, ← prod_singleton]
  have hb₁ : ((fun x : E => (x, b)) ∘ r) '' stdSimplexBoundary 2 = J₁ := by
    rw [image_comp, ← prod_singleton]
  have hJ₀W : J₀ ⊆ W := fun z hz => hzero z hz ▸ hρ.bijOn.mapsTo ⟨hz, le_rfl, hcd.le⟩
  have hWD : W ∩ D₀ = J₀ := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨(hWA hz.1).1, hz.2.2⟩
    · intro z hz
      exact ⟨hJ₀W hz, hJP hz.1, hz.2⟩
  have hρ' : IsPLHomeomorphOn ρ
      ((((fun x : E => (x, a)) ∘ r) '' stdSimplexBoundary 2) ×ˢ Icc c d) W := by
    rwa [hb₀]
  obtain ⟨q, hq, hqb, -⟩ := hr₀.exists_isPLHomeomorphOn_union_collar hcd hρ'
    (fun z hz => hzero z (hb₀.subset hz)) (by rwa [hb₀])
  rw [hb₀] at hqb
  change q '' stdSimplexBoundary 2 = L at hqb
  have hLW : L ⊆ W := by
    apply (image_mono _).trans hρ.image_eq.subset
    intro z hz
    exact ⟨hz.1, hz.2.symm ▸ ⟨hcd.le, le_rfl⟩⟩
  have hD₀S : D₀ ⊆ S := fun z hz => Or.inl ⟨hz.1, Or.inl hz.2⟩
  have hD₁S : D₁ ⊆ S := fun z hz => Or.inl ⟨hz.1, Or.inr hz.2⟩
  have hWS : W ⊆ S := hWA.trans subset_union_right
  have hdis : Disjoint (D₀ ∪ W) D₁ := by
    apply disjoint_left.mpr
    intro z hz hz₁
    rcases hz with hz | hz
    · exact hab.ne (hz.2.symm.trans hz₁.2)
    · exact disjoint_left.mp hWtop hz ⟨(hWA hz).1, hz₁.2⟩
  obtain ⟨η, hη, hηS, hη₀, hη₁, hηD₀, hηD₁, hcover⟩ :=
    exists_isPLHomeomorphOn_lateral_annulus_cover_of_disjoint_disks
      hS hq hr₁ hqb hb₁ (union_subset hD₀S hWS) hD₁S hdis
  let B := η '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
  have hLB : L ⊆ B := by
    rw [← hη₀]
    apply image_mono
    intro z hz
    exact ⟨hz.1, hz.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩
  have hJ₁B : J₁ ⊆ B := by
    rw [← hη₁]
    apply image_mono
    intro z hz
    exact ⟨hz.1, hz.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩
  have hBA : B ⊆ A := by
    intro z hz
    rcases hηS hz with ⟨hzP, hza | hzb⟩ | hzA
    · exact hWA (hLW (hηD₀ ▸ ⟨hz, Or.inl ⟨hzP, hza⟩⟩))
    · have hzJ : z ∈ J₁ := hηD₁ ▸ ⟨hz, hzP, hzb⟩
      exact ⟨hzJ.1, hzb.symm ▸ ⟨hab.le, le_rfl⟩⟩
    · exact hzA
  have hBW : B ∩ W = L := by
    apply Subset.antisymm
    · exact fun z hz => hηD₀ ▸ ⟨hz.1, Or.inr hz.2⟩
    · exact fun z hz => ⟨hLB hz, hLW hz⟩
  have hAB : W ∪ B = A := by
    apply Subset.antisymm (union_subset hWA hBA)
    intro z hz
    rcases hcover (Or.inr hz) with ((hzD | hzW) | hzD) | hzB
    · exact Or.inl (hJ₀W ⟨hz.1, hzD.2⟩)
    · exact Or.inl hzW
    · exact Or.inr (hJ₁B ⟨hz.1, hzD.2⟩)
    · exact Or.inr hzB
  have hAnn : IsAnnulusOn B L J₁ := by
    have h := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
      hη.isPiecewiseAffineOn.continuousOn hη.bijOn.injOn
    rwa [hη₀, hη₁] at h
  have hBcl : IsClosed B := hAnn.isCompact.isClosed
  have heq : closure (A \ W) = B := by
    apply Subset.antisymm
    · apply closure_minimal _ hBcl
      intro z hz
      exact (hAB.symm.subset hz.1).resolve_left hz.2
    · rw [← hAnn.closure_sdiff_ends]
      apply closure_mono
      intro z hz
      exact ⟨hBA hz.1, fun hzW => hz.2 (Or.inl (hBW ▸ ⟨hz.1, hzW⟩))⟩
  exact ⟨η, heq.symm ▸ hη, hη₀, hη₁, by rw [heq]; exact hBW,
    by rw [heq]; exact hAB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
