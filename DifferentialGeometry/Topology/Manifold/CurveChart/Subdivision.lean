import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry

variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M]

theorem exists_chart_subdivision
    {a b : ℝ} (hab : a ≤ b) {γ : ℝ → M}
    (hγ : ContinuousOn γ (Icc a b)) :
    ∃ t : ℕ → Icc a b,
      t 0 = ⟨a, left_mem_Icc.mpr hab⟩ ∧
      Monotone t ∧
      (∃ m, ∀ n ≥ m, t n = ⟨b, right_mem_Icc.mpr hab⟩) ∧
      ∀ n, ∃ p : M,
        MapsTo γ (Icc (t n : ℝ) (t (n + 1) : ℝ)) (chartAt H p).source := by
  let c : M → Set (Icc a b) := fun p ↦
    (fun r : Icc a b ↦ γ r) ⁻¹' (chartAt H p).source
  have hcopen : ∀ p, IsOpen (c p) := fun p ↦
    (chartAt H p).open_source.preimage hγ.domRestrict
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ p, c p := by
    intro r _
    refine mem_iUnion.mpr ⟨γ r, ?_⟩
    exact mem_chart_source H (γ r)
  obtain ⟨t, ht0, hmono, hlast, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hcopen hcover
  have ht0' : t 0 = ⟨a, left_mem_Icc.mpr hab⟩ := by
    apply Subtype.ext
    exact ht0
  obtain ⟨m, hm⟩ := hlast
  have hlast' : ∃ m, ∀ n ≥ m, t n = ⟨b, right_mem_Icc.mpr hab⟩ := by
    refine ⟨m, fun n hn ↦ ?_⟩
    apply Subtype.ext
    exact hm n hn
  refine ⟨t, ht0', hmono, hlast', ?_⟩
  intro n
  obtain ⟨p, hp⟩ := hsub n
  refine ⟨p, ?_⟩
  intro r hr
  have hrab : r ∈ Icc a b :=
    ⟨le_trans (t n).property.1 hr.1,
      le_trans hr.2 (t (n + 1)).property.2⟩
  exact hp (show (⟨r, hrab⟩ : Icc a b) ∈ Icc (t n) (t (n + 1)) from hr)

theorem exists_compact_chart_subdivision
    [LocallyCompactSpace M] [RegularSpace M]
    {a b : ℝ} (hab : a ≤ b) {γ : ℝ → M}
    (hγ : ContinuousOn γ (Icc a b)) :
    ∃ t : ℕ → Icc a b,
      t 0 = ⟨a, left_mem_Icc.mpr hab⟩ ∧
      Monotone t ∧
      (∃ m, ∀ n ≥ m, t n = ⟨b, right_mem_Icc.mpr hab⟩) ∧
      ∀ n, ∃ p : M, ∃ K : Set M,
        IsCompact K ∧
        K ⊆ (chartAt H p).source ∧
        MapsTo γ (Icc (t n : ℝ) (t (n + 1) : ℝ)) (interior K) := by
  obtain ⟨t, ht0, hmono, hlast, hchart⟩ :=
    exists_chart_subdivision (H := H) hab hγ
  refine ⟨t, ht0, hmono, hlast, ?_⟩
  intro n
  obtain ⟨p, hp⟩ := hchart n
  let J : Set ℝ := Icc (t n : ℝ) (t (n + 1) : ℝ)
  have hJsub : J ⊆ Icc a b := by
    intro r hr
    exact ⟨le_trans (t n).property.1 hr.1,
      le_trans hr.2 (t (n + 1)).property.2⟩
  have hJc : IsCompact J := isCompact_Icc
  have hImage : IsCompact (γ '' J) :=
    hJc.image_of_continuousOn (hγ.mono hJsub)
  have hImageSource : γ '' J ⊆ (chartAt H p).source :=
    mapsTo_iff_image_subset.mp hp
  obtain ⟨K, hKc, _hKclosed, hImageK, hKsrc⟩ :=
    exists_compact_closed_between hImage (chartAt H p).open_source hImageSource
  exact ⟨p, K, hKc, hKsrc, mapsTo_iff_image_subset.mpr hImageK⟩

end Geometry
end DifferentialGeometry

end
