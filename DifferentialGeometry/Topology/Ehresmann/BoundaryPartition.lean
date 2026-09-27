import DifferentialGeometry.Topology.Ehresmann.BoundaryCompletion
import DifferentialGeometry.Topology.Manifold.BoundaryOrder
import DifferentialGeometry.Topology.PartitionOfUnity.Locality
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

theorem regularIntervalDatum_partition_sum_of_boundary_pieces
    {ι : Type*} {E H W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [CompactSpace W] [PreconnectedSpace W]
    (ρ : SmoothPartitionOfUnity ι I W) (q : ι → W → ℝ)
    (hq : ∀ i, ∀ x ∈ tsupport (ρ i), ContMDiffAt I 𝓘(ℝ) ∞ (q i) x)
    (hreg : ∀ x, mvfderiv I (fun y ↦ ∑ᶠ i, ρ i y * q i y) x ≠ 0)
    (S₀ S₁ : Set W) (hS₀ : S₀.Nonempty) (hS₁ : S₁.Nonempty)
    (hboundary : I.boundary W = S₀ ∪ S₁) (i₀ i₁ : ι) (a b : ℝ) (hab : a < b)
    (hq₀ : ∀ x ∈ S₀, q i₀ x = a) (hq₁ : ∀ x ∈ S₁, q i₁ x = b)
    (hdisj₀ : ∀ j, j ≠ i₀ → Disjoint S₀ (tsupport (ρ j)))
    (hdisj₁ : ∀ j, j ≠ i₁ → Disjoint S₁ (tsupport (ρ j))) :
    let u := fun x ↦ ∑ᶠ i, ρ i x * q i x
    RegularIntervalDatum I u a b ∧
      u ⁻¹' ({a} : Set ℝ) = S₀ ∧ u ⁻¹' ({b} : Set ℝ) = S₁ ∧
      (∀ᶠ x in 𝓝ˢ S₀, u x = q i₀ x) ∧ ∀ᶠ x in 𝓝ˢ S₁, u x = q i₁ x := by
  let u := fun x ↦ ∑ᶠ i, ρ i x * q i x
  have hu : ContMDiff I 𝓘(ℝ) ∞ u := by
    simpa only [smul_eq_mul] using ρ.contMDiff_finsum_smul hq
  have hcoe (j : ι) (x : W) : ρ.toPartitionOfUnity j x = ρ j x := rfl
  have hlocal₀ : ∀ᶠ x in 𝓝ˢ S₀, u x = q i₀ x := by
    simpa only [hcoe, smul_eq_mul] using DifferentialGeometry.Topology.partition_patch_eq_near_of_disjoint_tsupport
      ρ.toPartitionOfUnity q S₀ i₀ hdisj₀
  have hlocal₁ : ∀ᶠ x in 𝓝ˢ S₁, u x = q i₁ x := by
    simpa only [hcoe, smul_eq_mul] using DifferentialGeometry.Topology.partition_patch_eq_near_of_disjoint_tsupport
      ρ.toPartitionOfUnity q S₁ i₁ hdisj₁
  have hval₀ (x) (hx : x ∈ S₀) : u x = a :=
    (subset_of_mem_nhdsSet hlocal₀ hx).trans (hq₀ x hx)
  have hval₁ (x) (hx : x ∈ S₁) : u x = b :=
    (subset_of_mem_nhdsSet hlocal₁ hx).trans (hq₁ x hx)
  have hbdy (x) (hx : I.IsBoundaryPoint x) : u x = a ∨ u x = b := by
    have h : x ∈ S₀ ∪ S₁ := hboundary ▸ hx
    exact h.elim (fun h ↦ Or.inl (hval₀ x h)) (fun h ↦ Or.inr (hval₁ x h))
  have hdata := regularIntervalDatum_of_boundary_values hab hu hreg hbdy
    (by obtain ⟨x, hx⟩ := hS₀; exact ⟨x, hval₀ x hx⟩)
    (by obtain ⟨x, hx⟩ := hS₁; exact ⟨x, hval₁ x hx⟩)
  refine ⟨hdata, ?_, ?_, hlocal₀, hlocal₁⟩
  · ext x
    change u x = a ↔ x ∈ S₀
    refine ⟨?_, hval₀ x⟩
    intro hx
    have hb : x ∈ I.boundary W := hdata.boundary_eq.symm ▸ Or.inl hx
    have hs : x ∈ S₀ ∪ S₁ := hboundary ▸ hb
    rcases hs with hs | hs
    · exact hs
    · exact (hab.ne (hx.symm.trans (hval₁ x hs))).elim
  · ext x
    change u x = b ↔ x ∈ S₁
    refine ⟨?_, hval₁ x⟩
    intro hx
    have hb : x ∈ I.boundary W := hdata.boundary_eq.symm ▸ Or.inr hx
    have hs : x ∈ S₀ ∪ S₁ := hboundary ▸ hb
    rcases hs with hs | hs
    · exact (hab.ne ((hval₀ x hs).symm.trans hx)).elim
    · exact hs

theorem regularIntervalDatum_partition_sum_of_inward_curve
    {ι : Type*} {E H W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [CompactSpace W] [PreconnectedSpace W]
    (ρ : SmoothPartitionOfUnity ι I W) (q : ι → W → ℝ)
    (hq : ∀ i, ∀ x ∈ tsupport (ρ i), ContMDiffAt I 𝓘(ℝ) ∞ (q i) x)
    (hreg : ∀ x, mvfderiv I (fun y ↦ ∑ᶠ i, ρ i y * q i y) x ≠ 0)
    (S₀ S₁ : Set W) (hS₀ : S₀.Nonempty) (hS₁ : S₁.Nonempty)
    (hboundary : I.boundary W = S₀ ∪ S₁) (i₀ i₁ : ι) (a b : ℝ)
    (hq₀ : ∀ x ∈ S₀, q i₀ x = a) (hq₁ : ∀ x ∈ S₁, q i₁ x = b)
    (hdisj₀ : ∀ j, j ≠ i₀ → Disjoint S₀ (tsupport (ρ j)))
    (hdisj₁ : ∀ j, j ≠ i₁ → Disjoint S₁ (tsupport (ρ j)))
    (γ : ℝ → W) (hγ : ContinuousWithinAt γ (Ici 0) 0) (hγ₀ : γ 0 ∈ S₀)
    (k : ℝ) (hk : 0 < k)
    (hcoordinate : ∀ᶠ t in 𝓝[≥] (0 : ℝ), q i₀ (γ t) = a + k * t) :
    let u := fun x ↦ ∑ᶠ i, ρ i x * q i x
    a < b ∧ RegularIntervalDatum I u a b ∧
      u ⁻¹' ({a} : Set ℝ) = S₀ ∧ u ⁻¹' ({b} : Set ℝ) = S₁ ∧
      (∀ᶠ x in 𝓝ˢ S₀, u x = q i₀ x) ∧ ∀ᶠ x in 𝓝ˢ S₁, u x = q i₁ x := by
  let u := fun x ↦ ∑ᶠ i, ρ i x * q i x
  have hcoe (j : ι) (x : W) : ρ.toPartitionOfUnity j x = ρ j x := rfl
  have hlocal₀ : ∀ᶠ x in 𝓝ˢ S₀, u x = q i₀ x := by
    simpa only [hcoe, smul_eq_mul] using DifferentialGeometry.Topology.partition_patch_eq_near_of_disjoint_tsupport
      ρ.toPartitionOfUnity q S₀ i₀ hdisj₀
  have hlocal₁ : ∀ᶠ x in 𝓝ˢ S₁, u x = q i₁ x := by
    simpa only [hcoe, smul_eq_mul] using DifferentialGeometry.Topology.partition_patch_eq_near_of_disjoint_tsupport
      ρ.toPartitionOfUnity q S₁ i₁ hdisj₁
  have hbdy (x) (hx : I.IsBoundaryPoint x) : u x = a ∨ u x = b := by
    have h : x ∈ S₀ ∪ S₁ := hboundary ▸ hx
    rcases h with hx | hx
    · exact Or.inl ((subset_of_mem_nhdsSet hlocal₀ hx).trans (hq₀ x hx))
    · exact Or.inr ((subset_of_mem_nhdsSet hlocal₁ hx).trans (hq₁ x hx))
  have hab := DifferentialGeometry.Topology.Manifold.boundary_value_lt_of_inward_coordinate
    hreg hbdy γ hγ (mem_nhdsSet_iff_forall.mp hlocal₀ _ hγ₀) hk hcoordinate
  exact ⟨hab, regularIntervalDatum_partition_sum_of_boundary_pieces
    ρ q hq hreg S₀ S₁ hS₀ hS₁ hboundary i₀ i₁ a b hab hq₀ hq₁ hdisj₀ hdisj₁⟩

end DifferentialGeometry.Topology.Ehresmann
