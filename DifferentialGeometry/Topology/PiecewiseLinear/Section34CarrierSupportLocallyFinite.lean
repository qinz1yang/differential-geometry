/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}

omit [FiniteDimensional ℝ Ea] in
theorem locallyFinite_section34CarrierSupport (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    (∀ t : Finset Ea, Section34CarrierSupport 𝒦 t ⊆ U) ∧
      ∀ x ∈ U, ∃ V ∈ 𝓝 x, {t : Finset Ea | t ∈ 𝒦.complex.faces ∧
        (Section34CarrierSupport 𝒦 t ∩ V).Nonempty}.Finite := by
  classical
  constructor
  · intro t y hy
    obtain ⟨w, hwt, hyw⟩ := mem_iUnion₂.mp hy
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hyw
    change y ∈ 𝒦.map '' convexHull ℝ ((s : Finset Ea) : Set Ea) at hys
    obtain ⟨z, hz, rfl⟩ := hys
    exact 𝒦.bijOn.mapsTo (𝒦.complex.convexHull_subset_space hs.1 hz)
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := 𝒦.bijOn.surjOn hx
    obtain ⟨W, hW, hfin⟩ := 𝒦.locallyFinite ⟨p, hp⟩
    rw [𝒦.isEmbedding.isInducing.nhds_eq_comap] at hW
    obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.mp hW
    have hcoface : ∀ w : Ea, w ∈ 𝒦.complex.vertices →
        {s : 𝒦.complex.faces | w ∈ (s : Set Ea)}.Finite := by
      intro w hw
      let q : 𝒦.complex.space := ⟨w, 𝒦.complex.vertices_subset_space hw⟩
      refine (𝒦.locallyFinite.point_finite q).subset ?_
      intro s hs
      change w ∈ (s : Set Ea) at hs
      change (q : Ea) ∈ convexHull ℝ ((s : Finset Ea) : Set Ea)
      simpa [q] using subset_convexHull ℝ _ hs
    have hshare : ∀ s : 𝒦.complex.faces,
        {t : 𝒦.complex.faces | ∃ w ∈ (s : Set Ea), w ∈ (t : Set Ea)}.Finite := by
      intro s
      refine (s.1.finite_toSet.biUnion fun w hw =>
        hcoface w (𝒦.complex.down_closed s.2
          (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w))).subset ?_
      intro t ht
      obtain ⟨w, hw, hwt⟩ := ht
      exact mem_iUnion₂.mpr ⟨w, hw, hwt⟩
    let S : Set 𝒦.complex.faces := {s |
      ((Subtype.val ⁻¹' convexHull ℝ ((s : Finset Ea) : Set Ea)) ∩ W).Nonempty}
    have hfinS : S.Finite := by
      simpa [S] using hfin
    have hfinite : (⋃ s ∈ S, {t : 𝒦.complex.faces |
        ∃ w ∈ (s : Set Ea), w ∈ (t : Set Ea)}).Finite :=
      hfinS.biUnion fun s _ => hshare s
    refine ⟨V, hV, ?_⟩
    refine (hfinite.image fun t : 𝒦.complex.faces => (t : Finset Ea)).subset ?_
    intro t ht
    obtain ⟨y, hyS, hyV⟩ := ht.2
    obtain ⟨w, hwt, hyS⟩ := mem_iUnion₂.mp hyS
    obtain ⟨s, hs, hyS⟩ := mem_iUnion₂.mp hyS
    change s ∈ 𝒦.complex.faces ∧ w ∈ s at hs
    change y ∈ 𝒦.map '' convexHull ℝ ((s : Finset Ea) : Set Ea) at hyS
    obtain ⟨z, hz, hzy⟩ := hyS
    let q : 𝒦.complex.space := ⟨z, 𝒦.complex.convexHull_subset_space hs.1 hz⟩
    have hqW : q ∈ W := hVW (show 𝒦.map q ∈ V from hzy ▸ hyV)
    have hsfh : (⟨s, hs.1⟩ : 𝒦.complex.faces) ∈ S := by
      change ((Subtype.val ⁻¹' convexHull ℝ ((s : Finset Ea) : Set Ea)) ∩ W).Nonempty
      exact ⟨q, ⟨hz, hqW⟩⟩
    refine ⟨⟨t, ht.1⟩, ?_, rfl⟩
    exact mem_iUnion₂.mpr ⟨⟨s, hs.1⟩, hsfh,
      ⟨w, hs.2, hwt⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
