/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierSupportLocallyFinite
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellLocallyFiniteCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Statements
import DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldOfLocallyFinitePLPieceIn
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsLocallyFinitePLPieceInOfIsOpen
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSubordinateToCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}

end Leaves

theorem finite_inter_nonempty_of_isCompact_of_locallyFinite {Λ : Type*} {M : Type*}
    [TopologicalSpace M] (sc : Λ → Set M) (Y K : Set M) (hK : IsCompact K) (hKY : K ⊆ Y)
    (hLF : ∀ x ∈ Y, ∃ V ∈ 𝓝 x, {l | (sc l ∩ V).Nonempty}.Finite) :
    {l | (sc l ∩ K).Nonempty}.Finite := by
  classical
  have key : ∀ x : M, ∃ V : Set M, x ∈ K → V ∈ 𝓝 x ∧ {l | (sc l ∩ V).Nonempty}.Finite := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨V, hV, hfin⟩ := hLF x (hKY hx)
      exact ⟨V, fun _ => ⟨hV, hfin⟩⟩
    · exact ⟨univ, fun hx' => absurd hx' hx⟩
  choose V hV using key
  obtain ⟨s, hsK, hs⟩ := hK.elim_nhds_subcover V fun x hx => (hV x hx).1
  refine (s.finite_toSet.biUnion fun x hx =>
    (hV x (hsK x (Finset.mem_coe.mp hx))).2).subset ?_
  rintro l ⟨y, hy, hyK⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hs hyK)
  exact mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, ⟨y, hy, hyx⟩⟩

theorem nonempty_section34CarrierSupport {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}
    (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    (Section34CarrierSupport 𝒦 t).Nonempty := by
  obtain ⟨w, hw⟩ := 𝒦.complex.nonempty_of_mem_faces ht
  exact ⟨𝒦.map w, Set.mem_biUnion (Finset.mem_coe.mpr hw)
    (Set.mem_biUnion (show t ∈ {s : Finset Ea | s ∈ 𝒦.complex.faces ∧ w ∈ s} from ⟨ht, hw⟩)
      (Set.mem_image_of_mem 𝒦.map (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))))⟩

theorem exists_section34ControlNeighborhood {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [MetricSpace M₂] {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hinj : InjOn h U)
    (himOpen : ∀ V : Set M₁, V ⊆ U → IsOpen V → IsOpen (h '' V)) (η : M₁ → ℝ)
    (hηc : ContinuousOn η U) (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ N : M₂ → Set M₂, ∀ y ∈ h '' U, N y ∈ 𝓝 y ∧
      ∀ w ∈ N y, ∀ z ∈ N y, ∀ x ∈ U, h x ∈ N y → dist w z < η x := by
  classical
  have key : ∀ y : M₂, ∃ Ny : Set M₂, y ∈ h '' U → Ny ∈ 𝓝 y ∧
      ∀ w ∈ Ny, ∀ z ∈ Ny, ∀ x ∈ U, h x ∈ Ny → dist w z < η x := by
    intro y
    by_cases hy : y ∈ h '' U
    · obtain ⟨x₀, hx₀, rfl⟩ := hy
      have hpos : 0 < η x₀ := hηpos x₀ hx₀
      refine ⟨Metric.ball (h x₀) (η x₀ / 8) ∩ h '' (U ∩ η ⁻¹' Set.Ioi (η x₀ / 2)),
        fun _ => ⟨?_, ?_⟩⟩
      · exact (Metric.isOpen_ball.inter (himOpen _ inter_subset_left
          (hηc.isOpen_inter_preimage hU isOpen_Ioi))).mem_nhds
          ⟨Metric.mem_ball_self (by linarith),
            ⟨x₀, ⟨hx₀, show η x₀ / 2 < η x₀ by linarith⟩, rfl⟩⟩
      · intro w hw z hz x hx hhx
        have hwd : dist w (h x₀) < η x₀ / 8 := Metric.mem_ball.mp hw.1
        have hzd : dist (h x₀) z < η x₀ / 8 := by
          rw [dist_comm]
          exact Metric.mem_ball.mp hz.1
        have htri := dist_triangle w (h x₀) z
        obtain ⟨x', hx', hx'eq⟩ := hhx.2
        have hxx : x' = x := hinj hx'.1 hx hx'eq
        have hηx : η x₀ / 2 < η x := by
          rw [← hxx]
          exact hx'.2
        linarith
    · exact ⟨univ, fun hy' => absurd hy' hy⟩
  choose N hN using key
  exact ⟨N, fun y hy => hN y hy⟩

theorem exists_section34CarrierControl_of_cellCover {Ea : Type} [NormedAddCommGroup Ea]
    [NormedSpace ℝ Ea] {M₁ M₂ : Type u} [TopologicalSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) {η : M₁ → ℝ}
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) {ι : Type*} (C G : ι → Set M₂)
    (hCcell : ∀ i, IsPLCellOn 3 (C i) (frontier (C i))) (hGC : ∀ i, G i ⊆ interior (C i))
    (hCU : ∀ i, C i ⊆ h '' U)
    (hCchart : ∀ i, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, C i ⊆ c.source)
    (hClf : ∀ y ∈ h '' U, ∃ V ∈ 𝓝 y, {i | (C i ∩ V).Nonempty}.Finite)
    (hCdiam : ∀ i : ι, ∀ x ∈ U, h x ∈ C i → ∀ y ∈ C i, ∀ z ∈ C i, dist y z < η x)
    (hSsub : ∀ t ∈ 𝒦.complex.faces, ∃ i, Section34CarrierSupport 𝒦 t ⊆ U ∩ h ⁻¹' G i)
    (hSlf : ∀ x ∈ U, ∃ V ∈ 𝓝 x, {t : Finset Ea | t ∈ 𝒦.complex.faces ∧
      (Section34CarrierSupport 𝒦 t ∩ V).Nonempty}.Finite) :
    ∃ H : Finset Ea → Set M₂, Section34CarrierControl U 𝒦 h η H := by
  classical
  choose idx hidx using fun τ : 𝒦.complex.faces => hSsub (τ : Finset Ea) τ.2
  have hpre : ∀ S : Set M₂, Subtype.val '' (U.domRestrict h ⁻¹' S) = U ∩ h ⁻¹' S := by
    intro S
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨x, hx⟩, hxS, rfl⟩
      exact ⟨hx, hxS⟩
    · rintro x ⟨hx, hxS⟩
      exact ⟨⟨x, hx⟩, hxS, rfl⟩
  have hrange : Set.range (U.domRestrict h) = h '' U := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hKcpt : ∀ i, IsCompact (U ∩ h ⁻¹' C i) := by
    intro i
    rw [← hpre]
    exact (hh.isInducing.isCompact_preimage' (hCcell i).isCompact
      (hrange ▸ hCU i)).image continuous_subtype_val
  have hfib : ∀ i : ι, {τ : 𝒦.complex.faces | idx τ = i}.Finite := by
    intro i
    refine (finite_inter_nonempty_of_isCompact_of_locallyFinite
      (fun τ : 𝒦.complex.faces => Section34CarrierSupport 𝒦 (τ : Finset Ea)) U
      (U ∩ h ⁻¹' C i) (hKcpt i) inter_subset_left (fun x hx => ?_)).subset ?_
    · obtain ⟨V, hV, hfin⟩ := hSlf x hx
      exact ⟨V, hV, (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset
        fun τ hτ => ⟨τ.2, hτ⟩⟩
    · intro τ hτ
      obtain ⟨x₁, hx₁⟩ := nonempty_section34CarrierSupport 𝒦 τ.2
      have hsub := hidx τ
      rw [hτ] at hsub
      have hmem : h x₁ ∈ C i := interior_subset (hGC i (hsub hx₁).2)
      exact ⟨x₁, hx₁, (hsub hx₁).1, hmem⟩
  have hcarrier : ∀ t : Finset Ea, ∃ Ht : Set M₂,
      ∀ ht : t ∈ 𝒦.complex.faces, Ht = C (idx ⟨t, ht⟩) := by
    intro t
    by_cases ht : t ∈ 𝒦.complex.faces
    · exact ⟨C (idx ⟨t, ht⟩), fun _ => rfl⟩
    · exact ⟨∅, fun ht' => absurd ht' ht⟩
  choose Hfam hHfam using hcarrier
  refine ⟨Hfam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hHfam t ht]
    rintro _ ⟨x, hx, rfl⟩
    exact hGC _ (hidx ⟨t, ht⟩ hx).2
  · intro t ht
    rw [hHfam t ht]
    exact hCU _
  · intro y hy
    obtain ⟨V, hV, hfin⟩ := hClf y hy
    refine ⟨V, mem_nhdsWithin_of_mem_nhds hV,
      ((hfin.biUnion fun i _ => hfib i).image Subtype.val).subset ?_⟩
    rintro t ⟨ht, hne⟩
    rw [hHfam t ht] at hne
    exact ⟨⟨t, ht⟩, mem_iUnion₂.mpr ⟨idx ⟨t, ht⟩, hne, rfl⟩, rfl⟩
  · intro t ht x hx y hy z hz
    rw [hHfam t ht] at hy hz
    exact hCdiam _ x (hidx ⟨t, ht⟩ hx).1
      (interior_subset (hGC _ (hidx ⟨t, ht⟩ hx).2)) y hy z hz
  · intro t ht
    rw [hHfam t ht]
    exact hCcell _
  · intro t ht
    rw [hHfam t ht]
    exact hCchart _

theorem section34Control : Section34ControlStatement.{u} := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  have himOpen : ∀ V : Set M₁, V ⊆ U → IsOpen V → IsOpen (h '' V) := fun V hVU hV =>
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hV (hcont.mono hVU)
      (hinj.mono hVU)
  obtain ⟨Nb, hNb⟩ := exists_section34ControlNeighborhood hU hinj himOpen η hηc hηpos
  obtain ⟨ι, C, G, hCcell, hGopen, hGC, hCU, hCN, hCchart, hcover, hClf⟩ :=
    exists_isPLCellOn_locallyFinite_cover_of_isOpen (himOpen U subset_rfl hU) Nb
      fun y hy => (hNb y hy).1
  obtain ⟨n, ⟨𝒦₀⟩⟩ := exists_locallyFinitePLPieceIn_of_isOpen (M₁ := M₁) hU
  obtain ⟨𝒦, -, -, h𝒦, hSsub⟩ :=
    exists_isSubdivision_section34CarrierSupport_subset hU 𝒦₀
      (isCombinatorialManifold_of_locallyFinitePLPieceIn hU 𝒦₀) (fun i => U ∩ h ⁻¹' G i)
      (fun i => hcont.isOpen_inter_preimage hU (hGopen i))
      (fun x hx => by
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
        exact mem_iUnion.mpr ⟨i, hx, hi⟩)
  obtain ⟨-, hSlf⟩ := locallyFinite_section34CarrierSupport 𝒦
  have hCdiam : ∀ i : ι, ∀ x ∈ U, h x ∈ C i → ∀ y ∈ C i, ∀ z ∈ C i, dist y z < η x := by
    intro i x hx hxC y hy z hz
    obtain ⟨y₀, hy₀, hsub⟩ := hCN i
    exact (hNb y₀ hy₀).2 y (hsub hy) z (hsub hz) x hx (hsub hxC)
  obtain ⟨H, hH⟩ := exists_section34CarrierControl_of_cellCover hh (η := η) 𝒦 C G hCcell hGC
    hCU hCchart hClf hCdiam hSsub hSlf
  exact ⟨n, 𝒦, H, h𝒦, hH⟩

end DifferentialGeometry.Topology.PiecewiseLinear
