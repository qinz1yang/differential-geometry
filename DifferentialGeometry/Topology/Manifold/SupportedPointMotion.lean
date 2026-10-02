import DifferentialGeometry.Topology.Manifold.AffineBallIsotopy
import DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.Manifold.IsotopyOrientation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

section SupportedIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

theorem exists_supported_isotopy_apply_eq_of_mem_nhds
    (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ V ∈ 𝓝 x, V ⊆ U ∧ ∀ y ∈ V,
      ∃ J : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
        J 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞ ∧ J 1 x = y ∧
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
          (fun q : ℝ × M => J q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
          (fun q : ℝ × M => (J q.1).symm q.2) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
          ∀ t z, z ∉ K → J t z = z ∧ (J t).symm z = z := by
  let A : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let φ := DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, E) ∞ x
  let c : PartialDiffeomorph 𝓘(ℝ, E)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞ :=
    φ.trans A.toDiffeomorph.toPartialDiffeomorph
  let e := c.toOpenPartialHomeomorph
  have hxsrc : x ∈ e.source := by
    change x ∈ φ.source ∧ φ x ∈ Set.univ
    exact ⟨mem_extChartAt_source x, mem_univ _⟩
  have hxt : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨e.map_source hxsrc, ?_⟩
    rw [mem_preimage, e.left_inv hxsrc]
    exact hx
  have htopen : IsOpen (e.target ∩ e.symm ⁻¹' U) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hU
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (htopen.mem_nhds hxt)
  let R := ρ / 2
  have hR : 0 < R := half_pos hρ
  have hRsub : Metric.closedBall (e x) R ⊆ e.target ∩ e.symm ⁻¹' U := by
    intro z hz
    exact hρsub (Metric.closedBall_subset_ball (half_lt_self hρ) hz)
  let V := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have hV : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxsrc, Metric.mem_ball_self hR⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hmem := (hRsub (Metric.ball_subset_closedBall hy.2)).2
    change e.symm (e y) ∈ U at hmem
    rwa [e.left_inv hy.1] at hmem
  refine ⟨V, hV.mem_nhds hxV, hVU, ?_⟩
  intro y hy
  obtain ⟨D, hD, hDi, hD0, hmove, hfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_isotopy_translate_on_closedBall
      (e x) (e y) (r := 0) (R := R) le_rfl (by
        have h := Metric.mem_ball.mp hy.2
        simpa only [zero_add, dist_eq_norm] using h)
  have hD1 : D 1 (e x) = e y := by
    simpa using hmove (e x) (Metric.mem_closedBall_self le_rfl)
  obtain ⟨J, hJ, hJi, hJe, hK, _, hJfix⟩ :=
    Manifold.exists_diffeomorph_extension_of_partial_chart_family e
      c.contMDiffOn_toFun c.contMDiffOn_invFun D hD hDi
      (isCompact_closedBall (e x) R) (fun z hz => (hRsub hz).1) hfix
  refine ⟨J, ?_, ?_, hJ, hJi, e.symm '' Metric.closedBall (e x) R, hK, ?_, hJfix⟩
  · apply Diffeomorph.ext
    intro z
    rw [(hJe 0 z).1, hD0, Manifold.extendChartById]
    by_cases hz : z ∈ e.source
    · simp only [ite_eq_left hz, Diffeomorph.coe_refl, id_eq, e.left_inv hz]
    · simp only [ite_eq_right hz, Diffeomorph.coe_refl, id_eq]
  · rw [(hJe 1 x).1, Manifold.extendChartById, ite_eq_left hxsrc, hD1, e.left_inv hy.1]
  · rintro z ⟨w, hw, rfl⟩
    exact (hRsub hw).2

theorem exists_supported_isotopy_apply_eq_of_isPreconnected
    (U : Set M) (hU : IsOpen U) (hc : IsPreconnected U)
    (x y : M) (hx : x ∈ U) (hy : y ∈ U) :
    ∃ J : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      J 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞ ∧ J 1 x = y ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => (J q.1).symm q.2) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
        ∀ t z, z ∉ K → J t z = z ∧ (J t).symm z = z := by
  let R (p q : M) : Prop :=
    ∃ J : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      J 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞ ∧ J 1 p = q ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun z : ℝ × M => J z.1 z.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun z : ℝ × M => (J z.1).symm z.2) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
        ∀ t z, z ∉ K → J t z = z ∧ (J t).symm z = z
  have hrefl (p : M) : R p p := by
    refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, E) M ∞, rfl, rfl, ?_, ?_,
      ∅, isCompact_empty, empty_subset _, ?_⟩
    · exact contMDiff_snd
    · exact contMDiff_snd
    · exact fun _ _ _ => ⟨rfl, rfl⟩
  have hsymm {p q : M} (hpq : R p q) : R q p := by
    obtain ⟨J, hJ0, hJ1, hJ, hJi, K, hK, hKU, hfix⟩ := hpq
    refine ⟨fun t => (J t).symm, ?_, ?_, hJi, ?_, K, hK, hKU, ?_⟩
    · simp only [hJ0, Diffeomorph.symm_refl]
    · rw [← hJ1, (J 1).symm_apply_apply]
    · change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun z : ℝ × M => J z.1 z.2)
      exact hJ
    · intro t z hz
      exact ⟨(hfix t z hz).2, (hfix t z hz).1⟩
  have htrans {p q r : M} (hpq : R p q) (hqr : R q r) : R p r := by
    obtain ⟨F, hF0, hF1, hF, hFi, K, hK, hKU, hfix⟩ := hpq
    obtain ⟨G, hG0, hG1, hG, hGi, L, hL, hLU, hgfix⟩ := hqr
    refine ⟨fun t => (F t).trans (G t), ?_, ?_, ?_, ?_,
      K ∪ L, hK.union hL, union_subset hKU hLU, ?_⟩
    · apply Diffeomorph.ext
      intro z
      change G 0 (F 0 z) = z
      simp only [hF0, hG0, Diffeomorph.coe_refl, id_eq]
    · change G 1 (F 1 p) = r
      rw [hF1, hG1]
    · change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun z : ℝ × M => G z.1 (F z.1 z.2))
      exact hG.comp (contMDiff_fst.prodMk hF)
    · change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun z : ℝ × M => (F z.1).symm ((G z.1).symm z.2))
      exact hFi.comp (contMDiff_fst.prodMk hGi)
    · intro t z hz
      have hzK : z ∉ K := fun h => hz (Or.inl h)
      have hzL : z ∉ L := fun h => hz (Or.inr h)
      constructor
      · change G t (F t z) = z
        rw [(hfix t z hzK).1, (hgfix t z hzL).1]
      · change (F t).symm ((G t).symm z) = z
        rw [(hgfix t z hzL).2, (hfix t z hzK).2]
  let S : Set U := {z | R x z.val}
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨V, hV, _, hlocal⟩ :=
      exists_supported_isotopy_apply_eq_of_mem_nhds (E := E) U hU z.val z.property
    apply Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hV)
    intro w hw
    exact htrans hz (hlocal w.val hw)
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨V, hV, _, hlocal⟩ :=
      exists_supported_isotopy_apply_eq_of_mem_nhds (E := E) U hU z.val z.property
    apply Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hV)
    intro w hw hwS
    exact hz (htrans hwS (hsymm (hlocal w.val hw)))
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hc
  have hne : S.Nonempty := ⟨⟨x, hx⟩, hrefl x⟩
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  have hyS : (⟨y, hy⟩ : U) ∈ S := by
    rw [hSuniv]
    exact mem_univ _
  exact hyS

end SupportedIsotopy

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [PreconnectedSpace M]

theorem exists_supported_diffeomorph_apply_eq_of_mem_nhds
    (o : ManifoldOrientation (𝓡 3) M 3) (U : Set M) (hU : IsOpen U)
    (x : M) (hx : x ∈ U) :
    ∃ V ∈ 𝓝 x, V ⊆ U ∧ ∀ z ∈ V,
      ∃ (F : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) (K : Set M),
        IsCompact K ∧ K ⊆ U ∧ F.preservesOrientation o o ∧ F x = z ∧
        ∀ y ∉ K, F y = y ∧ F.symm y = y := by
  obtain ⟨V, hV, hVU, hlocal⟩ :=
    exists_supported_isotopy_apply_eq_of_mem_nhds (E := E3) U hU x hx
  refine ⟨V, hV, hVU, ?_⟩
  intro z hz
  obtain ⟨J, hJ0, hJ1, hJ, _, K, hK, hKU, hfix⟩ := hlocal z hz
  exact ⟨J 1, K, hK, hKU,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_jointlySmooth_isotopy
      o J hJ0 hJ 1, hJ1, hfix 1⟩

theorem exists_supported_diffeomorph_apply_eq_of_isPreconnected
    (o : ManifoldOrientation (𝓡 3) M 3) (U : Set M) (hU : IsOpen U) (hc : IsPreconnected U)
    (x y : M) (hx : x ∈ U) (hy : y ∈ U) :
    ∃ (F : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) (K : Set M),
      IsCompact K ∧ K ⊆ U ∧ F.preservesOrientation o o ∧ F x = y ∧
      ∀ z ∉ K, F z = z ∧ F.symm z = z := by
  obtain ⟨J, hJ0, hJ1, hJ, _, K, hK, hKU, hfix⟩ :=
    exists_supported_isotopy_apply_eq_of_isPreconnected (E := E3) U hU hc x y hx hy
  exact ⟨J 1, K, hK, hKU,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_jointlySmooth_isotopy
      o J hJ0 hJ 1, hJ1, hfix 1⟩

end DifferentialGeometry.Topology
