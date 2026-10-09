import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

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
  let φ := DifferentialGeometry.PartialDiffeomorph.extChartAt (𝓡 3) ∞ x
  let e := φ.toOpenPartialHomeomorph
  have hxsrc : x ∈ e.source := mem_extChartAt_source x
  have hxt : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨e.map_source hxsrc, ?_⟩
    rw [mem_preimage, e.left_inv hxsrc]
    exact hx
  have htopen : IsOpen (e.target ∩ e.symm ⁻¹' U) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hU
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (htopen.mem_nhds hxt)
  let R := ρ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hRsub : Metric.closedBall (e x) R ⊆ e.target ∩ e.symm ⁻¹' U := by
    intro q hq
    apply hρsub
    exact Metric.closedBall_subset_ball (by dsimp [R]; linarith) hq
  let v : E3 := EuclideanSpace.single 0 1
  have hv : ‖v‖ = 1 := by simp [v]
  let q₀ := e x + (2 * R) • v
  have hqdist : dist q₀ (e x) = 2 * R := by
    rw [dist_eq_norm]
    change ‖e x + (2 * R) • v - e x‖ = _
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity), hv, mul_one]
  have hq₀ : q₀ ∈ e.target :=
    (hρsub (Metric.mem_ball.mpr (by rw [hqdist]; dsimp [R]; linarith))).1
  have hqnot : q₀ ∉ Metric.closedBall (e x) R := by
    rw [Metric.mem_closedBall, hqdist]
    linarith
  have houtside : e.symm q₀ ∉ e.symm '' Metric.closedBall (e x) R := by
    rintro ⟨q, hq, he⟩
    have heq := e.symm.injOn (hRsub hq).1 hq₀ he
    exact hqnot (heq ▸ hq)
  let V := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have hV : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxsrc, Metric.mem_ball_self hR⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hmem := (hRsub (Metric.ball_subset_closedBall hy.2)).2
    change e.symm (e y) ∈ U at hmem
    rwa [e.left_inv hy.1] at hmem
  refine ⟨V, hV.mem_nhds hxV, hVU, ?_⟩
  intro z hz
  obtain ⟨D, hmove, hfix⟩ := DifferentialGeometry.Analysis.exists_compact_diffeomorph_translate_on_closedBall
    (e x) (e z) (r := 0) (R := R) le_rfl (by
      have h := Metric.mem_ball.mp hz.2
      simpa only [zero_add, dist_eq_norm] using h)
  have hD : D (e x) = e z := by
    simpa using hmove (e x) (Metric.mem_closedBall_self le_rfl)
  obtain ⟨J, _, _, hJe, hKc, _, hJfix⟩ :=
    Manifold.exists_diffeomorph_extension_of_partial_chart_family e φ.contMDiffOn_toFun
      φ.contMDiffOn_invFun (fun _ : ℝ => D)
      (D.contDiff.comp contDiff_snd) (D.symm.contDiff.comp contDiff_snd)
      (isCompact_closedBall (e x) R) (fun q hq => (hRsub hq).1) (fun _ q hq => hfix q hq)
  have hJo : (J 1).preservesOrientation o o := by
    apply Diffeomorph.preservesOrientation_of_eventuallyEq_id
    exact Filter.eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds houtside)
      (fun y hy => (hJfix 1 y hy).1)
  refine ⟨J 1, e.symm '' Metric.closedBall (e x) R, hKc, ?_, hJo, ?_, hJfix 1⟩
  · rintro y ⟨q, hq, rfl⟩
    exact (hRsub hq).2
  · rw [(hJe 1 x).1, Manifold.extendChartById, ite_eq_left hxsrc, hD, e.left_inv hz.1]

theorem exists_supported_diffeomorph_apply_eq_of_isPreconnected
    (o : ManifoldOrientation (𝓡 3) M 3) (U : Set M) (hU : IsOpen U) (hc : IsPreconnected U)
    (x y : M) (hx : x ∈ U) (hy : y ∈ U) :
    ∃ (F : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) (K : Set M),
      IsCompact K ∧ K ⊆ U ∧ F.preservesOrientation o o ∧ F x = y ∧
      ∀ z ∉ K, F z = z ∧ F.symm z = z := by
  let R (p q : M) : Prop := ∃ (F : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) (K : Set M),
    IsCompact K ∧ K ⊆ U ∧ F.preservesOrientation o o ∧ F p = q ∧
      ∀ z ∉ K, F z = z ∧ F.symm z = z
  have hrefl (p : M) : R p p :=
    ⟨Diffeomorph.refl (𝓡 3) M ∞, ∅, isCompact_empty, empty_subset _,
      Diffeomorph.preservesOrientation_refl o, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  have hsymm {p q : M} (h : R p q) : R q p := by
    obtain ⟨F, K, hK, hKU, hFo, hF, hfix⟩ := h
    refine ⟨F.symm, K, hK, hKU, Diffeomorph.preservesOrientation_symm hFo, ?_, ?_⟩
    · rw [← hF, F.symm_apply_apply]
    · intro z hz
      exact ⟨(hfix z hz).2, (hfix z hz).1⟩
  have htrans {p q r : M} (hpq : R p q) (hqr : R q r) : R p r := by
    obtain ⟨F, K, hK, hKU, hFo, hF, hfix⟩ := hpq
    obtain ⟨G, L, hL, hLU, hGo, hG, hgfix⟩ := hqr
    refine ⟨F.trans G, K ∪ L, hK.union hL, union_subset hKU hLU,
      Diffeomorph.preservesOrientation_trans hFo hGo, ?_, ?_⟩
    · change G (F p) = r
      rw [hF, hG]
    · intro z hz
      have hzK : z ∉ K := fun h => hz (Or.inl h)
      have hzL : z ∉ L := fun h => hz (Or.inr h)
      constructor
      · change G (F z) = z
        rw [(hfix z hzK).1, (hgfix z hzL).1]
      · change F.symm (G.symm z) = z
        rw [(hgfix z hzL).2, (hfix z hzK).2]
  let S : Set U := {z | R x z.val}
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨V, hV, _, hlocal⟩ := exists_supported_diffeomorph_apply_eq_of_mem_nhds o U hU z.val z.property
    apply Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hV)
    intro w hw
    exact htrans hz (hlocal w.val hw)
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨V, hV, _, hlocal⟩ := exists_supported_diffeomorph_apply_eq_of_mem_nhds o U hU z.val z.property
    apply Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hV)
    intro w hw hwS
    exact hz (htrans hwS (hsymm (hlocal w.val hw)))
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hc
  have hne : S.Nonempty := ⟨⟨x, hx⟩, hrefl x⟩
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  have hyS : (⟨y, hy⟩ : U) ∈ S := hSuniv ▸ mem_univ _
  exact hyS

end DifferentialGeometry.Topology
