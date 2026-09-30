import DifferentialGeometry.Topology.Manifold.ManifoldIsotopyExtension
import DifferentialGeometry.Topology.Manifold.EmbeddedBallContraction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransitionDet
import DifferentialGeometry.Topology.Manifold.IsotopyOrientation

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

private theorem exists_compact_isotopy_eqOn_small_ballCharts_of_center_eq
    (c d : BallChart 3 (𝓡 3) M) (hc : c.chart (0 : E3) = d.chart (0 : E3))
    (hdet : 0 < (fderiv ℝ (fun x : E3 => d.chart.symm (c.chart x)) 0).det)
    {V : Set M} (hV : IsOpen V) (hcV : c.chart '' closedBall 0 2 ⊆ V)
    (hdV : d.chart '' closedBall 0 2 ⊆ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∃ J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
        ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => J q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => (J q.1).symm q.2) ∧
        J 0 = Diffeomorph.refl (𝓡 3) M ∞ ∧
        (∀ x ∈ closedBall (0 : E3) ρ, J 1 (c.chart x) = d.chart x) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ V ∧
          ∀ t x, x ∉ K → J t x = x ∧ (J t).symm x = x := by
  have h02 : (0 : E3) ∈ closedBall (0 : E3) 2 := mem_closedBall_self (by norm_num)
  have hc0 := c.closedBall_subset_source h02
  have hd0 := d.closedBall_subset_source h02
  have htarget : d.chart.target ∈ 𝓝 (c.chart (0 : E3)) := by
    rw [hc]
    exact d.chart.open_target.mem_nhds (d.chart.map_source hd0)
  have hcont : ContinuousAt (c.chart : E3 → M) 0 :=
    c.chart.contMDiffOn_toFun.continuousOn.continuousAt (c.chart.open_source.mem_nhds hc0)
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hcont.preimage_mem_nhds htarget)
  let ρ := min r 1
  have hρ : 0 < ρ := lt_min hr zero_lt_one
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρ2 : ρ ≤ 2 := hρ1.trans (by norm_num)
  have hρr : ρ ≤ r := min_le_left _ _
  have hsub : closedBall (0 : E3) ρ ⊆ closedBall (0 : E3) 2 :=
    closedBall_subset_closedBall hρ2
  have hover (x : E3) (hx : x ∈ closedBall (0 : E3) ρ) : c.chart x ∈ d.chart.target :=
    hrsub (closedBall_subset_closedBall hρr hx)
  let ψ := c.chart.trans d.chart.symm
  let W : Set E3 := d.chart.source ∩ d.chart ⁻¹' V
  have hW : IsOpen W := d.chart.toOpenPartialHomeomorph.isOpen_inter_preimage hV
  have hψsrc : closedBall (0 : E3) ρ ⊆ ψ.source := by
    intro x hx
    rw [PartialDiffeomorph.trans_source]
    exact ⟨c.closedBall_subset_source (hsub hx), hover x hx⟩
  have hψW : ψ '' closedBall (0 : E3) ρ ⊆ W := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨d.chart.symm.map_source (hover x hx), ?_⟩
    change d.chart (d.chart.symm (c.chart x)) ∈ V
    rw [PartialDiffeomorph.apply_symm_apply d.chart (hover x hx)]
    exact hcV ⟨x, hsub hx, rfl⟩
  let e : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    (Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞).toPartialDiffeomorph
  have heW : e '' closedBall (0 : E3) ρ ⊆ W := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨d.closedBall_subset_source (hsub hx), hdV ⟨x, hsub hx, rfl⟩⟩
  have hψ0 : ψ (0 : E3) = 0 := by
    change d.chart.symm (c.chart (0 : E3)) = 0
    rw [hc]
    exact d.chart.left_inv hd0
  have he0 : e (0 : E3) = 0 := rfl
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • ψ 0 + t • e 0 ∈ W := by
    intro t _
    rw [hψ0, he0, smul_zero, smul_zero, zero_add]
    exact ⟨hd0, hdV ⟨0, h02, rfl⟩⟩
  have hedet : (fderiv ℝ (e : E3 → E3) 0).det = 1 := by
    change (fderiv ℝ (id : E3 → E3) 0).det = 1
    rw [fderiv_id]
    exact map_one _
  have hori : 0 < (fderiv ℝ (ψ : E3 → E3) 0).det * (fderiv ℝ (e : E3 → E3) 0).det := by
    rw [hedet, mul_one]
    exact hdet
  obtain ⟨D, hD, hDi, hD0, hDact, K, hK, hKW, hDfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius
      ψ e hρ hψsrc (fun _ _ => mem_univ _) hW hψW heW hseg hori
  obtain ⟨J, hJ, hJi, hJe, hJK, _, hJfix⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family d.chart.symm.toOpenPartialHomeomorph
      d.chart.contMDiffOn_invFun d.chart.contMDiffOn_toFun D hD hDi hK
      (fun z hz => (hKW hz).1) hDfix
  refine ⟨ρ, hρ, hρ1, J, hJ, hJi, ?_, ?_, d.chart '' K, hJK, ?_, hJfix⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 0 x).1, hD0]
    change extendChartById d.chart.symm.toOpenPartialHomeomorph
      (Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞) x = x
    unfold extendChartById
    split_ifs with hx
    · exact d.chart.symm.left_inv hx
    · rfl
  · intro x hx
    rw [(hJe 1 (c.chart x)).1]
    unfold extendChartById
    rw [ite_eq_left (show c.chart x ∈ d.chart.symm.toOpenPartialHomeomorph.source from hover x hx)]
    change d.chart (D 1 (ψ x)) = d.chart x
    rw [hDact x hx]
    rfl
  · rintro x ⟨z, hz, rfl⟩
    exact (hKW hz).2

theorem exists_compact_isotopy_eqOn_ballCharts_of_center_eq
    (c d : BallChart 3 (𝓡 3) M) (hc : c.chart (0 : E3) = d.chart (0 : E3))
    (hdet : 0 < (fderiv ℝ (fun x : E3 => d.chart.symm (c.chart x)) 0).det)
    {V : Set M} (hV : IsOpen V) (hcV : c.chart '' closedBall 0 2 ⊆ V)
    (hdV : d.chart '' closedBall 0 2 ⊆ V) :
    ∃ J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 3) M ∞ ∧
      (∀ x ∈ closedBall (0 : E3) 2, J 1 (c.chart x) = d.chart x) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ V ∧
        ∀ t x, x ∉ K → J t x = x ∧ (J t).symm x = x := by
  obtain ⟨ρ, hρ, hρ1, A, hA, hAi, hA0, hAact, KA, hKA, hKAV, hAfix⟩ :=
    exists_compact_isotopy_eqOn_small_ballCharts_of_center_eq c d hc hdet hV hcV hdV
  obtain ⟨C, hC, hCi, hC0, hCact, KC, hKC, hKCV, _, hCfix⟩ :=
    exists_diffeomorphs_contracting_embedded_closedBall c.chart (by norm_num : (0 : ℝ) < 2)
      c.closedBall_subset_source hV hcV
  obtain ⟨D, hD, hDi, hD0, hDact, KD, hKD, hKDV, _, hDfix⟩ :=
    exists_diffeomorphs_contracting_embedded_closedBall d.chart (by norm_num : (0 : ℝ) < 2)
      d.closedBall_subset_source hV hdV
  let ε : ℝ := ρ / 2
  have hε : 0 < ε := half_pos hρ
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith
  let T : ℝ := -Real.log ε
  have hT : 0 ≤ T := neg_nonneg.mpr (Real.log_nonpos hε.le hε1)
  have hexp : Real.exp (-T) = ε := by simp only [T, neg_neg, Real.exp_log hε]
  let J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞ :=
    fun t => ((C (t * T)).trans (A t)).trans (D (t * T)).symm
  have htime : ContMDiff (𝓘(ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
      (fun q : ℝ × M => q.1 * T) := contMDiff_fst.mul contMDiff_const
  have hJ : ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => J q.1 q.2) :=
    hDi.comp (htime.prodMk (hA.comp (contMDiff_fst.prodMk
      (hC.comp (htime.prodMk contMDiff_snd)))))
  have hJi : ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M => (J q.1).symm q.2) :=
    hCi.comp (htime.prodMk (hAi.comp (contMDiff_fst.prodMk
      (hD.comp (htime.prodMk contMDiff_snd)))))
  refine ⟨J, hJ, hJi, ?_, ?_, KC ∪ KA ∪ KD, (hKC.union hKA).union hKD,
    union_subset (union_subset hKCV hKAV) hKDV, ?_⟩
  · apply Diffeomorph.ext
    intro x
    change (D (0 * T)).symm (A 0 (C (0 * T) x)) = x
    rw [zero_mul, hC0, hA0, hD0]
    rfl
  · intro x hx
    have hεx : ε • x ∈ closedBall (0 : E3) ρ := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      have hx2 := mem_closedBall_zero_iff.mp hx
      dsimp only [ε]
      nlinarith
    change (D (1 * T)).symm (A 1 (C (1 * T) (c.chart x))) = d.chart x
    rw [one_mul, hCact T x hT hx, hexp, hAact _ hεx]
    have hd := hDact T x hT hx
    rw [hexp] at hd
    rw [← hd, Diffeomorph.symm_apply_apply]
  · intro t x hx
    have hxC : x ∉ KC := fun h => hx (Or.inl (Or.inl h))
    have hxA : x ∉ KA := fun h => hx (Or.inl (Or.inr h))
    have hxD : x ∉ KD := fun h => hx (Or.inr h)
    have he : J t x = x := by
      change (D (t * T)).symm (A t (C (t * T) x)) = x
      rw [(hCfix _ _ hxC).1, (hAfix _ _ hxA).1, (hDfix _ _ hxD).2]
    refine ⟨he, ?_⟩
    have hi := (J t).symm_apply_apply x
    rw [he] at hi
    exact hi

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.OrientedBallChart

universe u

variable {M : ClosedOrientedManifold.{u} 3} [PreconnectedSpace M.Carrier]

theorem exists_compact_diffeomorph_of_center_eq
    (c d : OrientedBallChart M)
    (hc : c.chart (0 : EuclideanSpace ℝ (Fin 3)) = d.chart (0 : EuclideanSpace ℝ (Fin 3)))
    {V : Set M.Carrier} (hV : IsOpen V)
    (hcV : c.chart '' closedBall 0 2 ⊆ V) (hdV : d.chart '' closedBall 0 2 ⊆ V) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞,
      F.preservesOrientation M.orientation M.orientation ∧
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, F (c.chart x) = d.chart x) ∧
      ∃ K : Set M.Carrier, IsCompact K ∧ K ⊆ V ∧
        ∀ x ∉ K, F x = x ∧ F.symm x = x := by
  obtain ⟨J, hJ, _, hJ0, hJact, K, hK, hKV, hJfix⟩ :=
    Manifold.exists_compact_isotopy_eqOn_ballCharts_of_center_eq c.toBallChart d.toBallChart
      hc (det_fderiv_chartTransition_pos c d (by
        first
        | exact hc
        | rw [hc]
          exact d.chart.map_source (d.closedBall_subset_source (mem_closedBall_self (by norm_num)))))
      hV hcV hdV
  exact ⟨J 1,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.preservesOrientation_of_jointlySmooth_isotopy
      M.orientation J hJ0 hJ 1,
    hJact, K, hK, hKV, hJfix 1⟩

end DifferentialGeometry.Topology.OrientedBallChart
