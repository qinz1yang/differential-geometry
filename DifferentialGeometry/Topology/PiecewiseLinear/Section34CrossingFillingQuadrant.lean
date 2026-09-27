import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleCharts
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem interior_subset_one_side_of_frontier_contact
    {M : Type*} [TopologicalSpace M] {R X : Set M} (hX : IsClosed X)
    (hreg : closure (interior R) = R) (hconn : IsPreconnected (interior R))
    (hcontact : R ∩ frontier X ⊆ frontier R) :
    (interior R ⊆ interior X ∧ R ⊆ X) ∨
      (interior R ⊆ Xᶜ ∧ R ⊆ closure Xᶜ) := by
  have hcover : interior R ⊆ interior X ∪ Xᶜ := by
    intro x hx
    by_cases hxX : x ∈ X
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxX).mpr
        fun hfr => (hcontact ⟨interior_subset hx, hfr⟩).2 hx)
    · exact Or.inr hxX
  rcases hconn.subset_or_subset isOpen_interior hX.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · exact Or.inl ⟨hin, hreg ▸ closure_minimal (hin.trans interior_subset) hX⟩
  · exact Or.inr ⟨hout, hreg ▸ closure_mono hout⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem filling_eq_positive_quadrant
    {R U : Set E} {x : E} {φ : E → ℝ × ℝ × ℝ} {ρ : ℝ}
    (hR : IsClosed R) (hU : IsOpen U) (hxU : x ∈ U)
    (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ))
    (hxR : x ∈ closure (interior R))
    (hsub : ∀ y ∈ U, y ∈ R → 0 ≤ (φ y).2.1 ∧ 0 ≤ (φ y).2.2)
    (hfront : ∀ y ∈ U, y ∈ frontier R → (φ y).2.1 = 0 ∨ (φ y).2.2 = 0)
    (havoid : ∀ y ∈ U, y ∈ interior R → (φ y).2.1 ≠ 0 ∧ (φ y).2.2 ≠ 0) :
    ∀ y ∈ U, y ∈ R ↔ 0 ≤ (φ y).2.1 ∧ 0 ≤ (φ y).2.2 := by
  let ψ := Function.invFunOn φ U
  let Q : Set (ℝ × ℝ × ℝ) := Metric.ball 0 ρ ∩ {z | 0 < z.2.1 ∧ 0 < z.2.2}
  have hψc : ContinuousOn ψ (Metric.ball 0 ρ) :=
    hφ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hψU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, ψ z ∈ U :=
    fun z hz => hφ.symm.bijOn.mapsTo hz
  have hφψ : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, φ (ψ z) = z :=
    fun z hz => hφ.bijOn.invOn_invFunOn.2 hz
  have hQ : IsPreconnected Q := by
    exact ((convex_ball _ _).inter ((convex_halfSpace_gt
      (((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear) 0).inter
      (convex_halfSpace_gt
        (((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear) 0))).isPreconnected
  have hdis : Disjoint (ψ '' Q) (frontier R) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ hfr
    have h := hfront (ψ z) (hψU z hz.1) hfr
    rw [hφψ z hz.1] at h
    exact h.elim hz.2.1.ne' hz.2.2.ne'
  have hmeet : ((ψ '' Q) ∩ R).Nonempty := by
    obtain ⟨y, hyU, hyR⟩ := mem_closure_iff_nhds.mp hxR U (hU.mem_nhds hxU)
    have hy := hsub y hyU (interior_subset hyR)
    have hn := havoid y hyU hyR
    refine ⟨y, ⟨φ y, ⟨hφ.bijOn.mapsTo hyU,
      lt_of_le_of_ne hy.1 hn.1.symm, lt_of_le_of_ne hy.2 hn.2.symm⟩,
      hφ.bijOn.invOn_invFunOn.1 hyU⟩, interior_subset hyR⟩
  have hQR : ψ '' Q ⊆ R :=
    IsPreconnected.subset_of_disjoint_frontier
      (hQ.image ψ (hψc.mono inter_subset_left)) hmeet hdis
  intro y hyU
  refine ⟨hsub y hyU, fun hy => ?_⟩
  have hzQ : φ y ∈ closure Q := by
    let f : ℝ → ℝ × ℝ × ℝ := fun t => ((φ y).1, (φ y).2.1 + t, (φ y).2.2 + t)
    have hfc : Continuous f := by fun_prop
    have hlim : Filter.Tendsto f (𝓝[>] 0) (𝓝 (φ y)) := by
      simpa only [f, add_zero, Prod.eta] using
        (hfc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hlim
    filter_upwards [hlim.eventually_mem (Metric.isOpen_ball.mem_nhds
      (hφ.bijOn.mapsTo hyU)), self_mem_nhdsWithin] with t ht hpos
    exact ⟨ht, add_pos_of_nonneg_of_pos hy.1 hpos, add_pos_of_nonneg_of_pos hy.2 hpos⟩
  have hmem := (hψc.continuousAt
    (Metric.isOpen_ball.mem_nhds (hφ.bijOn.mapsTo hyU))).continuousWithinAt.mem_closure_image hzQ
  change Function.invFunOn φ U (φ y) ∈ closure (ψ '' Q) at hmem
  rw [hφ.bijOn.invOn_invFunOn.1 hyU] at hmem
  exact closure_minimal hQR hR hmem

private theorem filling_side_of_frontier_plane
    {R X U : Set E} {x : E} {φ : E → ℝ × ℝ × ℝ} {ρ : ℝ}
    (hX : IsClosed X) (hreg : closure (interior R) = R)
    (hconn : IsPreconnected (interior R)) (hcontact : R ∩ frontier X ⊆ frontier R)
    (hU : IsOpen U) (hxU : x ∈ U) (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ))
    (hφx : φ x = 0) (hread : ∀ y ∈ U, y ∈ frontier X ↔ (φ y).2.1 = 0)
    (hxX : x ∈ closure (interior X)) :
    (∀ y ∈ U, y ∈ R → 0 ≤ (φ y).2.1) ∨
      ∀ y ∈ U, y ∈ R → (φ y).2.1 ≤ 0 := by
  have hside := side_of_frontier_plane hU hxU hφ hφx hread hX hxX
  have hRside := interior_subset_one_side_of_frontier_contact hX hreg hconn hcontact
  have hout (hR : R ⊆ closure Xᶜ) : ∀ y ∈ R, y ∉ interior X := by
    intro y hy
    have hh := hR hy
    rwa [closure_compl] at hh
  rcases hside with hpos | hneg
  · rcases hRside with ⟨-, hin⟩ | ⟨-, hex⟩
    · exact Or.inl fun y hy hyR => (hpos y hy).mp (hin hyR)
    · refine Or.inr fun y hy hyR => le_of_not_gt fun hh => ?_
      exact hout hex y hyR ((mem_interior_iff_notMem_frontier
        ((hpos y hy).mpr hh.le)).mpr fun hfr => hh.ne' ((hread y hy).mp hfr))
  · rcases hRside with ⟨-, hin⟩ | ⟨-, hex⟩
    · exact Or.inr fun y hy hyR => (hneg y hy).mp (hin hyR)
    · refine Or.inl fun y hy hyR => le_of_not_gt fun hh => ?_
      exact hout hex y hyR ((mem_interior_iff_notMem_frontier
        ((hneg y hy).mpr hh.le)).mpr fun hfr => hh.ne ((hread y hy).mp hfr))

private theorem exists_signed_coordinate_chart
    [FiniteDimensional ℝ E] {U : Set E} {φ : E → ℝ × ℝ × ℝ} {ρ a b : ℝ}
    (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ))
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ∃ χ : E → ℝ × ℝ × ℝ, IsPLHomeomorphOn χ U (Metric.ball 0 ρ) ∧
      ∀ y, χ y = ((φ y).1, a * (φ y).2.1, b * (φ y).2.2) := by
  have haa : a * a = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hbb : b * b = 1 := by rcases hb with rfl | rfl <;> norm_num
  let L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    { toFun := fun z => (z.1, a * z.2.1, b * z.2.2)
      invFun := fun z => (z.1, a * z.2.1, b * z.2.2)
      map_add' := fun z w => Prod.ext rfl (Prod.ext (mul_add _ _ _) (mul_add _ _ _))
      map_smul' := fun s z => by
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
            <;> ring
      left_inv := fun z => by simp only [← mul_assoc, haa, hbb, one_mul, Prod.eta]
      right_inv := fun z => by simp only [← mul_assoc, haa, hbb, one_mul, Prod.eta] }
  have hLn (z : ℝ × ℝ × ℝ) : ‖L z‖ = ‖z‖ := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [L, Prod.norm_def]
  have hLB : L '' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simpa only [mem_ball_zero_iff, hLn] using hz
    · intro z hz
      exact ⟨L z, by simpa only [mem_ball_zero_iff, hLn] using hz, L.apply_symm_apply z⟩
  have hLφ : IsPLHomeomorphOn (L ∘ φ) U (Metric.ball 0 ρ) := by
    simpa only [hLB] using hφ.trans (isPLHomeomorphOn_linearEquiv L Metric.isOpen_ball)
  exact ⟨L ∘ φ, hLφ, fun _ => rfl⟩

theorem HasPLCrossingAt.exists_quadrant_chart_of_filling [FiniteDimensional ℝ E]
    {R X Y : Set E} {x : E}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) (frontier X)]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) (frontier Y)]
    (hcross : HasPLCrossingAt (frontier X) (frontier Y) x)
    (hR : IsClosed R) (hreg : closure (interior R) = R)
    (hconn : IsPreconnected (interior R)) (hX : IsClosed X) (hY : IsClosed Y)
    (hcontactX : R ∩ frontier X ⊆ frontier R)
    (hcontactY : R ∩ frontier Y ⊆ frontier R)
    (hfront : frontier R ⊆ frontier X ∪ frontier Y)
    (hxR : x ∈ R) (hxX : x ∈ frontier X) (hxY : x ∈ frontier Y)
    (hXreg : x ∈ closure (interior X)) (hYreg : x ∈ closure (interior Y)) :
    ∃ (U : Set E) (φ : E → ℝ × ℝ × ℝ) (ρ : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧ IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ y ∈ U, (y ∈ frontier X ↔ (φ y).2.1 = 0) ∧
          (y ∈ frontier Y ↔ (φ y).2.2 = 0) ∧
          (y ∈ R ↔ 0 ≤ (φ y).2.1 ∧ 0 ≤ (φ y).2.2) := by
  obtain ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, hread⟩ :=
    hcross.symm.exists_full_plane_coordinate_chart hxY hxX
  have hRX := filling_side_of_frontier_plane hX hreg hconn hcontactX hU hxU hφ hφx
    (fun y hy => (hread y hy).2) hXreg
  let L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    (LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.prodComm ℝ ℝ ℝ)
  have hLn (z : ℝ × ℝ × ℝ) : ‖L z‖ = ‖z‖ := by simp [L, Prod.norm_def, max_comm]
  have hLB : L '' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simpa only [mem_ball_zero_iff, hLn] using hz
    · intro z hz
      exact ⟨L z, by simpa only [mem_ball_zero_iff, hLn] using hz, L.apply_symm_apply z⟩
  have hLφ : IsPLHomeomorphOn (L ∘ φ) U (Metric.ball 0 ρ) := by
    simpa only [hLB] using hφ.trans (isPLHomeomorphOn_linearEquiv L Metric.isOpen_ball)
  have hRY : (∀ y ∈ U, y ∈ R → 0 ≤ (φ y).2.2) ∨
      ∀ y ∈ U, y ∈ R → (φ y).2.2 ≤ 0 :=
    filling_side_of_frontier_plane hY hreg hconn hcontactY hU hxU hLφ
      (by simp only [Function.comp_apply, hφx, map_zero])
      (fun y hy => (hread y hy).1) hYreg
  obtain ⟨a, ha, hapos⟩ : ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ y ∈ U, y ∈ R → 0 ≤ a * (φ y).2.1 := by
    rcases hRX with hpos | hneg
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hpos⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, neg_nonneg] using hneg⟩
  obtain ⟨b, hb, hbpos⟩ : ∃ b : ℝ, (b = 1 ∨ b = -1) ∧
      ∀ y ∈ U, y ∈ R → 0 ≤ b * (φ y).2.2 := by
    rcases hRY with hpos | hneg
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hpos⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, neg_nonneg] using hneg⟩
  obtain ⟨χ, hχ, hχread⟩ := exists_signed_coordinate_chart hφ ha hb
  have ha0 : a ≠ 0 := by rcases ha with rfl | rfl <;> norm_num
  have hb0 : b ≠ 0 := by rcases hb with rfl | rfl <;> norm_num
  have hχX (y : E) (hy : y ∈ U) : y ∈ frontier X ↔ (χ y).2.1 = 0 := by
    rw [hχread, mul_eq_zero, or_iff_right ha0]
    exact (hread y hy).2
  have hχY (y : E) (hy : y ∈ U) : y ∈ frontier Y ↔ (χ y).2.2 = 0 := by
    rw [hχread, mul_eq_zero, or_iff_right hb0]
    exact (hread y hy).1
  have hquad : ∀ y ∈ U, y ∈ R ↔ 0 ≤ (χ y).2.1 ∧ 0 ≤ (χ y).2.2 := by
    apply filling_eq_positive_quadrant hR hU hxU hχ (hreg.symm ▸ hxR)
    · intro y hy hyR
      rw [hχread]
      exact ⟨hapos y hy hyR, hbpos y hy hyR⟩
    · intro y hy hyfr
      exact (hfront hyfr).imp (hχX y hy).mp (hχY y hy).mp
    · intro y hy hyint
      exact ⟨fun hz => (hcontactX ⟨interior_subset hyint, (hχX y hy).mpr hz⟩).2 hyint,
        fun hz => (hcontactY ⟨interior_subset hyint, (hχY y hy).mpr hz⟩).2 hyint⟩
  refine ⟨U, χ, ρ, hU, hxU, hρ, hχ, ?_, fun y hy => ⟨hχX y hy, hχY y hy, hquad y hy⟩⟩
  simp [hχread, hφx]

end DifferentialGeometry.Topology.PiecewiseLinear
