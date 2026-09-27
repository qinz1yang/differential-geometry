import DifferentialGeometry.Topology.Embedding.PeriodicCurve
import DifferentialGeometry.External.Schoenflies.Realization

open Set Metric

namespace DifferentialGeometry.Topology.Planar

private theorem exists_uniform_positive_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E} (hv : ContinuousOn v (Icc 0 2))
    (hne : ∀ x ∈ Icc (0 : ℝ) 2, v x ≠ 0) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      ∃ L : E →L[ℝ] ℝ, ‖L‖ = 1 ∧
        ∀ y ∈ Icc x (x + δ), 0 < L (v y) := by
  obtain ⟨c, hc, d, hd, hproj⟩ :=
    DifferentialGeometry.Analysis.exists_uniform_positive_functionals hv hne
  refine ⟨min (d / 2) 1, lt_min (half_pos hd) zero_lt_one, min_le_right _ _, ?_⟩
  intro x hx
  obtain ⟨L, hL, hpos⟩ := hproj x ⟨hx.1, by linarith [hx.2]⟩
  refine ⟨L, hL, ?_⟩
  intro y hy
  apply hc.trans (hpos y ?_ ?_)
  · exact ⟨hx.1.trans hy.1, by linarith [hy.2, hx.2, min_le_right (d / 2) (1 : ℝ)]⟩
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.1)]
    linarith [hy.2, min_le_left (d / 2) (1 : ℝ)]

private theorem segment_inter_segment_subset_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {a b c d : E}
    (hab : L a < L b) (hbc : L b ≤ L c) (hcd : L c < L d) :
    segment ℝ a b ∩ segment ℝ c d ⊆ {b} ∩ {c} := by
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨u, hu, rfl⟩ := hz.1
  obtain ⟨v, hv, heq⟩ := (segment_eq_image_lineMap ℝ c d) ▸ hz.2
  have heq' := congrArg L heq
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul] at heq'
  have hleft : (1 - u) * L a + u * L b ≤ L b := by nlinarith [hu.2]
  have hright : L c ≤ (1 - v) * L c + v * L d := by nlinarith [hv.1]
  have hu1 : u = 1 := by nlinarith [hu.2]
  have hv0 : v = 0 := by nlinarith [hv.1]
  rw [hu1, AffineMap.lineMap_apply_one]
  refine ⟨mem_singleton _, ?_⟩
  simpa [hu1, hv0] using heq.symm

private theorem strictMonoOn_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ v : ℝ → E} (hγ : Continuous γ) (hd : ∀ x, HasDerivAt γ (v x) x)
    (L : E →L[ℝ] ℝ) {a b : ℝ} (hpos : ∀ x ∈ Icc a b, 0 < L (v x)) :
    StrictMonoOn (fun x => L (γ x)) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) (L.continuous.comp hγ).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(L.hasFDerivAt.comp_hasDerivAt x (hd x)).deriv]
  exact hpos x (Ioo_subset_Icc_self hx)

private theorem exists_uniform_chord_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ v : ℝ → E} (hγ : Continuous γ) (hv : Continuous v)
    (hd : ∀ x, HasDerivAt γ (v x) x) (hne : ∀ x, v x ≠ 0)
    (hperiod : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1)) :
    ∃ η > 0, η ≤ 1 ∧ ∀ h ∈ Ioo (0 : ℝ) η,
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        x + h ≤ y → y + h ≤ 1 →
        segment ℝ (γ x) (γ (x + h)) ∩ segment ℝ (γ y) (γ (y + h)) ⊆
          {γ x, γ (x + h)} ∩ {γ y, γ (y + h)} := by
  obtain ⟨δ, hδ, hδ1, hprojection⟩ :=
    exists_uniform_positive_projection hv.continuousOn (fun x _ => hne x)
  obtain ⟨ε, hε, hsep⟩ := PeriodicCurve.exists_uniform_separation hγ hperiod hinj (half_pos hδ)
  obtain ⟨d, hdpos, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hγ.continuousOn : ContinuousOn γ (Icc (0 : ℝ) 2))) (ε / 4) (by positivity)
  refine ⟨min (δ / 4) d, lt_min (by positivity) hdpos, ?_, ?_⟩
  · exact (min_le_left _ _).trans (by linarith)
  intro h hh x hx y hy hxy hyh
  have hhδ : h < δ / 4 := hh.2.trans_le (min_le_left _ _)
  have hhd : h < d := hh.2.trans_le (min_le_right _ _)
  have hxy' : x < y := by linarith [hh.1]
  have hxh : x + h ≤ 1 := hxy.trans hy.2
  have hchord : ∀ a ∈ Icc (0 : ℝ) 1, a + h ≤ 1 →
      segment ℝ (γ a) (γ (a + h)) ⊆ ball (γ a) (ε / 4) := by
    intro a ha hah
    apply (convex_ball (γ a) (ε / 4)).segment_subset
    · exact mem_ball_self (by positivity)
    · have haa : dist (a + h) a < d := by
        simpa [Real.dist_eq, abs_of_pos hh.1] using hhd
      exact hunif (a + h) ⟨by linarith [ha.1, hh.1], by linarith⟩
        a ⟨ha.1, by linarith [ha.2]⟩ haa
  intro z hz
  by_cases hnear : y - x < δ / 2
  · obtain ⟨L, hL, hpos⟩ := hprojection x hx
    have hm := strictMonoOn_projection hγ hd L hpos
    have hxmem : x ∈ Icc x (x + δ) := ⟨le_rfl, by linarith⟩
    have hxhmem : x + h ∈ Icc x (x + δ) := ⟨by linarith [hh.1], by linarith⟩
    have hymem : y ∈ Icc x (x + δ) := ⟨hxy'.le, by linarith⟩
    have hyhmem : y + h ∈ Icc x (x + δ) := ⟨by linarith [hh.1], by linarith⟩
    obtain ⟨hzx, hzy⟩ := segment_inter_segment_subset_endpoints L
      (hm hxmem hxhmem (by linarith [hh.1]))
      (hm.monotoneOn hxhmem hymem hxy)
      (hm hymem hyhmem (by linarith [hh.1])) hz
    exact ⟨Or.inr hzx, Or.inl hzy⟩
  by_cases hwrap : 1 - δ / 2 < y - x
  · obtain ⟨L, hL, hpos⟩ := hprojection y hy
    have hm := strictMonoOn_projection hγ hd L hpos
    have hymem : y ∈ Icc y (y + δ) := ⟨le_rfl, by linarith⟩
    have hyhmem : y + h ∈ Icc y (y + δ) := ⟨by linarith [hh.1], by linarith⟩
    have hxmem : x + 1 ∈ Icc y (y + δ) := ⟨by linarith [hy.2, hx.1], by linarith⟩
    have hxhmem : (x + h) + 1 ∈ Icc y (y + δ) :=
      ⟨by linarith [hy.2, hx.1, hh.1], by linarith⟩
    have hz' : z ∈ segment ℝ (γ y) (γ (y + h)) ∩
        segment ℝ (γ (x + 1)) (γ ((x + h) + 1)) := by
      simpa only [hperiod x, hperiod (x + h), mem_inter_iff] using And.intro hz.2 hz.1
    obtain ⟨hzy, hzx⟩ := segment_inter_segment_subset_endpoints L
      (hm hymem hyhmem (by linarith [hh.1]))
      (hm.monotoneOn hyhmem hxmem (by linarith [hx.1]))
      (hm hxmem hxhmem (by linarith [hh.1])) hz'
    rw [hperiod x] at hzx
    exact ⟨Or.inl hzx, Or.inr hzy⟩
  · have hdist := hsep x hx y hy (le_of_not_gt hnear) (le_of_not_gt hwrap)
    have hzx := hchord x hx hxh hz.1
    have hzy := hchord y hy hyh hz.2
    have htri := dist_triangle (γ x) z (γ y)
    rw [dist_comm (γ x) z] at htri
    exact False.elim (by linarith [mem_ball.mp hzx, mem_ball.mp hzy])

private theorem periodic_mesh_succ
    {E : Type*} {γ : ℝ → E} (hperiod : Function.Periodic γ 1)
    (m : ℕ) (i : ZMod (m + 3)) :
    γ ((↑(i + 1).val : ℝ) / (m + 3)) =
      γ ((i.val : ℝ) / (m + 3) + 1 / (m + 3)) := by
  have hN : 0 < (m : ℝ) + 3 := by positivity
  have hval := ZMod.val_lt i
  rw [ZMod.val_add, ZMod.val_one'' (by omega)]
  by_cases hi : i.val + 1 < m + 3
  · rw [Nat.mod_eq_of_lt hi, Nat.cast_add, Nat.cast_one, add_div]
  · have hi' : i.val + 1 = m + 3 := by omega
    rw [hi', Nat.mod_self, Nat.cast_zero, zero_div]
    have hi'' : (i.val : ℝ) + 1 = (m : ℝ) + 3 := by exact_mod_cast hi'
    rw [← add_div, hi'', div_self hN.ne']
    symm
    simpa using hperiod 0

private theorem mesh_vertex_injective
    {E : Type*} {γ : ℝ → E} (hinj : InjOn γ (Ico (0 : ℝ) 1)) (m : ℕ) :
    Function.Injective (fun i : ZMod (m + 3) => γ ((i.val : ℝ) / (m + 3))) := by
  have hN : 0 < (m : ℝ) + 3 := by positivity
  have hmem (i : ZMod (m + 3)) : (i.val : ℝ) / (m + 3) ∈ Ico (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hN.le, (div_lt_one hN).mpr ?_⟩
    exact_mod_cast ZMod.val_lt i
  intro i j hij
  apply ZMod.val_injective (m + 3)
  have heq := hinj (hmem i) (hmem j) hij
  have heq' := (div_left_inj' hN.ne').mp heq
  exact_mod_cast heq'

theorem exists_inscribed_prePolygon
    {γ v : ℝ → Schoenflies.Plane} (hv : Continuous v)
    (hd : ∀ x, HasDerivAt γ (v x) x) (hne : ∀ x, v x ≠ 0)
    (hperiod : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ P : Schoenflies.PrePolygon m,
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = γ ((i.val : ℝ) / (m + 3))) ∧
      ∀ i : ZMod (m + 3), ∃ L : Schoenflies.Plane →L[ℝ] ℝ,
        ‖L‖ = 1 ∧ ∀ x ∈ Icc ((i.val : ℝ) / (m + 3))
          ((i.val : ℝ) / (m + 3) + 2 / (m + 3)), 0 < L (v x) := by
  have hγ : Continuous γ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  obtain ⟨η, hη, hη1, hchords⟩ := exists_uniform_chord_intersection hγ hv hd hne hperiod hinj
  obtain ⟨δ, hδ, hδ1, hprojection⟩ :=
    exists_uniform_positive_projection hv.continuousOn (fun x _ => hne x)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt
    (lt_min hη (lt_min (by positivity : 0 < δ / 3) hε))
  have hN : 0 < (m : ℝ) + 3 := by positivity
  have hmesh : 1 / (m + 3 : ℝ) < min η (min (δ / 3) ε) :=
    (one_div_le_one_div_of_le (by positivity) (by linarith :
      (m : ℝ) + 1 ≤ m + 3)).trans_lt hm
  have hmesha : 1 / (m + 3 : ℝ) < η := hmesh.trans_le (min_le_left _ _)
  have hmeshb : 1 / (m + 3 : ℝ) < δ / 3 :=
    hmesh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hmeshc : 1 / (m + 3 : ℝ) < ε :=
    hmesh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let p : ZMod (m + 3) → Schoenflies.Plane := fun i => γ ((i.val : ℝ) / (m + 3))
  have hmem (i : ZMod (m + 3)) : (i.val : ℝ) / (m + 3) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hN.le, (div_le_one hN).mpr ?_⟩
    exact_mod_cast (ZMod.val_lt i).le
  have hend (i : ZMod (m + 3)) :
      (i.val : ℝ) / (m + 3) + 1 / (m + 3) ≤ 1 := by
    rw [← add_div, div_le_one hN]
    exact_mod_cast Nat.succ_le_of_lt (ZMod.val_lt i)
  have hsucc (i : ZMod (m + 3)) :
      p (i + 1) = γ ((i.val : ℝ) / (m + 3) + 1 / (m + 3)) :=
    periodic_mesh_succ hperiod m i
  have hordered (i j : ZMod (m + 3)) (hij : i.val < j.val) :
      segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) ⊆
        {p i, p (i + 1)} ∩ {p j, p (j + 1)} := by
    rw [hsucc i, hsucc j]
    apply hchords (1 / (m + 3)) ⟨by positivity, hmesha⟩
      _ (hmem i) _ (hmem j) _ (hend j)
    rw [← add_div, div_le_div_iff_of_pos_right hN]
    exact_mod_cast Nat.succ_le_of_lt hij
  have hedges (i j : ZMod (m + 3)) (hij : i ≠ j) :
      segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) ⊆
        {p i, p (i + 1)} := by
    have hval : i.val ≠ j.val := fun h => hij (ZMod.val_injective (m + 3) h)
    rcases lt_or_gt_of_ne hval with hi | hj
    · exact (hordered i j hi).trans inter_subset_left
    · intro z hz
      exact (hordered j i hj ⟨hz.2, hz.1⟩).2
  refine ⟨m, ⟨p, mesh_vertex_injective hinj m, hedges⟩, hmeshc, fun _ => rfl, ?_⟩
  intro i
  obtain ⟨L, hL, hpos⟩ := hprojection _ (hmem i)
  refine ⟨L, hL, fun x hx => hpos x ⟨hx.1, ?_⟩⟩
  have htwo : 2 / (m + 3 : ℝ) < δ := by
    rw [show 2 / (m + 3 : ℝ) = 2 * (1 / (m + 3)) by ring]
    linarith
  linarith [hx.2]

end DifferentialGeometry.Topology.Planar
