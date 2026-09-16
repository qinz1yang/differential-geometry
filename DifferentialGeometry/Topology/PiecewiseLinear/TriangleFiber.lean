import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem bijOn_snd_triangle_fiber_of_monotone {b : ℝ × ℝ → ℝ} {r t : ℝ}
    (hb : ContinuousOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1))
    (hr : AntitoneOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1))
    (ht : t ∈ Icc (0 : ℝ) 1) (hbt : b (0, t) = r) :
    BijOn Prod.snd {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r}
      (Icc 0 t) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨⟨hx, hy, hxy⟩, hbxy⟩
    have hy1 : y ≤ 1 := by linarith
    refine ⟨hy, le_of_not_gt fun hty => ?_⟩
    have h₁ := hl ht ⟨hy, hy1⟩ hty
    have h₂ := (hh y ⟨hy, hy1⟩).monotoneOn
      (show (0 : ℝ) ∈ Icc 0 (1 - y) from ⟨le_rfl, by linarith⟩)
      (show x ∈ Icc 0 (1 - y) from ⟨hx, by linarith⟩) hx
    dsimp at h₁ h₂
    linarith
  · rintro ⟨x, y⟩ ⟨⟨hx, hy, hxy⟩, hbxy⟩ ⟨x', y'⟩ ⟨⟨hx', hy', hx'y'⟩, hbx'y'⟩ hyy
    change y = y' at hyy
    subst y'
    have hy1 : y ≤ 1 := by linarith
    have hxx := (hh y ⟨hy, hy1⟩).injOn
      (show x ∈ Icc 0 (1 - y) from ⟨hx, by linarith⟩)
      (show x' ∈ Icc 0 (1 - y) from ⟨hx', by linarith⟩)
      (hbxy.trans hbx'y'.symm)
    exact Prod.ext hxx rfl
  · intro y hy
    have hy1 : y ≤ 1 := hy.2.trans ht.2
    have hleft : b (0, y) ≤ r := by
      rw [← hbt]
      exact hl.monotoneOn ⟨hy.1, hy1⟩ ht hy.2
    have hright : r ≤ b (1 - y, y) := by
      rw [← hbt]
      exact ((hh t ht).monotoneOn ⟨le_rfl, by linarith [ht.2]⟩
        ⟨by linarith [ht.2], le_rfl⟩ (by linarith [ht.2])).trans
        (hr ⟨hy.1, hy1⟩ ht hy.2)
    have hcont : ContinuousOn (fun x => b (x, y)) (Icc 0 (1 - y)) := by
      apply hb.comp (continuous_id.prodMk continuous_const).continuousOn
      rintro x ⟨hx, hxy⟩
      change 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1
      exact ⟨hx, hy.1, by linarith⟩
    obtain ⟨x, hx, hbx⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ 1 - y)
      hcont ⟨hleft, hright⟩
    exact ⟨(x, y), ⟨⟨hx.1, hy.1, by linarith [hx.2]⟩, hbx⟩, rfl⟩

theorem exists_bijOn_snd_triangle_fiber_of_monotone {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hb : ContinuousOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1))
    (hr : AntitoneOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1))
    (h₀ : b (0, 0) < r) (h₁ : r ≤ b (0, 1)) :
    ∃ t ∈ Ioc (0 : ℝ) 1, b (0, t) = r ∧
      BijOn Prod.snd {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r}
        (Icc 0 t) := by
  have hcont : ContinuousOn (fun y => b (0, y)) (Icc (0 : ℝ) 1) := by
    apply hb.comp (continuous_const.prodMk continuous_id).continuousOn
    intro y hy
    exact ⟨le_rfl, hy.1, by simpa using hy.2⟩
  obtain ⟨t, ht, hbt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hcont ⟨h₀.le, h₁⟩
  have htpos : 0 < t := lt_of_le_of_ne ht.1 fun ht0 => by
    subst t
    exact h₀.ne hbt
  exact ⟨t, ⟨htpos, ht.2⟩, hbt, bijOn_snd_triangle_fiber_of_monotone hb hh hl hr ht hbt⟩

theorem exists_bijOn_snd_triangle_fiber {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hb : ContinuousOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1))
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      BijOn Prod.snd {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r}
        (Icc 0 t) := by
  by_cases hmid : r ≤ b (0, 1)
  · obtain ⟨t, ht, -, hbij⟩ := exists_bijOn_snd_triangle_fiber_of_monotone
      hb hh hl hr.antitoneOn h₀ hmid
    exact ⟨t, ht, hbij⟩
  let σ : ℝ × ℝ → ℝ × ℝ := fun z => (1 - z.2 - z.1, z.2)
  let c : ℝ × ℝ → ℝ := fun z => -b (σ z)
  have hσcont : Continuous σ := by fun_prop
  have hσinv : Function.Involutive σ := by
    intro z
    apply Prod.ext
    · dsimp [σ]
      ring
    · rfl
  have hσmem : MapsTo σ {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
      {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} := by
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    change 0 ≤ 1 - y - x ∧ 0 ≤ y ∧ 1 - y - x + y ≤ 1
    exact ⟨by linarith, hy, by linarith⟩
  have hc : ContinuousOn c {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} :=
    (hb.comp hσcont.continuousOn hσmem).neg
  have hch : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => c (x, y)) (Icc 0 (1 - y)) := by
    intro y hy x hx x' hx' hxx
    dsimp [c, σ]
    apply neg_lt_neg
    exact hh y hy ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
      ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)
  have hcl : StrictMonoOn (fun y => c (0, y)) (Icc (0 : ℝ) 1) := by
    intro y hy y' hy' hyy
    simpa [c, σ] using neg_lt_neg (hr hy hy' hyy)
  have hcr : AntitoneOn (fun y => c (1 - y, y)) (Icc (0 : ℝ) 1) := by
    intro y hy y' hy' hyy
    simpa [c, σ] using neg_le_neg (hl.monotoneOn hy hy' hyy)
  obtain ⟨t, ht, -, hbij⟩ := exists_bijOn_snd_triangle_fiber_of_monotone (r := -r) hc hch hcl hcr
    (by simpa [c, σ] using neg_lt_neg h₁)
    (by simpa [c, σ] using neg_le_neg (le_of_not_ge hmid))
  have hflip : BijOn σ
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r}
      {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ c z = -r} := by
    refine ⟨?_, hσinv.injective.injOn, ?_⟩
    · intro z hz
      refine ⟨hσmem hz.1, ?_⟩
      dsimp only [c]
      rw [hσinv z, hz.2]
    · intro z hz
      refine ⟨σ z, ⟨hσmem hz.1, ?_⟩, hσinv z⟩
      exact neg_injective hz.2
  have hcompose := hbij.comp hflip
  exact ⟨t, ht, hcompose⟩

theorem exists_isPLHomeomorphOn_snd_triangle_fiber {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1))
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      IsPLHomeomorphOn Prod.snd
        {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} (Icc 0 t) := by
  let T : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
  have hTclosed : IsClosed T := (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hTcompact : IsCompact T := by
    have hbox : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    apply hbox.of_isClosed_subset hTclosed
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨⟨hx, show x ≤ (1 : ℝ) by linarith⟩, ⟨hy, show y ≤ (1 : ℝ) by linarith⟩⟩
  have hcompact : IsCompact (T ∩ b ⁻¹' {r}) := by
    let : CompactSpace T := isCompact_iff_compactSpace.mp hTcompact
    have hclosed : IsClosed {z : T | b z = r} :=
      isClosed_eq hb.continuousOn.domRestrict continuous_const
    convert hclosed.isCompact.image continuous_subtype_val using 1
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, mem_ofPred_eq,
      Subtype.exists, exists_and_right, exists_eq_right, exists_prop]
  have hpoly : IsPolyhedron (T ∩ b ⁻¹' {r}) :=
    isPolyhedron_inter_preimage_of_isCompact hb (isHPolytope_singleton r) hcompact
  obtain ⟨t, ht, hbij⟩ := exists_bijOn_snd_triangle_fiber hb.continuousOn hh hl hr h₀ h₁
  refine ⟨t, ht, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly ?_ hbij⟩
  exact (isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ).mono_of_isPolyhedron hpoly (subset_univ _)

theorem isPLBall_triangle_fiber_of_monotone {b : ℝ × ℝ → ℝ} {r : ℝ}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)))
    (hl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1))
    (hr : StrictAntiOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1))
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    IsPLBall 1 {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} := by
  obtain ⟨t, ht, hPL⟩ := exists_isPLHomeomorphOn_snd_triangle_fiber hb hh hl hr h₀ h₁
  exact (isPLBall_Icc ht.1).of_isPLHomeomorphOn hPL.symm

private theorem strictMono_affine_add_of_lipschitz {u : ℝ → ℝ} {a : ℝ} {k : NNReal}
    (hu : LipschitzWith k u) (hk : (k : ℝ) < a) (c : ℝ) :
    StrictMono (fun x => a * x + c + u x) := by
  intro x y hxy
  have hbound := hu.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hxy)] at hbound
  have hdiff := (le_abs_self (u x - u y)).trans hbound
  have hslope := mul_lt_mul_of_pos_right hk (sub_pos.mpr hxy)
  dsimp only
  nlinarith

theorem exists_isPLHomeomorphOn_snd_triangle_fiber_of_lipschitz
    {b : ℝ × ℝ → ℝ} {r a c d : ℝ} {k : NNReal}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hLip : LipschitzWith k (fun z => b z - (a * z.1 + c * z.2 + d)))
    (hc : (k : ℝ) < c) (hac : (k : ℝ) < a - c)
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      IsPLHomeomorphOn Prod.snd
        {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} (Icc 0 t) := by
  let u : ℝ × ℝ → ℝ := fun z => b z - (a * z.1 + c * z.2 + d)
  have hu : LipschitzWith k u := hLip
  have ha : (k : ℝ) < a := by linarith [k.coe_nonneg]
  have hh : ∀ y ∈ Icc (0 : ℝ) 1,
      StrictMonoOn (fun x => b (x, y)) (Icc 0 (1 - y)) := by
    intro y _
    have hu' : LipschitzWith k (fun x => u (x, y)) := by
      simpa only [mul_one, Function.comp_def] using hu.comp (LipschitzWith.prodMk_right y)
    have hm := strictMono_affine_add_of_lipschitz hu' ha (c * y + d)
    have heq : (fun x => a * x + (c * y + d) + u (x, y)) = fun x => b (x, y) := by
      funext x
      dsimp [u]
      ring
    rw [heq] at hm
    exact hm.strictMonoOn _
  have hl : StrictMonoOn (fun y => b (0, y)) (Icc (0 : ℝ) 1) := by
    have hu' : LipschitzWith k (fun y => u (0, y)) := by
      simpa only [mul_one, Function.comp_def] using hu.comp (LipschitzWith.prodMk_left (0 : ℝ))
    have hm := strictMono_affine_add_of_lipschitz hu' hc d
    have heq : (fun y => c * y + d + u (0, y)) = fun y => b (0, y) := by
      funext y
      dsimp [u]
      ring
    rw [heq] at hm
    exact hm.strictMonoOn _
  have hr : StrictAntiOn (fun y => b (1 - y, y)) (Icc (0 : ℝ) 1) := by
    have hedge : LipschitzWith 1 (fun y : ℝ => (1 - y, y)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Prod.dist_eq, NNReal.coe_one, one_mul, Real.dist_eq]
      have heq : 1 - x - (1 - y) = -(x - y) := by ring
      rw [heq, abs_neg, max_self]
    have hu' : LipschitzWith k (fun y => -u (1 - y, y)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_neg_neg, Function.comp_apply, NNReal.coe_mul, NNReal.coe_one, mul_one]
        using (hu.comp hedge).dist_le_mul x y
    have hm := strictMono_affine_add_of_lipschitz hu' hac (-a - d)
    have heq : (fun y => (a - c) * y + (-a - d) + -u (1 - y, y)) =
        fun y => -b (1 - y, y) := by
      funext y
      dsimp [u]
      ring
    rw [heq] at hm
    intro y hy y' hy' hyy
    exact neg_lt_neg_iff.mp (hm hyy)
  exact exists_isPLHomeomorphOn_snd_triangle_fiber hb hh hl hr h₀ h₁

theorem isPLBall_triangle_fiber_of_lipschitz {b : ℝ × ℝ → ℝ} {r a c d : ℝ} {k : NNReal}
    (hb : IsPiecewiseAffineOn b {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1})
    (hLip : LipschitzWith k (fun z => b z - (a * z.1 + c * z.2 + d)))
    (hc : (k : ℝ) < c) (hac : (k : ℝ) < a - c)
    (h₀ : b (0, 0) < r) (h₁ : r < b (1, 0)) :
    IsPLBall 1 {z | (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) ∧ b z = r} := by
  obtain ⟨t, ht, hPL⟩ :=
    exists_isPLHomeomorphOn_snd_triangle_fiber_of_lipschitz hb hLip hc hac h₀ h₁
  exact (isPLBall_Icc ht.1).of_isPLHomeomorphOn hPL.symm

end DifferentialGeometry.Topology.PiecewiseLinear
