import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckDiskDistNK

/-!
# Route W, IMS06′ 的组装（S-W-NECK G4，后缀 `_NK`，第 1 部分：`diskEDist_NK` 的基本性质）

`q^*g` 的多边形内蕴距离 `diskEDist_NK`（G3 定义）的性质，供 IMS05′ 的消费者使用：
`d(z, z) = 0`，`d ≤` 线段长度，三角不等式（经链的拼接 `diskEDist_le_append_NK`），
以及闭球 `closedBall a ρ ⊆ 开圆盘` 上的局部 Lipschitz 界 `d(p, p') ≤ C ‖p' - p‖`
（来自 `exists_compact_source_mfderiv_bound`；`q` 在开盘内光滑即可，不用 `λ > 0`）。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section Basic

variable (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M))

omit [FiniteDimensional ℝ E] in
theorem diskEDist_le_sum_NK {n : ℕ} {c : ℕ → ℂ} {z w : ℂ} (hz : c 0 = z) (hw : c n = w)
    (hc : ∀ i ≤ n, c i ∈ Metric.ball (0 : ℂ) 1) :
    diskEDist_NK g q z w ≤ ∑ i ∈ Finset.range n, diskSegLength_NK g q (c i) (c (i + 1)) :=
  iInf_le_of_le n (iInf_le_of_le c (iInf_le_of_le ⟨hz, hw, hc⟩ le_rfl))

omit [FiniteDimensional ℝ E] in
theorem diskEDist_self_NK {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    diskEDist_NK g q z z = 0 := by
  have := diskEDist_le_sum_NK g q (n := 0) (c := fun _ => z) rfl rfl (fun _ _ => hz)
  simpa using this

omit [FiniteDimensional ℝ E] in
theorem diskEDist_le_seg_NK {p p' : ℂ} (hp : p ∈ Metric.ball (0 : ℂ) 1)
    (hp' : p' ∈ Metric.ball (0 : ℂ) 1) :
    diskEDist_NK g q p p' ≤ diskSegLength_NK g q p p' := by
  have := diskEDist_le_sum_NK g q (n := 1) (c := fun i => if i = 0 then p else p')
    (z := p) (w := p') (by simp) (by simp) (by
      intro i hi
      by_cases h : i = 0 <;> simp [h, hp, hp'])
  simpa using this

omit [FiniteDimensional ℝ E] in
theorem exists_chain_lt_NK {z w : ℂ} {r : ℝ≥0∞} (h : diskEDist_NK g q z w < r) :
    ∃ (n : ℕ) (c : ℕ → ℂ), c 0 = z ∧ c n = w ∧ (∀ i ≤ n, c i ∈ Metric.ball (0 : ℂ) 1) ∧
      ∑ i ∈ Finset.range n, diskSegLength_NK g q (c i) (c (i + 1)) < r := by
  unfold diskEDist_NK at h
  simp only [iInf_lt_iff] at h
  obtain ⟨n, c, hc, hlt⟩ := h
  exact ⟨n, c, hc.1, hc.2.1, hc.2.2, hlt⟩

omit [FiniteDimensional ℝ E] in
theorem diskEDist_le_append_NK {n₁ n₂ : ℕ} {c₁ c₂ : ℕ → ℂ} {z w u : ℂ}
    (h1 : c₁ 0 = z ∧ c₁ n₁ = w ∧ ∀ i ≤ n₁, c₁ i ∈ Metric.ball (0 : ℂ) 1)
    (h2 : c₂ 0 = w ∧ c₂ n₂ = u ∧ ∀ i ≤ n₂, c₂ i ∈ Metric.ball (0 : ℂ) 1) :
    diskEDist_NK g q z u ≤ ∑ i ∈ Finset.range n₁, diskSegLength_NK g q (c₁ i) (c₁ (i + 1)) +
      ∑ i ∈ Finset.range n₂, diskSegLength_NK g q (c₂ i) (c₂ (i + 1)) := by
  set c : ℕ → ℂ := fun i => if i ≤ n₁ then c₁ i else c₂ (i - n₁) with hcdef
  have hc1 : ∀ i ≤ n₁, c i = c₁ i := fun i hi => by simp [hcdef, hi]
  have hc2 : ∀ x, c (n₁ + x) = c₂ x := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp only [add_zero, hcdef, le_refl, ite_true]
      rw [h1.2.1, h2.1]
    · have : ¬ n₁ + x ≤ n₁ := by omega
      simp [hcdef, this]
  have hsum := diskEDist_le_sum_NK g q (n := n₁ + n₂) (c := c) (z := z) (w := u)
    (by rw [hc1 0 (Nat.zero_le _)]; exact h1.1)
    (by rw [hc2 n₂]; exact h2.2.1)
    (by
      intro i hi
      by_cases h : i ≤ n₁
      · rw [hc1 i h]; exact h1.2.2 i h
      · have : i = n₁ + (i - n₁) := by omega
        rw [this, hc2]
        exact h2.2.2 _ (by omega))
  refine hsum.trans ?_
  rw [Finset.sum_range_add]
  apply add_le_add
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n₁ := Finset.mem_range.mp hi
    rw [hc1 i hi'.le, hc1 (i + 1) hi']
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro x _
    rw [hc2 x, show n₁ + x + 1 = n₁ + (x + 1) by ring, hc2 (x + 1)]

omit [FiniteDimensional ℝ E] in
/-- 三角不等式（经开圆盘内的点 `w`）。 -/
theorem diskEDist_triangle_NK {z w u : ℂ} :
    diskEDist_NK g q z u ≤ diskEDist_NK g q z w + diskEDist_NK g q w u := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by
    simp [hε.ne']
  have ha : diskEDist_NK g q z w ≠ ⊤ := (ENNReal.add_lt_top.mp hb).1.ne
  have hb' : diskEDist_NK g q w u ≠ ⊤ := (ENNReal.add_lt_top.mp hb).2.ne
  obtain ⟨n₁, c₁, h1a, h1b, h1c, h1d⟩ :=
    exists_chain_lt_NK g q (ENNReal.lt_add_right ha hε2)
  obtain ⟨n₂, c₂, h2a, h2b, h2c, h2d⟩ :=
    exists_chain_lt_NK g q (ENNReal.lt_add_right hb' hε2)
  calc diskEDist_NK g q z u
      ≤ _ + _ := diskEDist_le_append_NK g q ⟨h1a, h1b, h1c⟩ ⟨h2a, h2b, h2c⟩
    _ ≤ (diskEDist_NK g q z w + (ε : ℝ≥0∞) / 2) + (diskEDist_NK g q w u + (ε : ℝ≥0∞) / 2) :=
        add_le_add h1d.le h2d.le
    _ = diskEDist_NK g q z w + diskEDist_NK g q w u + ε := by
        rw [show ∀ a b h : ℝ≥0∞, a + h + (b + h) = a + b + (h + h) from fun a b h => by ring,
          ENNReal.add_halves]

omit [FiniteDimensional ℝ E] in
/-- 局部 Lipschitz 界：闭球 `closedBall a ρ ⊆ 开圆盘` 上，`q^*g` 沿线段的长度 `≤ C ·` 欧氏长度。 -/
theorem exists_diskSegLength_le_NK {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    {a : ℂ} {ρ : ℝ} (hS : Metric.closedBall a ρ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ C : ℝ≥0, ∀ p ∈ Metric.closedBall a ρ, ∀ p' ∈ Metric.closedBall a ρ,
      diskSegLength_NK g q p p' ≤ (C : ℝ≥0∞) * (‖p' - p‖₊ : ℝ≥0∞) := by
  have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension q) (Metric.ball (0 : ℂ) 1) :=
    hq.of_le (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g (V := ℂ) Metric.isOpen_ball hf
    (isCompact_closedBall a ρ) hS
  refine ⟨C, fun p hp p' hp' => ?_⟩
  unfold diskSegLength_NK
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1, riemannianCurveSpeed g
      (diskExtension q ∘ fun t : ℝ => p + t • (p' - p)) t ≤ ((C * ‖p' - p‖₊ : ℝ≥0) : ℝ) := by
    intro t ht
    have hmem : p + t • (p' - p) ∈ Metric.closedBall a ρ := by
      have h := (convex_closedBall a ρ) hp hp' (sub_nonneg.mpr ht.2) ht.1 (by ring)
      have e : p + t • (p' - p) = (1 - t) • p + t • p' := by module
      rw [e]
      exact h
    have hvd : HasDerivAt (fun t : ℝ => p + t • (p' - p)) (p' - p) t := by
      simpa using ((hasDerivAt_id t).smul_const (p' - p)).const_add p
    have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (p + t • (p' - p)) :=
      (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds (hS hmem))).mdifferentiableAt one_ne_zero
    have hs := riemannianCurveSpeed_comp (r := diskExtension q)
      (v := fun t : ℝ => p + t • (p' - p)) (t := t) g hmd hvd.differentiableAt
    rw [hs]
    refine (hC _ hmem (deriv (fun t : ℝ => p + t • (p' - p)) t)).trans ?_
    have hd : deriv (fun t : ℝ => p + t • (p' - p)) t = p' - p := hvd.deriv
    rw [hd]
    simp
  have h := riemannianCurveELength_le g hspeed
  simpa using h

omit [FiniteDimensional ℝ E] in
/-- 距离的局部上界：`closedBall a ρ ⊆ 开圆盘` 内 `d_q(z, w) ≤ C · ‖w - z‖`。 -/
theorem exists_diskEDist_le_NK {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    {a : ℂ} {ρ : ℝ} (hS : Metric.closedBall a ρ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ C : ℝ≥0, ∀ p ∈ Metric.closedBall a ρ, ∀ p' ∈ Metric.closedBall a ρ,
      diskEDist_NK g q p p' ≤ (C : ℝ≥0∞) * (‖p' - p‖₊ : ℝ≥0∞) := by
  obtain ⟨C, hC⟩ := exists_diskSegLength_le_NK g hq hS
  exact ⟨C, fun p hp p' hp' => (diskEDist_le_seg_NK g q (hS hp) (hS hp')).trans (hC p hp p' hp')⟩

end Basic

end GC.LongTime
