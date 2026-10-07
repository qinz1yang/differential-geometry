import DifferentialGeometry.Geometry.Metric.CompactSourceLipschitz
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz

/-!
# O-MY-R7E G3-e：闭盘上 Lipschitz 的局部—整体、粘合、换度量

`closedDisk` 是 `ℂ` 中的紧凸集；目标只要求是 pseudo-emetric（`riemannianEDistOf` 可以取 `∞`，
所以不用 Mathlib 的 `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`，它要 metric 目标）。

* `lipschitz_of_local_closedDisk_R7E`：局部 Lipschitz ⇒ 整体 Lipschitz（Lebesgue 数 + 沿线段 chaining）；
* `lipschitzOn_glue_closedDisk_R7E`：`ψ ≤ c` 处 `w = f₁`、`ψ ≥ c` 处 `w = f₂`，两支在球上 `K`-Lipschitz ⇒
  `w` 在球上 `K`-Lipschitz（线段上介值定理找到 `ψ = c` 的中间点）；
* `exists_local_riemannianEDistOf_comparison_R7E`：两个光滑度量的距离局部可比（chart 两边 Lipschitz）；
* `lipschitz_change_metric_R7E`：`g₁`-Lipschitz 盘也是 `g₂`-Lipschitz（R7-E transport 里 `Ĝ`-Lipschitz）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

section Disk

variable {Y : Type*} [PseudoEMetricSpace Y]

/-- 闭盘上线段点。 -/
def diskSegmentPoint_R7E (x y : closedDisk) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : closedDisk :=
  ⟨(x : ℂ) + t • ((y : ℂ) - x), by
    have h := (convex_closedBall (0 : ℂ) 1) x.2 y.2 (sub_nonneg.mpr ht.2) ht.1
      (by ring : (1 - t) + t = 1)
    have heq : (1 - t) • (x : ℂ) + t • (y : ℂ) = (x : ℂ) + t • ((y : ℂ) - x) := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rwa [heq] at h⟩

theorem dist_diskSegmentPoint_R7E (x y : closedDisk) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (diskSegmentPoint_R7E x y s hs) (diskSegmentPoint_R7E x y t ht) = |s - t| * dist x y := by
  change dist ((x : ℂ) + s • ((y : ℂ) - x)) ((x : ℂ) + t • ((y : ℂ) - x)) = _
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ← dist_eq_norm,
    dist_comm]
  rfl

/-- 局部 Lipschitz ⇒ 整体 Lipschitz（闭盘，pseudo-emetric 目标）。 -/
theorem lipschitz_of_local_closedDisk_R7E (f : closedDisk → Y)
    (hloc : ∀ z : closedDisk, ∃ s ∈ 𝓝 z, ∃ K : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s,
      edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y) :
    ∃ K : ℝ≥0, ∀ x y : closedDisk, edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y := by
  choose s hs K hK using hloc
  have hε : ∀ z : closedDisk, ∃ ε > 0, ball z ε ⊆ s z := fun z => Metric.mem_nhds_iff.mp (hs z)
  choose ε hεpos hεs using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z : closedDisk => ball z (ε z))
    (fun z => isOpen_ball) (fun z _ => mem_iUnion.mpr ⟨z, mem_ball_self (hεpos z)⟩)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun i : t => ball (i : closedDisk)
    (ε i)) isCompact_univ (fun i => isOpen_ball) (by
      intro x _
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (ht (mem_univ x))
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩)
  let Km : ℝ≥0 := t.sup K
  have hunif : ∀ x y : closedDisk, dist x y < δ → edist (f x) (f y) ≤ (Km : ℝ≥0∞) * edist x y := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hleb x (mem_univ x)
    have hx : x ∈ s i := hεs i (hi (mem_ball_self hδ))
    have hy : y ∈ s i := hεs i (hi (by rw [mem_ball, dist_comm]; exact hxy))
    refine (hK i x hx y hy).trans ?_
    gcongr
    exact Finset.le_sup (f := K) i.2
  refine ⟨Km, fun x y => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x y / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg dist_nonneg hδ.le) hn
  have hstep : dist x y / n < δ := by
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  have hmem : ∀ k : ℕ, k ≤ n → (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨div_nonneg (Nat.cast_nonneg k) hnpos.le,
      (div_le_one hnpos).mpr (by exact_mod_cast hk)⟩
  have hind : ∀ k : ℕ, ∀ hk : k ≤ n,
      edist (f x) (f (diskSegmentPoint_R7E x y ((k : ℝ) / n) (hmem k hk))) ≤
        (Km : ℝ≥0∞) * ENNReal.ofReal (k * (dist x y / n)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : diskSegmentPoint_R7E x y ((0 : ℕ) / n) (hmem 0 hk) = x := by
        apply Subtype.ext
        simp [diskSegmentPoint_R7E]
      rw [h0, edist_self]
      exact zero_le
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hd : dist (diskSegmentPoint_R7E x y ((k : ℝ) / n) (hmem k hk'))
          (diskSegmentPoint_R7E x y (((k + 1 : ℕ) : ℝ) / n) (hmem (k + 1) hk)) =
          dist x y / n := by
        rw [dist_diskSegmentPoint_R7E]
        have : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
          rw [Nat.cast_succ, ← sub_div, abs_div, abs_of_pos hnpos]
          norm_num
        rw [this]
        ring
      calc edist (f x) (f (diskSegmentPoint_R7E x y (((k + 1 : ℕ) : ℝ) / n) (hmem (k + 1) hk)))
          ≤ edist (f x) (f (diskSegmentPoint_R7E x y ((k : ℝ) / n) (hmem k hk'))) +
            edist (f (diskSegmentPoint_R7E x y ((k : ℝ) / n) (hmem k hk')))
              (f (diskSegmentPoint_R7E x y (((k + 1 : ℕ) : ℝ) / n) (hmem (k + 1) hk))) :=
            edist_triangle _ _ _
        _ ≤ (Km : ℝ≥0∞) * ENNReal.ofReal (k * (dist x y / n)) +
            (Km : ℝ≥0∞) * ENNReal.ofReal (dist x y / n) := by
            gcongr
            · exact ih hk'
            · refine (hunif _ _ (by rw [hd]; exact hstep)).trans ?_
              rw [edist_dist, hd]
        _ = (Km : ℝ≥0∞) * ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (dist x y / n)) := by
            rw [← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 2
            push_cast
            ring
  have hfin := hind n le_rfl
  have hn1 : diskSegmentPoint_R7E x y ((n : ℝ) / n) (hmem n le_rfl) = y := by
    apply Subtype.ext
    change (x : ℂ) + ((n : ℝ) / n) • ((y : ℂ) - x) = y
    rw [div_self hnpos.ne', one_smul]
    abel
  rw [hn1] at hfin
  have hval : (n : ℝ) * (dist x y / n) = dist x y := by
    field_simp
  rw [hval, ← edist_dist] at hfin
  exact hfin

/-- 粘合：`ψ ≤ c` 处 `w = f₁`、`ψ ≥ c` 处 `w = f₂`，两支在 `ball z₀ r` 的对应半边上 `K`-Lipschitz ⇒
`w` 在 `ball z₀ r` 上 `K`-Lipschitz。 -/
theorem lipschitzOn_glue_closedDisk_R7E {w f₁ f₂ : closedDisk → Y} {ψ : closedDisk → ℝ}
    (hψ : Continuous ψ) {c : ℝ} (hw₁ : ∀ x, ψ x ≤ c → w x = f₁ x)
    (hw₂ : ∀ x, c ≤ ψ x → w x = f₂ x) (z₀ : closedDisk) (r : ℝ) {K : ℝ≥0}
    (h₁ : ∀ x ∈ ball z₀ r, ∀ y ∈ ball z₀ r, ψ x ≤ c → ψ y ≤ c →
      edist (f₁ x) (f₁ y) ≤ (K : ℝ≥0∞) * edist x y)
    (h₂ : ∀ x ∈ ball z₀ r, ∀ y ∈ ball z₀ r, c ≤ ψ x → c ≤ ψ y →
      edist (f₂ x) (f₂ y) ≤ (K : ℝ≥0∞) * edist x y) :
    ∀ x ∈ ball z₀ r, ∀ y ∈ ball z₀ r, edist (w x) (w y) ≤ (K : ℝ≥0∞) * edist x y := by
  have hseg : ∀ x ∈ ball z₀ r, ∀ y ∈ ball z₀ r, ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
      diskSegmentPoint_R7E x y t ht ∈ ball z₀ r := by
    intro x hx y hy t ht
    have h := (convex_ball (z₀ : ℂ) r) (show (x : ℂ) ∈ ball (z₀ : ℂ) r from hx)
      (show (y : ℂ) ∈ ball (z₀ : ℂ) r from hy) (sub_nonneg.mpr ht.2) ht.1
      (by ring : (1 - t) + t = 1)
    have heq : (1 - t) • (x : ℂ) + t • (y : ℂ) = (x : ℂ) + t • ((y : ℂ) - x) := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [heq] at h
    exact h
  have hcross : ∀ x ∈ ball z₀ r, ∀ y ∈ ball z₀ r, ψ x ≤ c → c ≤ ψ y →
      edist (w x) (w y) ≤ (K : ℝ≥0∞) * edist x y := by
    intro x hx y hy hxc hyc
    let γ : Icc (0 : ℝ) 1 → closedDisk := fun t => diskSegmentPoint_R7E x y t t.2
    have hγc : Continuous γ := by
      apply Continuous.subtype_mk
      exact continuous_const.add (continuous_subtype_val.smul continuous_const)
    have hivt := intermediate_value_univ (⟨0, by simp⟩ : Icc (0 : ℝ) 1) ⟨1, by simp⟩
      (hψ.comp hγc)
    have hc0 : (ψ ∘ γ) ⟨0, by simp⟩ ≤ c := by
      have : γ ⟨0, by simp⟩ = x := Subtype.ext (by simp [γ, diskSegmentPoint_R7E])
      simp only [Function.comp_apply, this]
      exact hxc
    have hc1 : c ≤ (ψ ∘ γ) ⟨1, by simp⟩ := by
      have : γ ⟨1, by simp⟩ = y := Subtype.ext (by simp [γ, diskSegmentPoint_R7E])
      simp only [Function.comp_apply, this]
      exact hyc
    obtain ⟨t, ht⟩ := hivt ⟨hc0, hc1⟩
    set m := γ t with hm
    have hmc : ψ m = c := ht
    have hmB : m ∈ ball z₀ r := hseg x hx y hy t t.2
    have hx0 : x = diskSegmentPoint_R7E x y 0 (by simp) :=
      Subtype.ext (by simp [diskSegmentPoint_R7E])
    have hy1 : y = diskSegmentPoint_R7E x y 1 (by simp) := by
      apply Subtype.ext
      simp [diskSegmentPoint_R7E]
    have hdxm : dist x m = t * dist x y := by
      have h := dist_diskSegmentPoint_R7E x y (s := 0) (t := t) (by simp) t.2
      rw [← hx0] at h
      rw [h, zero_sub, abs_neg, abs_of_nonneg t.2.1]
    have hdmy : dist m y = (1 - t) * dist x y := by
      have h := dist_diskSegmentPoint_R7E x y (s := t) (t := 1) t.2 (by simp)
      rw [← hy1] at h
      rw [h, abs_of_nonpos (by linarith [t.2.2]), neg_sub]
    have hsum : edist x m + edist m y = edist x y := by
      rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
        hdxm, hdmy]
      congr 1
      ring
    calc edist (w x) (w y) ≤ edist (w x) (w m) + edist (w m) (w y) := edist_triangle _ _ _
      _ = edist (f₁ x) (f₁ m) + edist (f₂ m) (f₂ y) := by
          rw [hw₁ x hxc, hw₂ y hyc, ← hw₁ m hmc.le, ← hw₂ m hmc.ge]
      _ ≤ (K : ℝ≥0∞) * edist x m + (K : ℝ≥0∞) * edist m y := by
          gcongr
          · exact h₁ x hx m hmB hxc hmc.le
          · exact h₂ m hmB y hy hmc.ge hyc
      _ = (K : ℝ≥0∞) * edist x y := by rw [← mul_add, hsum]
  intro x hx y hy
  rcases le_total (ψ x) c with hxc | hxc <;> rcases le_total (ψ y) c with hyc | hyc
  · rw [hw₁ x hxc, hw₁ y hyc]
    exact h₁ x hx y hy hxc hyc
  · exact hcross x hx y hy hxc hyc
  · rw [edist_comm, edist_comm x]
    exact hcross y hy x hx hyc hxc
  · rw [hw₂ x hxc, hw₂ y hyc]
    exact h₂ x hx y hy hxc hyc

end Disk

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ, E) ∞ Y]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 两个光滑度量的距离局部可比：`d₂ ≤ K d₁` 于 `p` 的邻域（chart 对 `g₁` 局部 Lipschitz，
chart 逆对 `g₂` 局部 Lipschitz）。 -/
theorem exists_local_riemannianEDistOf_comparison_R7E [T3Space Y]
    (g₁ g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) Y) (p : Y) :
    ∃ s ∈ 𝓝 p, ∃ K : ℝ≥0, ∀ y ∈ s, ∀ y' ∈ s,
      riemannianEDistOf g₂ y y' ≤ (K : ℝ≥0∞) * riemannianEDistOf g₁ y y' := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Y → Type _) := ⟨g₁.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : Y → Type _) :=
    ⟨g₁.inner, g₁.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace Y := .ofRiemannianMetric 𝓘(ℝ, E) Y
  obtain ⟨K₁, s₁, hs₁, hK₁⟩ := Riemannian.exists_lipschitzOnWith_extChartAt (I := 𝓘(ℝ, E)) p
  obtain ⟨C, S, hS, hC⟩ := exists_local_source_riemannian_lipschitz g₂
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) (mem_extChartAt_target p)
  refine ⟨s₁ ∩ (extChartAt 𝓘(ℝ, E) p).source ∩ (extChartAt 𝓘(ℝ, E) p) ⁻¹' S,
    inter_mem (inter_mem hs₁ (extChartAt_source_mem_nhds p))
      ((continuousAt_extChartAt p).preimage_mem_nhds hS), C * K₁, ?_⟩
  rintro y ⟨⟨hy₁, hysrc⟩, hyS⟩ y' ⟨⟨hy₁', hysrc'⟩, hyS'⟩
  have h1 := hC _ hyS _ hyS'
  rw [(extChartAt 𝓘(ℝ, E) p).left_inv hysrc, (extChartAt 𝓘(ℝ, E) p).left_inv hysrc'] at h1
  have h2 : edist (extChartAt 𝓘(ℝ, E) p y) (extChartAt 𝓘(ℝ, E) p y') ≤
      (K₁ : ℝ≥0∞) * riemannianEDistOf g₁ y y' := hK₁ hy₁ hy₁'
  refine h1.trans ?_
  rw [ENNReal.coe_mul, mul_assoc]
  gcongr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 换度量：`g₁`-Lipschitz 盘也是 `g₂`-Lipschitz。 -/
theorem lipschitz_change_metric_R7E [T3Space Y] (g₁ g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) Y)
    {w : closedDisk → Y} {L : ℝ≥0}
    (hw : ∀ z z', riemannianEDistOf g₁ (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z') :
    ∃ K : ℝ≥0, ∀ z z', riemannianEDistOf g₂ (w z) (w z') ≤ (K : ℝ≥0∞) * edist z z' := by
  have hwc : Continuous w := continuous_of_riemannian_lipschitz g₁ hw
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Y → Type _) := ⟨g₂.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : Y → Type _) :=
    ⟨g₂.inner, g₂.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace Y := .ofRiemannianMetric 𝓘(ℝ, E) Y
  obtain ⟨K, hK⟩ := lipschitz_of_local_closedDisk_R7E w (fun z₀ => by
    obtain ⟨s, hs, K, hK⟩ := exists_local_riemannianEDistOf_comparison_R7E g₁ g₂ (w z₀)
    refine ⟨w ⁻¹' s, hwc.continuousAt.preimage_mem_nhds hs, K * L, fun x hx y hy => ?_⟩
    change riemannianEDistOf g₂ (w x) (w y) ≤ _
    refine (hK _ hx _ hy).trans ?_
    rw [ENNReal.coe_mul, mul_assoc]
    gcongr
    exact hw x y)
  exact ⟨K, fun z z' => hK z z'⟩

end Metric

end DifferentialGeometry.Geometry
