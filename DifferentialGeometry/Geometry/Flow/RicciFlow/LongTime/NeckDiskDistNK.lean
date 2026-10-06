import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckBandLengthNK
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk

/-!
# Route W, IMS06′ 的路径长度下界（S-W-NECK G3，后缀 `_NK`，第 2 部分：Morrey 盘的内蕴距离）

树里没有 branched Morrey 盘的内蕴距离（`q^*g` 在 branch point 退化，不是 Riemannian 度量），
所以这里显式定义（不加新结构、新 Prop）：

* `diskSegLength_NK g q p p'`：直线段 `p → p'` 经 `q` 的像的 `g`-长度（`riemannianCurveELength`）；
* `diskEDist_NK g q z w`：开单位圆盘里直线段链的 `q^*g`-长度的下确界（多边形内蕴距离；
  三角不等式只是链的拼接）。

**主定理 `ofReal_le_diskEDist_NK`**：`Z` 在开集 `N` 上光滑、band `{p ∈ N | |Z p| < 20}` 上
`|dZ|² ≤ 4 g` 且其闭包 `⊆ N`；若 `q(z₀)` 在 band 内而 `q(w)` 不在，则
`d_q(z₀, w) ≥ (20 - |Z (q z₀)|)/2`，`Z (q z₀) = 0`（中间球面）时 `≥ 10`
（`ofReal_ten_le_diskEDist_NK`）。证明：链上归纳，每条线段用 `stay_or_exit_NK`。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 直线段 `p → p'`（开圆盘内）经 `q` 的像的 `g`-长度，即 `q^*g` 沿线段的长度。 -/
def diskSegLength_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M))
    (p p' : ℂ) : ℝ≥0∞ :=
  riemannianCurveELength g (diskExtension q ∘ fun t : ℝ => p + t • (p' - p)) 0 1

/-- `q^*g` 在开单位圆盘上的（多边形）内蕴距离：直线段链的 `q^*g`-长度的下确界。 -/
def diskEDist_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M))
    (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (c : ℕ → ℂ) (_ : c 0 = z ∧ c n = w ∧ ∀ i ≤ n, c i ∈ Metric.ball (0 : ℂ) 1),
    ∑ i ∈ Finset.range n, diskSegLength_NK g q (c i) (c (i + 1))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskSegCurve_contMDiffOn_NK {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    {p p' : ℂ} (hp : p ∈ Metric.ball (0 : ℂ) 1) (hp' : p' ∈ Metric.ball (0 : ℂ) 1) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (diskExtension q ∘ fun t : ℝ => p + t • (p' - p))
      (Icc 0 1) := by
  have hseg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (fun t : ℝ => p + t • (p' - p)) :=
    (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => p + t • (p' - p))).contMDiff
  refine (hq.of_le (by exact_mod_cast le_top)).comp hseg.contMDiffOn ?_
  intro t ht
  have h := (convex_ball (0 : ℂ) 1) hp hp' (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have e : p + t • (p' - p) = (1 - t) • p + t • p' := by module
  change p + t • (p' - p) ∈ Metric.ball (0 : ℂ) 1
  rw [e]
  exact h

omit [FiniteDimensional ℝ E] in
/-- **链的 first-exit 下界**：开圆盘里的线段链 `c 0, …, c n`，起点的像在 band `B` 内、终点的像
不在 `B` 内，则 `20 - |Z (q (c 0))| ≤ 2 ×`（链的 `q^*g`-长度）。 -/
theorem chain_exit_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q) {Nset : Set M} (hN : IsOpen Nset) {Z : M → ℝ}
    (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
    (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
    (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    {n : ℕ} {c : ℕ → ℂ} (hc : ∀ i ≤ n, c i ∈ Metric.ball (0 : ℂ) 1)
    (h0 : diskExtension q (c 0) ∈ Nset) (h0' : |Z (diskExtension q (c 0))| < 20)
    (hn : ¬ (diskExtension q (c n) ∈ Nset ∧ |Z (diskExtension q (c n))| < 20)) :
    ENNReal.ofReal (20 - |Z (diskExtension q (c 0))|) ≤
      2 * ∑ i ∈ Finset.range n, diskSegLength_NK g q (c i) (c (i + 1)) := by
  set U := diskExtension q with hU
  set a₀ := Z (U (c 0)) with ha₀
  have key : ∀ m ≤ n,
      ((∀ i ≤ m, U (c i) ∈ Nset ∧ |Z (U (c i))| < 20) ∧
        ENNReal.ofReal |Z (U (c m)) - a₀| ≤
          2 * ∑ i ∈ Finset.range m, diskSegLength_NK g q (c i) (c (i + 1))) ∨
      ENNReal.ofReal (20 - |a₀|) ≤
        2 * ∑ i ∈ Finset.range m, diskSegLength_NK g q (c i) (c (i + 1)) := by
    intro m
    induction m with
    | zero =>
      intro _
      left
      refine ⟨fun i hi => ?_, by simp [ha₀]⟩
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact ⟨h0, h0'⟩
    | succ m ih =>
      intro hm
      have hm' : m ≤ n := Nat.le_of_succ_le hm
      have hcm : c m ∈ Metric.ball (0 : ℂ) 1 := hc m hm'
      have hcm1 : c (m + 1) ∈ Metric.ball (0 : ℂ) 1 := hc (m + 1) hm
      rw [Finset.sum_range_succ]
      rcases ih hm' with ⟨hin, hlen⟩ | hex
      · have hseg := stay_or_exit_NK g hN hZ hcl hdz
          (diskSegCurve_contMDiffOn_NK hq hcm hcm1) (by simpa using (hin m le_rfl).1)
          (by simpa using (hin m le_rfl).2)
        simp only [Function.comp_apply, zero_smul, add_zero, one_smul, add_sub_cancel] at hseg
        have hσ : diskSegLength_NK g q (c m) (c (m + 1)) =
            riemannianCurveELength g (U ∘ fun t : ℝ => c m + t • (c (m + 1) - c m)) 0 1 := rfl
        rcases hseg with ⟨hall, hlen2⟩ | hex2
        · left
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases hi.eq_or_lt with rfl | hlt
            · simpa using hall 1 ⟨zero_le_one, le_rfl⟩
            · exact hin i (Nat.lt_succ_iff.mp hlt)
          · calc ENNReal.ofReal |Z (U (c (m + 1))) - a₀|
                ≤ ENNReal.ofReal (|Z (U (c (m + 1))) - Z (U (c m))| + |Z (U (c m)) - a₀|) := by
                  apply ENNReal.ofReal_le_ofReal
                  have := abs_sub_le (Z (U (c (m + 1)))) (Z (U (c m))) a₀
                  linarith
              _ ≤ ENNReal.ofReal |Z (U (c (m + 1))) - Z (U (c m))| +
                    ENNReal.ofReal |Z (U (c m)) - a₀| := ENNReal.ofReal_add_le
              _ ≤ 2 * diskSegLength_NK g q (c m) (c (m + 1)) +
                    2 * ∑ i ∈ Finset.range m, diskSegLength_NK g q (c i) (c (i + 1)) :=
                  add_le_add (by rw [hσ]; exact hlen2) hlen
              _ = 2 * (∑ i ∈ Finset.range m, diskSegLength_NK g q (c i) (c (i + 1)) +
                    diskSegLength_NK g q (c m) (c (m + 1))) := by ring
        · right
          have hzm : |Z (U (c m))| < 20 := (hin m le_rfl).2
          calc ENNReal.ofReal (20 - |a₀|)
              ≤ ENNReal.ofReal ((20 - |Z (U (c m))|) + |Z (U (c m)) - a₀|) := by
                apply ENNReal.ofReal_le_ofReal
                have := abs_sub_abs_le_abs_sub (Z (U (c m))) a₀
                linarith
            _ ≤ ENNReal.ofReal (20 - |Z (U (c m))|) + ENNReal.ofReal |Z (U (c m)) - a₀| :=
                ENNReal.ofReal_add_le
            _ ≤ 2 * diskSegLength_NK g q (c m) (c (m + 1)) +
                  2 * ∑ i ∈ Finset.range m, diskSegLength_NK g q (c i) (c (i + 1)) :=
                add_le_add (by rw [hσ]; exact hex2) hlen
            _ = 2 * (∑ i ∈ Finset.range m, diskSegLength_NK g q (c i) (c (i + 1)) +
                  diskSegLength_NK g q (c m) (c (m + 1))) := by ring
      · right
        exact hex.trans (by gcongr; exact le_self_add)
  rcases key n le_rfl with ⟨hin, _⟩ | hex
  · exact absurd (hin n le_rfl) hn
  · exact hex

theorem ofReal_half_le_NK {x : ℝ} {S : ℝ≥0∞} (h : ENNReal.ofReal x ≤ 2 * S) :
    ENNReal.ofReal (x / 2) ≤ S := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  exact ENNReal.div_le_of_le_mul (by rwa [mul_comm] at h)

omit [FiniteDimensional ℝ E] in
/-- **G3 主定理（内蕴距离的 band 下界）**：`q(z₀)` 在 band `B` 内而 `q(w) ∉ B`，则
`q^*g` 的内蕴距离 `d_q(z₀, w) ≥ (20 - |Z (q z₀)|)/2`；`Z (q z₀) = 0`（中间球面）时 `≥ 10`。 -/
theorem ofReal_le_diskEDist_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q) {Nset : Set M} (hN : IsOpen Nset) {Z : M → ℝ}
    (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
    (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
    (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    {z₀ w : ℂ}
    (h0 : diskExtension q z₀ ∈ Nset) (h0' : |Z (diskExtension q z₀)| < 20)
    (hw' : ¬ (diskExtension q w ∈ Nset ∧ |Z (diskExtension q w)| < 20)) :
    ENNReal.ofReal ((20 - |Z (diskExtension q z₀)|) / 2) ≤ diskEDist_NK g q z₀ w := by
  unfold diskEDist_NK
  refine le_iInf fun n => le_iInf fun c => le_iInf fun hc => ?_
  have := chain_exit_NK g hq hN hZ hcl hdz hc.2.2 (by rw [hc.1]; exact h0)
    (by rw [hc.1]; exact h0') (by rw [hc.2.1]; exact hw')
  rw [hc.1] at this
  exact ofReal_half_le_NK this

omit [FiniteDimensional ℝ E] in
theorem ofReal_ten_le_diskEDist_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q) {Nset : Set M}
    (hN : IsOpen Nset) {Z : M → ℝ} (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
    (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
    (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    {z₀ w : ℂ} (h0 : diskExtension q z₀ ∈ Nset) (hz : Z (diskExtension q z₀) = 0)
    (hw' : ¬ (diskExtension q w ∈ Nset ∧ |Z (diskExtension q w)| < 20)) :
    ENNReal.ofReal 10 ≤ diskEDist_NK g q z₀ w := by
  have h := ofReal_le_diskEDist_NK g hq hN hZ hcl hdz h0 (by rw [hz]; norm_num) hw'
  rw [hz] at h
  have e : ENNReal.ofReal ((20 - |(0 : ℝ)|) / 2) = ENNReal.ofReal 10 := by norm_num
  rwa [e] at h

omit [FiniteDimensional ℝ E] in
/-- 对偶形式：`d_q(z₀, w) < 10`（中间球面的点 `z₀`）⇒ `q(w)` 仍在 band 内。 -/
theorem mem_band_of_diskEDist_lt_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q) {Nset : Set M}
    (hN : IsOpen Nset) {Z : M → ℝ} (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
    (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
    (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    {z₀ w : ℂ} (h0 : diskExtension q z₀ ∈ Nset) (hz : Z (diskExtension q z₀) = 0)
    (hlt : diskEDist_NK g q z₀ w < ENNReal.ofReal 10) :
    diskExtension q w ∈ Nset ∧ |Z (diskExtension q w)| < 20 := by
  by_contra hw'
  exact absurd (ofReal_ten_le_diskEDist_NK g hq hN hZ hcl hdz h0 hz hw') (not_le.mpr hlt)

omit [FiniteDimensional ℝ E] in
/-- consumer：中间球面上的点 `z₀` 的 `8`-闭内蕴球整个落在 band 的原像里（`8 < 10`），
IMS05′ 用它得到球上 `R ≥ 1/2`。 -/
theorem band_of_closedBall_eight_NK (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q) {Nset : Set M}
    (hN : IsOpen Nset) {Z : M → ℝ} (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
    (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
    (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    {z₀ w : ℂ} (h0 : diskExtension q z₀ ∈ Nset) (hz : Z (diskExtension q z₀) = 0)
    (hle : diskEDist_NK g q z₀ w ≤ ENNReal.ofReal 8) :
    diskExtension q w ∈ Nset ∧ |Z (diskExtension q w)| < 20 :=
  mem_band_of_diskEDist_lt_NK g hq hN hZ hcl hdz h0 hz
    (hle.trans_lt (ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)))

end GC.LongTime
