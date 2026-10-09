import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckDiskDistPropsNK
import DifferentialGeometry.Analysis.ODE.StabilityRadiusIF
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

/-!
# Route W, IMS06′ 的组装（S-W-NECK G4，后缀 `_NK`，第 2 部分：中间球面排除）

design §B.4：`N` 开、`Z : M → ℝ` 在 `N` 上光滑，band `B = {p ∈ N | |Z p| < 20}` 的闭包 `⊆ N`，
band 上 `R ≥ 1/2`、`|dZ|² ≤ 4 g`；`q` 是开盘内光滑的盘，`q(∂D) ∩ closure B = ∅`；
IMS05′（`σ = 1/2`）作显式参数（O-IFACE G3 的形状：`r ≤ 2π√(2/(3σ))`，或其 `L` 形式：
`∃ L ≥ r, σL² ≤ 8π²/3`）。结论 `∀ ζ, ¬ (q ζ ∈ N ∧ Z (q ζ) = 0)`。

证明（G3 + IFACE 数值）：`q ζ` 在中间球面上 ⇒ `ζ` 在开盘内（`q(∂D)` 在 `closure B` 外）；
G3 给 `d_q(ζ, w) ≥ 10`（对 `q(w) ∉ B`）；所以 `8`-闭内蕴球
* 在 band 的原像里（`R ≥ 1/2` 在球内各点邻域上，`eventually_scalar_of_diskEDist_NK`），
* 紧（`isCompact_diskEBall_NK`：球不趋近 `∂D`——`q` 连续、`q(∂D) ∉ closure B`——加局部
  Lipschitz 界与三角不等式得闭），
* 球面非空（`exists_diskEDist_eq_NK`：到 `∂D` 附近的线段上 `d_q(ζ, ·)` 连续，从 `0` 到 `≥ 10`，IVT）；
IMS05′ 给 `8 ≤ 2π√(2/(3·½)) = 4π/√3`，与 `4π/√3 < 8`
（`DifferentialGeometry.Analysis.two_pi_sqrt_two_div_three_half_lt_eight_IF`）矛盾。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

/-- 单位圆周上的点是某个 `diskBoundary θ`。 -/
theorem exists_diskBoundary_eq_NK (ζ : closedDisk) (h : ‖(ζ : ℂ)‖ = 1) :
    ∃ θ : ℝ, diskBoundary (θ : loopCircle) = ζ := by
  refine ⟨Complex.arg ζ / (2 * Real.pi), Subtype.ext ?_⟩
  rw [diskBoundary_coe]
  have h2 : (2 * Real.pi * (Complex.arg ζ / (2 * Real.pi)) : ℝ) = Complex.arg ζ := by
    field_simp
  rw [h2]
  have := Complex.norm_mul_exp_arg_mul_I (ζ : ℂ)
  rw [h] at this
  simpa using this

theorem continuous_diskExtension_NK {M : Type*} [TopologicalSpace M] (q : C(closedDisk, M)) :
    Continuous (diskExtension q) :=
  q.continuous.comp diskRetraction_lipschitz.continuous

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
  (hq : DiskSmoothInterior (E := E) q) {Nset : Set M} (hN : IsOpen Nset) {Z : M → ℝ}
  (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
  (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
  (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
    (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)

include hq hN hZ hcl hdz in
/-- `z₀` 在中间球面上、`8 < 10` 的半径：闭内蕴球 `{z ∈ 开圆盘 | d_q(z₀, z) ≤ r}`（`r < 10`）
是 `ℂ` 的紧集：`q` 在 `∂D` 上的值在 `closure B` 之外 + 球内的点的像在 band 内 ⇒ 球不趋近 `∂D`，
再用 `d_q` 的局部 Lipschitz 界和三角不等式得闭。 -/
theorem isCompact_diskEBall_NK
    (htrace : ∀ ζ : closedDisk, ‖(ζ : ℂ)‖ = 1 →
      q ζ ∉ closure {p : M | p ∈ Nset ∧ |Z p| < 20})
    {z₀ : ℂ} (h0 : diskExtension q z₀ ∈ Nset) (hz : Z (diskExtension q z₀) = 0)
    {r : ℝ} (hr : r < 10) :
    IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} := by
  set K : Set ℂ := {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
    diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} with hK
  set B : Set M := {p : M | p ∈ Nset ∧ |Z p| < 20} with hB
  have hUc := continuous_diskExtension_NK q
  have hKband : ∀ z ∈ K, diskExtension q z ∈ B := fun z hzK =>
    mem_band_of_diskEDist_lt_NK g hq hN hZ hcl hdz h0 hz
      (hzK.2.trans_lt (ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr hr)) |> fun h => h
  have hKsub : K ⊆ Metric.closedBall (0 : ℂ) 1 := fun z hzK =>
    Metric.ball_subset_closedBall hzK.1
  have hclosed : IsClosed K := by
    rw [← closure_subset_iff_isClosed]
    intro z hzcl
    have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      closure_minimal hKsub Metric.isClosed_closedBall hzcl
    have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
      by_contra hnot
      have hnorm : ‖z‖ = 1 := by
        have h1 : ‖z‖ ≤ 1 := by simpa using hzcb
        have h2 : ¬ ‖z‖ < 1 := by simpa using hnot
        exact le_antisymm h1 (not_lt.mp h2)
      have hmem : diskExtension q z ∈ closure B := by
        have h1 : diskExtension q z ∈ closure (diskExtension q '' K) :=
          image_closure_subset_closure_image hUc ⟨z, hzcl, rfl⟩
        exact closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact hKband w hw) h1
      have := htrace ⟨z, hzcb⟩ hnorm
      rw [← diskExtension_coe q ⟨z, hzcb⟩] at this
      exact this hmem
    refine ⟨hzball, ?_⟩
    obtain ⟨ε₀, hε₀, hsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hzball
    have hS : Metric.closedBall z (ε₀ / 2) ⊆ Metric.ball (0 : ℂ) 1 := fun w hw =>
      hsub (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith))
    obtain ⟨C, hC⟩ := exists_diskEDist_le_NK g hq hS
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    have hδ : 0 < min (ε₀ / 2) ((ε : ℝ) / (C + 1)) := lt_min (by linarith) (by positivity)
    obtain ⟨y, hyK, hyd⟩ := Metric.mem_closure_iff.mp hzcl _ hδ
    have hyz : dist z y < min (ε₀ / 2) ((ε : ℝ) / (C + 1)) := hyd
    have hyS : y ∈ Metric.closedBall z (ε₀ / 2) := by
      rw [Metric.mem_closedBall, dist_comm]
      exact (hyz.trans_le (min_le_left _ _)).le
    have hzS : z ∈ Metric.closedBall z (ε₀ / 2) := Metric.mem_closedBall_self (by linarith)
    have hstep := hC y hyS z hzS
    have hCle : (C : ℝ≥0∞) * (‖z - y‖₊ : ℝ≥0∞) ≤ ε := by
      have hnn : C * ‖z - y‖₊ ≤ ε := by
        rw [← NNReal.coe_le_coe]
        push_cast
        have h1 : ‖z - y‖ < (ε : ℝ) / (C + 1) := by
          rw [← dist_eq_norm]
          exact hyz.trans_le (min_le_right _ _)
        calc (C : ℝ) * ‖z - y‖ ≤ (C : ℝ) * ((ε : ℝ) / (C + 1)) :=
              mul_le_mul_of_nonneg_left h1.le C.2
          _ ≤ ε := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith [C.2]
      exact_mod_cast hnn
    calc diskEDist_NK g q z₀ z
        ≤ diskEDist_NK g q z₀ y + diskEDist_NK g q y z := diskEDist_triangle_NK g q
      _ ≤ ENNReal.ofReal r + ε := add_le_add hyK.2 (hstep.trans hCle)
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 1) hclosed hKsub

include hq hN hZ hcl hdz in
/-- 内蕴球面非空：`z₀` 到 `∂D` 附近（`q(w) ∉ closure B` 的点，`d_q ≥ 10`）的线段上，
`s ↦ d_q(z₀, z_s)` 连续（局部 Lipschitz + 三角不等式），从 `0` 变到 `≥ 10`，IVT 取到 `r ≤ 10`。 -/
theorem exists_diskEDist_eq_NK
    (htrace : ∀ ζ : closedDisk, ‖(ζ : ℂ)‖ = 1 →
      q ζ ∉ closure {p : M | p ∈ Nset ∧ |Z p| < 20})
    {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball (0 : ℂ) 1)
    (h0 : diskExtension q z₀ ∈ Nset) (hz : Z (diskExtension q z₀) = 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 10) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r := by
  set B : Set M := {p : M | p ∈ Nset ∧ |Z p| < 20} with hB
  have hUc := continuous_diskExtension_NK q
  set zs : ℝ → ℂ := fun s => z₀ + s • (1 - z₀) with hzs
  have hzsc : Continuous zs := by fun_prop
  have hU1 : diskExtension q 1 ∉ closure B := by
    have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
    have := htrace ⟨1, h1⟩ (by simp)
    rwa [← diskExtension_coe q ⟨1, h1⟩] at this
  have hev : ∀ᶠ s in 𝓝 (1 : ℝ), diskExtension q (zs s) ∈ (closure B)ᶜ := by
    have hc : ContinuousAt (fun s => diskExtension q (zs s)) 1 :=
      (hUc.comp hzsc).continuousAt
    have h1 : diskExtension q (zs 1) ∈ (closure B)ᶜ := by
      have : zs 1 = 1 := by simp [hzs]
      rw [this]
      exact hU1
    exact hc.eventually (isClosed_closure.isOpen_compl.mem_nhds h1)
  obtain ⟨s₁, ⟨hs₁B, hs₁pos⟩, hs₁lt⟩ : ∃ s₁ : ℝ,
      (diskExtension q (zs s₁) ∈ (closure B)ᶜ ∧ 0 < s₁) ∧ s₁ < 1 :=
    (((hev.filter_mono nhdsWithin_le_nhds).and
      ((lt_mem_nhds (one_pos : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)).and
      (self_mem_nhdsWithin : ∀ᶠ s in 𝓝[<] (1 : ℝ), s < 1)).exists
  have hz₀n : ‖z₀‖ < 1 := by simpa using hz₀
  set ρ' : ℝ := (1 - s₁) * ‖z₀‖ + s₁ with hρ'
  have hρ'lt : ρ' < 1 := by nlinarith [norm_nonneg z₀]
  have hznorm : ∀ s ∈ Icc (0 : ℝ) s₁, ‖zs s‖ ≤ ρ' := by
    intro s hs
    have h1 : zs s = (1 - s) • z₀ + s • (1 : ℂ) := by
      simp only [hzs]
      module
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hs.2]),
      Real.norm_of_nonneg hs.1, norm_one]
    nlinarith [norm_nonneg z₀, hs.2, hs.1]
  have hSsub : Metric.closedBall (0 : ℂ) ρ' ⊆ Metric.ball (0 : ℂ) 1 := fun w hw =>
    lt_of_le_of_lt (by simpa using hw) hρ'lt
  have hmem : ∀ s ∈ Icc (0 : ℝ) s₁, zs s ∈ Metric.closedBall (0 : ℂ) ρ' := fun s hs => by
    simpa using hznorm s hs
  have hz0mem : z₀ ∈ Metric.closedBall (0 : ℂ) ρ' := by
    have := hmem 0 ⟨le_rfl, hs₁pos.le⟩
    simpa [hzs] using this
  obtain ⟨C, hC⟩ := exists_diskEDist_le_NK g hq hSsub
  have hfin : ∀ s ∈ Icc (0 : ℝ) s₁, diskEDist_NK g q z₀ (zs s) ≠ ⊤ := fun s hs =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
      (hC z₀ hz0mem (zs s) (hmem s hs))
  set φ : ℝ → ℝ := fun s => (diskEDist_NK g q z₀ (zs s)).toReal with hφ
  have hlip : ∀ s ∈ Icc (0 : ℝ) s₁, ∀ s' ∈ Icc (0 : ℝ) s₁,
      φ s ≤ φ s' + C * (‖1 - z₀‖ * |s - s'|) := by
    intro s hs s' hs'
    have htri := diskEDist_triangle_NK g q (z := z₀) (w := zs s') (u := zs s)
    have hb := hC (zs s') (hmem s' hs') (zs s) (hmem s hs)
    have hnorm : ‖zs s - zs s'‖ = ‖1 - z₀‖ * |s - s'| := by
      have : zs s - zs s' = (s - s') • (1 - z₀) := by simp only [hzs]; module
      rw [this, norm_smul, Real.norm_eq_abs, mul_comm]
    have hfin' := hfin s' hs'
    have hle : diskEDist_NK g q z₀ (zs s) ≤
        diskEDist_NK g q z₀ (zs s') + (C : ℝ≥0∞) * (‖zs s - zs s'‖₊ : ℝ≥0∞) :=
      htri.trans (add_le_add le_rfl hb)
    have hne : diskEDist_NK g q z₀ (zs s') + (C : ℝ≥0∞) * (‖zs s - zs s'‖₊ : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfin', ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩
    have := ENNReal.toReal_mono hne hle
    rw [ENNReal.toReal_add hfin' (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top),
      ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, coe_nnnorm, hnorm] at this
    exact this
  have hlipschitz : LipschitzOnWith (C * ‖1 - z₀‖₊) φ (Icc (0 : ℝ) s₁) := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_
    rw [Real.dist_eq, Real.dist_eq, abs_le]
    have h1 := hlip s hs s' hs'
    have h2 := hlip s' hs' s hs
    rw [abs_sub_comm s' s] at h2
    push_cast
    constructor <;>
      nlinarith [mul_nonneg C.2 (mul_nonneg (norm_nonneg (1 - z₀)) (abs_nonneg (s - s')))]
  have hcont : ContinuousOn φ (Icc (0 : ℝ) s₁) := hlipschitz.continuousOn
  have hφ0 : φ 0 = 0 := by
    simp [hφ, hzs, diskEDist_self_NK g q hz₀]
  have hφ1 : 10 ≤ φ s₁ := by
    have hnotB : ¬ (diskExtension q (zs s₁) ∈ Nset ∧ |Z (diskExtension q (zs s₁))| < 20) :=
      fun h => hs₁B (subset_closure h)
    have h10 := ofReal_ten_le_diskEDist_NK g hq hN hZ hcl hdz h0 hz hnotB
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin s₁ ⟨hs₁pos.le, le_rfl⟩)).mp h10
  obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc hs₁pos.le hcont
    (show r ∈ Icc (φ 0) (φ s₁) from ⟨by rw [hφ0]; exact hr0, hr.trans hφ1⟩)
  refine ⟨zs s, hSsub (hmem s hs), ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin s hs)]
  exact congrArg ENNReal.ofReal hφs

include hq hN hZ hcl hdz in
/-- 球内每个点的邻域上 `R ≥ 1/2`：`d_q(z₀, z) ≤ r < 10` ⇒ `q(z)` 在 band 内，band 是开集，
`q` 连续，band 上 `R ≥ 1/2`。 -/
theorem eventually_scalar_of_diskEDist_NK
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (hR : ∀ p ∈ Nset, |Z p| < 20 → 1 / 2 ≤ metricScalarAt g p)
    {z₀ : ℂ} (h0 : diskExtension q z₀ ∈ Nset) (hz : Z (diskExtension q z₀) = 0)
    {r : ℝ} (hr : r < 10) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
      ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension q w) := by
  intro z _ hd
  have hb := mem_band_of_diskEDist_lt_NK g hq hN hZ hcl hdz h0 hz
    (hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 10)).mpr hr))
  have hBopen : IsOpen {p : M | p ∈ Nset ∧ |Z p| < 20} :=
    hZ.continuousOn.isOpen_inter_preimage hN (isOpen_lt continuous_abs continuous_const)
  have hev : ∀ᶠ w in 𝓝 z, diskExtension q w ∈ {p : M | p ∈ Nset ∧ |Z p| < 20} :=
    (continuous_diskExtension_NK q).continuousAt.eventually (hBopen.mem_nhds hb)
  exact hev.mono fun w hw => hR _ hw.1 hw.2

include hq hN hZ hcl hdz in
/-- **IMS06′（G4 主定理，IMS05′ 作显式参数）**。

设 `Z` 在开集 `N` 上光滑，band `B = {p ∈ N | |Z p| < 20}` 的闭包 `⊆ N`，band 上 `R ≥ 1/2`、
`|dZ|² ≤ 4 g`（G2 对 `NormalizedNeck` 给出这些）；`q` 是开盘内光滑的盘，`q(∂D)` 与 `closure B`
不交（`htrace`，design §B.4 的 `range (diskTrace q) ∩ closure B = ∅`）。`hIMS05` 是 IMS05′ 在
`σ = 1/2` 时的结论（O-IFACE G3 的 `r ≤ 2π√(2/(3σ))`）：以 `z₀` 为心的闭内蕴球
`{z ∈ 开盘 | d_q(z₀, z) ≤ r}` 紧、`r`-球面非空、球内每点邻域上 `R ≥ 1/2` ⇒ `r ≤ 2π√(2/(3·½))`。
则 `q` 不碰中间球面 `{x ∈ N | Z x = 0}`：碰到则 G3 给 `d_q ≥ 10`，所以半径 `8` 的闭球 紧
（`isCompact_diskEBall_NK`）、球面非空（IVT）、球上 `R ≥ 1/2`，IMS05′ 给 `8 ≤ 4π/√3 < 8`。 -/
theorem not_mem_middle_sphere_of_stability_bound_NK
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (hR : ∀ p ∈ Nset, |Z p| < 20 → 1 / 2 ≤ metricScalarAt g p)
    (htrace : ∀ θ : loopCircle, diskTrace q θ ∉ closure {p : M | p ∈ Nset ∧ |Z p| < 20})
    (hIMS05 : ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) :
    ∀ ζ : closedDisk, ¬ (q ζ ∈ Nset ∧ Z (q ζ) = 0) := by
  rintro ζ ⟨hζN, hζ0⟩
  have htrace' : ∀ ξ : closedDisk, ‖(ξ : ℂ)‖ = 1 →
      q ξ ∉ closure {p : M | p ∈ Nset ∧ |Z p| < 20} := by
    intro ξ hξ
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_NK ξ hξ
    have := htrace (θ : loopCircle)
    rwa [show diskTrace q (θ : loopCircle) = q ξ by
      rw [← hθ]; rfl] at this
  have hzball : (ζ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    by_contra hnot
    have hnorm : ‖(ζ : ℂ)‖ = 1 := by
      have h1 : ‖(ζ : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp ζ.2
      have h2 : ¬ ‖(ζ : ℂ)‖ < 1 := by simpa using hnot
      exact le_antisymm h1 (not_lt.mp h2)
    exact htrace' ζ hnorm (subset_closure ⟨hζN, by rw [hζ0]; norm_num⟩)
  have h0 : diskExtension q (ζ : ℂ) ∈ Nset := by rwa [diskExtension_coe]
  have hz : Z (diskExtension q (ζ : ℂ)) = 0 := by rwa [diskExtension_coe]
  have h8 := hIMS05 (ζ : ℂ) 8 hzball (by norm_num)
    (isCompact_diskEBall_NK g hq hN hZ hcl hdz htrace' h0 hz (by norm_num))
    (exists_diskEDist_eq_NK g hq hN hZ hcl hdz htrace' hzball h0 hz (by norm_num) (by norm_num))
    (eventually_scalar_of_diskEDist_NK g hq hN hZ hcl hdz hR h0 hz (by norm_num))
  exact absurd h8
    (not_le.mpr DifferentialGeometry.Analysis.two_pi_sqrt_two_div_three_half_lt_eight_IF)

include hq hN hZ hcl hdz in
/-- G4 的 `L` 形式（对齐 O-IFACE G3 的 `le_two_pi_sqrt_of_mul_sq_le_IF`）：IMS05′ 的消费形式是
"存在长度 `L ≥ r` 的 `g_Σ`-极小路径，满足加权稳定性 `σ L² ≤ 8π²/3`（`σ = 1/2`）"。 -/
theorem not_mem_middle_sphere_of_weighted_stability_NK
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (hR : ∀ p ∈ Nset, |Z p| < 20 → 1 / 2 ≤ metricScalarAt g p)
    (htrace : ∀ θ : loopCircle, diskTrace q θ ∉ closure {p : M | p ∈ Nset ∧ |Z p| < 20})
    (hIMS05 : ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension q w)) →
      ∃ L : ℝ, r ≤ L ∧ 1 / 2 * L ^ 2 ≤ 8 * Real.pi ^ 2 / 3) :
    ∀ ζ : closedDisk, ¬ (q ζ ∈ Nset ∧ Z (q ζ) = 0) :=
  not_mem_middle_sphere_of_stability_bound_NK g hq hN hZ hcl hdz hR htrace
    fun z₀ r hz₀ hr hK hS hRz => by
      obtain ⟨L, hrL, hL⟩ := hIMS05 z₀ r hz₀ hr hK hS hRz
      exact DifferentialGeometry.Analysis.le_two_pi_sqrt_of_mul_sq_le_IF (σ := 1 / 2)
        (by norm_num) (hr.le.trans hrL) hrL hL

end Main

end GC.LongTime
