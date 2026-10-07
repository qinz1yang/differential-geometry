import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricAreaR7A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundarySmoothness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz

/-!
# S-MY-R7A G5：极限识别链 ⇒ `IsMorreyDisk` ⇒ normalized uniqueness ⇒ 整序列收敛

外审 D-R-MY3-4/5：链
`A_G(q) ≤ A_G(u∞) ≤ liminf A_{Gₙ}(uₙ) ≤ limsup A_{Gₙ}(uₙ) ≤ A_G(q)`，末项由
`A_{Gₙ}(uₙ) ≤ A_{Gₙ}(q) → A_G(q)`（G1）；首项 `u∞` 是 `Γ`-weak-Jordan 的 Lipschitz competitor（F1a 给
闭盘光滑延拓 ⇒ Lipschitz）；`liminf` 一项是 G4 的面积下半连续。结论 `A_G(u∞) = A_G(q)` ⇒
`minimizesLipschitz` / `minimizesSmooth` / `finiteEnergy` ⇒ `IsMorreyDisk G Γ u∞`。

* `limit_identification_chain_R7A`：单个极限 `u∞`（连续到闭盘、内部共形调和、正确 weak trace、
  chart `C^∞_loc` 收敛）⇒ `IsMorreyDisk G Γ u∞`、`A_G(u∞) = A_G(q)`、`A_{Gₙ}(uₙ) → A_G(q)`。
* `varying_metric_compactness_of_subsequence_R7A`：子列形 precompactness 前提 `hsub`（`C^∞_loc`
  precompactness / no-bubbling 由 R7 本体供给）+ R5 的 normalized uniqueness `huniq` ⇒ 每个极限 `= q`
  ⇒ 整序列收敛（`C⁰` 一致 + chart `C^∞_loc`，逐字 R8 的 `hC0` / `hCk` 形）。

不含新 Prop / structure；`range u∞ ⊆ C` 不需要（链只用 `hrel` 于 `B` 与 `range uₙ ⊆ B`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **G5a**（极限识别链，单个极限）：`u∞ = w` 连续到闭盘、内部共形调和、weak Jordan trace `Γ`、
`uₙ → w` 在 chart `C^∞_loc`（`hCk` 形）、`Gₙ → G` 于 `B`（相对一致收敛）、`q` 与 `uₙ` 的像在 `B`、
`q` 为 `G`-Morrey 且光滑到边界 ⇒ `w` 是 `G`-Morrey 盘、`A_G(w) = A_G(q)`、`A_{Gₙ}(uₙ) → A_G(q)`。 -/
theorem limit_identification_chain_R7A [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q) (hqB : range q ⊆ B)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huB : ∀ n, range (u n) ⊆ B) {w : C(closedDisk, M)}
    (hwi : DiskSmoothInterior (E := E) w)
    (hwconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G (diskExtension w) z)
    (hwharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G (diskExtension w) z = 0)
    (hwtrace : DiskWeakJordanTrace Γ w)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc) :
    IsMorreyDisk G Γ w ∧ riemannianDiskArea G w = riemannianDiskArea G q ∧
      Tendsto (fun n => riemannianDiskArea (Gn n) (u n)) atTop (𝓝 (riemannianDiskArea G q)) := by
  obtain ⟨σ, hσm, hσ⟩ := hwtrace
  have hwtr : DiskWeakJordanTrace Γ w := ⟨σ, hσm, hσ⟩
  -- F1a：闭盘光滑延拓 ⇒ Lipschitz ⇒ 有限能量
  obtain ⟨W, hW⟩ := exists_smooth_extension_of_conformal_harmonic_disk G hΓ w hwi hwconf hwharm
    σ hσ
  obtain ⟨L, hL⟩ := hW.lipschitz G
  have hfin : IntegrableOn (diskMapEnergyDensity G (diskExtension w)) (Metric.closedBall 0 1) :=
    integrable_diskMapEnergyDensity G hL
  have hAn : Tendsto (fun n => riemannianDiskArea (Gn n) q) atTop
      (𝓝 (riemannianDiskArea G q)) := area_tendsto_of_metric_tendsto_R7A hrel hqB hq.integrableArea
  have hle_n : ∀ n, riemannianDiskArea (Gn n) (u n) ≤ riemannianDiskArea (Gn n) q :=
    area_le_common_competitor_R7A hq hQ hu
  have hint : ∀ n, IntegrableOn (riemannianAreaDensity (Gn n) (diskExtension (u n)))
      (Metric.closedBall (0 : ℂ) 1) := fun n => (hu n).integrableArea
  -- 链的上一半：`A_G(w) ≤ liminf ≤ lim A_{Gₙ}(q) = A_G(q)`
  have hup : ∀ c, riemannianDiskArea G q < c →
      IntegrableOn (riemannianAreaDensity G (diskExtension w)) (Metric.closedBall (0 : ℂ) 1) ∧
        riemannianDiskArea G w ≤ c := fun c hc =>
    area_lsc_of_bound_R7A hrel huB hCk hint
      (((tendsto_order.1 hAn).2 c hc).mono fun n hn => (hle_n n).trans hn.le)
  have hwA : riemannianDiskArea G w ≤ riemannianDiskArea G q :=
    le_of_forall_gt_imp_ge_of_dense fun c hc => (hup c hc).2
  -- 链的下一半：`w` 是 `Γ`-weak-Jordan 的 Lipschitz competitor，`q` 极小
  have hAw : riemannianDiskArea G q ≤ riemannianDiskArea G w :=
    hq.minimizesLipschitz w hwtr ⟨L, hL⟩
  have heq : riemannianDiskArea G w = riemannianDiskArea G q := le_antisymm hwA hAw
  have hMorrey : IsMorreyDisk G Γ w :=
    isMorreyDisk_of_minimizesLipschitz G hwi hwconf hwharm hfin hwtr fun v hv hvL => by
      rw [heq]
      exact hq.minimizesLipschitz v hv hvL
  refine ⟨hMorrey, heq, tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩⟩
  · rcases lt_or_ge c 0 with hc0 | hc0
    · exact Eventually.of_forall fun n => hc0.trans_le (riemannianDiskArea_nonneg _ _)
    · have hwint := (hup _ (lt_add_one _)).1
      have hlsc := area_lsc_R7A hrel huB hCk hint
      rw [← ofReal_integral_eq_lintegral_ofReal hwint
        (Eventually.of_forall fun z => riemannianAreaDensity_nonneg _ _ _)] at hlsc
      have hApos : 0 < riemannianDiskArea G q := hc0.trans_lt hc
      have hlt : ENNReal.ofReal c < liminf (fun n => ENNReal.ofReal
          (riemannianDiskArea (Gn n) (u n))) atTop := by
        refine lt_of_lt_of_le ?_ hlsc
        have : c < riemannianDiskArea G w := by rw [heq]; exact hc
        exact (ENNReal.ofReal_lt_ofReal_iff (hApos.trans_eq heq.symm)).mpr this
      filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
      exact (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1
  · exact ((tendsto_order.1 hAn).2 c hc).mono fun n hn => (hle_n n).trans_lt hn

/-- 子列原理：若每个子列都有一个更细的子列使 `P` 终将成立，则 `P` 对整列终将成立。 -/
theorem eventually_of_subseq_R7A {P : ℕ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ k in atTop, P (φ (ψ k))) :
    ∀ᶠ n in atTop, P n := by
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hne
  obtain ⟨ψ, -, hk⟩ := h φ hφ
  obtain ⟨k, hk⟩ := hk.exists
  exact hφP (ψ k) hk

/-- **G5b**（R7 的整序列升级）：子列形 precompactness 前提 `hsub`（`C^∞_loc` precompactness / no-bubbling
由 R7 本体供给：每个子列有更细的子列与极限 `w`：`C⁰` 一致于闭盘、chart `C^∞_loc`、内部共形调和、weak
trace `Γ`）+ R5 的 normalized uniqueness `huniq` ⇒ 每个极限 `= q`（G5a 识别 `IsMorreyDisk`，三点归一由
`C⁰` 收敛继承）⇒ 整序列 `C⁰` 一致 + chart `C^∞_loc` 收敛到 `q`（`hC0` / `hCk` 逐字 R8 形），
且 `A_{Gₙ}(uₙ) → A_G(q)`。 -/
theorem varying_metric_compactness_of_subsequence_R7A [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q) (hqB : range q ⊆ B)
    (θ : Fin 3 → loopCircle)
    (huniq : ∀ w : C(closedDisk, M), IsMorreyDisk G Γ w →
      (∀ j, diskTrace w (θ j) = Γ (θ j)) → w = q)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huθ : ∀ n j, diskTrace (u n) (θ j) = Γ (θ j)) (huB : ∀ n, range (u n) ⊆ B)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ w : C(closedDisk, M),
      (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ k in atTop, ∀ z, riemannianEDistOf G (u (φ (ψ k)) z) (w z) < ε) ∧
      (∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
        Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
        (∀ᶠ n in atTop, MapsTo (diskExtension (u (φ (ψ n)))) Kc
          (extChartAt 𝓘(ℝ, E) p).source) ∧
        ∀ k : ℕ, TendstoUniformlyOn
          (fun n => iteratedFDeriv ℝ k
            (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u (φ (ψ n))) z)))
          (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc) ∧
      DiskSmoothInterior (E := E) w ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G (diskExtension w) z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G (diskExtension w) z = 0) ∧
      DiskWeakJordanTrace Γ w) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (q z) < ε) ∧
    (∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) ∧
    Tendsto (fun n => riemannianDiskArea (Gn n) (u n)) atTop (𝓝 (riemannianDiskArea G q)) := by
  -- 每个子列的更细子列的极限都是 `q`
  have key : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ k in atTop, ∀ z, riemannianEDistOf G (u (φ (ψ k)) z) (q z) < ε) ∧
      (∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
        Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
        (∀ᶠ n in atTop, MapsTo (diskExtension (u (φ (ψ n)))) Kc
          (extChartAt 𝓘(ℝ, E) p).source) ∧
        ∀ k : ℕ, TendstoUniformlyOn
          (fun n => iteratedFDeriv ℝ k
            (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u (φ (ψ n))) z)))
          (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) ∧
      Tendsto (fun k => riemannianDiskArea (Gn (φ (ψ k))) (u (φ (ψ k)))) atTop
        (𝓝 (riemannianDiskArea G q)) := by
    intro φ hφ
    obtain ⟨ψ, hψ, w, hC0, hCk, hwi, hwconf, hwharm, hwtr⟩ := hsub φ hφ
    have hat : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφ.comp hψ).tendsto_atTop
    have hrel' : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
        |(Gn (φ (ψ k))).inner x v v - G.inner x v v| ≤ ε * G.inner x v v := fun ε hε =>
      hat.eventually (hrel ε hε)
    obtain ⟨hM, -, hT⟩ := limit_identification_chain_R7A (u := fun k => u (φ (ψ k)))
      (Gn := fun k => Gn (φ (ψ k))) hrel' hΓ hq hQ hqB (fun k => hu _) (fun k => huB _)
      hwi hwconf hwharm hwtr hCk
    -- 三点归一由 `C⁰` 收敛继承
    have hθw : ∀ j, diskTrace w (θ j) = Γ (θ j) := by
      intro j
      by_contra hne
      have hne' : riemannianEDistOf G (w (diskBoundary (θ j))) (Γ (θ j)) ≠ 0 := fun h0 =>
        hne (eq_of_riemannianEDistOf_eq_zero_R8 G h0)
      obtain ⟨k, hk⟩ := (hC0 _ (pos_iff_ne_zero.mpr hne')).exists
      have hk' := hk (diskBoundary (θ j))
      have hu0 : u (φ (ψ k)) (diskBoundary (θ j)) = Γ (θ j) := huθ _ j
      rw [hu0, riemannianEDistOf_comm] at hk'
      exact lt_irrefl _ hk'
    have hwq : w = q := huniq w hM hθw
    rw [hwq] at hC0 hCk
    exact ⟨ψ, hψ, hC0, hCk, hT⟩
  refine ⟨fun ε hε => eventually_of_subseq_R7A fun φ hφ => ?_, fun p Kc hKc hKs => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨ψ, hψ, hC0, -, -⟩ := key φ hφ
    exact ⟨ψ, hψ, hC0 ε hε⟩
  · refine eventually_of_subseq_R7A fun φ hφ => ?_
    obtain ⟨ψ, hψ, -, hCk, -⟩ := key φ hφ
    exact ⟨ψ, hψ, (hCk p Kc hKc hKs).1⟩
  · intro k U hU
    refine eventually_of_subseq_R7A fun φ hφ => ?_
    obtain ⟨ψ, hψ, -, hCk, -⟩ := key φ hφ
    exact ⟨ψ, hψ, (hCk p Kc hKc hKs).2 k U hU⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    refine eventually_of_subseq_R7A fun φ hφ => ?_
    obtain ⟨ψ, hψ, -, -, hT⟩ := key φ hφ
    exact ⟨ψ, hψ, Metric.tendsto_nhds.mp hT ε hε⟩

/-- **G5 consumer**（R7A → R8 接口）：G5b 的整序列 `hC0` / `hCk` 逐字喂
`second_trim_regular_collar_R8`（R7 本体 precompactness 前提 `hsub` + R5 唯一性 `huniq` ⇒ 二次 trim 的
rank / collar / 自身 trace 极小）。 -/
theorem second_trim_regular_collar_of_subsequence_R7A [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hd : Module.finrank ℝ E = 3)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q) (hqB : range q ⊆ B)
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {ρ₁ s : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hs : s < 1)
    (hqcol : ∀ z w : closedDisk, ρ₁ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (θ : Fin 3 → loopCircle)
    (huniq : ∀ w : C(closedDisk, M), IsMorreyDisk G Γ w →
      (∀ j, diskTrace w (θ j) = Γ (θ j)) → w = q)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huθ : ∀ n j, diskTrace (u n) (θ j) = Γ (θ j)) (huB : ∀ n, range (u n) ⊆ B)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ w : C(closedDisk, M),
      (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ k in atTop, ∀ z, riemannianEDistOf G (u (φ (ψ k)) z) (w z) < ε) ∧
      (∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
        Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension w ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
        (∀ᶠ n in atTop, MapsTo (diskExtension (u (φ (ψ n)))) Kc
          (extChartAt 𝓘(ℝ, E) p).source) ∧
        ∀ k : ℕ, TendstoUniformlyOn
          (fun n => iteratedFDeriv ℝ k
            (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u (φ (ψ n))) z)))
          (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension w z))) atTop Kc) ∧
      DiskSmoothInterior (E := E) w ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G (diskExtension w) z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G (diskExtension w) z = 0) ∧
      DiskWeakJordanTrace Γ w) :
    ∃ μ : ℝ, μ < 1 ∧ ∀ᶠ n in atTop,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z)) ∧
      (∀ z w : closedDisk, μ < ‖(z : ℂ)‖ →
        affineSubdisk (u n) 0 s z = affineSubdisk (u n) 0 s w → z = w) ∧
      IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk (u n) 0 s)) ∧
      IsMorreyDisk (Gn n) (diskTrace (affineSubdisk (u n) 0 s)) (affineSubdisk (u n) 0 s) := by
  obtain ⟨hC0, hCk, -⟩ := varying_metric_compactness_of_subsequence_R7A hrel hΓ hq hQ hqB θ huniq
    hu huθ huB hsub
  exact second_trim_regular_collar_R8 hΓ hd hq hqrank hρ₁ hρ₁s hs hqcol hu hC0 hCk

end DifferentialGeometry.Geometry

end
