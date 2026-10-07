import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NoTransverseTransportHC_R15T
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetAdaptersADP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SecondTrimR8
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TrimCollarMR1

/-!
# S-MY-R8 consumer：二次 trim 数据（G1–G5）接 R15T / ADAPT 的终端接口

* `hMY_concl_of_second_trim_HC2_R8`：`_HC2` 形。R15T 的 `hMY_concl_of_c1_limit_trimmed_HC2_R15T` 要一列
  `v n : ℂ → U` 满足 `hv / hinj / hval / hchart / hder`；这里 `v n z := diskExtension (u n) (r • z)`，
  `hv / hval / hchart / hder` 全部由 G5（`second_trim_c1_data_R8`）从显式 chart `C^∞_loc` 数据 `hCk` 给出，
  **只剩单射性**（`hinj`，R9–R14 的输出）作显式假设。
* `noTransverse_of_second_trim_open_ADP_R8`：open-target 形。`K° = O ↪ M`，`q₂ : C(closedDisk, O)` 是
  `O`-Morrey 极限盘，`qO = affineSubdisk q₂ 0 r`；ADAPT 的 `noTransverse_of_c1_limit_open_trimmed_ADP`
  同样由 G5 喂满，剩单射性。
* `lemma_R1_of_second_trim_R8`：G2 + G3 + G4 合成后，`n` 充分大时 `vₙ = affineSubdisk (uₙ) 0 s`
  满足 R1（`lemma_R1_MR1`）的全部前提（对**自身** trace 的 Morrey disk、smooth embedded loop、闭盘 smooth
  extension + rank、内部不碰边界曲线），于是二次 trim 盘再次进入 R1 / R9。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.CuspP1

universe w

/-- **R8 + R15 → `hMY` 结论（`_HC2` 形，G5 喂满）。** collar `ρ₀` 之后、任意 `r ∈ (ρ₀, 1)`：给定一列
`un : ℕ → C(closedDisk, U)`，内部光滑，且（对 `q` 的 chart `C^∞_loc` 收敛 `hCk`，U 的 chart）、
`vₙ = un(r·)` 在 `ball 0 1` 上单射 ⇒ `Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧ 闭盘 rank`。
`hv / hval / hchart / hder` 全由 `second_trim_c1_data_R8` 给出；单射性 `hinj` 是 R9–R14 的输出。 -/
theorem hMY_concl_of_second_trim_HC2_R8
    {P : OrientedThreeStage.{w}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    let ι : C(U, (postStage F.observation t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
        ∀ un : ℕ → C(closedDisk, U),
          (∀ n, ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension (un n)) (Metric.ball (0 : ℂ) 1)) →
          (∀ (p : U) (Kc : Set ℂ), IsCompact Kc →
            Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt (𝓡 3) p).source →
            (∀ᶠ n in atTop, MapsTo (diskExtension (un n)) Kc (extChartAt (𝓡 3) p).source) ∧
            ∀ k : ℕ, TendstoUniformlyOn
              (fun n => iteratedFDeriv ℝ k
                (fun z => extChartAt (𝓡 3) p (diskExtension (un n) z)))
              (iteratedFDeriv ℝ k (fun z => extChartAt (𝓡 3) p (diskExtension q z)))
              atTop Kc) →
          (∀ᶠ n in atTop, InjOn (fun z : ℂ => diskExtension (un n) (r • z))
            (Metric.ball (0 : ℂ) 1)) →
          Function.Injective q ∧
            ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
              ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
                Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd
  obtain ⟨ρ₀, hρ₀, hρ₀1, h⟩ :=
    hMY_concl_of_c1_limit_trimmed_HC2_R15T t a ha ρ hρ hcvx γU q hsm hMor hneg hbd
  refine ⟨ρ₀, hρ₀, hρ₀1, fun r hr hr1 un hus hCk hinj => ?_⟩
  obtain ⟨hv, -, hval, hchart, hder⟩ :=
    second_trim_c1_data_R8 (hρ₀.trans hr) hr1 hMor.smoothInterior hus hCk
  exact h r hr hr1 (fun n z => diskExtension (un n) (r • z)) (Eventually.of_forall hv) hinj
    hval hchart hder

/-- **ADAPT open-target 形**（`K° = O ↪ M = U`）：`q₂ : C(closedDisk, O)` 是 `O`-Morrey 极限盘
（`q = ι ∘ q₂`，`ι : O ↪ M`），`un : ℕ → C(closedDisk, O)` 在 `q₂` 的 `O`-chart 下 `C^∞_loc` 收敛（`hCk`）。
`qO := affineSubdisk q₂ 0 r`；ADAPT 的 `noTransverse_of_c1_limit_open_trimmed_ADP` 的
`hQO / hqO / hv / hval / hchart / hder` 全由 `IsMorreyDisk.smoothDiskExtension_affineSubdisk` 与 G5 给出，
只剩单射性 `hinj`。 -/
theorem noTransverse_of_second_trim_open_ADP_R8
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {O : Opens M} {gO : SmoothRiemannianMetric 𝓘(ℝ, E) O} {Γ : freeLoop O}
    {q₂ : C(closedDisk, O)} (hq₂ : IsMorreyDisk gO Γ q₂) {q : C(closedDisk, M)}
    (hqq₂ : (⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp q₂ = q) {ρ₀ r : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : 0 < r) (hρr : ρ₀ < r) (hr1 : r < 1) {un : ℕ → C(closedDisk, O)}
    (hus : ∀ n, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension (un n)) (Metric.ball (0 : ℂ) 1))
    (hCk : ∀ (p : O) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q₂ ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (un n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (un n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q₂ z))) atTop Kc)
    (hinj : ∀ᶠ n in atTop, InjOn (fun z : ℂ => diskExtension (un n) (r • z))
      (Metric.ball (0 : ℂ) 1)) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y))) := by
  have hinside : ‖(0 : ℂ)‖ + r < 1 := by simpa using hr1
  have hQO := hq₂.smoothDiskExtension_affineSubdisk 0 r hr.le hinside
  obtain ⟨hv, -, hval, hchart, hder⟩ := second_trim_c1_data_R8 hr hr1 hq₂.smoothInterior hus hCk
  subst hqq₂
  exact noTransverse_of_c1_limit_open_trimmed_ADP hcol hr hρr hQO rfl
    (v := fun n z => diskExtension (un n) (r • z)) (Eventually.of_forall hv) hinj hval hchart hder

/-- **G2 + G3 + G4 ⇒ R1 的前提**：`n` 充分大时 `vₙ = affineSubdisk (uₙ) 0 s` 满足 `lemma_R1_MR1` 的全部
前提（G4：对自身 trace 的 Morrey disk 与 smooth embedded loop；闭盘 smooth extension
`fun z => diskExtension (uₙ) (s • z)`；G2：闭盘 rank；G3：内部不碰边界曲线），于是 R1 给出每个 `vₙ` 的
collision 源点 `ε`-分离与一致 fiber 基数界。 -/
theorem second_trim_collision_data_R8
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hd : Module.finrank ℝ E = 3)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q)
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {ρ₁ s : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hs : s < 1)
    (hqcol : ∀ z w : closedDisk, ρ₁ < ‖(z : ℂ)‖ → q z = q w → z = w)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (hC0 : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (q z) < ε)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    ∀ᶠ n in atTop,
      (∃ ε : ℝ, 0 < ε ∧ ∀ x y : closedDisk, x ≠ y →
        affineSubdisk (u n) 0 s x = affineSubdisk (u n) 0 s y → ε ≤ dist (x : ℂ) (y : ℂ)) ∧
      ∃ m : ℕ, ∀ p : M, ((affineSubdisk (u n) 0 s) ⁻¹' {p}).Finite ∧
        ((affineSubdisk (u n) 0 s) ⁻¹' {p}).ncard ≤ m := by
  have hs0 : 0 < s := hρ₁.trans hρ₁s
  obtain ⟨μ, hμ, h⟩ := second_trim_regular_collar_R8 hΓ hd hq hqrank hρ₁ hρ₁s hs hqcol hu hC0 hCk
  filter_upwards [h] with n ⟨h1, h2, h3, h4⟩
  have hQ : SmoothDiskExtension (E := E) (affineSubdisk (u n) 0 s)
      (fun z => diskExtension (u n) (s • z)) := by
    have := (hu n).smoothDiskExtension_affineSubdisk 0 s hs0.le (by simpa using hs)
    simpa only [zero_add] using this
  have hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle,
      affineSubdisk (u n) 0 s z ≠ diskTrace (affineSubdisk (u n) 0 s) θ := by
    intro z hz θ hzθ
    have hb : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := Circle.norm_coe _
    have h5 : diskBoundary θ = z := h2 (diskBoundary θ) z (by rw [hb]; exact hμ) hzθ.symm
    have h6 : ‖(z : ℂ)‖ = 1 := by rw [← h5]; exact hb
    exact absurd hz (by rw [h6]; exact lt_irrefl 1)
  obtain ⟨-, -, -, -, -, hε, hm⟩ := lemma_R1_MR1 h4 h3 hQ h1 hsep
  exact ⟨hε, hm⟩

end GC.LongTime.CuspP1
