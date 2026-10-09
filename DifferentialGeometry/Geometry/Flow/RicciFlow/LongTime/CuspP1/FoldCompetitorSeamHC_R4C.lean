import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorSeamR4C

/-!
# S-MY-R4C G2：`_HC2` 的 (U, G) 上的 general-seam / chart fold competitor（外审 R4 → R12 / R13 用法形状）

G1 `exists_better_competitor_of_fold_seam_R4C`（`Plateau/FoldCompetitorSeamR4C`）在 `_HC2`
（`exists_eventual_confined_morrey_disk_HC2` 的 clause）的 target `U = {ρ < a}` 与 metric
`G = canonicalPositiveDomainMetric_P2A …` 上的实例：binder 前缀（`t a ha ρ hρ`，`let U δ hδ hU G`）
与 R4B 的 `FoldCompetitorHC_R4B` 逐字相同。target 是 `U` 本身，所以 W = `Set.univ`：`hpW` 自动成立，
competitor 仍落在 `U` 内；面积是 `G` 下的 `riemannianDiskArea`。与 R4B G2 的区别：seam 是 IMS03
`sourceChart` `χ` 下的任意内部光滑弧 `χ '' [p - R, p + R]`，sheet 是 `U₀ ∘ ψᵢ` 形的 reparametrization。

* `exists_better_competitor_of_fold_seam_HC2_R4C`：G1 在 (U, G) 上的实例（`range ⊆ U` 平凡，省略）。
* `fold_seam_conormal_sum_eq_zero_of_minimal_HC2_R4C`：R12 / R13 的用法形状 —— `f` 对同 `diskTrace`、
  metric-Lipschitz 的 admissible 盘面积极小 ⇒ chart seam 点处 `η₊ + η₋ = 0`（反证）。
* `fold_seam_area_gt_morrey_HC2_R4C`：Morrey 版 —— `q` 是 `γU` 的 `IsMorreyDisk`（`U₀ = diskExtension q`
  就是原极小盘），`f` 是带同一 weak Jordan trace 的 Lipschitz 盘，两侧 sheet 是 `q` 的
  reparametrization；seam 点 `η₊ + η₋ ≠ 0` ⇒ `A(q) < A(f)`。
* `exchange_seam_conormal_sum_eq_zero_HC2_R4C`：**R13 的用法形状** —— `f` 是 R13 的 exchange disk
  `f̂`（`ℓ` 外 `= q`、`Ω₂` 内 `= q ∘ B`，同 trace，面积合同 `A(f̂) ≤ A(q)`）；seam 点非 corner
  的 regular 光滑弧上 `ψ₁ = χ`、`ψ₂ = B ∘ χ ∘ conj`；于是 seam 点处 `η₊ + η₋ = 0`，即 R13 的
  「横截 ⇒ fold ⇒ 矛盾」中的矛盾一半。（R13 本体——cornered Schoenflies 延拓 `B` 与面积换元——不在此。）
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology NNReal ENNReal ComplexConjugate

namespace GC.LongTime.CuspP1

universe u

/-- **G1 在 `_HC2` 的 (U, G) 上的实例（general seam）。**  `f : C(closedDisk, U)` 是 `G`-Lipschitz 盘；
`χ` 是 `sourceChart`；seam 两侧在 chart 里的闭半盘 sheet `f ∘ χ`、`f ∘ χ ∘ conj` 是 `C¹` 到 seam、
differential 单射、且是 conformal harmonic 盘 `U₀` 的 reparametrization `U₀ ∘ ψᵢ`；seam 点 `χ p` 处
`η₊ + η₋ ≠ 0` ⇒ ∃ admissible `v`（Lipschitz、同 `diskTrace`）与紧集 `S ⊆ D°`
（`S = χ '' closedBall p r`，`r ≤ R`，seam 弧邻域内的 patch），`S` 外（含 `∂D`）`v = f`，
`A_G(v) < A_G(f)`。 -/
theorem exists_better_competitor_of_fold_seam_HC2_R4C
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (f : C(closedDisk, U)) {L : ℝ≥0},
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      ∀ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source →
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ (U₀ : ℂ → U),
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U₀ (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G U₀ z) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G U₀ z = 0) →
      ∀ (ψ₁ ψ₂ : ℂ → ℂ) {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R) →
      MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z)) →
      EqOn (diskExtension f ∘ χ) (U₀ ∘ ψ₁) (openHalfDisk p R) →
      EqOn (diskExtension f ∘ χ ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R) →
      inwardConormalWithin G (diskExtension f ∘ χ) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ χ ∘ conj) (p : ℂ))
          ((diskExtension f ∘ χ) (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R)
            (p : ℂ)) ≠ 0 →
    ∃ (v : C(closedDisk, U)) (K : ℝ≥0) (S : Set ℂ),
      IsCompact S ∧ S ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∃ r : ℝ, 0 < r ∧ r ≤ R ∧ S = χ '' Metric.closedBall (p : ℂ) r) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ S → v z = f z) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → v z = f z) ∧
      (∀ z w, riemannianEDistOf G (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace f ∧
      riemannianDiskArea G v < riemannianDiskArea G f := by
  intro U δ hδ hU G f L hfLip χ hsrc hinside U₀ hU₀ hconf₀ htension₀ ψ₁ ψ₂ p R hR hpR hsh hshr hi
    hir hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂ hfold
  obtain ⟨v, K, S, hS, hSD, hSr, hout, hbd, hvLip, hvtrace, -, hvarea⟩ :=
    exists_better_competitor_of_fold_seam_R4C G f hfLip (W := Set.univ) (Set.subset_univ _) χ
      hsrc hinside U₀ ψ₁ ψ₂ hU₀ hconf₀ htension₀ hR hpR hsh hshr hi hir hψ₁ hψ₂ hmaps₁ hmaps₂
      hbij₁ hbij₂ heq₁ heq₂ (by rw [interior_univ]; exact Set.mem_univ _) hfold
  exact ⟨v, K, S, hS, hSD, hSr, hout, hbd, hvLip, hvtrace, hvarea⟩

/-- **面积极小 ⇒ chart seam 处 `η₊ + η₋ = 0`。**  `f : C(closedDisk, U)` 对同一 `diskTrace` 的
metric-Lipschitz admissible 盘面积极小（`hmin`，即 `IsMorreyDisk.minimizesLipschitz` 的显式形），
seam 两侧是 conformal harmonic 盘 `U₀` 的 reparametrization ⇒ seam 点处两个 inward conormal 的和为 `0`。
证明：否则 G1 给出面积严格更小的 admissible competitor，与 `hmin` 矛盾。 -/
theorem fold_seam_conormal_sum_eq_zero_of_minimal_HC2_R4C
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (f : C(closedDisk, U)) {L : ℝ≥0},
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      (∀ v : C(closedDisk, U), diskTrace v = diskTrace f →
        (∃ K : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) →
          riemannianDiskArea G f ≤ riemannianDiskArea G v) →
      ∀ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source →
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ (U₀ : ℂ → U),
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U₀ (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G U₀ z) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G U₀ z = 0) →
      ∀ (ψ₁ ψ₂ : ℂ → ℂ) {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R) →
      MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z)) →
      EqOn (diskExtension f ∘ χ) (U₀ ∘ ψ₁) (openHalfDisk p R) →
      EqOn (diskExtension f ∘ χ ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R) →
      inwardConormalWithin G (diskExtension f ∘ χ) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ χ ∘ conj) (p : ℂ))
          ((diskExtension f ∘ χ) (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R)
            (p : ℂ)) = 0 := by
  intro U δ hδ hU G f L hfLip hmin χ hsrc hinside U₀ hU₀ hconf₀ htension₀ ψ₁ ψ₂ p R hR hpR hsh hshr
    hi hir hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂
  by_contra hfold
  obtain ⟨v, K, -, -, -, -, -, -, hvLip, hvtrace, hvarea⟩ :=
    exists_better_competitor_of_fold_seam_HC2_R4C t a ha ρ hρ f hfLip χ hsrc hinside U₀ hU₀ hconf₀
      htension₀ ψ₁ ψ₂ hR hpR hsh hshr hi hir hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂ hfold
  exact absurd (hmin v hvtrace ⟨K, hvLip⟩) (not_le.mpr hvarea)

/-- **Morrey 版（chart seam）。**  `q` 是 `γU` 的 `IsMorreyDisk`，其延拓 `diskExtension q` 就是 conformal
harmonic 的原极小盘 `U₀`；`f` 是带同一 weak Jordan trace 的 `G`-Lipschitz 盘，seam 两侧 sheet 是 `q` 的
reparametrization；seam 点 `χ p` 处 `η₊ + η₋ ≠ 0` ⇒ `A_G(q) < A_G(f)`。证明：G1 给出 `A(v) < A(f)` 的
admissible `v`（同 `diskTrace`，故同 weak Jordan trace），`q` 的极小性给 `A(q) ≤ A(v)`。 -/
theorem fold_seam_area_gt_morrey_HC2_R4C
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)), IsMorreyDisk G γU q →
    ∀ (f : C(closedDisk, U)) {L : ℝ≥0}, DiskWeakJordanTrace γU f →
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      ∀ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source →
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ (ψ₁ ψ₂ : ℂ → ℂ) {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R) →
      MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z)) →
      EqOn (diskExtension f ∘ χ) (diskExtension q ∘ ψ₁) (openHalfDisk p R) →
      EqOn (diskExtension f ∘ χ ∘ conj) (diskExtension q ∘ ψ₂) (openHalfDisk p R) →
      inwardConormalWithin G (diskExtension f ∘ χ) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ χ ∘ conj) (p : ℂ))
          ((diskExtension f ∘ χ) (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R)
            (p : ℂ)) ≠ 0 →
    riemannianDiskArea G q < riemannianDiskArea G f := by
  intro U δ hδ hU G γU q hq f L hftr hfLip χ hsrc hinside ψ₁ ψ₂ p R hR hpR hsh hshr hi hir
    hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂ hfold
  obtain ⟨v, K, -, -, -, -, -, -, hvLip, hvtrace, hvarea⟩ :=
    exists_better_competitor_of_fold_seam_HC2_R4C t a ha ρ hρ f hfLip χ hsrc hinside
      (diskExtension q) hq.smoothInterior hq.conformal hq.harmonic ψ₁ ψ₂ hR hpR hsh hshr hi hir
      hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂ hfold
  obtain ⟨σ, hσ, hσf⟩ := hftr
  exact (hq.minimizesLipschitz v ⟨σ, hσ, hvtrace.trans hσf⟩ ⟨K, hvLip⟩).trans_lt hvarea

/-- **R13 的用法形状：exchange disk 在 regular seam 上无 fold。**  `q` 是 `γU` 的 `IsMorreyDisk`，
`f` 是 R13 的 exchange disk `f̂`（`Ω₂` 外 `= q`、`Ω₂` 内 `= q ∘ B`，`B : ∂Ω₂ → ∂Ω₁` 的 bi-Lipschitz
延拓），带同一 weak Jordan trace，面积合同 `A(f̂) ≤ A(q)`（R13 的 exchange 步：
`A(f̂) = A(q) - A(q|Ω₂) + A(q|Ω₁) ≤ A(q)`）。在 `∂Ω₂` 的非 corner regular 点，取 sourceChart `χ`
把该点邻域的 `∂Ω₂` 弧拉直成实轴段（`χ` 的上半盘在 `Ω₂` 外，`χ ∘ conj` 的上半盘在 `Ω₂` 内），
则两侧 sheet 是 `q` 的 reparametrization：外侧 `ψ₁ = χ`，内侧 `ψ₂`（`= B ∘ χ ∘ conj`）。结论：seam 点
`χ p` 处 `η₊ + η₋ = 0`；因此 R13 里「两切平面横截 ⇒ `η₊ + η₋ ≠ 0`」与它矛盾。证明：`q` 极小
给 `A(q) ≤ A(f̂) ≤ A(q)`，fold 则 `fold_seam_area_gt_morrey_HC2_R4C` 给 `A(q) < A(f̂)`。 -/
theorem exchange_seam_conormal_sum_eq_zero_HC2_R4C
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)), IsMorreyDisk G γU q →
    ∀ (f : C(closedDisk, U)) {L : ℝ≥0}, DiskWeakJordanTrace γU f →
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea G f ≤ riemannianDiskArea G q →
      ∀ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source →
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ (ψ₁ ψ₂ : ℂ → ℂ) {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R) →
      MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z)) →
      EqOn (diskExtension f ∘ χ) (diskExtension q ∘ ψ₁) (openHalfDisk p R) →
      EqOn (diskExtension f ∘ χ ∘ conj) (diskExtension q ∘ ψ₂) (openHalfDisk p R) →
      inwardConormalWithin G (diskExtension f ∘ χ) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ χ ∘ conj) (p : ℂ))
          ((diskExtension f ∘ χ) (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R)
            (p : ℂ)) = 0 := by
  intro U δ hδ hU G γU q hq f L hftr hfLip hfa χ hsrc hinside ψ₁ ψ₂ p R hR hpR hsh hshr hi hir
    hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂
  by_contra hfold
  have hgt := fold_seam_area_gt_morrey_HC2_R4C t a ha ρ hρ γU q hq f hftr hfLip χ hsrc hinside
    ψ₁ ψ₂ hR hpR hsh hshr hi hir hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂ hfold
  exact absurd hfa (not_le.mpr hgt)

/-- **R13 的用法形状（pairing 版）：exchange disk 在 regular seam 上无 fold。**  与
`exchange_seam_conormal_sum_eq_zero_HC2_R4C` 同一结论，但 `ψ₁`、`ψ₂` 不再抽象给出，而由 R13 的
exchange 构造的**局部数据**推出：`f = q` 在 `χ` 的上半盘（`Ω₂` 外），`f = q ∘ B` 在 `χ ∘ conj` 的
上半盘（`Ω₂` 内，`B` 是 Schoenflies 延拓在 `∂Ω₂` 非 corner 点附近的光滑分支，开集 `N` 上
`C^∞`、导数处处双射、像落在 `D°`）。于是 `ψ₁ = χ`（局部微分同胚）、`ψ₂ = B ∘ χ ∘ conj`（光滑、导数
双射）。 -/
theorem exchange_seam_conormal_sum_eq_zero_of_pairing_HC2_R4C
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)), IsMorreyDisk G γU q →
    ∀ (f : C(closedDisk, U)) {L : ℝ≥0}, DiskWeakJordanTrace γU f →
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea G f ≤ riemannianDiskArea G q →
      ∀ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source →
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ (B : ℂ → ℂ) (N : Set ℂ), IsOpen N → ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ B N →
      (∀ x ∈ N, Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) B x)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ),
        χ (conj z) ∈ N ∧ B (χ (conj z)) ∈ Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskExtension f (χ z) = diskExtension q (χ z)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ),
        diskExtension f (χ (conj z)) = diskExtension q (B (χ (conj z)))) →
      inwardConormalWithin G (diskExtension f ∘ χ) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ χ ∘ conj) (p : ℂ))
          ((diskExtension f ∘ χ) (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R)
            (p : ℂ)) = 0 := by
  intro U δ hδ hU G γU q hq f L hftr hfLip hfa χ hsrc hinside B N hN p R hR hpR hsh hshr hi hir hB
    hBbij hBN hf₁ hf₂
  have hopenClosed : (openHalfDisk p R : Set ℂ) ⊆ closedHalfDisk p R :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hHB : ∀ z ∈ Metric.closedBall (p : ℂ) R, z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hn : ‖z‖ ≤ dist z (p : ℂ) + ‖(p : ℂ)‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - (p : ℂ)) (p : ℂ)
    have hd := Metric.mem_closedBall.mp hz
    linarith
  have hbarunit : ∀ z ∈ (openHalfDisk p R : Set ℂ), conj z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    apply hHB
    rw [Metric.mem_closedBall, Complex.dist_conj_comm, Complex.conj_ofReal]
    exact (Metric.mem_ball.mp hz.2).le
  let χr := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  have hχsrc : ∀ z ∈ (openHalfDisk p R : Set ℂ), z ∈ χ.source :=
    fun z hz => hsrc (hHB z (Metric.ball_subset_closedBall hz.2))
  have hχrsrc : ∀ z ∈ (openHalfDisk p R : Set ℂ), z ∈ χr.source :=
    fun z hz => ⟨mem_univ _, hsrc (hbarunit z hz)⟩
  have hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (χ : ℂ → ℂ) (openHalfDisk p R) :=
    χ.contMDiffOn_toFun.mono hχsrc
  have hmaps₁ : MapsTo (χ : ℂ → ℂ) (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => hinside ⟨z, hHB z (Metric.ball_subset_closedBall hz.2), rfl⟩
  have hbij₁ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (χ : ℂ → ℂ) z) :=
    fun z hz => ((χ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hsrc (hHB z
      (Metric.ball_subset_closedBall hz.2)))).mfderivToContinuousLinearEquiv (by simp)).bijective
  have hmapsN : MapsTo χr (openHalfDisk p R) N := fun z hz => (hBN z hz).1
  have hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (B ∘ χr) (openHalfDisk p R) :=
    hB.comp (χr.contMDiffOn_toFun.mono hχrsrc) hmapsN
  have hmaps₂ : MapsTo (B ∘ χr) (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hBN z hz).2
  have hbij₂ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (B ∘ χr) z) := by
    intro z hz
    have hdB : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) B (χr z) :=
      (hB.contMDiffAt (hN.mem_nhds (hmapsN hz))).mdifferentiableAt (by simp)
    have hdχr : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) χr z :=
      (χr.contMDiffOn_toFun.contMDiffAt (χr.open_source.mem_nhds (hχrsrc z hz))).mdifferentiableAt
        (by simp)
    rw [mfderiv_comp z hdB hdχr]
    exact (hBbij _ (hmapsN hz)).comp ((χr.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (hχrsrc z hz)).mfderivToContinuousLinearEquiv (by simp)).bijective
  exact exchange_seam_conormal_sum_eq_zero_HC2_R4C t a ha ρ hρ γU q hq f hftr hfLip hfa χ hsrc
    hinside (χ : ℂ → ℂ) (B ∘ χr) hR hpR hsh hshr hi hir hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂
    (fun z hz => hf₁ z hz) (fun z hz => hf₂ z hz)

/-- **Consumer（R13 的矛盾形）。**  R13 的 exchange disk `f̂ = f`（面积合同 `A(f̂) ≤ A(q)`、同 weak
Jordan trace）在 `∂Ω₂` 的非 corner regular 点的 chart seam 上，若两侧 conormal 的和非零（R13：
两切平面横截），则 `False`。直接使用 `exchange_seam_conormal_sum_eq_zero_of_pairing_HC2_R4C`。 -/
example
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)), IsMorreyDisk G γU q →
    ∀ (f : C(closedDisk, U)) {L : ℝ≥0}, DiskWeakJordanTrace γU f →
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea G f ≤ riemannianDiskArea G q →
      ∀ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source →
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ (B : ℂ → ℂ) (N : Set ℂ), IsOpen N → ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ B N →
      (∀ x ∈ N, Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) B x)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ),
        χ (conj z) ∈ N ∧ B (χ (conj z)) ∈ Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskExtension f (χ z) = diskExtension q (χ z)) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ),
        diskExtension f (χ (conj z)) = diskExtension q (B (χ (conj z)))) →
      inwardConormalWithin G (diskExtension f ∘ χ) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ χ ∘ conj) (p : ℂ))
          ((diskExtension f ∘ χ) (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ χ ∘ conj) (closedHalfDisk p R)
            (p : ℂ)) ≠ 0 → False := by
  intro U δ hδ hU G γU q hq f L hftr hfLip hfa χ hsrc hinside B N hN p R hR hpR hsh hshr hi hir hB
    hBbij hBN hf₁ hf₂ hfold
  exact hfold (exchange_seam_conormal_sum_eq_zero_of_pairing_HC2_R4C t a ha ρ hρ γU q hq f hftr
    hfLip hfa χ hsrc hinside B N hN hR hpR hsh hshr hi hir hB hBbij hBN hf₁ hf₂)

end GC.LongTime.CuspP1
