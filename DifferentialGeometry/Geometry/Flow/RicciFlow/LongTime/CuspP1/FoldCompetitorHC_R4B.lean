import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorR4B

/-!
# S-MY-R4B G2：`_HC2` 的 (U, G) 上的 fold competitor（外审 R4 → R12 用法形状）

G1 `exists_better_competitor_of_fold_R4B`（`Plateau/FoldCompetitorR4B`）在 `_HC2`
（`exists_eventual_confined_morrey_disk_HC2` 的 clause）的 target `U = {ρ < a}` 与 metric
`G = canonicalPositiveDomainMetric_P2A …` 上的实例：binder 前缀（`t a ha ρ hρ`，`let U δ hδ hU G`）
与 `closed_rank_of_HC_clauses_KP` 逐字相同（`hcvx` 在 fold lemma 里不用，按「无未用假设」省略）。
target 是 `U` 本身，所以 W = `Set.univ`：`hpW` 自动成立，competitor 仍落在 `U` 内；面积是 `G` 下的
`riemannianDiskArea G`。

* `exists_better_competitor_of_fold_HC2_R4B`：G1 在 (U, G) 上的实例（`range ⊆ U` 是平凡的，省略）。
* `fold_conormal_sum_eq_zero_of_minimal_HC2_R4B`：R12 的用法形状 —— `f` 对同 `diskTrace`、
  metric-Lipschitz 的 admissible 盘面积极小 ⇒ seam 处 `η₊ + η₋ = 0`（反证：fold ⇒ G1 给出严格更小
  的 admissible competitor）。
* `fold_area_gt_morrey_HC2_R4B`：同一形状的 Morrey 版 —— `q` 是 `γU` 的 `IsMorreyDisk`，`f` 是
  带同一 weak Jordan trace 的 Lipschitz 盘；`f` 在 seam 点 `η₊ + η₋ ≠ 0` ⇒ `A(q) < A(f)`。
* `cap_conormal_sum_eq_zero_of_area_sum_le_HC2_R4B`：R12 的两 cap 形（`A(a₊) + A(a₋) ≤ 2A(q)`，
  `q` 极小 ⇒ 两边取等号 ⇒ 每个 cap 在 regular seam 处 `η₊ + η₋ = 0`）。
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

/-- **G1 在 `_HC2` 的 (U, G) 上的实例。**  `f : C(closedDisk, U)` 是 `G`-Lipschitz 盘；seam 两侧的
闭半盘 sheet 是 conformal harmonic、`C¹` 到 seam、differential 单射（原极小盘的片）；seam 点 `p`
处 `η₊ + η₋ ≠ 0` ⇒ ∃ admissible `v`（Lipschitz、同 `diskTrace`）与紧集 `S ⊆ D°`（seam 点处的
闭 patch 圆盘，半径 `r ≤ R`），`S` 外（含 `∂D`）`v = f`，`A_G(v) < A_G(f)`。 -/
theorem exists_better_competitor_of_fold_HC2_R4B
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
      ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f) (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f ∘ conj) (openHalfDisk p R) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f ∘ conj) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f) z = 0) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f ∘ conj) z = 0) →
      inwardConormalWithin G (diskExtension f) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ conj) (p : ℂ)) (diskExtension f (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0 →
    ∃ (v : C(closedDisk, U)) (K : ℝ≥0) (S : Set ℂ),
      IsCompact S ∧ S ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∃ r : ℝ, 0 < r ∧ r ≤ R ∧ S = Metric.closedBall (p : ℂ) r) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ S → v z = f z) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → v z = f z) ∧
      (∀ z w, riemannianEDistOf G (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace f ∧
      riemannianDiskArea G v < riemannianDiskArea G f := by
  intro U δ hδ hU G f L hfLip p R hR hpR hsh hshr hi hir hshi hshri hconf hconfr htension
    htensionr hfold
  obtain ⟨v, K, S, hS, hSD, hSr, hout, hbd, hvLip, hvtrace, -, hvarea⟩ :=
    exists_better_competitor_of_fold_R4B G f hfLip (W := Set.univ) (Set.subset_univ _) hR hpR
      hsh hshr hi hir hshi hshri hconf hconfr htension htensionr
      (by rw [interior_univ]; exact Set.mem_univ _) hfold
  exact ⟨v, K, S, hS, hSD, hSr, hout, hbd, hvLip, hvtrace, hvarea⟩

/-- **R12 的用法形状：面积极小 ⇒ seam 处 `η₊ + η₋ = 0`。**  `f : C(closedDisk, U)` 对同一
`diskTrace` 的 metric-Lipschitz admissible 盘面积极小（`hmin`，即 `IsMorreyDisk.minimizesLipschitz`
的显式形），seam 两侧是 conformal harmonic 的闭半盘 sheet ⇒ seam 点 `p` 处两个 inward conormal
的和为 `0`。证明：否则 G1 给出面积严格更小的 admissible competitor，与 `hmin` 矛盾。 -/
theorem fold_conormal_sum_eq_zero_of_minimal_HC2_R4B
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
      ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f) (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f ∘ conj) (openHalfDisk p R) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f ∘ conj) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f) z = 0) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f ∘ conj) z = 0) →
    inwardConormalWithin G (diskExtension f) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast (𝓡 3) ((diskExtension f ∘ conj) (p : ℂ)) (diskExtension f (p : ℂ))
        (inwardConormalWithin G (diskExtension f ∘ conj) (closedHalfDisk p R) (p : ℂ)) = 0 := by
  intro U δ hδ hU G f L hfLip hmin p R hR hpR hsh hshr hi hir hshi hshri hconf hconfr htension
    htensionr
  by_contra hfold
  obtain ⟨v, K, -, -, -, -, -, -, hvLip, hvtrace, hvarea⟩ :=
    exists_better_competitor_of_fold_HC2_R4B t a ha ρ hρ f hfLip hR hpR hsh hshr hi hir hshi
      hshri hconf hconfr htension htensionr hfold
  exact absurd (hmin v hvtrace ⟨K, hvLip⟩) (not_le.mpr hvarea)

/-- **Morrey 版（R12 的严格形）。**  `q` 是 `γU` 的 `IsMorreyDisk`（对同 weak Jordan trace 的
Lipschitz 盘面积极小），`f` 是带同一 weak Jordan trace 的 `G`-Lipschitz 盘；`f` 在 seam 点 `p`
处 `η₊ + η₋ ≠ 0` ⇒ `A_G(q) < A_G(f)`。证明：G1 给出 `A(v) < A(f)` 的 admissible `v`（同
`diskTrace`，故同 weak Jordan trace），`q` 的极小性给 `A(q) ≤ A(v)`。 -/
theorem fold_area_gt_morrey_HC2_R4B
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
      ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f) (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f ∘ conj) (openHalfDisk p R) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f ∘ conj) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f) z = 0) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f ∘ conj) z = 0) →
      inwardConormalWithin G (diskExtension f) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ conj) (p : ℂ)) (diskExtension f (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0 →
    riemannianDiskArea G q < riemannianDiskArea G f := by
  intro U δ hδ hU G γU q hq f L hftr hfLip p R hR hpR hsh hshr hi hir hshi hshri hconf hconfr
    htension htensionr hfold
  obtain ⟨v, K, -, -, -, -, -, -, hvLip, hvtrace, hvarea⟩ :=
    exists_better_competitor_of_fold_HC2_R4B t a ha ρ hρ f hfLip hR hpR hsh hshr hi hir hshi
      hshri hconf hconfr htension htensionr hfold
  obtain ⟨σ, hσ, hσf⟩ := hftr
  exact (hq.minimizesLipschitz v ⟨σ, hσ, hvtrace.trans hσf⟩ ⟨K, hvLip⟩).trans_lt hvarea

/-- **R12 的两 cap 形。**  `q` 是 `γU` 的 `IsMorreyDisk`；两个 cap `f`（= `a₊`）、`f'`（= `a₋`）是
带同一 weak Jordan trace 的 `G`-Lipschitz 盘，面积和 `A(f) + A(f') ≤ 2 A(q)`。`q` 极小给
`A(q) ≤ A(f')`；若 `f` 在某 regular seam 点 `η₊ + η₋ ≠ 0`，`fold_area_gt_morrey_HC2_R4B` 给
`A(q) < A(f)`，两者相加与面积和的上界矛盾。故 seam 点处 `η₊ + η₋ = 0`。 -/
theorem cap_conormal_sum_eq_zero_of_area_sum_le_HC2_R4B
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
    ∀ (f f' : C(closedDisk, U)) {L L' : ℝ≥0}, DiskWeakJordanTrace γU f →
      DiskWeakJordanTrace γU f' →
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      (∀ z w, riemannianEDistOf G (f' z) (f' w) ≤ (L' : ℝ≥0∞) * edist z w) →
      riemannianDiskArea G f + riemannianDiskArea G f' ≤ 2 * riemannianDiskArea G q →
      ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f) (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f ∘ conj) (openHalfDisk p R) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f ∘ conj) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f) z = 0) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f ∘ conj) z = 0) →
    inwardConormalWithin G (diskExtension f) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast (𝓡 3) ((diskExtension f ∘ conj) (p : ℂ)) (diskExtension f (p : ℂ))
        (inwardConormalWithin G (diskExtension f ∘ conj) (closedHalfDisk p R) (p : ℂ)) = 0 := by
  intro U δ hδ hU G γU q hq f f' L L' hftr hftr' hfLip hfLip' hsum p R hR hpR hsh hshr hi hir
    hshi hshri hconf hconfr htension htensionr
  by_contra hfold
  have hgt := fold_area_gt_morrey_HC2_R4B t a ha ρ hρ γU q hq f hftr hfLip hR hpR hsh hshr hi hir
    hshi hshri hconf hconfr htension htensionr hfold
  have hle := hq.minimizesLipschitz f' hftr' ⟨L', hfLip'⟩
  linarith

/-- **Consumer（R12 的 equal-area 用法）。**  `q` 是 `γU` 的 `IsMorreyDisk`，`f` 带同一 weak Jordan
trace 且 `A(f) ≤ A(q)`（R2 / R12 的 cap collapse 面积合同给出）；则 `f` 对同 `diskTrace` 的
Lipschitz admissible 盘面积极小，`fold_conormal_sum_eq_zero_of_minimal_HC2_R4B` 给 seam 点处
`η₊ + η₋ = 0`。 -/
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
      riemannianDiskArea G f ≤ riemannianDiskArea G q →
      (∀ z w, riemannianEDistOf G (f z) (f w) ≤ (L : ℝ≥0∞) * edist z w) →
      ∀ {p R : ℝ}, 0 < R → ‖(p : ℂ)‖ + R < 1 →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f) (closedHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) 1 (diskExtension f ∘ conj) (closedHalfDisk p R) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f) (closedHalfDisk p R) z)) →
      (∀ z ∈ closedHalfDisk p R, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension f ∘ conj) (closedHalfDisk p R) z)) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f) (openHalfDisk p R) →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ (diskExtension f ∘ conj) (openHalfDisk p R) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt G (diskExtension f ∘ conj) z) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f) z = 0) →
      (∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension G (diskExtension f ∘ conj) z = 0) →
      inwardConormalWithin G (diskExtension f) (closedHalfDisk p R) (p : ℂ) +
        tangentSpaceCast (𝓡 3) ((diskExtension f ∘ conj) (p : ℂ)) (diskExtension f (p : ℂ))
          (inwardConormalWithin G (diskExtension f ∘ conj) (closedHalfDisk p R) (p : ℂ)) = 0 := by
  intro U δ hδ hU G γU q hq f L hftr hfa hfLip p R hR hpR hsh hshr hi hir hshi hshri hconf hconfr
    htension htensionr
  refine fold_conormal_sum_eq_zero_of_minimal_HC2_R4B t a ha ρ hρ f hfLip ?_ hR hpR hsh hshr hi hir
    hshi hshri hconf hconfr htension htensionr
  obtain ⟨σ, hσ, hσf⟩ := hftr
  exact fun v hv hvLip => hfa.trans (hq.minimizesLipschitz v ⟨σ, hσ, hv.trans hσf⟩ hvLip)

end GC.LongTime.CuspP1
