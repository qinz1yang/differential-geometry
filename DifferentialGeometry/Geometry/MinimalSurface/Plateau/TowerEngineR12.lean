import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Variation.NonzeroFoldFlow
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import Mathlib.Topology.Covering.Basic

/-!
# S-MY-R12 G1 / G2：R12 本体与 tower 总装的 conditional engine（`_R12`）

外审 D-R-MY2-20：R12 可以先交付验收为 conditional engine。本文件把 scratch
`MYD3/R10R14.lean` 的 `top_caps_force_injective_MYD3`（R12）与 `prepared_least_area_embedded_MYD3`
（总装）搬入源码树，**未证明的合同全部写成定理的显式 ∀-前提（hypothesis 参数）**——不新建具名 Prop
作假设、无未证目标：

* G1 `top_caps_force_injective_R12`：前提 `hcaps`（10.3/10.4 弱版的输出：同 trace 的 Lipschitz caps、
  `A(a₊) + A(a₋) ≤ 2A(f)`、`f` 非单射 ⇒ 严格亏损 ∨ Fold）与 `hR4r`（R4r：reparametrized fold ⇒ 严格更小
  的同 trace Lipschitz competitor；S-MY-R4C `exists_better_competitor_of_fold_seam_R4C` 的同型合同）
  ⇒ `f` 单射。证明 = 极小性排严格亏损分支；两个 fold 分支经 `hR4r` 与极小性矛盾。
* G2 `prepared_least_area_embedded_R12`：tower 总装。对
  `n ≥ (vertexCollisionPairs T (diskExtension f ∘ α)).card` 强归纳（`T, α` 全程固定、量化在
  `∀ M : Type u` 内，D-22）；每一层取 R10.1 的 `(Nb, R)`：`∂Nb` 含 trace 的分量同胚 `S²` ⇒ R12（G1）；
  否则 R11-step 给 genuine double cover `pr : M' → O` 与严格降的 lift `f'`，
  IH ⇒ `f'` 单射，再经 R14 descent ⇒ `f` 单射。五条前提（R10.1 producer、10.3/10.4 弱版 producer、
  R4r、R11-step、R14）逐字取 scratch 合同的陈述；R10.1 的 notion 在这里作**谓词参数**
  `RelNbhd f F T α Nb R`（不重复定义）：O-MY-R10PL 的输出形状是
  `IsRelRegularNbhd_R10 f Nb R ∧ IsSectorControlledCollapse_R10 F T α Nb R`（同一 `Nb R`），
  实例化 `RelNbhd := fun f F T α Nb R => 该合取`；另附投影前提 `hspine : RelNbhd … → range f ⊆ Nb`
  （对真 notion 是 `IsRelRegularNbhd_R10` 的 `⟨hLN, _⟩` 部分的 `.1`，一行 discharge）。
* G4（`Plateau/FoldCompetitorR4rR12`）：`reparametrized_fold_competitor_R12` 经 S-MY-R4C 证明 R4r，
  所以 `hR4r` 前提可由它 discharge（`[T2Space M]` 对流形给出 `[T3Space M]`）。
* 外审 R-MY3 措辞（lead 转达）：10.3/10.4 的 coverage 部分**不是**「面积取等 ⇒ 两 cap 恰好各覆盖每个面一次」，
  正确表述是 multiplicity bound `A(a₊) + A(a₋) = Σ_σ (m₊,σ + m₋,σ) A_σ` 且 `m₊,σ + m₋,σ ≤ 2`，
  取等 ⇒ `m₊,σ + m₋,σ = 2`（`(2,0)` / `(0,2)` 未被排除），即「每个面的两份 side 在两 caps 的并中被完整计数」。
  这一步整个留在 **producer**（产出 `Fold` 的证明）里；本文件的 `hcaps` 只含弱析取形
  `<` ∨ Fold ∨ Fold，不含任何 coverage 子句。
* `HasReparametrizedFold_R12`：scratch `HasReparametrizedFold_MYD3` 的逐字对象级定义（R4C 无此名；
  它就是 `exists_better_competitor_of_fold_seam_R4C` 在 `χ = 同胚缩放` 下的前提表）。

“0 行”只表示 conditional consumer 完成，不表示 producer 已存在（D-R-MY2-20、D-32）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

universe u

/-- 单位 2-球面（R10.2 / R11 的 stopping rule 用）。 -/
abbrev sphere2_R12 : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- reparametrized fold（scratch `HasReparametrizedFold_MYD3` 逐字；= `NonzeroFoldFlow` 的前提表，
sheet = `U₀ ∘ ψᵢ`，`U₀` 是原极小盘的 conformal harmonic 延拓）。 -/
def HasReparametrizedFold_R12 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : C(closedDisk, M))
    (U₀ : ℂ → M) : Prop :=
  ∃ (p R : ℝ) (ψ₁ ψ₂ : ℂ → ℂ), 0 < R ∧ ‖(p : ℂ)‖ + R < 1 ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension a) (closedHalfDisk p R) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension a ∘ conj) (closedHalfDisk p R) ∧
    (∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension a) (closedHalfDisk p R) z)) ∧
    (∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension a ∘ conj) (closedHalfDisk p R) z)) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R) ∧
    MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) ∧
    MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z)) ∧
    (∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z)) ∧
    EqOn (diskExtension a) (U₀ ∘ ψ₁) (openHalfDisk p R) ∧
    EqOn (diskExtension a ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R) ∧
    inwardConormalWithin g (diskExtension a) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension a ∘ conj) (p : ℂ)) (diskExtension a (p : ℂ))
        (inwardConormalWithin g (diskExtension a ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0

/-- **G1（R12 本体，conditional engine）。** `f` 是 Morrey 盘（极小）。`hcaps`：10.3/10.4 弱版的输出——
同 trace（weak Jordan）的两个 metric-Lipschitz caps `a±`，`A(a₊) + A(a₋) ≤ 2A(f)`，且 `f` 非单射 ⇒
`A(a₊) + A(a₋) < 2A(f)` 或某个 cap 有 reparametrized fold（sheet = `diskExtension f ∘ ψ`）。
`hR4r`：R4r——Lipschitz、`U₀` conformal harmonic 的 reparametrized fold ⇒ 同 trace、严格更小面积的
Lipschitz competitor。结论 `f` 单射：严格亏损分支直接与极小性矛盾；fold 分支经 `hR4r` 与极小性矛盾。 -/
theorem top_caps_force_injective_R12 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M}
    {f : C(closedDisk, M)} (hf : IsMorreyDisk g Γ f)
    (hR4r : ∀ {U₀ : ℂ → M}, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₀ (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₀ z) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₀ z = 0) →
      ∀ a : C(closedDisk, M),
        (∃ L : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf g (a z) (a w) ≤ (L : ℝ≥0∞) * edist z w) →
        HasReparametrizedFold_R12 g a U₀ →
        ∃ v : C(closedDisk, M),
          (∃ K : ℝ≥0, ∀ z w : closedDisk,
            riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
          diskTrace v = diskTrace a ∧ riemannianDiskArea g v < riemannianDiskArea g a)
    (hcaps : ∃ ap am : C(closedDisk, M),
      (∃ L : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf g (ap z) (ap w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      (∃ L : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf g (am z) (am w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      DiskWeakJordanTrace Γ ap ∧ DiskWeakJordanTrace Γ am ∧
      riemannianDiskArea g ap + riemannianDiskArea g am ≤ 2 * riemannianDiskArea g f ∧
      ((∃ x y : closedDisk, x ≠ y ∧ f x = f y) →
        riemannianDiskArea g ap + riemannianDiskArea g am < 2 * riemannianDiskArea g f ∨
          HasReparametrizedFold_R12 g ap (diskExtension f) ∨
            HasReparametrizedFold_R12 g am (diskExtension f))) :
    Function.Injective f := by
  obtain ⟨ap, am, hLp, hLm, htp, htm, hsum, hfold⟩ := hcaps
  intro x y hxy
  by_contra hne
  have hp := hf.minimizesLipschitz ap htp hLp
  have hm := hf.minimizesLipschitz am htm hLm
  have key : ∀ a : C(closedDisk, M), DiskWeakJordanTrace Γ a →
      (∃ L : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf g (a z) (a w) ≤ (L : ℝ≥0∞) * edist z w) →
      HasReparametrizedFold_R12 g a (diskExtension f) →
      riemannianDiskArea g f < riemannianDiskArea g a := by
    intro a ht hL hF
    obtain ⟨v, hvL, hvtr, hvA⟩ := hR4r hf.smoothInterior hf.conformal hf.harmonic a hL hF
    have hvt : DiskWeakJordanTrace Γ v := by
      obtain ⟨σ, hσ, hσeq⟩ := ht
      exact ⟨σ, hσ, hvtr.trans hσeq⟩
    exact (hf.minimizesLipschitz v hvt hvL).trans_lt hvA
  rcases hfold ⟨x, y, hne, hxy⟩ with hlt | hF | hF
  · linarith
  · have := key ap htp hLp hF
    linarith
  · have := key am htm hLm hF
    linarith

/-- **G2（tower 总装，conditional engine）。** prepared least-area disk ⇒ injective。对
`n ≥ |P_T(f, α)| = (vertexCollisionPairs T (diskExtension f ∘ α)).card` 强归纳；`T, α` 全程固定（D-22）；
量化在 `∀ M : Type u` 内；stopping rule「`∂Nb` 含 trace 的分量是 `S²`」是充分、可能更早停的规则（D-23）。

显式前提（逐字取 scratch `MYD3/R10R14.lean` 的合同陈述；每条都是尚未证明的 producer，**不是** axiom）：
* `RelNbhd` / `hspine`：R10.1 / R10.2 的输出 notion（`IsRelRegularNbhd ∧ IsSectorControlledCollapse`，谓词
  参数；对真 notion 实例化，`hspine` 是 `range f ⊆ Nb` 的投影）；
* `hR10`：R10.1 producer（`relative_regular_nbhd_spine`）：Morrey 盘 + prepared 数据 ⇒
  `∃ Nb R, RelNbhd f F T α Nb R`；
* `hcaps`：10.3/10.4 弱版 producer（`caps_area_or_fold`；`lp lm` 与 `IsPiecewiseAffineIntoComplex` 两处与 R12
  无关，在此只保留 R12 消费的部分——真 producer 的结论对它是一次投影）；
* `hR4r`：R4r（`reparametrized_fold_competitor`；S-MY-R4C
  `exists_better_competitor_of_fold_seam_R4C` 同型）；
* `hR11`：R11-step（`double_cover_step`）：非 `S²` 分量 ⇒ `O` 上的 genuine connected double cover + 严格降 lift；
* `hR14`：R14 descent（`descent_innermost_paired`）：上层单射 ⇒ 下层单射。

归纳起点由 `flatDisk_complexity_zero_FIX`（`|P_T| = 0`）给出（consumer 见 `CuspP1/TowerEngineHC_R12`）。 -/
theorem prepared_least_area_embedded_R12 (hdim : Module.finrank ℝ E = 3)
    (RelNbhd : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M], C(closedDisk, M) → (ℂ → M) → _root_.Geometry.SimplicialComplex ℝ ℂ →
      (ℂ → ℂ) → Set M → (M → M) → Prop)
    (hspine : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
      {α : ℂ → ℂ} {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R → Set.range f ⊆ Nb)
    (hR10 : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M], Module.finrank ℝ E = 3 →
      ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
      IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
      {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      ∃ (Nb : Set M) (R : M → M), RelNbhd f F T α Nb R)
    (hcaps : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M], Module.finrank ℝ E = 3 →
      ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
      IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
      {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      ∀ {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R →
      Nonempty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
      ∃ ap am : C(closedDisk, M),
        (∃ L : ℝ≥0, ∀ z w : closedDisk,
          riemannianEDistOf g (ap z) (ap w) ≤ (L : ℝ≥0∞) * edist z w) ∧
        (∃ L : ℝ≥0, ∀ z w : closedDisk,
          riemannianEDistOf g (am z) (am w) ≤ (L : ℝ≥0∞) * edist z w) ∧
        DiskWeakJordanTrace Γ ap ∧ DiskWeakJordanTrace Γ am ∧
        riemannianDiskArea g ap + riemannianDiskArea g am ≤ 2 * riemannianDiskArea g f ∧
        ((∃ x y : closedDisk, x ≠ y ∧ f x = f y) →
          riemannianDiskArea g ap + riemannianDiskArea g am < 2 * riemannianDiskArea g f ∨
            HasReparametrizedFold_R12 g ap (diskExtension f) ∨
              HasReparametrizedFold_R12 g am (diskExtension f)))
    (hR4r : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U₀ : ℂ → M},
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₀ (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₀ z) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₀ z = 0) →
      ∀ a : C(closedDisk, M),
        (∃ L : ℝ≥0, ∀ z w : closedDisk, riemannianEDistOf g (a z) (a w) ≤ (L : ℝ≥0∞) * edist z w) →
        HasReparametrizedFold_R12 g a U₀ →
        ∃ v : C(closedDisk, M),
          (∃ K : ℝ≥0, ∀ z w : closedDisk,
            riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
          diskTrace v = diskTrace a ∧ riemannianDiskArea g v < riemannianDiskArea g a)
    (hR11 : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M], Module.finrank ℝ E = 3 →
      ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
      IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
      [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
      {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      ∀ {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R →
      IsEmpty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
      ∃ (O : TopologicalSpace.Opens M) (M' : Type u) (_ : TopologicalSpace M')
        (_ : ChartedSpace E M') (_ : IsManifold 𝓘(ℝ, E) ∞ M') (_ : T2Space M') (pr : M' → M)
        (hπ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ pr)
        (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) pr x))
        (τ : M' → M') (f' : C(closedDisk, M')) (Γ' : freeLoop M'),
        Nb ⊆ O ∧ IsConnected (O : Set M) ∧
        (∃ HO : unitInterval × M → M, ContinuousOn HO (univ ×ˢ (O : Set M)) ∧
          (∀ x ∈ (O : Set M), HO (0, x) = x) ∧ (∀ x ∈ (O : Set M), HO (1, x) ∈ Nb) ∧
          (∀ t, ∀ x ∈ Nb, HO (t, x) = x) ∧ ∀ t, MapsTo (fun x => HO (t, x)) O O) ∧
        Set.range pr = O ∧ IsCoveringMapOn pr (O : Set M) ∧ ConnectedSpace M' ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ τ ∧
        (∀ x, pr (τ x) = pr x) ∧ (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧
        (∀ x y, pr x = pr y → y = x ∨ y = τ x) ∧ IsConnected (pr ⁻¹' Set.range f) ∧
        (∀ z, pr (f' z) = f z) ∧ (∀ θ, pr (Γ' θ) = Γ θ) ∧
        IsMorreyDisk (g.pullback pr hπ himm) Γ' f' ∧
        (∃ (F' : ℂ → M') (N' : ℕ)
          (A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
          (φ' : ℂ → EuclideanSpace ℝ (Fin N')) (h' : EuclideanSpace ℝ (Fin N') → M'),
          IsPreparedSheetComplex_FIX (E := E) f' F' T α N' A' φ' h') ∧
        vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
          vertexCollisionPairs T (diskExtension f ∘ α))
    (hR14 : ∀ {M M' : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M] [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) ∞ M']
      [T2Space M'], Module.finrank ℝ E = 3 →
      ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
      IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
      {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      ∀ (O : TopologicalSpace.Opens M) (pr : M' → M) (_ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ pr),
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) pr x)) →
      IsCoveringMapOn pr (O : Set M) → Set.range pr = O → Set.range f ⊆ O →
      ∀ (τ : M' → M'), (∀ x, pr (τ x) = pr x) → (∀ x, τ (τ x) = x) → (∀ x, τ x ≠ x) →
      (∀ x y, pr x = pr y → y = x ∨ y = τ x) →
      ∀ (f' : C(closedDisk, M')), (∀ z, pr (f' z) = f z) → Function.Injective f' →
      Function.Injective f)
    (n : ℕ) :
    ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
      {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)} {F : ℂ → M}
      {T : _root_.Geometry.SimplicialComplex ℝ ℂ} [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
      {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsMorreyDisk g Γ f → IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      (vertexCollisionPairs T (diskExtension f ∘ α)).card ≤ n → Function.Injective f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ g Γ f F T _ α N A φ h hf hprep hcard
  obtain ⟨Nb, R, hN⟩ := hR10 hdim hf hprep
  by_cases hs : Nonempty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12)
  · exact top_caps_force_injective_R12 hf (hR4r g) (hcaps hdim hf hprep hN hs)
  · obtain ⟨O, M', _, _, _, _, pr, hpr, himm, τ, f', Γ', hNO, -, -, hrange, hcov, -, -,
      hτ₁, hτ₂, hτ₃, hfib, -, hlift, -, hf', ⟨F', N', A', φ', h', hprep'⟩, hlt⟩ :=
      hR11 hdim hf hprep hN (not_nonempty_iff.mp hs)
    have hcard' : (vertexCollisionPairs T (diskExtension f' ∘ α)).card < n :=
      (Finset.card_lt_card hlt).trans_le hcard
    have hinj' : Function.Injective f' := ih _ hcard' hf' hprep' le_rfl
    exact hR14 hdim hf hprep O pr hpr himm hcov hrange ((hspine hN).trans hNO) τ hτ₁ hτ₂ hτ₃
      hfib f' hlift hinj'

end DifferentialGeometry.Geometry
