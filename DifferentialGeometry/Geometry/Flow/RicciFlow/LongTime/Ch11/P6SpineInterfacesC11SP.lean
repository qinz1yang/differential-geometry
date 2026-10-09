import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedGuardRegimeCXSP
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Neck.FiniteEnd

/-!
# O-CH11-SPINE-IFACE G1：hspine 的两个未核接口（后缀 `_C11SP`）

CODEX-C §6/§7 列为"未核"的两件，这里只用**树内 tracked** 模块付清（不 import 任何 untracked CXSP）：

* **(4) `AntitoneOn q.neckRadius (Ici 0)` producer**（§7.2 "hanti 来源没找到"）：来源 =
  `PreparedSpatialChain.exists_surgery_with_spatial_control`
  （`Surgery/History/PreparedSpatialSurgery.lean:23`），
  它在 :147 用 `(S.state (n+1)).radius_antitone` + successor 的 `parameters_past` compat 喂
  `CutoffParameters.diagonal_neckRadius_antitone`，输出 glued `q₀` 的 antitone 与前缀一致
  `q₀ = (S.observation n).parameters` on `[0, n]`。`chainDiagonal_C11A S` 在 `[0, ∞)` 上逐点等于 `q₀`
  （diagonal 在 `t` 处读 `⌈t⌉` 号 observation），再经合同的 hdiag 搬到任意 `q`。
  不用 PARAMCOMPAT 的 `paramCompat_of_chain_P6PC`（它是 hstep 条件形、未审计），不用 SCRS⁺ / Budget。
* **G11 二分的合同形实例化**：`seed_guard_late_subsequence_or_native_CXSP`（tracked G11）的
  `hpos` / `hanti` 由 `q.neckRadius_pos` 与上条付清，只剩序列前提。另记：若序列已有 `t → ∞`
  （G37 / G41 输出），guard / native 二分根本不需要 antitone（`guard_or_native_of_tendsto_C11SP`）。
* **(1) hsec**：曲率算子非负 ⇒ FiniteEnd 的 `hsec` 形，树内
  `metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional`
  （`Curvature/DimensionThree/CurvatureOperator/Nonnegative.lean:13`）
  + `finrank_euclideanSpace_fin` 直接付；
  lead 22:5x：A1 直接用 iff 付，故这里只留 FiniteEnd 形的 consumer `example`（核 `hdim` 与实例路径），
  不新增 wrapper 定理。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

section Antitone

variable {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `chainDiagonal_C11A S` 在 `[0, ∞)` 上逐点等于树内 glued 参数 `q₀`
（`exists_surgery_with_spatial_control` 的前缀一致分量，取 `n = ⌈t⌉`），且 `q₀.neckRadius` antitone。 -/
theorem exists_antitone_eq_chainDiagonal_neckRadius_C11SP
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) :
    ∃ q₀ : CutoffParameters, AntitoneOn q₀.neckRadius (Ici 0) ∧
      ∀ t : ℝ, 0 ≤ t → (chainDiagonal_C11A S).neckRadius t = q₀.neckRadius t := by
  have hctl := S.exists_surgery_with_spatial_control
  obtain ⟨_F, q₀, _κ, _records, -, -, -, -, -, hρanti, hpref, -⟩ := hctl
  refine ⟨q₀, hρanti, fun t ht => ?_⟩
  have h := (hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩).2.1
  exact h.symm

/-- **(4) PROVED**：任一 `PreparedSpatialChain` 的对角参数 `chainDiagonal_C11A S` 的 neck radius 在
`[0, ∞)` 上 antitone（树内 tracked 来源，见模块注释）。 -/
theorem chainDiagonal_neckRadius_antitone_C11SP
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) :
    AntitoneOn (chainDiagonal_C11A S).neckRadius (Ici 0) := by
  obtain ⟨q₀, hanti, heq⟩ := exists_antitone_eq_chainDiagonal_neckRadius_C11SP S
  intro s hs t ht hst
  rw [heq s (mem_Ici.mp hs), heq t (mem_Ici.mp ht)]
  exact hanti hs ht hst

/-- **(4) 合同形 PROVED**：`HSpineTwoLevelTime_C11G7B` 的 hdiag（tower / diagonal 识别）⇒
`AntitoneOn q.neckRadius (Ici 0)`；只读 hdiag 的 neckRadius 分量。 -/
theorem neckRadius_antitone_of_chainDiagonal_C11SP
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) :
    AntitoneOn q.neckRadius (Ici 0) := by
  intro s hs t ht hst
  rw [(hdiag s (mem_Ici.mp hs)).2, (hdiag t (mem_Ici.mp ht)).2]
  exact chainDiagonal_neckRadius_antitone_C11SP S hs ht hst

/-- **G11 二分的合同形实例化**：`hpos := q.neckRadius_pos`、`hanti` 由 hdiag 付清；
guard 晚期子列（原时间 → ∞）∨ 最终 native `r < nr(t)`。 -/
theorem seed_guard_late_or_native_of_chainDiagonal_C11SP
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    {t r : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, q.neckRadius (t (φ n)) ≤ r (φ n)) ∧
      Tendsto (fun n => t (φ n)) atTop atTop) ∨
      ∀ᶠ n in atTop, r n < q.neckRadius (t n) :=
  seed_guard_late_subsequence_or_native_CXSP (fun s hs => q.neckRadius_pos s hs)
    (neckRadius_antitone_of_chainDiagonal_C11SP S q hdiag) ht hsmall

end Antitone

/-- **二分（无 antitone 版，PROVED）**：序列已有 `t → ∞`（G37 / G41 输出）时，guard / native 二分是纯
filter 事实：guard 频繁 ⇒ guard 子列（时间仍 → ∞）；否则最终 native。对任意 `nr` 成立。 -/
theorem guard_or_native_of_tendsto_C11SP {nr : ℝ → ℝ} {t r : ℕ → ℝ}
    (htop : Tendsto t atTop atTop) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, nr (t (φ n)) ≤ r (φ n)) ∧
      Tendsto (fun n => t (φ n)) atTop atTop) ∨
      ∀ᶠ n in atTop, r n < nr (t n) := by
  by_cases hfreq : ∃ᶠ n in atTop, nr (t n) ≤ r n
  · obtain ⟨φ, hφ, hguard⟩ := extraction_of_frequently_atTop hfreq
    exact Or.inl ⟨φ, hφ, hguard, htop.comp hφ.tendsto_atTop⟩
  · exact Or.inr (by simpa only [not_frequently, not_le] using hfreq)

/-- consumer（4）：任一 chain 与满足 hdiag 的 `q` 上，guard 时刻在后的 neck radius 不超过先前的，
即 G11 的 `seed_guard_eventually_late_CXSP` 可直接用于合同的 `q`。 -/
example {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    {t r : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1)) (B : ℝ) :
    ∀ᶠ n in atTop, q.neckRadius (t n) ≤ r n → B ≤ t n :=
  seed_guard_eventually_late_CXSP (fun s hs => q.neckRadius_pos s hs)
    (neckRadius_antitone_of_chainDiagonal_C11SP S q hdiag) ht hsmall B

/-- consumer（二分）：guard 恒成立的情形里第二支不可能与 guard 同时最终成立。 -/
example {nr : ℝ → ℝ} {t r : ℕ → ℝ} (htop : Tendsto t atTop atTop)
    (hguard : ∀ n, nr (t n) ≤ r n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, nr (t (φ n)) ≤ r (φ n)) ∧
      Tendsto (fun n => t (φ n)) atTop atTop := by
  rcases guard_or_native_of_tendsto_C11SP (nr := nr) (r := r) htop with h | h
  · exact h
  · obtain ⟨n, hn⟩ := h.exists
    exact absurd (hguard n) (not_le.mpr hn)

section Hsec

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

/-- consumer（1）：曲率算子非负（G54 / G60 输出形）经树内 iff 付 FiniteEnd 的 `hsec`，喂
`exists_punctured_cone_end_of_spatial_necks`（其余 binder 原样作 example 参数）。核 `hdim` 与实例路径：
`[MetricSpace M]` 下 T2 由 metric 给出。 -/
example {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (metric : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf metric x y)
    {b alpha : ℝ} (hb : 0 < b) (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000)
    (hcone : ∀ z : M, metricAlgebraicCurvatureTensorAt metric z ∈
      algebraicCurvatureOperatorNonnegativeCone)
    (γ : C(Ico 0 b, M)) (hγ : Isometry γ)
    (hblow : Tendsto (fun t => metricScalarAt metric (γ t))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) atTop)
    (q : UniformSpace.Completion M)
    (hq : Tendsto (fun t => (γ t : UniformSpace.Completion M))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) (𝓝 q))
    (hnecks : ∀ᶠ tau : Ico 0 b in comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b),
      Nonempty (SpatialNeck metric alpha (γ tau))) :
    ∃ W : TopologicalSpace.Opens M, Nonempty (PathConnectedSpace W) := by
  have hsec : ∀ (x : M) (v w : TangentSpace I3 x),
      0 ≤ metricRm04StandardAt metric x v w w v := fun x =>
    (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      metric x finrank_euclideanSpace_fin).mp (hcone x)
  obtain ⟨W, hW, -⟩ := exists_punctured_cone_end_of_spatial_necks metric hmetric hb ha hsmall
    hsec γ hγ hblow q hq hnecks
  exact ⟨W, ⟨hW⟩⟩

end Hsec

end GC.LongTime.Ch11
