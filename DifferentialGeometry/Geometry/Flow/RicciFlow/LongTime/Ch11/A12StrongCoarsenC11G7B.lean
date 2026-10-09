import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV7C11G7

set_option autoImplicit false

/-!
# S16 strong supply 的精度单调与 noncollapsing a³（O-CH11-GAPTOP7B G2，后缀 `_C11G7B`）

R-C11-11 D-2 / Q2 表：两级装配中 S16 与 S6 从 `Γf` 搬到粗 `Γ` 的两条搬运义务。
* **`SpatialCanonicalWitness.alternative_monoEps_neck_C11G7B`**（alternative 反演）：
  `(W.monoEps).alternative = neck nk'` ⇒ `∃ nk, W.alternative = neck nk ∧ nk' = nk.monoEps`——新的 neck
  alternative 来自旧的 neck alternative（cap / positive / round 三支构造子不同，不可能）。
* **`strongCanonicalSupplyV2_monoEps_C11G7B`**（S16 精度 + 常数联合单调）：
  `S16 F ρ ε C1 C2`、`ε ≤ ε' < 1/11`、`C1 ≤ C1'`、`C2 ≤ C2'` ⇒ `S16 F ρ ε' C1' C2'`。同一 `T`、同一阈值 `ρ`；
  witness 用 `monoEps`，neck 支经反演取回旧 neck，**原样保留** `U / hxU / a / E / S` 与完整时间窗
  `[t − R⁻¹, t]`（`RealTimeInterval.closed (s.time − R⁻¹) s.time`），只把 strong neck 经 `StrongNeck.mono`
  放宽到 `ε'`；常数由 `strongCanonicalSupplyV2_mono_C12X`（只增常数）。GAPTOP7 L2
  `strongCanonicalSupplyV2_monoEps_C11G7` 为同精度常数不变的特例。
* **`noncollapsed_coarsen_a3_C11G7B`**（S6 扩半径）：`FineOf Γf Γ`、`a := Γf.ε / Γ.ε ∈ (0, 1/2]`，
  `NoncollapsedBefore (κ t) Γf.ε t` ⇒ `NoncollapsedBefore (κ t · a³) Γ.ε t`，且 `κ · a³` 仍正、仍 antitone
  （受控球半径 `r ≤ Γ.ε` 缩到同中心 `a r ≤ Γf.ε`，体积单调；GAPTOP7 L1 `noncollapsedBefore_coarsen_C11G7`）。
  **不沿用原 κ**（审稿 Q2）。
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M}

/-- **alternative 反演**：粗化 witness 的 neck alternative 来自原 witness 的 neck alternative，且就是其
`monoEps`。 -/
theorem SpatialCanonicalWitness.alternative_monoEps_neck_C11G7B {eps eps' C1 C2 : ℝ} {x : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (heps : eps ≤ eps') (hsmall : eps' < 1 / 11)
    {nk' : SpatialLocalNeck g eps' x W.domain.carrier}
    (h : (W.monoEps heps hsmall).alternative = SpatialCanonicalAlternative.neck nk') :
    ∃ nk : SpatialLocalNeck g eps x W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck nk ∧ nk' = nk.monoEps heps hsmall := by
  change W.alternative.monoEps W.eps_pos heps hsmall = SpatialCanonicalAlternative.neck nk' at h
  cases halt : W.alternative with
  | neck data =>
    rw [halt] at h
    change SpatialCanonicalAlternative.neck (data.monoEps heps hsmall) =
      SpatialCanonicalAlternative.neck nk' at h
    cases h
    exact ⟨data, rfl, rfl⟩
  | cap data deep =>
    rw [halt] at h
    cases h
  | positive whole data sec =>
    rw [halt] at h
    cases h
  | round whole data =>
    rw [halt] at h
    cases h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **S16 精度 + 常数联合单调**：见文件头。neck 支保留 `U / hxU / a / E / S` 与时间窗 `[t − R⁻¹, t]`，只放宽
strong neck 的精度。 -/
theorem strongCanonicalSupplyV2_monoEps_C11G7B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε ε' C1 C2 C1' C2' : ℝ}
    (h : StrongCanonicalSupplyV2_C11E F ρ ε C1 C2) (hε : ε ≤ ε') (hsmall : ε' < 1 / 11)
    (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    StrongCanonicalSupplyV2_C11E F ρ ε' C1' C2' := by
  refine strongCanonicalSupplyV2_mono_C12X ?_ h1 h2
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hWc, hWn⟩ := hT s hs x hR
  refine ⟨W.monoEps hε hsmall, hWc.mono_eps hε hsmall hε hsmall, fun nk' heq => ?_⟩
  obtain ⟨nk, hnk, -⟩ := W.alternative_monoEps_neck_C11G7B hε hsmall heq
  obtain ⟨U, hxU, a, E, S, ha, hS, hpull, hrestr, ⟨nkS⟩⟩ := hWn nk hnk
  exact ⟨U, hxU, a, E, S, ha, hS, hpull, hrestr, ⟨nkS.mono hε hsmall⟩⟩

/-- 两级比 `a := Γf.ε / Γ.ε`：`0 < a ≤ 1/2`（`Γf.ε ≤ p6FineEta Γ.ε ≤ Γ.ε / 2`）。 -/
theorem fineRatio_mem_C11G7B {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ) :
    0 < Γf.epsilon / Γ.epsilon ∧ Γf.epsilon / Γ.epsilon ≤ 1 / 2 := by
  have h0 := Γ.epsilon_pos
  refine ⟨div_pos Γf.epsilon_pos h0, ?_⟩
  rw [div_le_iff₀ h0]
  have h1 := p6FineEta_le_C11GT6 Γ.epsilon
  linarith [hfine.1]

/-- **noncollapsing a³**：见文件头。`κ` 的族版（A12′ 元组的 `κ : ℝ → ℝ` 槽）。 -/
theorem noncollapsed_coarsen_a3_C11G7B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {Γ Γf : ClosedBirthConstants}
    (hfine : FineOf_C11G2.{u} Γf Γ) {κ : ℝ → ℝ} (hκ : ∀ t, 0 < κ t) (hκanti : Antitone κ)
    (hnc : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
      (F.tower.history n).NoncollapsedBefore (κ t) Γf.epsilon t) :
    (∀ t, 0 < κ t * (Γf.epsilon / Γ.epsilon) ^ 3) ∧
      Antitone (fun t => κ t * (Γf.epsilon / Γ.epsilon) ^ 3) ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t * (Γf.epsilon / Γ.epsilon) ^ 3)
          Γ.epsilon t := by
  have hc3 : 0 < (Γf.epsilon / Γ.epsilon) ^ 3 := pow_pos (fineRatio_mem_C11G7B hfine).1 3
  exact ⟨fun t => mul_pos (hκ t) hc3,
    fun a b hab => mul_le_mul_of_nonneg_right (hκanti hab) hc3.le,
    fun n t ht => noncollapsedBefore_coarsen_C11G7 _ (hκ t).le Γf.epsilon_pos
      hfine.epsilon_le (hnc n t ht)⟩

/-- consumer：细 `Γf` 处 S16（shared ceiling 常数）搬到粗 `Γ` 的 P6 ceiling 常数（v7 装配实际用的形），同时
noncollapsing 付 a³。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ρ : ℝ → ℝ} {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ)
    (hS : StrongCanonicalSupplyV2_C11E F ρ Γf.epsilon (C1ceil_C11SC.{u} Γf) (C2ceil_C11SC.{u} Γf))
    {κ : ℝ → ℝ} (hκ : ∀ t, 0 < κ t) (hκanti : Antitone κ)
    (hnc : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
      (F.tower.history n).NoncollapsedBefore (κ t) Γf.epsilon t) :
    StrongCanonicalSupplyV2_C11E F ρ Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t * (Γf.epsilon / Γ.epsilon) ^ 3)
          Γ.epsilon t := by
  have hΓ11 : Γ.epsilon < 1 / 11 := (epsilon_mem_C11GT6 Γ).2
  exact ⟨strongCanonicalSupplyV2_monoEps_C11G7B hS hfine.epsilon_le hΓ11
      (hfine.2.1.trans (C1ceil_le_C1P6_C11GT6 _ Γ)) (hfine.2.2.1.trans (C2ceil_le_C2P6_C11GT6 _ Γ)),
    (noncollapsed_coarsen_a3_C11G7B hfine hκ hκanti hnc).2.2⟩

/-- consumer：GAPTOP7 L2（同常数）是本引理在 `C1' = C1`、`C2' = C2` 的特例。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ρ : ℝ → ℝ} {ε ε' C1 C2 : ℝ} (h : StrongCanonicalSupplyV2_C11E F ρ ε C1 C2) (hε : ε ≤ ε')
    (hsmall : ε' < 1 / 11) : StrongCanonicalSupplyV2_C11E F ρ ε' C1 C2 :=
  strongCanonicalSupplyV2_monoEps_C11G7B h hε hsmall le_rfl le_rfl

end GC.LongTime.Ch11
