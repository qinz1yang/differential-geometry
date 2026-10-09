import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalClockSupport
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# S-CH11-FIX8 port of astra `PhysicalWeightedLocalizedBarrier`（`PortC11P`）

来源：donor `PhysicalWeightedLocalizedBarrier.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 全文 6 处 `MDiffAt (T% fun y => gradientFun g X y) q`（陈述 1 处 + 证明体 5 处）：本树的 `T%`
  elaborator 只在 local instances 里找 `(H.stage first).Carrier` 的 `ChartedSpace`，找不到 model with
  corners。全部写成它的展开式（同一个项，仓库里 `NeckCylindricalChartBridge` 等已有此写法）：
  `MDifferentiableAt ThreeModel ThreeModel.tangent
    (fun y : (H.stage first).Carrier => (⟨y, gradientFun g X y⟩ : TangentBundle …)) q`；
* `huSpace`：`hy.sub mdifferentiableAt_const` 的常数是 `A * (1 - 2 * tau (y, t0).2)`（含 `y` 的项，
  高阶模式统一不了）→ 显式 `(c := A * (1 - 2 * tau t0))`；
* `hsqrt`：`simpa only [hroot] using hs.sqrt …` 的 `hs` 里有 `id`（`id` 不是 reducible，`rw` 也匹配不上），
  simp 只改一半 → 改为 `have h := …; simp only [id_eq] at h; rw [hroot] at h; exact h`；
* `hzle`：`add_le_add_right hcostle (2 * r * …)` 在本树 Mathlib 里把加项放在左边（左右约定相反）→
  `add_le_add hcostle le_rfl`；
* `hweightedTime`：`HasDerivAt.mul` 的结论在本树是 Pi 乘法 `(phi ∘ f) * g`，后面 `rw [hweightedTime.deriv]`
  匹配不上 `deriv (fun s ↦ weighted (q, s))` → 给 `hweightedTime` 显式类型
  `HasDerivAt (fun s => weighted (q, s)) _ t0`（导数值由统一给出，defeq 展开 Pi 乘法）；
* `hheatIdentity`：`rw [hweightedTime.deriv, …]` 之后目标里有未归约的 `(phi ∘ fun s ↦ u (q, s)) t0`，
  `ring` 把它与 `phi (u (q, t0))` 当不同原子 → `ring` 前补 `simp only [Function.comp_apply]`；
* `hheat` 末行 `add_le_add_right (add_le_add hfirst hsecond) _`（同一左右约定问题）→
  `add_le_add (add_le_add hfirst hsecond) le_rfl`；
* `huTime`：`convert … using 1 <;> ring` 只剩一个目标，`<;>` 触发 `unnecessarySeqFocus` 警告 → 换行写
  `using 1` 与 `ring`；
* `hZslice`：`contMDiffAt_const` 的函数是 `fun y => 2 * r * √(T - (y, t0).2)`，高阶模式不能把含 `y`
  的项当常数 → 显式 `contMDiffAt_const (c := 2 * r * Real.sqrt (T - t0))`（`(y, t0).2` ≡ `t0`）。

原路径 `PhysicalWeightedLocalizedBarrier` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

/-- The same physical cost support, weighted by a local distance support at an
actual weighted minimum. The original endpoint velocity is retained and its
relation to the cutoff gradient follows from that minimum. -/
theorem weighted_physical_history_support_heat_lower_at_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T Bfloor : ℝ) {v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
    let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
    let p := gamma jl 0
    let q := gamma jf v
    let L := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)
    let g := H.stageMetric first (T - v ^ 2)
    let V : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v
    let R := metricScalarAt g q
    ∀ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U → (q, v) ∈ U →
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U →
      F (q, v) = L →
      H.regularizedCost first last hle T Bfloor 0 v p q = (L : WithTop ℝ) →
      (∀ z ∈ U, H.regularizedCost first last hle T Bfloor 0 z.2 p z.1 ≤
        (F z : WithTop ℝ)) →
      gradientFun g (fun y => F (y, v)) q = V →
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v →
    ∀ epsilon : ℝ,
      laplacian (LeviCivita g) g (fun y => F (y, v)) q <
        3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + epsilon →
    let t0 := T - v ^ 2
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (T - z.2) * F (z.1, Real.sqrt (T - z.2))
    ∀ (r : ℝ), 0 < r →
    ∀ (O : (H.stage first).Carrier) (A D0 C beta : ℝ)
      (dSup : ℝ → (H.stage first).Carrier → ℝ),
      dSup t0 q = (riemannianEDistOf g O q).toReal →
      0 < dSup t0 q →
      (∀ᶠ y in 𝓝 q, ∀ s : ℝ,
        riemannianEDistOf (H.stageMetric first s) O y ≤ ENNReal.ofReal (dSup s y)) →
      DifferentiableAt ℝ (fun s => dSup s q) t0 →
      (∀ᶠ y in 𝓝 q, MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (dSup t0) y) →
      MDifferentiableAt ThreeModel ThreeModel.tangent
        (fun y : (H.stage first).Carrier =>
          (⟨y, gradientFun g (dSup t0) y⟩ :
            TangentBundle ThreeModel (H.stage first).Carrier)) q →
      g.inner q (gradientFun g (dSup t0) q) (gradientFun g (dSup t0) q) = 1 →
      -D0 / r ≤ deriv (fun s => dSup s q) t0 -
        laplacian (LeviCivita g) g (dSup t0) q →
    ∀ (phi : ℝ → ℝ),
      ContDiffOn ℝ 2 phi (Iio beta) →
      (∀ z ∈ Iio beta, 0 < phi z) →
      MonotoneOn phi (Iio beta) →
      (∀ z ∈ Iio beta, (2 * A + D0) * deriv phi z - C * phi z ≤
        2 * (deriv phi z) ^ 2 / phi z - deriv (deriv phi) z) →
    let tau : ℝ → ℝ := fun s => (T - s) / r ^ 2
    let u : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => dSup z.2 z.1 / r - A * (1 - 2 * tau z.2)
    let Z : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => Aphys z + 2 * r * Real.sqrt (T - z.2)
    let weighted : (H.stage first).Carrier × ℝ → ℝ := fun z => phi (u z) * Z z
    let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      phi ((riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * tau s)) *
      (2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - s)) p y).untopD 0 +
        2 * r * Real.sqrt (T - s))
    u (q, t0) < beta → 0 < Z (q, t0) → IsLocalMin (actualWeighted t0) q →
      weighted (q, t0) = actualWeighted t0 q ∧
      (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ weighted (y, t0)) ∧
      (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ weighted (q, s)) ∧
      IsLocalMin (fun y => weighted (y, t0)) q ∧
      (2 * v) • V =
        (-(Z (q, t0) * deriv phi (u (q, t0)) / phi (u (q, t0)))) •
          gradientFun g (fun y => dSup t0 y / r) q ∧
      DifferentiableAt ℝ (fun s => weighted (q, s)) t0 ∧
      0 ≤ laplacian (LeviCivita g) g (fun y => weighted (y, t0)) q ∧
      -(C / r ^ 2) * weighted (q, t0) -
        (6 + 2 * v * epsilon + r / v) * phi (u (q, t0)) ≤
      deriv (fun s => weighted (q, s)) t0 -
        laplacian (LeviCivita g) g (fun y => weighted (y, t0)) q := by
  intro jf jl p q L g V R U F hU hqU hF hcontact hcost hupper
    hgradient hclock epsilon htrace t0 Aphys r hr O A D0 C beta dSup
    hdcontact hdpos hdupper hdtime hdspace hdgrad hdnorm hdheat
    phi hphi hphipos hphimono hphibound tau u Z weighted actualWeighted
    huBeta hZpos hmin
  let Omega : Set ((H.stage first).Carrier × ℝ) :=
    {z | z.2 < T ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
      (z.1, Real.sqrt (T - z.2)) ∈ U}
  obtain ⟨hOmega, hqOmega, hA, _hAcontact, hcostNear, hcostContact,
      hAgradient, hAtime, _hAlap, hAheat⟩ :=
    H.physical_clock_support_of_same_history_jets first last hle T Bfloor hv hpast gamma
      U F hU hqU hF hcontact hcost hupper hgradient hclock epsilon htrace
  change IsOpen Omega at hOmega
  change (q, t0) ∈ Omega at hqOmega
  change ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega at hA
  have hroot : Real.sqrt (T - t0) = v := by
    dsimp only [t0]
    rw [show T - (T - v ^ 2) = v ^ 2 by ring, Real.sqrt_sq hv.le]
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (T - s))
      (-1 / (2 * v)) t0 := by
    have hs := (hasDerivAt_id t0).const_sub T
    have h := hs.sqrt (ne_of_gt (sub_pos.mpr hqOmega.1))
    simp only [id_eq] at h
    rw [hroot] at h
    exact h
  have hspOmega : ∀ᶠ y in 𝓝 q, (y, t0) ∈ Omega :=
    (hOmega.preimage (continuous_id.prodMk continuous_const)).mem_nhds hqOmega
  have htmOmega : ∀ᶠ s in 𝓝 t0, (q, s) ∈ Omega :=
    (hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hqOmega
  have hAslice (y : (H.stage first).Carrier) (hy : (y, t0) ∈ Omega) :
      ContMDiffAt ThreeModel 𝓘(ℝ, ℝ) 2 (fun y => Aphys (y, t0)) y :=
    (hA.contMDiffAt (hOmega.mem_nhds hy)).comp y
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hZslice (y : (H.stage first).Carrier) (hy : (y, t0) ∈ Omega) :
      ContMDiffAt ThreeModel 𝓘(ℝ, ℝ) 2 (fun y => Z (y, t0)) y :=
    (hAslice y hy).add (contMDiffAt_const (c := 2 * r * Real.sqrt (T - t0)))
  have hZspace : ∀ᶠ y in 𝓝 q,
      MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (fun y => Z (y, t0)) y := by
    filter_upwards [hspOmega] with y hy
    exact (hZslice y hy).mdifferentiableAt (by norm_num)
  have hZgrad : MDifferentiableAt ThreeModel ThreeModel.tangent
        (fun y : (H.stage first).Carrier =>
          (⟨y, gradientFun g (fun y => Z (y, t0)) y⟩ :
            TangentBundle ThreeModel (H.stage first).Carrier)) q :=
    (gradientFun_contMDiffAt_one g (hZslice q hqOmega)).mdifferentiableAt (by norm_num)
  have hZtime : HasDerivAt (fun s => Z (q, s))
      (deriv (fun s => Aphys (q, s)) t0 - r / v) t0 := by
    convert hAtime.add (hsqrt.const_mul (2 * r)) using 1
    rw [hAtime.deriv]
    field_simp [hv.ne']
    ring
  have hZlap : laplacian (LeviCivita g) g (fun y => Z (y, t0)) q =
      laplacian (LeviCivita g) g (fun y => Aphys (y, t0)) q := by
    have hAsp : ∀ᶠ y in 𝓝 q,
        MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (fun y => Aphys (y, t0)) y := by
      filter_upwards [hspOmega] with y hy
      exact (hAslice y hy).mdifferentiableAt (by norm_num)
    have hAg := (gradientFun_contMDiffAt_one g (hAslice q hqOmega)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    simpa only [Z, add_comm] using
      laplacian_add_const (LeviCivita g) g (2 * r * Real.sqrt (T - t0)) hAsp hAg
  have hZgradient : gradientFun g (fun y => Z (y, t0)) q = (2 * v) • V := by
    change gradientFun g (fun y => Aphys (y, t0) + 2 * r * Real.sqrt (T - t0)) q = _
    rw [gradientFun_add g ((hAslice q hqOmega).mdifferentiableAt (by norm_num))
      mdifferentiableAt_const, gradientFun_const, add_zero]
    exact hAgradient
  have hZheat : -(6 + 2 * v * epsilon + r / v) <
      deriv (fun s => Z (q, s)) t0 -
        laplacian (LeviCivita g) g (fun y => Z (y, t0)) q := by
    rw [hZtime.deriv, hZlap]
    linarith
  let dHat : (H.stage first).Carrier → ℝ := fun y => dSup t0 y / r
  have hdHatEq : dHat = (1 / r) • dSup t0 := by
    funext y
    simp only [dHat, Pi.smul_apply, smul_eq_mul]
    ring
  have hdHatSpace : ∀ᶠ y in 𝓝 q,
      MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) dHat y := by
    filter_upwards [hdspace] with y hy
    rw [hdHatEq]
    exact hy.const_smul (1 / r)
  have hdHatGradient : ∀ᶠ y in 𝓝 q,
      gradientFun g dHat y = (1 / r) • gradientFun g (dSup t0) y := by
    filter_upwards [hdspace] with y hy
    rw [hdHatEq, gradientFun_const_smul g (1 / r) hy]
  have hdHatGrad : MDifferentiableAt ThreeModel ThreeModel.tangent
        (fun y : (H.stage first).Carrier =>
          (⟨y, gradientFun g dHat y⟩ :
            TangentBundle ThreeModel (H.stage first).Carrier)) q := by
    apply (hdgrad.smul_const_section (a := 1 / r)).congr_of_eventuallyEq
    filter_upwards [hdHatGradient] with y hy
    change TotalSpace.mk' _ y (gradientFun g dHat y) =
      TotalSpace.mk' _ y ((1 / r) • gradientFun g (dSup t0) y)
    rw [hy]
  have huSpace : ∀ᶠ y in 𝓝 q,
      MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (fun y => u (y, t0)) y := by
    filter_upwards [hdHatSpace] with y hy
    exact hy.sub (mdifferentiableAt_const (c := A * (1 - 2 * tau t0)))
  have huGradient : ∀ᶠ y in 𝓝 q,
      gradientFun g (fun y => u (y, t0)) y = gradientFun g dHat y := by
    filter_upwards [hdHatSpace] with y hy
    change gradientFun g (fun y => dHat y - A * (1 - 2 * tau t0)) y = _
    rw [gradientFun_sub g hy mdifferentiableAt_const, gradientFun_const, sub_zero]
  have huGrad : MDifferentiableAt ThreeModel ThreeModel.tangent
        (fun y : (H.stage first).Carrier =>
          (⟨y, gradientFun g (fun y => u (y, t0)) y⟩ :
            TangentBundle ThreeModel (H.stage first).Carrier)) q := by
    apply hdHatGrad.congr_of_eventuallyEq
    filter_upwards [huGradient] with y hy
    change TotalSpace.mk' _ y (gradientFun g (fun y => u (y, t0)) y) =
      TotalSpace.mk' _ y (gradientFun g dHat y)
    rw [hy]
  have huLap : laplacian (LeviCivita g) g (fun y => u (y, t0)) q =
      (1 / r) * laplacian (LeviCivita g) g (dSup t0) q := by
    have heq : (fun y => u (y, t0)) =
        fun y => -(A * (1 - 2 * tau t0)) + dHat y := by
      funext y
      dsimp only [u, dHat]
      ring
    rw [heq, laplacian_add_const (LeviCivita g) g _ hdHatSpace hdHatGrad,
      hdHatEq, laplacian_smul_at (LeviCivita g) g (1 / r) hdspace hdgrad]
  have huNorm : g.inner q (gradientFun g (fun y => u (y, t0)) q)
      (gradientFun g (fun y => u (y, t0)) q) = 1 / r ^ 2 := by
    rw [huGradient.self_of_nhds, hdHatGradient.self_of_nhds]
    simp only [map_smul, smul_apply, smul_eq_mul, hdnorm]
    ring
  have huTime : HasDerivAt (fun s => u (q, s))
      (deriv (fun s => dSup s q) t0 / r - 2 * A / r ^ 2) t0 := by
    have htau : HasDerivAt tau (-1 / r ^ 2) t0 :=
      ((hasDerivAt_id t0).const_sub T).div_const (r ^ 2)
    convert (hdtime.hasDerivAt.div_const r).sub
      (((htau.const_mul 2).const_sub 1).const_mul A) using 1
    ring
  have huHeat : -(2 * A + D0) / r ^ 2 ≤
      deriv (fun s => u (q, s)) t0 -
        laplacian (LeviCivita g) g (fun y => u (y, t0)) q := by
    have hh := div_le_div_of_nonneg_right hdheat hr.le
    rw [huTime.deriv, huLap]
    convert (sub_le_sub_right hh (2 * A / r ^ 2)) using 1 <;>
      field_simp [hr.ne'] <;> ring
  have hphiAt : ContDiffAt ℝ 2 phi (u (q, t0)) :=
    hphi.contDiffAt (isOpen_Iio.mem_nhds huBeta)
  have hphiDiff : DifferentiableAt ℝ phi (u (q, t0)) :=
    hphiAt.differentiableAt (by norm_num)
  have hphiNear : ∀ᶠ z in 𝓝 (u (q, t0)), DifferentiableAt ℝ phi z := by
    filter_upwards [isOpen_Iio.mem_nhds huBeta] with z hz
    exact (hphi.contDiffAt (isOpen_Iio.mem_nhds hz)).differentiableAt (by norm_num)
  have hphiDeriv : DifferentiableAt ℝ (deriv phi) (u (q, t0)) :=
    (hphiAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hphiNonneg : 0 ≤ deriv phi (u (q, t0)) := by
    rw [← derivWithin_of_isOpen isOpen_Iio huBeta]
    exact hphimono.derivWithin_nonneg
  have hphiPos : 0 < phi (u (q, t0)) := hphipos _ huBeta
  have hPhiSpace : ∀ᶠ y in 𝓝 q,
      MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (fun y => phi (u (y, t0))) y := by
    filter_upwards [huSpace, huSpace.self_of_nhds.continuousAt.eventually hphiNear]
      with y hy hphiy
    exact hphiy.mdifferentiableAt.comp y hy
  have hPhiGradient : ∀ᶠ y in 𝓝 q,
      gradientFun g (fun y => phi (u (y, t0))) y =
        deriv phi (u (y, t0)) • gradientFun g (fun y => u (y, t0)) y := by
    filter_upwards [huSpace, huSpace.self_of_nhds.continuousAt.eventually hphiNear]
      with y hy hphiy
    exact gradientFun_comp g hphiy hy
  have hPhiGrad : MDifferentiableAt ThreeModel ThreeModel.tangent
        (fun y : (H.stage first).Carrier =>
          (⟨y, gradientFun g (fun y => phi (u (y, t0))) y⟩ :
            TangentBundle ThreeModel (H.stage first).Carrier)) q := by
    have hcoeff := hphiDeriv.mdifferentiableAt.comp q huSpace.self_of_nhds
    apply (hcoeff.smul_section huGrad).congr_of_eventuallyEq
    filter_upwards [hPhiGradient] with y hy
    change TotalSpace.mk' _ y (gradientFun g (fun y => phi (u (y, t0))) y) =
      TotalSpace.mk' _ y
        (deriv phi (u (y, t0)) • gradientFun g (fun y => u (y, t0)) y)
    rw [hy]
  have hweightedSpace : ∀ᶠ y in 𝓝 q,
      MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (fun y => weighted (y, t0)) y := by
    filter_upwards [hPhiSpace, hZspace] with y hy hz
    exact hy.mul hz
  have hweightedGradient : ∀ᶠ y in 𝓝 q,
      gradientFun g (fun y => weighted (y, t0)) y =
        phi (u (y, t0)) • gradientFun g (fun y => Z (y, t0)) y +
          Z (y, t0) • gradientFun g (fun y => phi (u (y, t0))) y := by
    filter_upwards [hPhiSpace, hZspace] with y hy hz
    exact gradientFun_mul g hy hz
  have hweightedGrad : MDifferentiableAt ThreeModel ThreeModel.tangent
        (fun y : (H.stage first).Carrier =>
          (⟨y, gradientFun g (fun y => weighted (y, t0)) y⟩ :
            TangentBundle ThreeModel (H.stage first).Carrier)) q := by
    have hleft := hPhiSpace.self_of_nhds.smul_section hZgrad
    have hright := hZspace.self_of_nhds.smul_section hPhiGrad
    apply (mdifferentiableAt_add_section hleft hright).congr_of_eventuallyEq
    filter_upwards [hweightedGradient] with y hy
    change TotalSpace.mk' _ y (gradientFun g (fun y => weighted (y, t0)) y) =
      TotalSpace.mk' _ y
        (phi (u (y, t0)) • gradientFun g (fun y => Z (y, t0)) y +
          Z (y, t0) • gradientFun g (fun y => phi (u (y, t0))) y)
    rw [hy]
  have hweightedTime : HasDerivAt (fun s => weighted (q, s)) _ t0 :=
    (hphiDiff.hasDerivAt.comp t0 huTime).mul hZtime
  have hdom (y : (H.stage first).Carrier) (s : ℝ)
      (hys : (y, s) ∈ Omega) (hds : 0 < dSup s y) (hus : u (y, s) < beta)
      (hzs : 0 ≤ Z (y, s))
      (hEDist : riemannianEDistOf (H.stageMetric first s) O y ≤
        ENNReal.ofReal (dSup s y)) :
      actualWeighted s y ≤ weighted (y, s) := by
    have hdist : (riemannianEDistOf (H.stageMetric first s) O y).toReal ≤ dSup s y := by
      have hd := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEDist
      simpa only [ENNReal.toReal_ofReal hds.le] using hd
    have harg : (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * tau s) ≤ u (y, s) :=
      sub_le_sub_right (div_le_div_of_nonneg_right hdist hr.le) _
    have hargBeta := lt_of_le_of_lt harg hus
    have hpnonneg := (hphipos _ hargBeta).le
    have hple := hphimono hargBeta hus harg
    obtain ⟨cost, hcosteq, hcostle⟩ := hcostNear (y, s) hys
    have hzle : 2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - s)) p y).untopD 0 +
          2 * r * Real.sqrt (T - s) ≤ Z (y, s) := by
      rw [hcosteq]
      exact add_le_add hcostle le_rfl
    exact (mul_le_mul_of_nonneg_left hzle hpnonneg).trans
      (mul_le_mul_of_nonneg_right hple hzs)
  have hweightedContact : weighted (q, t0) = actualWeighted t0 q := by
    have hc : (H.regularizedCost first last hle T Bfloor 0
        (Real.sqrt (T - t0)) p q).untopD 0 = L := by
      rw [hcostContact]
      rfl
    dsimp only [weighted, actualWeighted, u, Z]
    rw [hdcontact, hc]
    congr 1
    dsimp only [Aphys]
    rw [hroot, hcontact]
  have huSpCont : ContinuousAt (fun y => u (y, t0)) q :=
    huSpace.self_of_nhds.continuousAt
  have hweightedUpper : ∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ weighted (y, t0) := by
    filter_upwards [hspOmega, hdupper,
      hdspace.self_of_nhds.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hdpos),
      huSpCont.preimage_mem_nhds (Iio_mem_nhds huBeta),
      hZspace.self_of_nhds.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hZpos)]
      with y hy hd hdp hub hzp
    exact hdom y t0 hy hdp hub hzp.le (hd t0)
  have hweightedTimeUpper : ∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ weighted (q, s) := by
    filter_upwards [htmOmega,
      hdtime.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hdpos),
      huTime.continuousAt.preimage_mem_nhds (Iio_mem_nhds huBeta),
      hZtime.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hZpos)]
      with s hs hdp hub hzp
    exact hdom q s hs hdp hub hzp.le (hdupper.self_of_nhds s)
  have hweightedMin : IsLocalMin (fun y => weighted (y, t0)) q := by
    filter_upwards [hmin, hweightedUpper] with y hy hup
    exact hweightedContact.trans_le (hy.trans hup)
  have hzero := gradientFun_eq_zero_of_isLocalMin g hweightedMin
    hweightedSpace.self_of_nhds
  rw [hweightedGradient.self_of_nhds, hPhiGradient.self_of_nhds, smul_smul] at hzero
  have hbalance : gradientFun g (fun y => Z (y, t0)) q =
      (-(Z (q, t0) * deriv phi (u (q, t0)) / phi (u (q, t0)))) •
        gradientFun g (fun y => u (y, t0)) q := by
    have hmove : phi (u (q, t0)) • gradientFun g (fun y => Z (y, t0)) q =
        -(Z (q, t0) * deriv phi (u (q, t0))) •
          gradientFun g (fun y => u (y, t0)) q := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hzero
    calc
      gradientFun g (fun y => Z (y, t0)) q =
          (1 / phi (u (q, t0))) •
            (phi (u (q, t0)) • gradientFun g (fun y => Z (y, t0)) q) := by
              simp only [smul_smul, one_div, inv_mul_cancel₀ hphiPos.ne', one_smul]
      _ = _ := by
        rw [hmove, smul_smul]
        congr 1
        ring
  have hvelocity : (2 * v) • V =
      (-(Z (q, t0) * deriv phi (u (q, t0)) / phi (u (q, t0)))) •
        gradientFun g (fun y => dSup t0 y / r) q := by
    rw [← hZgradient]
    simpa only [huGradient.self_of_nhds] using hbalance
  have hcross : g.inner q
      (gradientFun g (fun y => phi (u (y, t0))) q)
      (gradientFun g (fun y => Z (y, t0)) q) =
        -(Z (q, t0) / r ^ 2) * (deriv phi (u (q, t0))) ^ 2 / phi (u (q, t0)) := by
    rw [hPhiGradient.self_of_nhds, hbalance]
    simp only [map_smul, smul_apply, smul_eq_mul, huNorm]
    ring
  have hPhiLap := laplacian_comp_of_eventually_differentiable
    (LeviCivita g) g hphiNear hphiDeriv huSpace huGrad
  have hweightedLap := laplacian_mul_at (LeviCivita g) g
    hPhiSpace hZspace hPhiGrad hZgrad
  have hheatIdentity :
      deriv (fun s => weighted (q, s)) t0 -
          laplacian (LeviCivita g) g (fun y => weighted (y, t0)) q =
        phi (u (q, t0)) *
          (deriv (fun s => Z (q, s)) t0 -
            laplacian (LeviCivita g) g (fun y => Z (y, t0)) q) +
        Z (q, t0) * deriv phi (u (q, t0)) *
          (deriv (fun s => u (q, s)) t0 -
            laplacian (LeviCivita g) g (fun y => u (y, t0)) q) +
        (Z (q, t0) / r ^ 2) *
          (2 * (deriv phi (u (q, t0))) ^ 2 / phi (u (q, t0)) -
            deriv (deriv phi) (u (q, t0))) := by
    rw [hweightedTime.deriv, hweightedLap, hPhiLap, huNorm, hcross,
      huTime.deriv, hZtime.deriv]
    simp only [Function.comp_apply]
    ring
  have hheat : -(C / r ^ 2) * weighted (q, t0) -
      (6 + 2 * v * epsilon + r / v) * phi (u (q, t0)) ≤
      deriv (fun s => weighted (q, s)) t0 -
        laplacian (LeviCivita g) g (fun y => weighted (y, t0)) q := by
    rw [hheatIdentity]
    have hfirst := mul_le_mul_of_nonneg_left hZheat.le hphiPos.le
    have hsecond := mul_le_mul_of_nonneg_left huHeat (mul_nonneg hZpos.le hphiNonneg)
    have hcutoff := mul_le_mul_of_nonneg_left (hphibound _ huBeta)
      (div_nonneg hZpos.le (sq_nonneg r))
    calc
      -(C / r ^ 2) * weighted (q, t0) -
          (6 + 2 * v * epsilon + r / v) * phi (u (q, t0)) ≤
        phi (u (q, t0)) * (-(6 + 2 * v * epsilon + r / v)) +
        Z (q, t0) * deriv phi (u (q, t0)) * (-(2 * A + D0) / r ^ 2) +
        (Z (q, t0) / r ^ 2) *
          (2 * (deriv phi (u (q, t0))) ^ 2 / phi (u (q, t0)) -
            deriv (deriv phi) (u (q, t0))) := by
              dsimp only [weighted]
              linear_combination hcutoff
      _ ≤ _ := add_le_add (add_le_add hfirst hsecond) le_rfl
  have hnonneg := laplacian_nonneg_at_spatial_min_of_metricCompatible
    (LeviCivita g) g (LeviCivita_isMetricCompatible g) hweightedMin
    hweightedSpace.self_of_nhds hweightedSpace hweightedGrad
  exact ⟨hweightedContact, hweightedUpper, hweightedTimeUpper, hweightedMin,
    hvelocity, hweightedTime.differentiableAt, hnonneg, hheat⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
