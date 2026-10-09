import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedLocalizedBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.StageSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Laplacian
import DifferentialGeometry.Geometry.Comparison.DistanceFamily
import DifferentialGeometry.Analysis.Calculus.Cutoff.SingularBarrier

/-!
# S-CH11-FIX9 port of astra `PhysicalWeightedSupportBranches`（`PortC11P`）

来源：donor `PhysicalWeightedSupportBranches.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 4 个定理陈述里 `let actualWeighted … := fun s y => phi (…) * (… + 2 * r * √(T - s))` 的值
  与下一行 `riemannianEDistOf g O q < …`（缩进 6 > `let` 的列）相连：本树 parser 把后者当成
  括号项的 application 实参，`let` 吞掉整个后续陈述，随后在 `:= by` 处报
  `expected ';' or line break`。每处在值末尾补 `;` 断开（项完全相同）；
* `hdistCont`：`(ENNReal.continuousAt_toReal hfinG).comp hmetricCont` 的 `f` 被一阶近似统一成
  `riemannianEDistOf (…) O`（只含 `q`），而 `hmetricCont` 是 `(t0, q)` 处的联合连续性 →
  显式 `ContinuousAt.comp (g := ENNReal.toReal) (f := fun z => riemannianEDistOf (…) O z.2)
  (x := (t0, q))`，先 `have hcomp : ContinuousAt (fun z => (…).toReal) (t0, q)`（`∘` 与 lambda
  defeq）再 `simpa only [hGmetric] using hcomp`；
* `hZslice`：`(hAslice y hy).add contMDiffAt_const` 的常数是 `2 * r * √(T - (y, t0).2)`（含 `y`
  的项，高阶模式统一不了）→ 显式 `(c := 2 * r * Real.sqrt (T - t0))`；
* `hZgrad` 的 `MDiffAt (T% …)`：本树 `T%` elaborator 找不到 `(H.stage first).Carrier` 的 model with
  corners → 写成展开式 `MDifferentiableAt ThreeModel ThreeModel.tangent (fun y => ⟨y, …⟩) q`
  （同 FIX8 `PhysicalWeightedLocalizedBarrier`）；
* `add_le_add_right hcostle c` 在本树把加项放左边（左右约定相反）→ `add_le_add hcostle le_rfl`；
* `hsqrt`：`simpa only [hroot] using hs.sqrt …` 里的 `id` 不被 simp 处理 →
  `simp only [id_eq] at h; rw [hroot] at h; exact h`；
* `hcoefficient`：`field_simp` 在本树已关掉目标，随后的 `ring` 报 `No goals` → 删去；
* 末尾 `rw [hWcontact, hdcontact] at hWheat`：`change` 后 `hWheat` 里的 `W (q, t0)` 是 let 变量
  `W` 的应用，而 `hWcontact` 的 LHS 是展开后的 lambda → 先 `have hWc : W (q, t0) = … := hWcontact`
  （defeq）再 `rw [hWc, hdcontact]`。

原路径 `PhysicalWeightedSupportBranches` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

/-- One geometric branch proof for a positive core fraction whose open core
lies in the cutoff plateau. The original curve, cost and physical jets are fixed. -/
private theorem exists_weighted_physical_history_support_at_core_fraction
    (A Lambda theta : ℝ) (hA : 1 ≤ A) (hLambda : 0 ≤ Lambda)
    (htheta : 0 < theta)
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T Bfloor : ℝ) {v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    let D0 := 4 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 / theta + Lambda * theta
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound (2 * A + D0)
    let phi := DifferentialGeometry.Analysis.SingularBarrier.value
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
    ∀ (r : ℝ), 0 < r → theta ≤ A * (1 - 2 * (v ^ 2 / r ^ 2)) + 1 / 20 → 0 < L + r →
    ∀ (O : (H.stage first).Carrier),
      (∀ y : (H.stage first).Carrier,
        riemannianEDistOf g O y < ENNReal.ofReal (theta * r) →
        ∀ w : TangentSpace ThreeModel y,
          ricciTensor g y w w ≤ (Lambda / r ^ 2) * g.inner y w w) →
    let tau : ℝ → ℝ := fun s => (T - s) / r ^ 2
    let Z : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => Aphys z + 2 * r * Real.sqrt (T - z.2)
    let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * tau s)
    let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      phi (actualArg s y) *
      (2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - s)) p y).untopD 0 +
        2 * r * Real.sqrt (T - s));
      riemannianEDistOf g O q <
        ENNReal.ofReal (r * (A * (1 - 2 * tau t0) + 1 / 10)) →
      IsLocalMin (actualWeighted t0) q →
      ∃ W : (H.stage first).Carrier × ℝ → ℝ,
        (((riemannianEDistOf g O q).toReal < theta * r ∧ W = Z) ∨
          (theta * r ≤ (riemannianEDistOf g O q).toReal ∧
            ∃ dSup : ℝ → (H.stage first).Carrier → ℝ,
              dSup t0 q = (riemannianEDistOf g O q).toReal ∧
              (∀ᶠ y in 𝓝 q, ∀ s : ℝ,
                riemannianEDistOf (H.stageMetric first s) O y ≤
                  ENNReal.ofReal (dSup s y)) ∧
              W = fun z => phi (dSup z.2 z.1 / r - A * (1 - 2 * tau z.2)) * Z z)) ∧
        W (q, t0) = actualWeighted t0 q ∧
        (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
        (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
        IsLocalMin (fun y => W (y, t0)) q ∧
        DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
        0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        -(C / r ^ 2) * actualWeighted t0 q -
          (6 + 2 * v * epsilon + r / v) * phi (actualArg t0 q) ≤
        deriv (fun s => W (q, s)) t0 -
          laplacian (LeviCivita g) g (fun y => W (y, t0)) q := by
  intro D0 C phi jf jl p q L g V R U F hU hqU hF hcontact hcost hupper
    hgradient hclock epsilon htrace t0 Aphys r hr hgate hLr O hRic
    tau Z actualArg actualWeighted hinside hmin
  have hroot : Real.sqrt (T - t0) = v := by
    dsimp only [t0]
    rw [show T - (T - v ^ 2) = v ^ 2 by ring, Real.sqrt_sq hv.le]
  have hfinite : riemannianEDistOf g O q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinside.le
  have harg : actualArg t0 q < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hinside
    change (riemannianEDistOf g O q).toReal / r - A * (1 - 2 * tau t0) < 1 / 10
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith only [hd]
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD : 0 ≤ 2 * A + D0 := by linarith
  have hC : 0 ≤ C := DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg hD
  have hZpos : 0 < Z (q, t0) := by
    have hprod := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hv) hLr
    dsimp only [Z, Aphys]
    rw [hroot, hcontact]
    nlinarith only [hprod]
  obtain ⟨G, hGmetric⟩ := H.exists_stage_incomingSlab_metric first (hpast.1.trans hpast.2)
  have htG : t0 ∈ (RealTimeInterval.closedOpen (H.time first)
      (H.stageEndTime first) G.lt).regular := hpast
  have hcomplete : RiemannianMetricComplete (I := ThreeModel) (G.flow.base.metric t0) :=
    RiemannianMetricComplete.of_compact _
  by_cases hnear : (riemannianEDistOf g O q).toReal < theta * r
  · have hplateauAt : actualArg t0 q < 1 / 20 := by
      have hd : (riemannianEDistOf g O q).toReal / r < theta :=
        (div_lt_iff₀ hr).mpr (by nlinarith only [hnear])
      have hgate' : theta ≤ A * (1 - 2 * tau t0) + 1 / 20 := by
        simpa only [tau, t0, sub_sub_cancel] using hgate
      change (riemannianEDistOf g O q).toReal / r - A * (1 - 2 * tau t0) < 1 / 20
      linarith only [hd, hgate']
    have hmetricCont := continuousAt_riemannianEDistOf G.flow.base.metric
      G.equation.smoothMetric.metricTensor_cont
      ((RealTimeInterval.closedOpen _ _ G.lt).regular_mem_nhds htG) hcomplete O q
    have hdistCont : ContinuousAt
        (fun z : ℝ × (H.stage first).Carrier =>
          (riemannianEDistOf (H.stageMetric first z.1) O z.2).toReal) (t0, q) := by
      have hfinG : riemannianEDistOf (G.flow.base.metric t0) O q ≠ ⊤ := by
        simpa only [hGmetric] using hfinite
      have hcomp : ContinuousAt (fun z : ℝ × (H.stage first).Carrier =>
          (riemannianEDistOf (G.flow.base.metric z.1) O z.2).toReal) (t0, q) :=
        ContinuousAt.comp (g := ENNReal.toReal)
          (f := fun z : ℝ × (H.stage first).Carrier =>
            riemannianEDistOf (G.flow.base.metric z.1) O z.2) (x := (t0, q))
          (ENNReal.continuousAt_toReal hfinG) hmetricCont
      simpa only [hGmetric] using hcomp
    have hargCont : ContinuousAt
        (fun z : ℝ × (H.stage first).Carrier => actualArg z.1 z.2) (t0, q) :=
      (hdistCont.div_const r).sub
        (continuousAt_const.mul
          (continuousAt_const.sub
            (continuousAt_const.mul ((continuousAt_const.sub continuousAt_fst).div_const (r ^ 2)))))
    have hone : ∀ᶠ z : ℝ × (H.stage first).Carrier in 𝓝 (t0, q),
        phi (actualArg z.1 z.2) = 1 := by
      filter_upwards [hargCont.eventually (Iio_mem_nhds hplateauAt)] with z hz
      exact DifferentialGeometry.Analysis.SingularBarrier.one_of_le hz.le
    have honeAt : phi (actualArg t0 q) = 1 := hone.self_of_nhds
    have honeSpace : ∀ᶠ y in 𝓝 q, phi (actualArg t0 y) = 1 :=
      (continuousAt_const.prodMk continuousAt_id).eventually hone
    have honeTime : ∀ᶠ s in 𝓝 t0, phi (actualArg s q) = 1 :=
      (continuousAt_id.prodMk continuousAt_const).eventually hone
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < T ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (T - z.2)) ∈ U}
    obtain ⟨hOmega, hqOmega, hAphys, _hAcontact, hcostNear, hcostContact,
        _hAgradient, hAtime, _hAlap, hAheat⟩ :=
      H.physical_clock_support_of_same_history_jets first last hle T Bfloor hv hpast gamma
        U F hU hqU hF hcontact hcost hupper hgradient hclock epsilon htrace
    change IsOpen Omega at hOmega
    change (q, t0) ∈ Omega at hqOmega
    change ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega at hAphys
    have hspOmega : ∀ᶠ y in 𝓝 q, (y, t0) ∈ Omega :=
      (hOmega.preimage (continuous_id.prodMk continuous_const)).mem_nhds hqOmega
    have htmOmega : ∀ᶠ s in 𝓝 t0, (q, s) ∈ Omega :=
      (hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hqOmega
    have hAslice (y : (H.stage first).Carrier) (hy : (y, t0) ∈ Omega) :
        ContMDiffAt ThreeModel 𝓘(ℝ, ℝ) 2 (fun y => Aphys (y, t0)) y :=
      (hAphys.contMDiffAt (hOmega.mem_nhds hy)).comp y
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
    have hdom (y : (H.stage first).Carrier) (s : ℝ)
        (hys : (y, s) ∈ Omega) (honeys : phi (actualArg s y) = 1) :
        actualWeighted s y ≤ Z (y, s) := by
      obtain ⟨cost, hcosteq, hcostle⟩ := hcostNear (y, s) hys
      dsimp only [actualWeighted]
      rw [honeys, one_mul, hcosteq]
      exact add_le_add hcostle le_rfl
    have hZcontact : Z (q, t0) = actualWeighted t0 q := by
      have hc : (H.regularizedCost first last hle T Bfloor 0
          (Real.sqrt (T - t0)) p q).untopD 0 = L := by
        rw [hcostContact]
        rfl
      dsimp only [actualWeighted, Z, Aphys]
      rw [honeAt, one_mul, hc, hroot, hcontact]
    have hZupper : ∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ Z (y, t0) := by
      filter_upwards [hspOmega, honeSpace] with y hy ho
      exact hdom y t0 hy ho
    have hZtimeUpper : ∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ Z (q, s) := by
      filter_upwards [htmOmega, honeTime] with s hs ho
      exact hdom q s hs ho
    have hZmin : IsLocalMin (fun y => Z (y, t0)) q := by
      filter_upwards [hmin, hZupper] with y hy hup
      exact hZcontact.trans_le (hy.trans hup)
    have hZlapNonneg := laplacian_nonneg_at_spatial_min_of_metricCompatible
      (LeviCivita g) g (LeviCivita_isMetricCompatible g) hZmin
      hZspace.self_of_nhds hZspace hZgrad
    have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (T - s)) (-1 / (2 * v)) t0 := by
      have hs := (hasDerivAt_id t0).const_sub T
      have h := hs.sqrt (ne_of_gt (sub_pos.mpr hqOmega.1))
      simp only [id_eq] at h
      rw [hroot] at h
      exact h
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
    refine ⟨Z, Or.inl ⟨hnear, rfl⟩, hZcontact, hZupper, hZtimeUpper, hZmin,
      hZtime.differentiableAt, hZlapNonneg, ?_⟩
    have hpenalty : 0 ≤ (C / r ^ 2) * Z (q, t0) :=
      mul_nonneg (div_nonneg hC (sq_nonneg r)) hZpos.le
    rw [← hZcontact, honeAt, mul_one, hZtime.deriv, hZlap]
    linarith
  · have hfar : theta * r ≤ (riemannianEDistOf g O q).toReal := le_of_not_gt hnear
    have hRicG : ∀ y : (H.stage first).Carrier,
        riemannianEDistOf (G.flow.base.metric t0) O y < ENNReal.ofReal (theta * r) →
        ∀ w : TangentSpace ThreeModel y,
          ricciTensor (G.flow.base.metric t0) y w w ≤
            (Lambda / r ^ 2) * (G.flow.base.metric t0).inner y w w := by
      simpa only [hGmetric] using hRic
    have hfarG : theta * r ≤ (riemannianEDistOf (G.flow.base.metric t0) O q).toReal := by
      simpa only [hGmetric] using hfar
    let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
    obtain ⟨dSup, hdcontact, hdUpper, hdTime, hdSpace, hdGrad, hdNorm, hdHeat⟩ :=
      exists_distance_upper_support_of_ricci_le_on_ball G.flow G.equation htG hcomplete O
        (by positivity : 0 < theta * r) (div_nonneg hLambda (sq_nonneg r)) hRicG q hfarG
    simp only [hGmetric] at hdcontact hdUpper hdGrad hdNorm hdHeat
    have hdpos : 0 < dSup t0 q := by rw [hdcontact]; exact (by positivity : 0 < theta * r).trans_le hfar
    have hcoefficient :
        2 * (Module.finrank ℝ ThreeSpace - 1 : ℝ) *
            DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 / (theta * r) +
          (Lambda / r ^ 2) * (theta * r) = D0 / r := by
      norm_num [ThreeSpace, D0]
      field_simp [hr.ne', htheta.ne']
    rw [hcoefficient] at hdHeat
    have hdHeat' : -D0 / r ≤ deriv (fun s => dSup s q) t0 -
        laplacian (LeviCivita g) g (dSup t0) q := by
      simpa only [neg_div] using hdHeat
    let W : (H.stage first).Carrier × ℝ → ℝ := fun z =>
      phi (dSup z.2 z.1 / r - A * (1 - 2 * tau z.2)) * Z z
    have huBeta : dSup t0 q / r - A * (1 - 2 * tau t0) < 1 / 10 := by
      simpa only [hdcontact] using harg
    obtain ⟨hWcontact, hWupper, hWtimeUpper, hWmin, _hvelocity, hWtime, hWlap, hWheat⟩ :=
      H.weighted_physical_history_support_heat_lower_at_minimum first last hle T Bfloor
        hv hpast gamma U F hU hqU hF hcontact hcost hupper hgradient hclock epsilon htrace
        r hr O A D0 C (1 / 10) dSup hdcontact hdpos hdUpper hdTime hdSpace hdGrad hdNorm hdHeat'
        phi DifferentialGeometry.Analysis.SingularBarrier.contDiffOn
        (fun _ hz => DifferentialGeometry.Analysis.SingularBarrier.pos hz)
        DifferentialGeometry.Analysis.SingularBarrier.monotoneOn
        (fun _ hz => DifferentialGeometry.Analysis.SingularBarrier.differential_bound hD hz)
        huBeta hZpos hmin
    refine ⟨W, Or.inr ⟨hfar, dSup, hdcontact, hdUpper, rfl⟩,
      hWcontact, hWupper, hWtimeUpper, hWmin, hWtime, hWlap, ?_⟩
    change -(C / r ^ 2) * W (q, t0) -
        (6 + 2 * v * epsilon + r / v) *
          phi (dSup t0 q / r - A * (1 - 2 * tau t0)) ≤ _ at hWheat
    have hWc : W (q, t0) = actualWeighted t0 q := hWcontact
    rw [hWc, hdcontact] at hWheat
    exact hWheat

/-- Positive shifted action pays the weighted-support positivity gate on the same
actual compact history stage. Both geometric branches keep the original curve,
physical metric and cost support. -/
theorem exists_weighted_physical_history_support_of_seed_ricci_of_shifted_pos
    (A Lambda : ℝ) (hA : 1 ≤ A) (hLambda : 0 ≤ Lambda)
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T Bfloor : ℝ) {v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    let D0 := 16 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + Lambda / 4
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound (2 * A + D0)
    let phi := DifferentialGeometry.Analysis.SingularBarrier.value
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
    ∀ (r : ℝ), 0 < r → v ^ 2 ≤ r ^ 2 / 4 → 0 < L + r →
    ∀ (O : (H.stage first).Carrier),
      (∀ y : (H.stage first).Carrier,
        riemannianEDistOf g O y < ENNReal.ofReal (r / 4) →
        ∀ w : TangentSpace ThreeModel y,
          ricciTensor g y w w ≤ (Lambda / r ^ 2) * g.inner y w w) →
    let tau : ℝ → ℝ := fun s => (T - s) / r ^ 2
    let Z : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => Aphys z + 2 * r * Real.sqrt (T - z.2)
    let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * tau s)
    let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      phi (actualArg s y) *
      (2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - s)) p y).untopD 0 +
        2 * r * Real.sqrt (T - s));
      riemannianEDistOf g O q <
        ENNReal.ofReal (r * (A * (1 - 2 * tau t0) + 1 / 10)) →
      IsLocalMin (actualWeighted t0) q →
      ∃ W : (H.stage first).Carrier × ℝ → ℝ,
        (((riemannianEDistOf g O q).toReal < r / 4 ∧ W = Z) ∨
          (r / 4 ≤ (riemannianEDistOf g O q).toReal ∧
            ∃ dSup : ℝ → (H.stage first).Carrier → ℝ,
              dSup t0 q = (riemannianEDistOf g O q).toReal ∧
              (∀ᶠ y in 𝓝 q, ∀ s : ℝ,
                riemannianEDistOf (H.stageMetric first s) O y ≤
                  ENNReal.ofReal (dSup s y)) ∧
              W = fun z => phi (dSup z.2 z.1 / r - A * (1 - 2 * tau z.2)) * Z z)) ∧
        W (q, t0) = actualWeighted t0 q ∧
        (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
        (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
        IsLocalMin (fun y => W (y, t0)) q ∧
        DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
        0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        -(C / r ^ 2) * actualWeighted t0 q -
          (6 + 2 * v * epsilon + r / v) * phi (actualArg t0 q) ≤
        deriv (fun s => W (q, s)) t0 -
          laplacian (LeviCivita g) g (fun y => W (y, t0)) q := by
  intro D0 C phi jf jl p q L g V R U F hU hqU hF hcontact hcost hupper
    hgradient hclock epsilon htrace t0 Aphys r hr htime hLr O hRic
    tau Z actualArg actualWeighted hinside hmin
  have hratio : v ^ 2 / r ^ 2 ≤ 1 / 4 :=
    (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith only [htime])
  have hfactor : 1 / 2 ≤ 1 - 2 * (v ^ 2 / r ^ 2) := by
    linarith only [hratio]
  have hshift : 1 / 2 ≤ A * (1 - 2 * (v ^ 2 / r ^ 2)) := by
    have hmul := mul_le_mul_of_nonneg_right hA
      (by linarith only [hfactor] : 0 ≤ 1 - 2 * (v ^ 2 / r ^ 2))
    nlinarith only [hfactor, hmul]
  have hgate : (1 / 4 : ℝ) ≤ A * (1 - 2 * (v ^ 2 / r ^ 2)) + 1 / 20 := by
    linarith only [hshift]
  have hcore := exists_weighted_physical_history_support_at_core_fraction
    A Lambda (1 / 4) hA hLambda (by norm_num) H first last hle T Bfloor hv hpast gamma
    U F hU hqU hF hcontact hcost hupper hgradient hclock epsilon htrace
    r hr hgate hLr O (by simpa only [show (1 / 4 : ℝ) * r = r / 4 by ring] using hRic)
    hinside hmin
  simpa only [show (4 : ℝ) * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 /
      (1 / 4) + Lambda * (1 / 4) =
      16 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + Lambda / 4 by ring,
    show (1 / 4 : ℝ) * r = r / 4 by ring] using hcore

/-- The actual compact history stage pays the distance-support prerequisites.
The near-core case uses a genuine constant-cutoff neighborhood, and the other
case uses the produced distance support on the same physical slice. -/
theorem exists_weighted_physical_history_support_of_seed_ricci
    (A Lambda : ℝ) (hA : 1 ≤ A) (hLambda : 0 ≤ Lambda)
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T Bfloor : ℝ) {v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    let D0 := 16 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + Lambda / 4
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound (2 * A + D0)
    let phi := DifferentialGeometry.Analysis.SingularBarrier.value
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
    ∀ (r : ℝ), 0 < r → v ^ 2 ≤ r ^ 2 / 4 → (2 * Bfloor / 3) * v ^ 3 < r →
    ∀ (O : (H.stage first).Carrier),
      (∀ y : (H.stage first).Carrier,
        riemannianEDistOf g O y < ENNReal.ofReal (r / 4) →
        ∀ w : TangentSpace ThreeModel y,
          ricciTensor g y w w ≤ (Lambda / r ^ 2) * g.inner y w w) →
    let tau : ℝ → ℝ := fun s => (T - s) / r ^ 2
    let Z : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => Aphys z + 2 * r * Real.sqrt (T - z.2)
    let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * tau s)
    let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      phi (actualArg s y) *
      (2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - s)) p y).untopD 0 +
        2 * r * Real.sqrt (T - s));
      riemannianEDistOf g O q <
        ENNReal.ofReal (r * (A * (1 - 2 * tau t0) + 1 / 10)) →
      IsLocalMin (actualWeighted t0) q →
      ∃ W : (H.stage first).Carrier × ℝ → ℝ,
        (((riemannianEDistOf g O q).toReal < r / 4 ∧ W = Z) ∨
          (r / 4 ≤ (riemannianEDistOf g O q).toReal ∧
            ∃ dSup : ℝ → (H.stage first).Carrier → ℝ,
              dSup t0 q = (riemannianEDistOf g O q).toReal ∧
              (∀ᶠ y in 𝓝 q, ∀ s : ℝ,
                riemannianEDistOf (H.stageMetric first s) O y ≤
                  ENNReal.ofReal (dSup s y)) ∧
              W = fun z => phi (dSup z.2 z.1 / r - A * (1 - 2 * tau z.2)) * Z z)) ∧
        W (q, t0) = actualWeighted t0 q ∧
        (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
        (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
        IsLocalMin (fun y => W (y, t0)) q ∧
        DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
        0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        -(C / r ^ 2) * actualWeighted t0 q -
          (6 + 2 * v * epsilon + r / v) * phi (actualArg t0 q) ≤
        deriv (fun s => W (q, s)) t0 -
          laplacian (LeviCivita g) g (fun y => W (y, t0)) q := by
  intro D0 C phi jf jl p q L g V R U F hU hqU hF hcontact hcost hupper
    hgradient hclock epsilon htrace t0 Aphys r hr htime hroom O hRic
    tau Z actualArg actualWeighted hinside hmin
  have hlow := H.regularizedCost_ge first last hle T Bfloor 0 v p q
  rw [hcost] at hlow
  have hlowReal : -(2 * Bfloor / 3) * v ^ 3 ≤ L := by
    simpa only [zero_pow (by decide : 3 ≠ 0), sub_zero] using WithTop.coe_le_coe.mp hlow
  have hLr : 0 < L + r := by linarith
  exact exists_weighted_physical_history_support_of_seed_ricci_of_shifted_pos
    A Lambda hA hLambda H first last hle T Bfloor hv hpast gamma
    U F hU hqU hF hcontact hcost hupper hgradient hclock epsilon htrace
    r hr htime hLr O hRic hinside hmin

/-- The same physical weighted support through the half seed clock, using the
actual r/40 Ricci core and the original positive shifted action. -/
theorem exists_weighted_physical_history_support_on_half_seed_clock
    (A Lambda : ℝ) (hA : 1 ≤ A) (hLambda : 0 ≤ Lambda)
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T Bfloor : ℝ) {v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    let D0 := 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + Lambda / 40
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound (2 * A + D0)
    let phi := DifferentialGeometry.Analysis.SingularBarrier.value
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
    ∀ (r : ℝ), 0 < r → v ^ 2 ≤ r ^ 2 / 2 → 0 < L + r →
    ∀ (O : (H.stage first).Carrier),
      (∀ y : (H.stage first).Carrier,
        riemannianEDistOf g O y < ENNReal.ofReal (r / 40) →
        ∀ w : TangentSpace ThreeModel y,
          ricciTensor g y w w ≤ (Lambda / r ^ 2) * g.inner y w w) →
    let tau : ℝ → ℝ := fun s => (T - s) / r ^ 2
    let Z : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => Aphys z + 2 * r * Real.sqrt (T - z.2)
    let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * tau s)
    let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      phi (actualArg s y) *
      (2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - s)) p y).untopD 0 +
        2 * r * Real.sqrt (T - s));
      riemannianEDistOf g O q <
        ENNReal.ofReal (r * (A * (1 - 2 * tau t0) + 1 / 10)) →
      IsLocalMin (actualWeighted t0) q →
      ∃ W : (H.stage first).Carrier × ℝ → ℝ,
        (((riemannianEDistOf g O q).toReal < r / 40 ∧ W = Z) ∨
          (r / 40 ≤ (riemannianEDistOf g O q).toReal ∧
            ∃ dSup : ℝ → (H.stage first).Carrier → ℝ,
              dSup t0 q = (riemannianEDistOf g O q).toReal ∧
              (∀ᶠ y in 𝓝 q, ∀ s : ℝ,
                riemannianEDistOf (H.stageMetric first s) O y ≤
                  ENNReal.ofReal (dSup s y)) ∧
              W = fun z => phi (dSup z.2 z.1 / r - A * (1 - 2 * tau z.2)) * Z z)) ∧
        W (q, t0) = actualWeighted t0 q ∧
        (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
        (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
        IsLocalMin (fun y => W (y, t0)) q ∧
        DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
        0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        -(C / r ^ 2) * actualWeighted t0 q -
          (6 + 2 * v * epsilon + r / v) * phi (actualArg t0 q) ≤
        deriv (fun s => W (q, s)) t0 -
          laplacian (LeviCivita g) g (fun y => W (y, t0)) q := by
  intro D0 C phi jf jl p q L g V R U F hU hqU hF hcontact hcost hupper
    hgradient hclock epsilon htrace t0 Aphys r hr htime hLr O hRic
    tau Z actualArg actualWeighted hinside hmin
  have hratio : v ^ 2 / r ^ 2 ≤ 1 / 2 :=
    (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith only [htime])
  have hshift : 0 ≤ A * (1 - 2 * (v ^ 2 / r ^ 2)) :=
    mul_nonneg (by linarith only [hA]) (by linarith only [hratio])
  have hgate : (1 / 40 : ℝ) ≤ A * (1 - 2 * (v ^ 2 / r ^ 2)) + 1 / 20 := by
    linarith only [hshift]
  have hcore := exists_weighted_physical_history_support_at_core_fraction
    A Lambda (1 / 40) hA hLambda (by norm_num) H first last hle T Bfloor hv hpast gamma
    U F hU hqU hF hcontact hcost hupper hgradient hclock epsilon htrace
    r hr hgate hLr O (by simpa only [show (1 / 40 : ℝ) * r = r / 40 by ring] using hRic)
    hinside hmin
  simpa only [show (4 : ℝ) * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 /
      (1 / 40) + Lambda * (1 / 40) =
      160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + Lambda / 40 by ring,
    show (1 / 40 : ℝ) * r = r / 40 by ring] using hcore

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
