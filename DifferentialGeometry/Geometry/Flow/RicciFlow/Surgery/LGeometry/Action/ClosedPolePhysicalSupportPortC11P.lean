import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AttainedPhysicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ZeroPoleSupport

/-!
# S-CH11-FIX9 port of astra `ClosedPolePhysicalSupport`（`PortC11P`）

来源：donor `ClosedPolePhysicalSupport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `/-- docstring -/ attribute [-instance] … in theorem` 的顺序对调；
* 3 处 `simpa only [← hreal] using X`（`Loriginal` 是 let，simp 之后与 `X` 的形不一致）→
  `rw [hLor]; exact X`（先 `have hLor : Loriginal = ∑ …gammaOld… := hreal`，defeq；把目标里的
  `Loriginal` 换成旧和）；
* `WithTop.not_top_le_coe hcompare`：本树 `WithTop.not_top_le_coe` 的 `a` 是显式参数 →
  `WithTop.not_top_le_coe _ hcompare`。

原路径 `ClosedPolePhysicalSupport` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Bundle Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- A closed-time pole retains the same attained curve and physical support.
At birth only its zero-duration last stage is removed to construct the support;
the original cost receives that same support by zero-pole comparison. -/
theorem exists_physical_cost_upper_support_of_attained_action_at_closed_pole
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hC1Atv : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 1
      (gamma ⟨first, le_rfl, hle⟩) v)
    (hcross : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ))))
    {etaError : ℝ} (hetaError : 0 < etaError) :
    let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first last,
      H.stageRegularizedAction x.val T (gamma x)
        (H.regularizedStageStart T 0 x.val) (H.regularizedStageEnd T v x.val);
    let gOriginal := H.stageMetric first (T - v ^ 2);
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first last hle T B 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first last hle T B 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < T ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (T - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (T - z.2) * F (z.1, Real.sqrt (T - z.2));
    IsOpen Omega ∧ (q, T - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, T - v ^ 2) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first last hle T B 0 (Real.sqrt (T - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (T - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first last hle T B 0
        (Real.sqrt (T - (T - v ^ 2))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, T - v ^ 2)) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ 2 * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (T - v ^ 2) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, T - v ^ 2)) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (T - v ^ 2) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, T - v ^ 2)) q := by
  classical
  by_cases hstrict : H.time last < T
  · exact H.exists_physical_cost_upper_support_of_attained_action first last hle hv
      ⟨hstrict, hupper.2⟩ hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      hC1Atv hcross hetaError
  have hT : T = H.time last := le_antisymm (not_lt.mp hstrict) hupper.1
  have hfirstlt : first < last := lt_of_le_of_ne hle (by
    intro heq
    have htime : H.time first < T := hpast.1.trans_le (sub_le_self T (sq_nonneg v))
    rw [heq, hT] at htime
    exact (lt_irrefl _ htime))
  obtain ⟨i, rfl⟩ : ∃ i : Fin H.eventCount, i.succ = last := by
    have hvlt : first.val < last.val := hfirstlt
    have hlastBound := last.isLt
    refine ⟨⟨last.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    change last.val - 1 + 1 = last.val
    omega
  subst T
  have hf : first ≤ i.castSucc := by
    change first.val ≤ i.val
    change first.val < i.val + 1 at hfirstlt
    omega
  intro jf jl q Loriginal gOriginal Vorig Roriginal
  let gammaOld : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier :=
    fun j => gamma ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  obtain ⟨z, hzOld, hzNew⟩ : ∃ z : (H.event i).old,
      z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0 ∧
      (H.event i).oldOutput z = gamma ⟨i.succ, hle, le_rfl⟩ 0 := by
    simpa only [sub_self, Real.sqrt_zero] using hgammaNodes i hf le_rfl
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  obtain ⟨hreal, hExt, hOldAttain⟩ :=
    H.regularizedCost_attained_of_zero_pole_restriction first i hf hv.le hpastD
      gamma hgammaAC hgammaInt hgammaNodes hscalar hmin z hzOld hzNew
  have hupperOld : H.time i.succ ∈ Ioc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [H.stageEndTime_castSucc]
    exact ⟨H.time_strictMono i.castSucc_lt_succ, le_rfl⟩
  have hOldAC (j : H.StageInterval first i.castSucc) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (gammaOld j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) :=
    hgammaAC ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  have hOldInt (j : H.StageInterval first i.castSucc) : IntervalIntegrable
      (H.stageRegularizedLagrangian j.val (H.time i.succ) (gammaOld j)) volume
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) :=
    hgammaInt ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩
  have hOldNodes : ∀ (k : Fin H.eventCount)
      (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
      ∃ z : (H.event k).old,
        z.val.val = gammaOld ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = gammaOld ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) :=
    fun k hkf hkl => hgammaNodes k hkf (hkl.trans i.castSucc_le_succ)
  have hOldCross : ∀ (k : Fin H.eventCount)
      (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
      (H.event k).RegularCrossing
        (gammaOld ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)))
        (gammaOld ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ))) :=
    fun k hkf hkl => hcross k hkf (hkl.trans i.castSucc_le_succ)
  obtain ⟨U, F, hU, hqU, hF, hFvalue, hOldContact, hOldBound,
      hGradient, hDeriv, hLaplacian, hPhysical⟩ :=
    H.exists_physical_cost_upper_support_of_attained_action first i.castSucc hf hv
      hupperOld hpast hscalar gammaOld hOldAC hOldInt hOldNodes hOldAttain
      hC1Atv hOldCross hetaError
  have hLor : Loriginal = ∑ x : H.StageInterval first i.castSucc,
      H.stageRegularizedAction x.val (H.time i.succ) (gammaOld x)
        (H.regularizedStageStart (H.time i.succ) 0 x.val)
        (H.regularizedStageEnd (H.time i.succ) v x.val) := hreal
  have hFfull : F (q, v) = Loriginal := hFvalue.trans hreal.symm
  have hNewContact : H.regularizedCost first i.succ hle (H.time i.succ) B 0 v
      (gamma jl 0) q = (F (q, v) : WithTop ℝ) :=
    hmin.symm.trans (hExt.trans (hOldAttain.trans hOldContact))
  have hNewBound : ∀ y ∈ U,
      H.regularizedCost first i.succ hle (H.time i.succ) B 0 y.2
        (gamma jl 0) y.1 ≤ (F y : WithTop ℝ) := by
    intro y hy
    have hcompare := H.regularizedCost_le_of_zero_pole first i hf B y.2 z y.1
    rw [hzOld, hzNew] at hcompare
    exact hcompare.trans (hOldBound y hy)
  refine ⟨U, F, hU, hqU, hF, hFfull, hNewContact, hNewBound,
    hGradient, hDeriv, ?_, ?_⟩
  · rw [hLor]
    exact hLaplacian
  intro Omega Aphys
  rcases hPhysical with ⟨hOmega, hqOmega, hAphys, hAvalue, hOldPhysical,
    _hOldPhysicalContact, hAGradient, hADeriv, hALaplacian, hHeat⟩
  refine ⟨hOmega, hqOmega, hAphys, ?_, ?_, ?_, hAGradient, ?_, hALaplacian, hHeat⟩
  · rw [hLor]
    exact hAvalue
  · intro y hy
    obtain ⟨oldCost, hOldCost, hPhysicalBound⟩ := hOldPhysical y hy
    have hcompare := H.regularizedCost_le_of_zero_pole first i hf B
      (Real.sqrt (H.time i.succ - y.2)) z y.1
    rw [hzOld, hzNew, hOldCost] at hcompare
    have hfinite : H.regularizedCost first i.succ hle (H.time i.succ) B 0
        (Real.sqrt (H.time i.succ - y.2)) (gamma jl 0) y.1 ≠ ⊤ := by
      intro htop
      rw [htop] at hcompare
      exact WithTop.not_top_le_coe _ hcompare
    obtain ⟨newCost, hNewCost⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hcostLe : newCost ≤ oldCost := by
      apply WithTop.coe_le_coe.mp
      simpa only [hNewCost] using hcompare
    refine ⟨newCost, hNewCost.symm, ?_⟩
    exact (mul_le_mul_of_nonneg_left hcostLe
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).trans hPhysicalBound
  · have hsqrt : Real.sqrt (H.time i.succ - (H.time i.succ - v ^ 2)) = v := by
      rw [sub_sub_cancel, Real.sqrt_sq hv.le]
    rw [hsqrt, hNewContact, hFfull]
  · rw [hLor]
    exact hADeriv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
