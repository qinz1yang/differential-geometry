import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineScaleC11Q5
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestriction

/-!
# fine realization 的两条 outer 供给口（O-CH11-FINECAP G3，后缀 `_C11Q5`）

`hact`（`ActualCanonicalInsertion_C11Q5`，G1/G2）之外，树内 outer 已有第二种 fine-cap 来源：astra
retention 族 `PreparedSpatialStepRetention` 的 `fineRecords / fineWindows`（每块请求
`(εcut, Dcut, mcut)` 上的 canonical static caps，`full_records` 说粗 records 的 static cap 是它们的
`restrictModelWindow` 的平移）。本文件给这条路线（R1）的消费端：

* `FineCapRealization_C11Q5.mono`：fine realization 对请求单调（半径缩小 `D'' ≤ D'`、阶降低、误差放大；
  `transitionEnd < D'' + 1` 保证帽核仍在窗口内）——`restrictWindow` + `weakenOrderAccuracy` + `J ∘ incl`。
* `fineCapRealization_of_sameCap_C11Q5`：同一 event 上另一顶 static cap `S'`（同 neck 尺度、同实际帽
  `inclusion ∘ witness.cap`）有 canonical window ⇒ `S` 在 `S'` 的 model tuple 上有 fine realization。
* **`surgeryActionBarrier_of_fineReal_C11Q5`**（R1 的 K3 producer）：窗口内每个 event 有**不弱于**请求
  `(R₀, m₀, ε₀)(A, t)` 的 fine realization + δ 条件 `α A s ≤ δ₀(A, t)` ⇒ `SurgeryActionBarrier_C11Q`。
  与 `surgeryActionBarrier_of_fineCap_C11Q5`（R2：`hact` + δ_* 预算）并列。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

section Mono

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- **请求单调性**：`(D', m', ε')` 上的 fine realization ⇒ 任一更弱请求 `(D'', m'', ε'')` 上的
（`0 < D'' ≤ D'`、`transitionEnd < D'' + 1`、`m'' ≤ m'`、`ε' ≤ ε''`）。 -/
theorem FineCapRealization_C11Q5.mono {S : E.PresentedStaticCap fixed D m ε b}
    {D' D'' ε' ε'' : ℝ} {m' m'' : ℕ} (h : FineCapRealization_C11Q5 S D' m' ε')
    (hD'' : 0 < D'') (hDD : D'' ≤ D') (hcap : StandardCap.transitionEnd < D'' + 1)
    (hm : m'' ≤ m') (hε : ε' ≤ ε'') : FineCapRealization_C11Q5 S D'' m'' ε'' := by
  obtain ⟨x₀, δ, k, d, w, J, hJ, hscale, hmetric, hcover⟩ := h
  let hsub : standardCapWindow D'' ≤ standardCapWindow D' :=
    fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1))
  refine ⟨x₀, δ, k, d, (w.weakenOrderAccuracy hm hε).restrictWindow hD'' hDD,
    J ∘ TopologicalSpace.Opens.inclusion hsub,
    hJ.comp (isSmoothEmbedding_opens_inclusion hsub) (by simp), hscale, ?_, ?_⟩
  · intro x v z
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric,
      StandardCap.CanonicalStaticInsertionWitness.weakenOrderAccuracy_windowMetric]
    refine (hmetric (TopologicalSpace.Opens.inclusion hsub x) v z).trans ?_
    have hmd : MDifferentiableAt ThreeModel ThreeModel J
        (TopologicalSpace.Opens.inclusion hsub x) :=
      hJ.contMDiff.mdifferentiableAt (by simp)
    have hmd' : MDifferentiableAt ThreeModel ThreeModel (TopologicalSpace.Opens.inclusion hsub) x :=
      (contMDiff_inclusion (I := ThreeModel) (n := ∞) hsub).contMDiffAt.mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    rw [mfderiv_comp_apply x (f := TopologicalSpace.Opens.inclusion hsub) (g := J) hmd hmd' v,
      mfderiv_comp_apply x (f := TopologicalSpace.Opens.inclusion hsub) (g := J) hmd hmd' z,
      mfderiv_opens_incl (I := ThreeModel) hsub x]
    rfl
  · intro z
    obtain ⟨x, hx, hpoint⟩ := hcover z
    refine ⟨⟨x.val, hx.trans_lt hcap⟩, hx, ?_⟩
    change J ⟨x.val, (hx.trans_lt hcap).trans_le (add_le_add hDD (le_refl 1))⟩ = _
    exact hpoint

/-- **同一实际帽**：同 event 的另一顶 static cap `S'`（同 neck 尺度、同 `inclusion ∘ witness.cap`）有
canonical window ⇒ `S` 在 `S'` 的 model tuple 上有 fine realization（`J = S'.window`）。 -/
theorem fineCapRealization_of_sameCap_C11Q5 (S : E.PresentedStaticCap fixed D m ε b)
    {D' ε' : ℝ} {m' : ℕ} (S' : E.PresentedStaticCap fixed D' m' ε' b)
    (hS' : S'.hasCanonicalWindow) (hscale : S'.neck.scale = S.neck.scale)
    (hcap : ∀ z, S'.inclusion (S'.witness.cap z) = S.inclusion (S.witness.cap z)) :
    FineCapRealization_C11Q5 S D' m' ε' := by
  obtain ⟨x₀, δ, k, d, w, hsc, hmetric, hcover⟩ := hS'
  refine ⟨x₀, δ, k, d, w, S'.window, S'.window_smooth, hsc.trans hscale, ?_, ?_⟩
  · intro x v z
    rw [← hscale]
    exact hmetric x v z
  · intro z
    obtain ⟨x, hx, hpoint⟩ := hcover z
    exact ⟨x, hx, hpoint.trans (hcap z)⟩

end Mono

/-- **K3 producer（R1：直接 fine realization 供给）**：窗口内（`t/2 ≤ time i.succ < t`）每个 static cap
有不弱于请求 `(R₀, m₀, ε₀)(A, t)` 的 fine realization（如 astra retention 的 fine records 经
`fineCapRealization_of_sameCap_C11Q5`），且 `α A s ≤ δ₀(A, t)` ⇒ `SurgeryActionBarrier_C11Q`。 -/
theorem surgeryActionBarrier_of_fineReal_C11Q5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr Λ : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s) (hΛ : ∀ A, 0 < A → 0 < Λ A)
    (Eb r₀ qcan ρbar : ℝ → ℝ) (hEb : ∀ t, 0 < t → Real.sqrt (t / 2) ≤ Eb t)
    (hr₀ : ∀ t, 0 < t → 0 < r₀ t ∧ r₀ t ≤ nr t / 100)
    (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
    (hneck : ∀ t s, 0 < t → t / 2 ≤ s → s ≤ t → params.neckRadius s ≤ ρbar t)
    (Ctime : ℝ≥0)
    (hderiv : ∀ n, ∀ (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (j : Fin ((F.tower.history n).toHistory.eventCount + 1))
      (y : ((F.tower.history n).toHistory.stage j).Carrier),
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j →
      ∀ s ∈ Ioo ((F.tower.history n).toHistory.time j)
        ((F.tower.history n).toHistory.stageEndTime j), s < t.val →
        qcan t < metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt ((F.tower.history n).toHistory.stageMetric j z) y)
              (Iic s) s| ≤
            Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hreal : ∀ A, 0 < A → ∀ n (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon),
      0 < (t : ℝ) → ∀ (i : Fin (F.tower.history n).toHistory.eventCount) b,
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time i.succ →
      (F.tower.history n).toHistory.time i.succ < t →
      ∃ (D' ε' : ℝ) (m' : ℕ),
        (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.2.1
          ≤ D' ∧
        (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.2.2
          ≤ m' ∧
        ε' ≤ (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.1 ∧
        FineCapRealization_C11Q5 ((records n i).static b) D' m' ε')
    (hfineδ : ∀ A, 0 < A → ∀ t, 0 < t → ∀ s ∈ Icc (t / 2) t,
      α A s ≤ (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).1) :
    SurgeryActionBarrier_C11Q F δ α nr Λ := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf v hv
  have hr0 : 0 < r := hsmall.1
  have ht0 : 0 < (t : ℝ) := by nlinarith
  have hid : Nonempty (InitialIdentification P g R.toHistory) := ⟨F.tower.initial n⟩
  obtain ⟨hv2, -, hsq, hvE, hslice⟩ := halfClock_slice_facts_C11Q2 R hr hb hv
  refine ⟨?_, fun _ => cutoffValue_attained_C11Q2 R hid (records n) hBf hbt seedTrace x hr0
    hv.1 hv2 hr hslice⟩
  intro q hq
  have hΛrec : 0 < params.recenterConstant :=
    lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four
  obtain ⟨hr₀t, hr₀nr⟩ := hr₀ t ht0
  have hEt := hEb t ht0
  have hE0 : 0 ≤ Eb t := (Real.sqrt_nonneg _).trans hEt
  have hE2 : (t : ℝ) - Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hball' : H.isParabolicallyRmControlledBall t x (r₀ t) :=
    ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hr₀t (hr₀nr.trans hϱ₀)
  have hspec := fineBarrierConsts_spec_C11Q5 P g (A := Λ A * Eb t) Ctime hE0 hr₀t (hqcan t ht0)
    hΛrec (hρbar t ht0)
  have hα := hfineδ A hA t ht0
  have hrt : r ≤ Real.sqrt ((t : ℝ) / 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  refine fineWindowBarrier_slice_C11Q5 (A := Λ A * Eb t) R hid params (records n) Ctime hE0 hr₀t
    (hqcan t ht0) (hρbar t ht0) t (Real.sqrt ((t : ℝ) / 2)) hEt ?_ ?_ ?_ ?_ x hball' hBf _ q ?_ ?_
  · intro j hj1 hj2
    rw [hE2] at hj1
    have htime0 : 0 ≤ H.time j.succ := by linarith
    exact (hδ _ htime0).trans ((hacc _ ⟨hj1, hj2⟩).le.trans (hα _ ⟨hj1, hj2⟩))
  · intro j hj1 hj2
    rw [hE2] at hj1
    exact hneck t _ ht0 hj1 hj2
  · intro j y hj s hs hst hqs
    rw [hE2] at hj
    exact hderiv n t j y hj s hs hst hqs
  · intro i b hi1 hi2
    rw [hE2] at hi1
    obtain ⟨D', ε', m', hD', hm', hε', hfine⟩ := hreal A hA n t ht0 i b hi1 hi2
    have hR := hspec.2.2.1
    exact hfine.mono (StandardCap.transitionEnd_pos.trans hR) hD' (by linarith) hm' hε'
  · rw [hsq]
    exact hvE
  · refine lt_of_le_of_lt hq (WithTop.coe_lt_coe.mpr ?_)
    have hΛA := hΛ A hA
    nlinarith

/-- **consumer**：R2（`hact`）的 fine realization 也满足 R1 的供给形（`D' = R₀` 等取等号）——两个 K3 producer
在同一请求上相容。 -/
example {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) {R₀ ε₀ : ℝ} {m₀ : ℕ}
    (h : FineCapRealization_C11Q5 S R₀ m₀ ε₀) :
    ∃ (D' ε' : ℝ) (m' : ℕ), R₀ ≤ D' ∧ m₀ ≤ m' ∧ ε' ≤ ε₀ ∧ FineCapRealization_C11Q5 S D' m' ε' :=
  ⟨R₀, ε₀, m₀, le_rfl, le_rfl, le_rfl, h⟩

end GC.LongTime.Ch11
