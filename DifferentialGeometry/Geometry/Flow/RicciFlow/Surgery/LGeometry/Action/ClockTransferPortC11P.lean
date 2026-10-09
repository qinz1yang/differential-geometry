import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.LocalClockTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Joining
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.StageSolution

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Surgery.LGeometry.Action.ClockTransfer`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (6 errors).  `LocalClockTransfer` is now a shim
over `LocalClockTransferPortC11P`; private declarations are mangled in the port module, so the
`open private` has to name the port module.  Elaboration-level repairs:
* `open private DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_exists_contDiff_clock_warp_
  action_le from ..LocalClockTransferPortC11P` (was `.. from ..LocalClockTransfer`), and the call
  `hwarp := ..` uses the full name `DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_..`.
* `hend` (donor l.63): `H.regularizedStageEnd_eq_of_same_stage hw hv k ..` becomes
  `regularizedStageEnd_eq_of_same_stage H hw hv k ..` (field notation no longer finds an
  `open private` name).
* `huppercc` (donor l.141): `And.intro ..` becomes `Set.mem_Icc.mpr (And.intro ..)`.
* `hnonneg` (donor l.147-149): `norm_num at hm ⊢; linarith` becomes `norm_num at hm ⊢` (the goal is
  now closed by `norm_num`, `linarith` had no goal).
* `hbox` (donor l.168-171): `obtain ⟨hs1, hs2⟩ := hs` before `constructor <;> linarith ..`
  (`s ∈ Icc a b` is not seen by `linarith`).
* `hlagEq` (donor l.226 and l.230): `rw [hθid hz.le]` becomes
  `rw [hθid (Set.mem_Iic.mpr (Set.mem_Iio.mp hz).le)]`; the closing `simp only [..]` is followed by
  `rw [heval]; rfl` (`tangentSpaceCast` is the identity but `simp` cannot rewrite the dependent
  point `γ s`).
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.ClockTransfer` is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open private regularizedStageEnd_eq_of_same_stage from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Joining
open private sum_stageInterval_self from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
open private DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_exists_contDiff_clock_warp_action_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.LocalClockTransferPortC11P

universe u
variable (H : ObservedHistory.{u})

private theorem exists_regularizedC1ActionValues_of_first_stage_replacement_two_sided
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u w v Anew B : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hw : T - w ^ 2 ∈ H.stageDomain first) (hv : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (α : (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier)
    (hα : ∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α k))
    (hint : ∀ k, IntervalIntegrable (H.stageRegularizedLagrangian k.val T (α k)) volume
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val))
    (hp : α ⟨last, hle, le_rfl⟩ u = p)
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hsum : (∑ k : H.StageInterval first last, H.stageRegularizedAction k.val T (α k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val)) = Anew)
    (γ : ℝ → (H.stage first).Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hγint : IntervalIntegrable (H.stageRegularizedLagrangian first T γ) volume
      (H.regularizedStageStart T u first) v)
    (hγstart : γ (H.regularizedStageStart T u first) =
      α ⟨first, le_rfl, hle⟩ (H.regularizedStageStart T u first))
    (hγend : γ v = q)
    (hγact : H.stageRegularizedAction first T γ (H.regularizedStageStart T u first) v ≤
      H.stageRegularizedAction first T (α ⟨first, le_rfl, hle⟩) (H.regularizedStageStart T u first) w + B) :
    ∃ A : ℝ, A ∈ H.regularizedC1ActionValues first last hle T u v p q ∧ A ≤ Anew + B := by
  classical
  let k₀ : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let β := Function.update α k₀ γ
  have hβ₀ : β k₀ = γ := Function.update_self _ _ _
  have hβother (k : H.StageInterval first last) (hk : k ≠ k₀) : β k = α k :=
    Function.update_of_ne hk _ _
  have hfirstendw : H.regularizedStageEnd T w first = w :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huw) hw
  have hfirstendv : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hv
  have hend (k : H.StageInterval first last) (hk : k ≠ k₀) :
      H.regularizedStageEnd T v k.val = H.regularizedStageEnd T w k.val :=
    regularizedStageEnd_eq_of_same_stage H hw hv k (fun h => hk (Subtype.ext h))
  let Aval := ∑ k : H.StageInterval first last, H.stageRegularizedAction k.val T (β k)
    (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)
  refine ⟨Aval, ⟨hu, huv, hupper, hv, β, ?_, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · intro k
    by_cases hk : k = k₀
    · subst k; rw [hβ₀]; exact hγ
    · rw [hβother k hk]; exact hα k
  · intro k
    by_cases hk : k = k₀
    · subst k; rw [hβ₀]; simpa only [k₀, hfirstendv] using hγint
    · rw [hβother k hk, hend k hk]; exact hint k
  · by_cases he : first = last
    · subst last
      have hs : H.regularizedStageStart T u first = u := H.regularizedStageStart_eq_of_mem_Icc hu hupper
      have hk : (⟨first, hle, le_rfl⟩ : H.StageInterval first first) = k₀ := rfl
      change β k₀ u = p
      rw [hβ₀, ← hs]
      exact hγstart.trans (by simpa only [hs] using hp)
    · rw [hβother _ (by intro h; exact he (congrArg Subtype.val h).symm)]
      exact hp
  · rw [hβ₀]
    exact hγend
  · intro i hf hl
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    refine ⟨z, ?_, ?_⟩
    · by_cases hif : i.castSucc = first
      · subst first
        change z.val.val = β k₀ (Real.sqrt (T - H.time i.succ))
        rw [hβ₀]
        have hs : H.regularizedStageStart T u i.castSucc = Real.sqrt (T - H.time i.succ) :=
          H.regularizedStageStart_castSucc_eq_event_clock hupper i hl
        rw [← hs, hγstart]
        simpa only [k₀, ← hs] using hzold
      · rw [hβother _ (fun h => hif (congrArg Subtype.val h))]
        exact hzold
    · rw [hβother _ (by
        intro h
        have hh : i.succ = first := congrArg Subtype.val h
        exact (not_lt_of_ge (hh ▸ hf)) i.castSucc_lt_succ)]
      exact hznew
  · let fnew := fun k : H.StageInterval first last => H.stageRegularizedAction k.val T (β k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)
    let fold := fun k : H.StageInterval first last => H.stageRegularizedAction k.val T (α k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val)
    have hpoint : ∀ k, fnew k ≤ fold k + if k = k₀ then B else 0 := by
      intro k
      by_cases hk : k = k₀
      · subst k; simp only [fnew, fold, hβ₀, k₀, hfirstendv, hfirstendw, ite_true]; exact hγact
      · simp only [fnew, fold, hβother k hk, hend k hk, ite_eq_right hk, add_zero, le_refl]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpoint k)
    rw [Finset.sum_add_distrib] at hh
    have hBsum : (∑ k : H.StageInterval first last, if k = k₀ then B else 0) = B := by simp
    rw [hBsum] at hh
    exact hh.trans_eq (congrArg (fun z => z + B) hsum)

/-- Uniform transfer of an actual bounded-action competitor to a nearby fixed
clock. Only its first curve changes; every original event node is retained. -/
private theorem eventually_regularizedC1ActionValues_transfer_clock_on_sublevel
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hupper : T ∈ H.stageDomain last)
    (hclock : ∀ w ∈ Icc a b,
      T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ y : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (x : (H.stage last).Carrier) (v : ℝ) (hv : v ∈ Icc a b)
    (E ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝[Icc a b] v, ∀ (q : (H.stage first).Carrier) (ell : ℝ),
      ell ∈ H.regularizedC1ActionValues first last hle T 0 w x q → ell ≤ E →
      ∃ ell' ∈ H.regularizedC1ActionValues first last hle T 0 v x q, ell' ≤ ell + ε := by
  classical
  have hv0 : 0 < v := ha.trans_le hv.1
  have hvclock := hclock v hv
  have hvpast := H.mem_stageDomain_of_mem_Ioo hvclock
  have huppercc : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using
      Set.mem_Icc.mpr (And.intro (H.time_le_of_mem_stageDomain hupper)
        (H.le_stageEndTime_of_mem_stageDomain hupper))
  let s₀ := H.regularizedStageStart T 0 first
  have hs₀ : 0 ≤ s₀ := Real.sqrt_nonneg _
  have hs₀v : s₀ < v := by
    have hnonneg : 0 ≤ T - min (T - 0 ^ 2) (H.stageEndTime first) := by
      have hm := min_le_left (T - 0 ^ 2) (H.stageEndTime first)
      norm_num at hm ⊢
    have hsquare : s₀ ^ 2 = T - min (T - 0 ^ 2) (H.stageEndTime first) :=
      Real.sq_sqrt hnonneg
    have hmin : T - v ^ 2 < min (T - 0 ^ 2) (H.stageEndTime first) :=
      lt_min (by nlinarith [sq_pos_of_pos hv0]) hvclock.2
    by_contra hnot
    have hh := pow_le_pow_left₀ hv0.le (le_of_not_gt hnot) 2
    nlinarith
  let U : Set ℝ := {s | 0 < s ∧ s₀ < s ∧
    T - s ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)}
  have hU : IsOpen U := isOpen_Ioi.inter
    (isOpen_Ioi.inter (isOpen_Ioo.preimage (continuous_const.sub (continuous_id.pow 2))))
  obtain ⟨c₀, d₀, hvc₀d₀, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds ⟨hv0, hs₀v, hvclock⟩)
  let c : ℝ := (c₀ + v) / 2
  let d : ℝ := (v + d₀) / 2
  have hcv : c < v := by dsimp only [c]; linarith [hvc₀d₀.1]
  have hvd : v < d := by dsimp only [d]; linarith [hvc₀d₀.2]
  have hbox : ∀ s ∈ Icc c d, s ∈ U := by
    intro s hs
    apply hsub
    dsimp only [c, d] at hs
    obtain ⟨hs1, hs2⟩ := hs
    constructor <;> linarith [hvc₀d₀.1, hvc₀d₀.2]
  have hcU := hbox c ⟨le_rfl, hcv.le.trans hvd.le⟩
  have hc0 : 0 < c := hcU.1
  have hs₀c : s₀ < c := hcU.2.1
  have hcdomain (s : ℝ) (hs : s ∈ Icc c d) :
      T - s ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := (hbox s hs).2.2
  obtain ⟨G, hG⟩ := H.exists_stage_incomingSlab_metric first
    (hvclock.1.trans hvclock.2)
  have hreg (s : ℝ) (hs : s ∈ Icc c d) :
      T - s ^ 2 ∈ (RealTimeInterval.closedOpen (H.time first)
        (H.stageEndTime first) G.lt).regular := hcdomain s hs
  have hlag (α : ℝ → (H.stage first).Carrier) :
      lRegularizedLagrangian G.flow T α = H.stageRegularizedLagrangian first T α := by
    funext s
    simp only [lRegularizedLagrangian, stageRegularizedLagrangian,
      SolutionOn.scalar, SolutionFamily.scalar, hG]
  have hact (α : ℝ → (H.stage first).Carrier) (l u : ℝ) :
      lRegularizedAction G.flow T α l u = H.stageRegularizedAction first T α l u := by
    simp only [lRegularizedAction, stageRegularizedAction, hlag]
  have hwarp :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_exists_contDiff_clock_warp_action_le
      G.flow G.equation hc0 hcv hvd hreg (E + (2 * B / 3) * c ^ 3) ε hε
  filter_upwards [nhdsWithin_le_nhds hwarp, self_mem_nhdsWithin] with w hw hwab
  obtain ⟨hcw, hwd, θ, hθ, hθid, hθv, hθaction⟩ := hw
  intro q ell hmember hell
  obtain ⟨_, hw0, _, hwpast, α, hα, hint, hp, hq, hnodes, hsum⟩ := hmember
  let k₀ : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hscalarw (j : H.StageInterval first last) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) (α j s) :=
    hscalar j s ⟨hs.1, hs.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val hw0 (ha.le.trans hab) hwab.2)⟩ (α j s)
  have hcclock : T - c ^ 2 ∈ Icc (H.time first) (H.stageEndTime first) :=
    ⟨hcU.2.2.1.le, hcU.2.2.2.le⟩
  have htail := H.sum_stageRegularizedAction_subinterval_le_of_scalar_lower_bound
    (first' := first) (last' := first) le_rfl le_rfl hle
    (T := T) (u := 0) (a := c) (b := w) (v := w) (B := B)
    le_rfl hc0.le hcw.le le_rfl huppercc hwpast hcclock hwpast α hint hscalarw
  rw [sum_stageInterval_self H first,
    H.regularizedStageStart_eq_of_mem_Icc hc0.le hcclock,
    H.regularizedStageEnd_eq_of_mem_stageDomain hw0 hwpast, hsum] at htail
  have htailE : H.stageRegularizedAction first T (α k₀) c w ≤ E + (2 * B / 3) * c ^ 3 := by
    dsimp only [k₀]
    norm_num only [zero_pow (by decide : 3 ≠ 0), sub_zero] at htail
    nlinarith
  have hnewtail := hθaction (α k₀) (hα k₀) (by simpa only [hact] using htailE)
  rw [hact, hact] at hnewtail
  let γ : ℝ → (H.stage first).Carrier := α k₀ ∘ θ
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ :=
    (hα k₀).comp (hθ.of_le (by simp)).contMDiff
  have hlagEq : EqOn (H.stageRegularizedLagrangian first T γ)
      (H.stageRegularizedLagrangian first T (α k₀)) (Ioo s₀ c) := by
    intro s hs
    have he : γ =ᶠ[𝓝 s] α k₀ := by
      filter_upwards [Iio_mem_nhds hs.2] with z hz
      change α k₀ (θ z) = α k₀ z
      rw [hθid (Set.mem_Iic.mpr (Set.mem_Iio.mp hz).le)]
      rfl
    have heval := he.self_of_nhds
    have hder := he.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    simp only [stageRegularizedLagrangian, lVelocity, heval, hder]
    rw [heval]
    rfl
  have hfirstendw := H.regularizedStageEnd_eq_of_mem_stageDomain hw0 hwpast
  have hintold : IntervalIntegrable (H.stageRegularizedLagrangian first T (α k₀)) volume s₀ w := by
    simpa only [k₀, s₀, hfirstendw] using hint k₀
  have hintoldleft : IntervalIntegrable (H.stageRegularizedLagrangian first T (α k₀)) volume s₀ c :=
    hintold.mono_set (by
      rw [uIcc_of_le (hs₀c.le.trans hcw.le), uIcc_of_le hs₀c.le]
      exact Icc_subset_Icc le_rfl hcw.le)
  have hintoldright : IntervalIntegrable (H.stageRegularizedLagrangian first T (α k₀)) volume c w :=
    hintold.mono_set (by
      rw [uIcc_of_le (hs₀c.le.trans hcw.le), uIcc_of_le hcw.le]
      exact Icc_subset_Icc hs₀c.le le_rfl)
  have hintnewleft : IntervalIntegrable (H.stageRegularizedLagrangian first T γ) volume s₀ c :=
    hintoldleft.congr_uIoo (by simpa only [uIoo_of_le hs₀c.le] using hlagEq.symm)
  have hintnewright : IntervalIntegrable (H.stageRegularizedLagrangian first T γ) volume c v := by
    rw [← hlag γ]
    apply ((lRegularizedLagrangian_continuousOn_carrier G.flow G.equation γ hγ).comp
      (continuous_const.prodMk continuous_id).continuousOn ?_).intervalIntegrable_of_Icc hcv.le
    intro s hs
    exact (RealTimeInterval.closedOpen _ _ G.lt).regular_subset
      (hreg s ⟨hs.1, hs.2.trans hvd.le⟩)
  have hleftEq : H.stageRegularizedAction first T γ s₀ c =
      H.stageRegularizedAction first T (α k₀) s₀ c :=
    intervalIntegral.integral_congr_uIoo (by simpa only [uIoo_of_le hs₀c.le] using hlagEq)
  have hγaction : H.stageRegularizedAction first T γ s₀ v ≤
      H.stageRegularizedAction first T (α k₀) s₀ w + ε := by
    unfold stageRegularizedAction at hleftEq hnewtail ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals hintnewleft hintnewright,
      ← intervalIntegral.integral_add_adjacent_intervals hintoldleft hintoldright,
      hleftEq]
    linarith
  exact exists_regularizedC1ActionValues_of_first_stage_replacement_two_sided H first last hle
    le_rfl hw0 hv0.le huppercc hwpast hvpast x q α hα hint hp hnodes hsum γ hγ
    (hintnewleft.trans hintnewright)
    (by change α k₀ (θ s₀) = α k₀ s₀; rw [hθid hs₀c.le]; rfl)
    (by change α k₀ (θ v) = q; rw [hθv]; exact hq)
    hγaction

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
