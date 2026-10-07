import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.VelocityComposition
import DifferentialGeometry.Geometry.Metric.Family.TimeDerivative
import DifferentialGeometry.Geometry.Metric.Family.Comparison
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Perelman.LGeometry.Action.Regularized.LocalClockTransfer`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree: a rewrite failure in
`exists_clock_metric_exp_comparison` and, in
`eventually_exists_contDiff_clock_warp_action_le`, a single declaration that exceeds the default
200000 heartbeats (about 1.8M used, 52 s of it in one failing unification).  Elaboration-level
repairs only (no budget option is used; the declaration is repaired, not split):
* `exists_clock_metric_exp_comparison`: `simp only` gets `id_eq, Nat.reduceSub` so that
  `id r ^ (2 - 1)` becomes `r` (and the now unused `sub_zero` is dropped).
* `hV`: the map `hmap`, its `MapsTo` fact `hmaps` and `hcomp := hS.scalarCont.comp ..` are stated
  first and closed by `exact hcomp` (the one-term `exact` made the unifier unfold `S.scalar`).
* `hαlag`: `(f := fun s : ℝ => (T, s))` is given to `ContinuousOn.comp`; without it the expected
  type `ContinuousOn (lRegularizedLagrangian S T α) _` is unified against `g ∘ ?f` and fails only
  after about 52 s (this is the heartbeat blow-up).
* `hP`: `hVP` is a separate `have` (a `by` block cannot be the head of `.trans`).
* `χ.contDiff (n := 1)` / `(n := 0)`, `χ.nonneg (x := s)`, `χ.le_one (x := s)`: implicit
  arguments that the old elaboration order determined are given explicitly.
* `hθid`, `hθc`: `Set.mem_Iic.mp/.mpr` (`s ∈ Iic c` is no longer seen by `linarith`/`le_rfl`).
* `hpos`: `Ioi_mem_nhds (a := 0)`.  `hleft`, `hVθ`: `ContinuousAt.comp` gets `(f := ..) (x := ..)`.
  `hpotential`: `refine hsub.eventually (p := fun y => y < η) ?_` and the closing `simpa` adds
  `Pi.sub_apply, Pi.mul_apply, Prod.mk.eta` (the `ContinuousAt.sub/mul` statements now use `f - g`).
* `hkin`: `Pi.sub_apply` added to the `dsimp only` before `ring`.  `hkinint`, `hlagint`, `hpotint`:
  explicit `IntervalIntegrable .. volume c w` types.  `hpotlower`: `mul_neg` added to `simpa only`.
* `hi`: `integral_mono_on (μ := volume)`.  `hsub`: `integral_comp_mul_deriv_of_deriv_nonneg
  (a := c) (b := v)`.  The final `rw [..] at hi` chain is cut in two with
  `simp only [Pi.mul_apply, Function.comp_apply] at hi` in between (`ContinuousOn.mul` now yields
  `(f * g) x`, which `hsub` cannot match).
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Action.Regularized.LocalClockTransfer` is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F}
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

private theorem exists_clock_metric_exp_comparison
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hreg : ∀ s ∈ Icc c d, T - s ^ 2 ∈ D.regular) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc c d, ∀ t ∈ Icc c d,
      ∀ y : M, ∀ z : TangentSpace I y,
        (S.base.metric (T - s ^ 2)).inner y z z ≤
          Real.exp (K * |s - t|) * (S.base.metric (T - t ^ 2)).inner y z z := by
  have hd0 : 0 < d := hc.trans_le hcd
  obtain ⟨C, hC, hbound⟩ := hS.smoothMetric.exists_inner_time_deriv_bound
    (isCompact_Icc.image (continuous_const.sub (continuous_id.pow 2)))
    (by rintro _ ⟨s, hs, rfl⟩; exact hreg s hs)
  refine ⟨2 * d * C, by positivity, ?_⟩
  intro s hs t ht y z
  apply inner_le_exp_mul_inner_of_abs_deriv_le
    (fun r => S.base.metric (T - r ^ 2)) y z ?_ hs ht
  intro r hr
  have hd := (hS.smoothMetric.hasDerivAt_inner (hreg r hr) y z z).comp r
    ((hasDerivAt_const r T).sub ((hasDerivAt_id r).pow 2))
  refine ⟨_, hd.hasDerivWithinAt, ?_⟩
  have hr0 : 0 < r := hc.trans_le hr.1
  have hg0 := metric_inner_self_nonneg (S.base.metric (T - r ^ 2)) y z
  have hb := hbound (T - r ^ 2) ⟨r, hr, rfl⟩ y z
  simp only [Nat.cast_ofNat, id_eq, Nat.reduceSub, pow_one, mul_one] at hd ⊢
  rw [abs_mul]
  have habs : |0 - 2 * r| = 2 * r := by
    rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs]
  calc
    _ ≤ (C * (S.base.metric (T - r ^ 2)).inner y z z) * (2 * r) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ ≤ (C * (S.base.metric (T - r ^ 2)).inner y z z) * (2 * d) :=
      mul_le_mul_of_nonneg_left (by linarith [hr.2]) (mul_nonneg hC hg0)
    _ = _ := by ring

/-- A change of the past clock confined to one regular tail. The neighborhood is
uniform over all endpoints and all curves below the stated action ceiling. -/
private theorem eventually_exists_contDiff_clock_warp_action_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T c v d : ℝ} (hc : 0 < c) (hcv : c < v) (hvd : v < d)
    (hreg : ∀ s ∈ Icc c d, T - s ^ 2 ∈ D.regular)
    (E₀ ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 v, c < w ∧ w < d ∧
      ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ EqOn θ id (Iic c) ∧ θ v = w ∧
        ∀ (α : ℝ → M), ContMDiff 𝓘(ℝ, ℝ) I 1 α →
          lRegularizedAction S T α c w ≤ E₀ →
          lRegularizedAction S T (α ∘ θ) c v ≤ lRegularizedAction S T α c w + ε := by
  classical
  let U : Set ℝ := {s | T - s ^ 2 ∈ D.regular}
  have hU : IsOpen U := D.regular_isOpen.preimage
    (continuous_const.sub (continuous_id.pow 2))
  let V : ℝ × M → ℝ := fun p => 2 * p.1 ^ 2 * S.scalar (T - p.1 ^ 2) p.2
  have hV : ContinuousOn V (U ×ˢ univ) := by
    apply (continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul
    have hmap : Continuous (fun p : ℝ × M => (T - p.1 ^ 2, p.2)) :=
      (continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd
    have hmaps : MapsTo (fun p : ℝ × M => (T - p.1 ^ 2, p.2)) (U ×ˢ univ)
        (D.carrier ×ˢ univ) := fun p hp => ⟨D.regular_subset hp.1, mem_univ _⟩
    have hcomp := hS.scalarCont.comp hmap.continuousOn hmaps
    exact hcomp
  have hVat (s : ℝ) (hs : s ∈ Icc c d) (y : M) : ContinuousAt V (s, y) :=
    hV.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hreg s hs, mem_univ y⟩)
  obtain ⟨P₀, hP₀⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
    (hV.mono (fun p hp => ⟨hreg p.1 hp.1, hp.2⟩))
  let P : ℝ := max P₀ 0
  have hP : ∀ s ∈ Icc c d, ∀ y : M, |V (s, y)| ≤ P := by
    intro s hs y
    have hVP : |V (s, y)| ≤ P₀ := by
      simpa only [Real.norm_eq_abs] using hP₀ (s, y) ⟨hs, mem_univ y⟩
    exact hVP.trans (le_max_left _ _)
  obtain ⟨K, hK, hmetric⟩ := exists_clock_metric_exp_comparison S hS hc
    (hcv.le.trans hvd.le) hreg
  let χ : ContDiffBump v :=
    ⟨(v - c) / 4, (v - c) / 2, by linarith, by linarith⟩
  let θ : ℝ → ℝ → ℝ := fun w s => s + (w - v) * χ s
  let θ' : ℝ → ℝ → ℝ := fun w s => 1 + (w - v) * deriv χ s
  have hθ (w : ℝ) : ContDiff ℝ ∞ (θ w) :=
    contDiff_id.add (contDiff_const.mul χ.contDiff)
  have hθderiv (w s : ℝ) : HasDerivAt (θ w) (θ' w s) s := by
    exact (hasDerivAt_id s).add
      (((χ.contDiff (n := 1)).differentiable (by simp)).differentiableAt.hasDerivAt.const_mul
        (w - v))
  have hθcont : Continuous (fun p : ℝ × ℝ => θ p.1 p.2) :=
    continuous_snd.add ((continuous_fst.sub continuous_const).mul
      ((χ.contDiff (n := 0)).continuous.comp continuous_snd))
  have hθ'cont : Continuous (fun p : ℝ × ℝ => θ' p.1 p.2) :=
    continuous_const.add ((continuous_fst.sub continuous_const).mul
      (((χ.contDiff (n := 1)).continuous_deriv (by simp)).comp continuous_snd))
  have hθid (w : ℝ) : EqOn (θ w) id (Iic c) := by
    intro s hs
    have hs' : s ≤ c := Set.mem_Iic.mp hs
    have hz : χ s = 0 := χ.zero_of_le_dist (by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : s - v ≤ 0)]
      dsimp only [χ]
      linarith)
    simp only [θ, hz, mul_zero, add_zero, id_eq]
  have hθv (w : ℝ) : θ w v = w := by
    have hχ : χ v = 1 := χ.eventuallyEq_one.self_of_nhds
    simp only [θ, hχ, mul_one]
    ring
  have hθc (w : ℝ) : θ w c = c := hθid w (Set.mem_Iic.mpr le_rfl)
  have hshift (w s : ℝ) : |s - θ w s| ≤ |w - v| := by
    have he : s - θ w s = -((w - v) * χ s) := by dsimp only [θ]; ring
    rw [he, abs_neg, abs_mul, abs_of_nonneg (χ.nonneg (x := s))]
    exact mul_le_of_le_one_right (abs_nonneg _) (χ.le_one (x := s))
  let Q : ℝ := max (E₀ + P * (d - c)) 0
  let η : ℝ := ε / (2 * (Q + (v - c) + 1))
  have hQ : 0 ≤ Q := le_max_right _ _
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsmall : η * Q + η * (v - c) ≤ ε := by
    have hden : 0 < 2 * (Q + (v - c) + 1) := by positivity
    have he : η * (2 * (Q + (v - c) + 1)) = ε := by
      dsimp only [η]
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith
  have hderiv : ∀ᶠ w in 𝓝 v, ∀ s ∈ Icc c v, 0 < θ' w s ∧
      θ' w s * Real.exp (K * |w - v|) < 1 + η := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hpos := (hθ'cont.continuousAt (x := (v, s))).eventually (Ioi_mem_nhds (a := (0 : ℝ)) (by
      simp only [θ', sub_self, zero_mul, add_zero]; norm_num))
    have hfac : Continuous (fun p : ℝ × ℝ =>
        θ' p.1 p.2 * Real.exp (K * |p.1 - v|)) :=
      hθ'cont.mul (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_fst.sub continuous_const).abs)))
    have hlt := (hfac.continuousAt (x := (v, s))).eventually (Iio_mem_nhds (by
      simpa only [θ', sub_self, zero_mul, mul_zero, Real.exp_zero,
        add_zero, mul_one, abs_zero] using lt_add_of_pos_right (1 : ℝ) hη))
    exact hpos.and hlt
  have hpotential : ∀ᶠ w in 𝓝 v, ∀ p ∈ Icc c v ×ˢ (univ : Set M),
      V p - θ' w p.1 * V (θ w p.1, p.2) < η := by
    apply (isCompact_Icc.prod isCompact_univ).eventually_forall_of_forall_eventually
    intro p hp
    have hpreg : p.1 ∈ Icc c d := ⟨hp.1.1, hp.1.2.trans hvd.le⟩
    have hleft : ContinuousAt (fun z : ℝ × (ℝ × M) => V z.2) (v, p) :=
      (hVat p.1 hpreg p.2).comp (f := fun z : ℝ × (ℝ × M) => z.2) (x := (v, p))
        continuous_snd.continuousAt
    have hright : ContinuousAt
        (fun z : ℝ × (ℝ × M) => V (θ z.1 z.2.1, z.2.2)) (v, p) := by
      have hm : Continuous (fun z : ℝ × (ℝ × M) => (θ z.1 z.2.1, z.2.2)) :=
        (hθcont.comp (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd)
      have he : θ v p.1 = p.1 := by simp only [θ, sub_self, zero_mul, add_zero]
      have hVθ : ContinuousAt V (θ v p.1, p.2) := by
        simpa only [he] using hVat p.1 hpreg p.2
      exact hVθ.comp (f := fun z : ℝ × (ℝ × M) => (θ z.1 z.2.1, z.2.2)) (x := (v, p))
        hm.continuousAt
    have hder : Continuous (fun z : ℝ × (ℝ × M) => θ' z.1 z.2.1) :=
      hθ'cont.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hsub := hleft.sub (hder.continuousAt.mul hright)
    refine hsub.eventually (p := fun y : ℝ => y < η) ?_
    apply Iio_mem_nhds
    simpa only [Pi.sub_apply, Pi.mul_apply, θ, θ', sub_self, zero_mul, add_zero, one_mul,
      Prod.mk.eta] using hη
  filter_upwards [Ioo_mem_nhds hcv hvd, hderiv, hpotential] with w hw hd hp
  refine ⟨hw.1, hw.2, θ w, hθ w, hθid w, hθv w, ?_⟩
  intro α hα hact
  have hmono : MonotoneOn (θ w) (Icc c v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hθ w).continuous.continuousOn
      ((hθ w).differentiable (by simp)).differentiableOn
    intro s hs
    rw [(hθderiv w s).deriv]
    exact (hd s (interior_subset hs)).1.le
  have hmaps (s : ℝ) (hs : s ∈ Icc c v) : θ w s ∈ Icc c w := by
    constructor
    · simpa only [hθc w] using hmono ⟨le_rfl, hcv.le⟩ hs hs.1
    · simpa only [hθv w] using hmono hs ⟨hcv.le, le_rfl⟩ hs.2
  have hcw (s : ℝ) (hs : s ∈ Icc c w) : T - s ^ 2 ∈ D.carrier :=
    D.regular_subset (hreg s ⟨hs.1, hs.2.trans hw.2.le⟩)
  have hcvreg (s : ℝ) (hs : s ∈ Icc c v) : T - s ^ 2 ∈ D.carrier :=
    D.regular_subset (hreg s ⟨hs.1, hs.2.trans hvd.le⟩)
  have hαlag : ContinuousOn (lRegularizedLagrangian S T α) (Icc c w) :=
    (lRegularizedLagrangian_continuousOn_carrier S hS α hα).comp (f := fun s : ℝ => (T, s))
      (continuous_const.prodMk continuous_id).continuousOn hcw
  have hαpot : ContinuousOn (fun s => V (s, α s)) (Icc c w) :=
    hV.comp (continuous_id.prodMk hα.continuous).continuousOn
      (fun s hs => ⟨hreg s ⟨hs.1, hs.2.trans hw.2.le⟩, mem_univ _⟩)
  let kinetic : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * (S.base.metric (T - s ^ 2)).inner (α s)
      (lVelocity (I := I) α s) (lVelocity (I := I) α s)
  have hkin : ContinuousOn kinetic (Icc c w) := by
    convert hαlag.sub hαpot using 1
    funext s
    dsimp only [Pi.sub_apply, kinetic, lRegularizedLagrangian, V]
    ring
  have hkinint : IntervalIntegrable kinetic volume c w := hkin.intervalIntegrable_of_Icc hw.1.le
  have hlagint : IntervalIntegrable (lRegularizedLagrangian S T α) volume c w :=
    hαlag.intervalIntegrable_of_Icc hw.1.le
  have hpotint : IntervalIntegrable (fun s => V (s, α s)) volume c w :=
    hαpot.intervalIntegrable_of_Icc hw.1.le
  have hpotlower : -(P * (w - c)) ≤ ∫ s in c..w, V (s, α s) := by
    have hi := intervalIntegral.integral_mono_on hw.1.le intervalIntegrable_const hpotint
      (fun s hs => (neg_le_neg (hP s ⟨hs.1, hs.2.trans hw.2.le⟩ (α s))).trans
        (neg_abs_le (V (s, α s))))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_neg, neg_mul, mul_comm]
      using hi
  have hkinsum : (∫ s in c..w, kinetic s) + (∫ s in c..w, V (s, α s)) =
      lRegularizedAction S T α c w := by
    rw [← intervalIntegral.integral_add hkinint hpotint]
    rfl
  have hkinbound : (∫ s in c..w, kinetic s) ≤ Q := by
    have hPd : P * (w - c) ≤ P * (d - c) :=
      mul_le_mul_of_nonneg_left (by linarith [hw.2]) (le_max_right _ _)
    have hEQ := le_max_left (E₀ + P * (d - c)) 0
    dsimp only [Q]
    linarith
  have hβ : ContMDiff 𝓘(ℝ, ℝ) I 1 (α ∘ θ w) :=
    hα.comp ((hθ w).of_le (by simp)).contMDiff
  have hβlag := (lRegularizedLagrangian_continuousOn_carrier S hS (α ∘ θ w) hβ).comp
    (continuous_const.prodMk continuous_id).continuousOn hcvreg
  have hθ'int : ContinuousOn (θ' w) (Icc c v) :=
    (hθ'cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hlagcomp := hαlag.comp (hθ w).continuous.continuousOn hmaps
  have hkincomp := hkin.comp (hθ w).continuous.continuousOn hmaps
  have hnew : ∀ s ∈ Icc c v,
      lRegularizedLagrangian S T (α ∘ θ w) s ≤
        lRegularizedLagrangian S T α (θ w s) * θ' w s +
          η * (kinetic (θ w s) * θ' w s) + η := by
    intro s hs
    have ht := hmaps s hs
    have hv := lVelocity_comp_of_hasDerivAt
      ((hα.mdifferentiable (by simp)).mdifferentiableAt) (hθderiv w s)
    have hq0 := metric_inner_self_nonneg (S.base.metric (T - (θ w s) ^ 2))
      (α (θ w s)) (lVelocity (I := I) α (θ w s))
    have hm := hmetric s ⟨hs.1, hs.2.trans hvd.le⟩ (θ w s)
      ⟨ht.1, ht.2.trans hw.2.le⟩ (α (θ w s)) (lVelocity (I := I) α (θ w s))
    have hexp : Real.exp (K * |s - θ w s|) ≤ Real.exp (K * |w - v|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hshift w s) hK)
    have hm' := hm.trans (mul_le_mul_of_nonneg_right hexp hq0)
    have hk₁ := mul_le_mul_of_nonneg_left hm' (sq_nonneg (θ' w s))
    have hk₂ := mul_le_mul_of_nonneg_right (hd s hs).2.le
      (mul_nonneg (hd s hs).1.le hq0)
    have hpot := (hp (s, α (θ w s)) ⟨hs, mem_univ _⟩).le
    dsimp only [lRegularizedLagrangian, kinetic, Function.comp_apply]
    rw [hv, metric_smul2]
    dsimp only [V] at hpot
    nlinarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hcv.le
    (hβlag.intervalIntegrable_of_Icc hcv.le)
    ((((hlagcomp.mul hθ'int).intervalIntegrable_of_Icc hcv.le).add
      (((hkincomp.mul hθ'int).intervalIntegrable_of_Icc hcv.le).const_mul η)).add
      intervalIntegrable_const) hnew
  have hsub (f : ℝ → ℝ) :
      (∫ s in c..v, f (θ w s) * θ' w s) = ∫ s in c..w, f s := by
    have hh := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := c) (b := v) (f := θ w) (f' := θ' w) (g := f) (hθ w).continuous.continuousOn
      (fun s _ => hθderiv w s) (fun s hs => (hd s (by
        simpa only [min_eq_left hcv.le, max_eq_right hcv.le] using Ioo_subset_Icc_self hs)).1.le)
    simpa only [hθc w, hθv w, Function.comp_apply] using hh
  rw [intervalIntegral.integral_add
      (((hlagcomp.mul hθ'int).intervalIntegrable_of_Icc hcv.le).add
        (((hkincomp.mul hθ'int).intervalIntegrable_of_Icc hcv.le).const_mul η))
      intervalIntegrable_const,
    intervalIntegral.integral_add ((hlagcomp.mul hθ'int).intervalIntegrable_of_Icc hcv.le)
      (((hkincomp.mul hθ'int).intervalIntegrable_of_Icc hcv.le).const_mul η),
    intervalIntegral.integral_const_mul] at hi
  simp only [Pi.mul_apply, Function.comp_apply] at hi
  rw [hsub, hsub, intervalIntegral.integral_const, smul_eq_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hkinbound hη.le
  change lRegularizedAction S T (α ∘ θ w) c v ≤ _ at hi
  change lRegularizedAction S T (α ∘ θ w) c v ≤ _
  dsimp only [lRegularizedAction] at hact ⊢
  dsimp only [lRegularizedAction] at hi
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
