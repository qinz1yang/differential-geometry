import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem timeJets_restrict (J : ℕ → ℝ → ℝ) {a b c : ℝ}
    (hab : a < b) (hbc : b < c)
    (hzero : ContDiffOn ℝ ∞ (J 0) (Set.Ioo a c))
    (hstep : ∀ k s, s ∈ Set.Icc a c →
      J (k + 1) s = derivWithin (J k) (Set.Icc a c) s) :
    ∀ k s, s ∈ Set.Icc b c →
      J (k + 1) s = derivWithin (J k) (Set.Icc b c) s := by
  have hsmooth : ∀ k, ContDiffOn ℝ ∞ (J k) (Set.Ioo a c) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k hk =>
      apply (hk.deriv_of_isOpen isOpen_Ioo (by simp)).congr
      intro s hs
      exact (hstep k s ⟨hs.1.le, hs.2.le⟩).trans
        (derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2))
  intro k s hs
  rw [hstep k s ⟨hab.le.trans hs.1, hs.2⟩]
  rcases hs.2.eq_or_lt with heq | hlt
  · subst s
    apply derivWithin_congr_set
    filter_upwards [Ioi_mem_nhds hbc] with t ht
    have hbt : b < t := ht
    apply propext
    change (a ≤ t ∧ t ≤ c) ↔ (b ≤ t ∧ t ≤ c)
    simp only [(hab.trans hbt).le, hbt.le, true_and]
  · have hsin : s ∈ Set.Ioo a c := ⟨hab.trans_le hs.1, hlt⟩
    have hd : DifferentiableAt ℝ (J k) s :=
      ((hsmooth k).contDiffAt (isOpen_Ioo.mem_nhds hsin)).differentiableAt (by simp)
    rw [hd.derivWithin (uniqueDiffOn_Icc (hab.trans hbc) s ⟨hsin.1.le, hs.2⟩),
      hd.derivWithin (uniqueDiffOn_Icc hbc s hs)]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

def WindowedModelWitness.mono_of_regular {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} (hS : IsSolutionOn S)
    {delta eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hde : delta ≤ eps) (he : eps < 1)
    (hreg : ∀ s ∈ Set.Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular) :
    WindowedModelWitness eps kappa S x t := by
  have heps : 0 < eps := W.eps_pos.trans_le hde
  have hdepth := modelDepth_anti W.eps_pos hde
  have htimes : Set.Icc (-modelDepth eps) 0 ⊆ Set.Icc (-modelDepth delta) 0 :=
    Set.Icc_subset_Icc (by linarith) le_rfl
  have hball : riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius eps) ⊆
        riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius delta) :=
    riemannianClosedBallOf_mono _ _ (modelRadius_anti W.eps_pos hde)
  refine
    { eps_pos := heps
      eps_lt_one := he
      time_mem := W.time_mem
      scalar_pos := W.scalar_pos
      window_mem := ?_
      model := W.model
      model_ancient := W.model_ancient
      model_scalar_base := W.model_scalar_base
      embedding := W.embedding
      buffered_ball := ?_
      base_map := W.base_map
      comparison :=
        { pullback := W.comparison.pullback
          pullback_eq := fun s y hy v => W.comparison.pullback_eq s y (hball hy) v
          jet := W.comparison.jet
          jet_zero := W.comparison.jet_zero
          jet_succ := ?_
          equivalence := ?_
          close := ?_ }
      source_capture := ?_ }
  · have hinv : (eps * S.scalar t x)⁻¹ ≤ (delta * S.scalar t x)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact div_le_div_of_nonneg_left zero_le_one (mul_pos W.eps_pos W.scalar_pos)
        (mul_le_mul_of_nonneg_right hde W.scalar_pos.le)
    intro s hs
    exact W.window_mem ⟨by linarith [hs.1], hs.2⟩
  · exact (riemannianClosedBallOf_mono _ _
      (show modelRadius eps + 1 ≤ modelRadius delta + 1 by
        linarith [modelRadius_anti W.eps_pos hde])).trans W.buffered_ball
  · intro k s hs y hy v
    rcases hde.eq_or_lt with heq | hlt
    · subst eps
      exact W.comparison.jet_succ k s hs y hy v
    have hleft : -modelDepth delta < -modelDepth eps := by
      have h := one_div_lt_one_div_of_lt W.eps_pos hlt
      simpa only [one_div, modelDepth, neg_lt_neg_iff] using h
    have hright : -modelDepth eps < 0 := neg_lt_zero.mpr (inv_pos.mpr heps)
    apply timeJets_restrict (fun n a => W.comparison.jet n a y v) hleft hright ?_
      (fun n a ha => W.comparison.jet_succ n a ha y (hball hy) v) k s hs
    have htime : ContDiff ℝ ∞ (parabolicTime t (S.scalar t x)) :=
      contDiff_const.add (contDiff_id.div_const _)
    have hsource := (hS.smoothMetric.coeff (W.embedding y)
      (mfderiv I3 I3 W.embedding y (v 0))
      (mfderiv I3 I3 W.embedding y (v 1))).comp htime.contDiffOn hreg
    have hscaled : ContDiffOn ℝ ∞
        (fun a => (rescaledMetric S t (S.scalar t x) W.scalar_pos a).inner
          (W.embedding y) (mfderiv I3 I3 W.embedding y (v 0))
          (mfderiv I3 I3 W.embedding y (v 1))) (Set.Ioo (-modelDepth delta) 0) := by
      simpa only [rescaledMetric, scaleMetric_inner, SolutionOn.family,
        Function.comp_def, smul_eq_mul] using
        hsource.const_smul (S.scalar t x)
    have hpull : ContDiffOn ℝ ∞ (fun a => W.comparison.pullback a y v)
        (Set.Ioo (-modelDepth delta) 0) :=
      hscaled.congr (fun a _ => W.comparison.pullback_eq a y (hball hy) v)
    have hmodel : ContDiffOn ℝ ∞
        (fun a => (W.model.S.base.metric a).inner y (v 0) (v 1))
        (Set.Ioo (-modelDepth delta) 0) :=
      (W.model.isSolution.smoothMetric.coeff y (v 0) (v 1)).mono (fun _ ha => ha.2)
    exact (hpull.sub hmodel).congr (fun a _ => W.comparison.jet_zero a y v)
  · intro s hs y hy v
    obtain ⟨hl, hu⟩ := W.comparison.equivalence s (htimes hs) y (hball hy) v
    have hn := inner_self_nonneg (I := I3) (W.model.S.base.metric s) y v
    constructor <;> nlinarith
  · intro a b hab s hs y hy
    exact (W.comparison.close a b (hab.trans (modelOrder_anti W.eps_pos hde))
      s (htimes hs) y (hball hy)).trans hde
  · exact (riemannianBallOf_mono _ _
      (sub_le_sub_right (modelRadius_anti W.eps_pos hde) 1)).trans W.source_capture

theorem orientedWitness_mono_closed {T : ℝ} {hT : 0 ≤ T}
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closed 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta ≤ eps) (he : eps < 1)
    {x : M} {t : ℝ} (hw : OrientedWitness S o delta kappa x t) :
    OrientedWitness S o eps kappa x t := by
  obtain ⟨W, oN, hO⟩ := hw
  have hstart : 0 ≤ t - (delta * S.scalar t x)⁻¹ := by
    exact (W.window_mem ⟨le_rfl, sub_le_self _
      (inv_nonneg.mpr (mul_nonneg W.eps_pos.le W.scalar_pos.le))⟩).1
  have hstart' : 0 ≤ t + (-modelDepth delta) / S.scalar t x := by
    simpa only [modelDepth, mul_inv, div_eq_mul_inv, neg_mul, sub_eq_add_neg] using hstart
  have hreg : ∀ s ∈ Set.Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈
        (RealTimeInterval.closed 0 T hT).regular := by
    intro s hs
    have hl := div_lt_div_of_pos_right hs.1 W.scalar_pos
    have hr := div_neg_of_neg_of_pos hs.2 W.scalar_pos
    have ht := W.time_mem.2
    exact ⟨by change 0 < t + s / S.scalar t x; linarith,
      by change t + s / S.scalar t x < T; linarith⟩
  exact ⟨W.mono_of_regular hS hde he hreg, oN, hO⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
