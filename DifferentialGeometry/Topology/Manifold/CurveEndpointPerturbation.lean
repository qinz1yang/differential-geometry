import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry

open Filter Set
open scoped ContDiff Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiff_endpoint_perturbation_eqOn
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hab : a < b) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I (gamma b) (gamma b) ∈ V ∧
      ∃ alpha : E × ℝ → M,
        ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ (univ : Set ℝ)) ∧
        (∀ A ∈ V, ContMDiff 𝓘(ℝ, ℝ) I 1 (fun s => alpha (A, s))) ∧
        (∀ A ∈ V, EqOn (fun s => alpha (A, s)) gamma (Iic a)) ∧
        (∀ A ∈ V, alpha (A, b) = (extChartAt I (gamma b)).symm A) ∧
        ∀ s, alpha (extChartAt I (gamma b) (gamma b), s) = gamma s := by
  classical
  let p := gamma b
  let q : E := extChartAt I p p
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := I) p) q (mem_extChartAt_target p)
  let r := eps / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have houter : Metric.ball q (2 * r) ⊆ (extChartAt I p).target := by
    intro z hz
    exact hball (lt_of_lt_of_le hz (by change 2 * r ≤ eps; dsimp only [r]; linarith))
  have hcoord : ContinuousAt (fun s => extChartAt I p (gamma s)) b :=
    (continuousAt_extChartAt (I := I) p).comp hgamma.continuous.continuousAt
  have hgood : {s : ℝ | gamma s ∈ (extChartAt I p).source ∧
      extChartAt I p (gamma s) ∈ Metric.ball q r} ∈ 𝓝 b := by
    filter_upwards [hgamma.continuous.continuousAt.eventually
      ((isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)),
      hcoord.eventually (Metric.ball_mem_nhds q hr)] with s hs hc
    exact ⟨hs, hc⟩
  obtain ⟨delta, hdelta, hdeltaGood⟩ := Metric.mem_nhds_iff.mp hgood
  let d : ℝ := min delta (b - a)
  have hd : 0 < d := lt_min hdelta (sub_pos.mpr hab)
  let cut : ContDiffBump b :=
    { rIn := d / 4, rOut := d / 2, rIn_pos := by positivity,
      rIn_lt_rOut := by linarith }
  let W : Set ℝ := Metric.ball b delta
  let V : Set E := Metric.ball q r
  let coord : E × ℝ → E := fun z =>
    extChartAt I p (gamma z.2) + cut z.2 • (z.1 - q)
  let alpha : E × ℝ → M := fun z =>
    if z.2 ∈ W then (extChartAt I p).symm (coord z) else gamma z.2
  have hV : IsOpen V := Metric.isOpen_ball
  have hqV : q ∈ V := Metric.mem_ball_self hr
  have hW : IsOpen W := Metric.isOpen_ball
  have hbW : b ∈ W := Metric.mem_ball_self hdelta
  have htarget (A : E) (hA : A ∈ V) (s : ℝ) (hs : s ∈ W) :
      coord (A, s) ∈ (extChartAt I p).target := by
    apply houter
    rw [Metric.mem_ball, dist_eq_norm]
    have hu : ‖extChartAt I p (gamma s) - q‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using (hdeltaGood hs).2
    have hv : ‖A - q‖ < r := by simpa only [V, Metric.mem_ball, dist_eq_norm] using hA
    have hpert : ‖cut s • (A - q)‖ ≤ ‖A - q‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg cut.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) cut.le_one
    calc
      ‖coord (A, s) - q‖ = ‖(extChartAt I p (gamma s) - q) + cut s • (A - q)‖ := by
        congr 1
        dsimp only [coord]
        abel
      _ ≤ ‖extChartAt I p (gamma s) - q‖ + ‖cut s • (A - q)‖ := norm_add_le _ _
      _ < 2 * r := by linarith
  have hzero (s : ℝ) (hs : cut s = 0) (A : E) : alpha (A, s) = gamma s := by
    dsimp only [alpha]
    split_ifs with hsW
    · dsimp only [coord]
      rw [hs, zero_smul, add_zero]
      exact (extChartAt I p).left_inv (hdeltaGood hsW).1
    · rfl
  have halphaAt (z : E × ℝ) (hz : z.1 ∈ V) :
      ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha z := by
    by_cases hs : z.2 ∈ W
    · have hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
          (fun s => extChartAt I p (gamma s)) z.2 :=
        (contMDiffAt_extChartAt' (I := I) (n := 1) (x := p)
          (by simpa only [extChartAt_source] using (hdeltaGood hs).1)).comp
            z.2 (hgamma z.2)
      have hcoordMD : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 1 coord z :=
        (hc.comp z contMDiffAt_snd).add
          (((cut.contDiff.contMDiff).contMDiffAt.comp z contMDiffAt_snd).smul
            (contMDiffAt_fst.sub contMDiffAt_const))
      have hi : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I p).symm (coord z) :=
        (contMDiffOn_extChartAt_symm (I := I) (n := 1) p _ (htarget z.1 hz z.2 hs)).contMDiffAt
          ((isOpen_extChartAt_target (I := I) p).mem_nhds (htarget z.1 hz z.2 hs))
      apply (hi.comp z hcoordMD).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually (hW.mem_nhds hs)] with y hy
      exact if_pos hy
    · have hout : d / 2 < dist z.2 b := by
        have hn : delta ≤ dist z.2 b := le_of_not_gt hs
        have hdDelta : d ≤ delta := min_le_left _ _
        linarith
      have hnzero : ∀ᶠ s in 𝓝 z.2, cut s = 0 := by
        filter_upwards [(continuous_id.dist continuous_const).continuousAt.eventually
          (Ioi_mem_nhds hout)] with s hs
        exact cut.zero_of_le_dist hs.le
      apply (hgamma.contMDiffAt.comp z contMDiffAt_snd).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.tendsto.eventually hnzero] with y hy
      exact hzero y.2 hy y.1
  have halpha : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha
      (V ×ˢ (univ : Set ℝ)) := fun z hz => (halphaAt z hz.1).contMDiffWithinAt
  refine ⟨V, hV, hqV, alpha, halpha, ?_, ?_, ?_, ?_⟩
  · intro A hA s
    exact (halphaAt (A, s) hA).comp s (contMDiffAt_const.prodMk contMDiffAt_id)
  · intro A hA s hs
    apply hzero s
    apply cut.zero_of_le_dist
    have hdba : d ≤ b - a := min_le_right _ _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hs.trans hab.le))]
    dsimp only [cut]
    have hsle : s ≤ a := hs
    linarith
  · intro A hA
    have hone : cut b = 1 := cut.one_of_mem_closedBall (Metric.mem_closedBall_self cut.rIn_pos.le)
    dsimp only [alpha]
    rw [if_pos hbW]
    dsimp only [coord, p, q]
    rw [hone, one_smul, add_sub_cancel]
  · intro s
    dsimp only [alpha]
    split_ifs with hs
    · dsimp only [coord]
      rw [sub_self, smul_zero, add_zero]
      exact (extChartAt I p).left_inv (hdeltaGood hs).1
    · rfl

theorem exists_contMDiff_endpoint_perturbation
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hab : a < b) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I (gamma b) (gamma b) ∈ V ∧
      ∃ alpha : E × ℝ → M,
        ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ (univ : Set ℝ)) ∧
        (∀ A ∈ V, ContMDiff 𝓘(ℝ, ℝ) I 1 (fun s => alpha (A, s))) ∧
        (∀ A ∈ V, alpha (A, a) = gamma a) ∧
        (∀ A ∈ V, alpha (A, b) = (extChartAt I (gamma b)).symm A) ∧
        ∀ s, alpha (extChartAt I (gamma b) (gamma b), s) = gamma s := by
  obtain ⟨V, hV, hqV, alpha, halpha, hslices, hfixed, hend, hcenter⟩ :=
    exists_contMDiff_endpoint_perturbation_eqOn gamma hgamma hab
  exact ⟨V, hV, hqV, alpha, halpha, hslices,
    fun A hA => hfixed A hA (mem_Iic.mpr le_rfl), hend, hcenter⟩

theorem exists_contMDiff_two_endpoint_perturbation
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hab : a < b) :
    ∃ V W : Set E, IsOpen V ∧ IsOpen W ∧
      extChartAt I (gamma a) (gamma a) ∈ V ∧
      extChartAt I (gamma b) (gamma b) ∈ W ∧
      ∃ alpha : (E × E) × ℝ → M,
        ContMDiffOn (𝓘(ℝ, E × E).prod 𝓘(ℝ, ℝ)) I 1 alpha ((V ×ˢ W) ×ˢ univ) ∧
        (∀ A ∈ V, ∀ B ∈ W, ContMDiff 𝓘(ℝ, ℝ) I 1 (fun s => alpha ((A, B), s))) ∧
        (∀ A ∈ V, ∀ B ∈ W, alpha ((A, B), a) = (extChartAt I (gamma a)).symm A) ∧
        (∀ A ∈ V, ∀ B ∈ W, alpha ((A, B), b) = (extChartAt I (gamma b)).symm B) ∧
        ∀ s, alpha ((extChartAt I (gamma a) (gamma a),
          extChartAt I (gamma b) (gamma b)), s) = gamma s := by
  classical
  let c : ℝ := (3 * a + b) / 4
  let d : ℝ := (a + 3 * b) / 4
  let m : ℝ := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hcm : c < m := by dsimp only [c, m]; linarith
  have hmd : m < d := by dsimp only [m, d]; linarith
  have hdb : d < b := by dsimp only [d]; linarith
  let gammaRev : ℝ → M := fun s => gamma (-s)
  have hrev : ContMDiff 𝓘(ℝ, ℝ) I 1 gammaRev :=
    hgamma.comp contDiff_neg.contMDiff
  obtain ⟨V, hV, hqV, left, hleft, hleftSlices, hleftFixed, hleftEnd, hleftCenter⟩ :=
    exists_contMDiff_endpoint_perturbation_eqOn gammaRev hrev (neg_lt_neg hac)
  obtain ⟨W, hW, hqW, right, hright, hrightSlices, hrightFixed, hrightEnd, hrightCenter⟩ :=
    exists_contMDiff_endpoint_perturbation_eqOn gamma hgamma hdb
  have hqV' : extChartAt I (gamma a) (gamma a) ∈ V := by
    simpa only [gammaRev, neg_neg] using hqV
  let U : Set ((E × E) × ℝ) := (V ×ˢ W) ×ˢ univ
  let alpha : (E × E) × ℝ → M := fun z =>
    if z.2 ≤ m then left (z.1.1, -z.2) else right (z.1.2, z.2)
  have hU : IsOpen U := (hV.prod hW).prod isOpen_univ
  have hleftEq (A : E) (hA : A ∈ V) (s : ℝ) (hs : c ≤ s) :
      left (A, -s) = gamma s := by
    have hh := hleftFixed A hA (neg_le_neg hs)
    simpa only [gammaRev, neg_neg] using hh
  have hrightEq (B : E) (hB : B ∈ W) (s : ℝ) (hs : s ≤ d) :
      right (B, s) = gamma s := hrightFixed B hB hs
  have hleftAt (z : (E × E) × ℝ) (hz : z ∈ U) :
      ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, ℝ)) I 1
        (fun z : (E × E) × ℝ => left (z.1.1, -z.2)) z := by
    have hbase := (hleft (z.1.1, -z.2) ⟨hz.1.1, mem_univ _⟩).contMDiffAt
      ((hV.prod isOpen_univ).mem_nhds ⟨hz.1.1, mem_univ _⟩)
    apply hbase.comp z
    exact ((contDiff_fst.contMDiff).contMDiffAt.comp z contMDiffAt_fst).prodMk
      (contMDiffAt_snd.neg)
  have hrightAt (z : (E × E) × ℝ) (hz : z ∈ U) :
      ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, ℝ)) I 1
        (fun z : (E × E) × ℝ => right (z.1.2, z.2)) z := by
    have hbase := (hright (z.1.2, z.2) ⟨hz.1.2, mem_univ _⟩).contMDiffAt
      ((hW.prod isOpen_univ).mem_nhds ⟨hz.1.2, mem_univ _⟩)
    apply hbase.comp z
    exact ((contDiff_snd.contMDiff).contMDiffAt.comp z contMDiffAt_fst).prodMk contMDiffAt_snd
  have halphaAt (z : (E × E) × ℝ) (hz : z ∈ U) :
      ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, ℝ)) I 1 alpha z := by
    rcases lt_trichotomy z.2 m with hs | hs | hs
    · apply (hleftAt z hz).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually (Iio_mem_nhds hs)] with w hw
      exact if_pos hw.le
    · have htime : z.2 ∈ Ioo c d := by rw [hs]; exact ⟨hcm, hmd⟩
      apply (hgamma.contMDiffAt.comp z contMDiffAt_snd).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hz,
        continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds htime)] with w hw htw
      dsimp only [alpha]
      split_ifs
      · exact hleftEq w.1.1 hw.1.1 w.2 htw.1.le
      · exact hrightEq w.1.2 hw.1.2 w.2 htw.2.le
    · apply (hrightAt z hz).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually (Ioi_mem_nhds hs)] with w hw
      exact if_neg (not_le.mpr hw)
  refine ⟨V, W, hV, hW, hqV', hqW, alpha,
    fun z hz => (halphaAt z hz).contMDiffWithinAt, ?_, ?_, ?_, ?_⟩
  · intro A hA B hB s
    exact (halphaAt ((A, B), s) ⟨⟨hA, hB⟩, mem_univ _⟩).comp s
      (contMDiffAt_const.prodMk contMDiffAt_id)
  · intro A hA B hB
    have ham : a ≤ m := (hac.trans hcm).le
    dsimp only [alpha]
    rw [if_pos ham]
    simpa only [gammaRev, neg_neg] using hleftEnd A hA
  · intro A hA B hB
    have hbm : ¬ b ≤ m := not_le.mpr (hmd.trans hdb)
    dsimp only [alpha]
    rw [if_neg hbm]
    exact hrightEnd B hB
  · intro s
    dsimp only [alpha]
    split_ifs
    · simpa only [gammaRev, neg_neg] using hleftCenter (-s)
    · exact hrightCenter s


end DifferentialGeometry.Geometry
