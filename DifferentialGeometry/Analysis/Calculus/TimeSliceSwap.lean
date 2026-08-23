import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace DifferentialGeometry
namespace Analysis

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem jet_time_cont
    {R : ℝ → E → F} {J : Set ℝ} {V : Set E} {m : ℕ}
    (hjet : ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ m (R p.1) p.2) (J ×ˢ V))
    {a b : ℝ} (hab : uIcc a b ⊆ J) {x : E} (hx : x ∈ V) :
    ContinuousOn (fun t => iteratedFDeriv ℝ m (R t) x) (uIcc a b) := by
  exact hjet.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun t ht => ⟨hab ht, hx⟩)

omit [NormedSpace ℝ E] in
private theorem tube_bound
    {W : Type*} [NormedAddCommGroup W]
    {Φ : ℝ × E → W} {J : Set ℝ} {V : Set E}
    (hJ : IsOpen J) (hV : IsOpen V)
    (hΦ : ContinuousOn Φ (J ×ˢ V))
    {a b : ℝ} (hab : uIcc a b ⊆ J) {x : E} (hx : x ∈ V) :
    ∃ C : ℝ,
      {y : E | y ∈ V ∧ ∀ t ∈ uIcc a b, ‖Φ (t, y)‖ ≤ C} ∈ nhds x := by
  have hfixed : ContinuousOn (fun t : ℝ => ‖Φ (t, x)‖) (uIcc a b) :=
    hΦ.norm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hab ht, hx⟩)
  obtain ⟨C₀, hC₀⟩ := (isCompact_uIcc.image_of_continuousOn hfixed).bddAbove
  refine ⟨C₀ + 1, ?_⟩
  have hlocal : ∀ t ∈ uIcc a b,
      ∀ᶠ z : E × ℝ in nhds (x, t), ‖Φ (z.2, z.1)‖ ≤ C₀ + 1 := by
    intro t ht
    have hc : ContinuousAt (fun z : E × ℝ => Φ (z.2, z.1)) (x, t) :=
      (hΦ.continuousAt ((hJ.prod hV).mem_nhds ⟨hab ht, hx⟩)).comp
        (continuous_snd.prodMk continuous_fst).continuousAt
    filter_upwards [hc (Metric.closedBall_mem_nhds (Φ (t, x)) zero_lt_one)] with z hz
    exact (norm_le_norm_add_const_of_dist_le hz).trans
      (by simpa [add_comm] using add_le_add_right (hC₀ ⟨t, ht, rfl⟩) 1)
  have hall : ∀ᶠ y in nhds x, ∀ t ∈ uIcc a b, ‖Φ (t, y)‖ ≤ C₀ + 1 :=
    isCompact_uIcc.eventually_forall_of_forall_eventually hlocal
  filter_upwards [hall, hV.mem_nhds hx] with y hyall hyV
  exact ⟨hyV, hyall⟩

omit [NormedSpace ℝ E] in
private theorem tube_bound_on
    {W : Type*} [NormedAddCommGroup W]
    {Φ : ℝ × E → W} {J : Set ℝ} {V : Set E}
    (hV : IsOpen V)
    (hΦ : ContinuousOn Φ (J ×ˢ V))
    {a b : ℝ} (hab : uIcc a b ⊆ J) {x : E} (hx : x ∈ V) :
    ∃ C : ℝ,
      {y : E | y ∈ V ∧ ∀ t ∈ uIcc a b, ‖Φ (t, y)‖ ≤ C} ∈ nhds x := by
  have hfixed : ContinuousOn (fun t : ℝ => ‖Φ (t, x)‖) (uIcc a b) :=
    hΦ.norm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hab ht, hx⟩)
  obtain ⟨C₀, hC₀⟩ := (isCompact_uIcc.image_of_continuousOn hfixed).bddAbove
  refine ⟨C₀ + 1, ?_⟩
  have hlocal : ∀ t ∈ uIcc a b,
      ∀ᶠ z : E × ℝ in nhds (x, t),
        z.1 ∈ V → z.2 ∈ J → ‖Φ (z.2, z.1)‖ ≤ C₀ + 1 := by
    intro t ht
    have hswap : ContinuousOn (fun z : E × ℝ => (z.2, z.1)) (V ×ˢ J) :=
      (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun z : E × ℝ => (z.2, z.1)) (V ×ˢ J) (J ×ˢ V) :=
      fun _ hz => ⟨hz.2, hz.1⟩
    have hc : ContinuousWithinAt (fun z : E × ℝ => Φ (z.2, z.1))
        (V ×ˢ J) (x, t) :=
      (hΦ.comp hswap hmaps) (x, t) ⟨hx, hab ht⟩
    have hev := eventually_nhdsWithin_iff.mp
      (hc (Metric.closedBall_mem_nhds (Φ (t, x)) zero_lt_one))
    filter_upwards [hev] with z hz hzV hzJ
    exact (norm_le_norm_add_const_of_dist_le (hz ⟨hzV, hzJ⟩)).trans
      (by simpa [add_comm] using add_le_add_right (hC₀ ⟨t, ht, rfl⟩) 1)
  have hall₀ : ∀ᶠ y in nhds x, ∀ t ∈ uIcc a b,
      y ∈ V → t ∈ J → ‖Φ (t, y)‖ ≤ C₀ + 1 :=
    isCompact_uIcc.eventually_forall_of_forall_eventually
      (P := fun y t => y ∈ V → t ∈ J → ‖Φ (t, y)‖ ≤ C₀ + 1) hlocal
  have hall : ∀ᶠ y in nhds x, ∀ t ∈ uIcc a b, ‖Φ (t, y)‖ ≤ C₀ + 1 :=
    hall₀.and (hV.mem_nhds hx) |>.mono fun y hy t ht => hy.1 t ht hy.2 (hab ht)
  filter_upwards [hall, hV.mem_nhds hx] with y hyall hyV
  exact ⟨hyV, hyall⟩

private theorem iterF_integral
    {R : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : IsOpen J) (hV : IsOpen V)
    (hRs : ∀ t ∈ J, ContDiffOn ℝ ∞ (R t) V)
    (r : ℕ)
    (hRjet : ∀ m ≤ r,
      ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ m (R p.1) p.2)
        (J ×ˢ V))
    {a b : ℝ} (hab : uIcc a b ⊆ J) {x : E} (hx : x ∈ V) :
    iteratedFDeriv ℝ r (fun y => ∫ t in a..b, R t y) x =
      ∫ t in a..b, iteratedFDeriv ℝ r (R t) x := by
  induction r generalizing x with
  | zero =>
      have h₀ := jet_time_cont (hRjet 0 le_rfl) hab hx
      have hR : ContinuousOn (fun t => R t x) (uIcc a b) :=
        ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn h₀).congr
          (fun t _ => by simp only [Function.comp_apply,
            continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply])
      let L₀ : F →L[ℝ] E [×0]→L[ℝ] F :=
        (continuousMultilinearCurryFin0 ℝ E F).symm
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using
        (L₀.intervalIntegral_comp_comm hR.intervalIntegrable).symm
  | succ n ih =>
      letI : NormedAddCommGroup (E [×n]→L[ℝ] F) :=
        ContinuousMultilinearMap.normedAddCommGroup'
      letI : CompleteSpace (E [×n]→L[ℝ] F) :=
        ContinuousMultilinearMap.instCompleteSpace
      letI : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] F) :=
        ContinuousLinearMap.toNormedAddCommGroup
      letI : SecondCountableTopologyEither ℝ
          (E →L[ℝ] E [×n]→L[ℝ] F) :=
        secondCountableTopologyEither_of_left ℝ _
      let L : (E →L[ℝ] E [×n]→L[ℝ] F) →L[ℝ] E [×(n + 1)]→L[ℝ] F :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm
      let H : E → ℝ → E [×n]→L[ℝ] F :=
        fun y t => iteratedFDeriv ℝ n (R t) y
      let H' : E → ℝ → (E →L[ℝ] E [×n]→L[ℝ] F) :=
        fun y t => fderiv ℝ (iteratedFDeriv ℝ n (R t)) y
      have hnle : n ≤ n + 1 := Nat.le_succ n
      have hnext := hRjet (n + 1) le_rfl
      have hH' : ContinuousOn (fun p : ℝ × E => H' p.2 p.1) (J ×ˢ V) := by
        have hc :=
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (n + 1) => E) F).continuous.comp_continuousOn hnext
        exact hc.congr fun _ _ => rfl
      obtain ⟨C, hC⟩ := tube_bound
        (E := E) (Φ := fun p : ℝ × E => H' p.2 p.1)
        (J := J) (V := V) hJ hV hH' hab hx
      have hHcont (y : E) (hy : y ∈ V) :
          ContinuousOn (H y) (uIcc a b) :=
        jet_time_cont (hRjet n hnle) hab hy
      have hH'cont (y : E) (hy : y ∈ V) :
          ContinuousOn (H' y) (uIcc a b) :=
        hH'.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun t ht => ⟨hab ht, hy⟩)
      have hparam : HasFDerivAt
          (fun y => ∫ t in a..b, H y t) (∫ t in a..b, H' x t) x := by
        apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
          (s := {y : E | y ∈ V ∧ ∀ t ∈ uIcc a b, ‖H' y t‖ ≤ C}) hC
        · filter_upwards [hV.mem_nhds hx] with y hy
          exact ((hHcont y hy).mono uIoc_subset_uIcc).aestronglyMeasurable
            measurableSet_uIoc
        · exact (hHcont x hx).intervalIntegrable
        · exact ((hH'cont x hx).mono uIoc_subset_uIcc).aestronglyMeasurable
            measurableSet_uIoc
        · exact ae_of_all _ fun t ht y hy => hy.2 t (uIoc_subset_uIcc ht)
        · exact intervalIntegrable_const
        · exact ae_of_all _ fun t ht y hy =>
            ((hRs t (hab (uIoc_subset_uIcc ht))).contDiffAt
              (hV.mem_nhds hy.1)).differentiableAt_iteratedFDeriv (by
                show (n : WithTop ℕ∞) < ∞
                exact_mod_cast ENat.coe_lt_top n)
              |>.hasFDerivAt
      have hEq :
          iteratedFDeriv ℝ n (fun y => ∫ t in a..b, R t y) =ᶠ[nhds x]
            fun y => ∫ t in a..b, H y t := by
        filter_upwards [hV.mem_nhds hx] with y hy
        exact ih (fun m hm => hRjet m (hm.trans hnle)) hy
      have hH'int : IntervalIntegrable (H' x) volume a b :=
        (hH'cont x hx).intervalIntegrable
      have hL (f : E →L[ℝ] E [×n]→L[ℝ] F) : L f = f.uncurryLeft := by
        rfl
      have hcomm : L (∫ t in a..b, H' x t) = ∫ t in a..b, L (H' x t) := by
        simp only [hL]
        ext v
        simp only [ContinuousLinearMap.uncurryLeft_apply]
        rw [ContinuousLinearMap.intervalIntegral_apply hH'int (v 0)]
        let ev : (E [×n]→L[ℝ] F) →L[ℝ] F :=
          ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F (Fin.tail v)
        let evFull : (E [×(n + 1)]→L[ℝ] F) →L[ℝ] F :=
          ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => E) F v
        have hevInt : IntervalIntegrable (fun t => H' x t (v 0)) volume a b :=
          ((hH'cont x hx).clm_apply continuousOn_const).intervalIntegrable
        have huncInt : IntervalIntegrable
            (fun t => ContinuousLinearMap.uncurryLeft
              (Ei := fun _ : Fin (n + 1) => E) (H' x t)) volume a b := by
          have hLInt : IntervalIntegrable (fun t => L (H' x t)) volume a b :=
            (L.continuous.comp_continuousOn (hH'cont x hx)).intervalIntegrable
          simpa only [hL] using hLInt
        calc
          (∫ t in a..b, H' x t (v 0)) (Fin.tail v) =
              ∫ t in a..b, H' x t (v 0) (Fin.tail v) :=
            (ev.intervalIntegral_comp_comm hevInt).symm
          _ = ∫ t in a..b, (H' x t).uncurryLeft v := by
            apply intervalIntegral.integral_congr
            intro t _
            rfl
          _ = (∫ t in a..b, (H' x t).uncurryLeft) v :=
            evFull.intervalIntegral_comp_comm huncInt
      calc
        iteratedFDeriv ℝ (n + 1) (fun y => ∫ t in a..b, R t y) x =
            L (fderiv ℝ (iteratedFDeriv ℝ n
              (fun y => ∫ t in a..b, R t y)) x) := rfl
        _ = L (fderiv ℝ (fun y => ∫ t in a..b, H y t) x) := by
          rw [hEq.fderiv_eq]
        _ = L (∫ t in a..b, H' x t) := by rw [hparam.fderiv]
        _ = ∫ t in a..b, L (H' x t) := hcomm
        _ = ∫ t in a..b, iteratedFDeriv ℝ (n + 1) (R t) x := by
          apply intervalIntegral.integral_congr
          intro t _
          rfl

private theorem iterF_integral_Icc
    {R : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hV : IsOpen V)
    (hRs : ∀ t ∈ J, ContDiffOn ℝ ∞ (R t) V)
    (r : ℕ)
    (hRjet : ∀ m ≤ r,
      ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ m (R p.1) p.2)
        (J ×ˢ V))
    {a b : ℝ} (hab : uIcc a b ⊆ J) {x : E} (hx : x ∈ V) :
    iteratedFDeriv ℝ r (fun y => ∫ t in a..b, R t y) x =
      ∫ t in a..b, iteratedFDeriv ℝ r (R t) x := by
  induction r generalizing x with
  | zero =>
      have h₀ := jet_time_cont (hRjet 0 le_rfl) hab hx
      have hR : ContinuousOn (fun t => R t x) (uIcc a b) :=
        ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn h₀).congr
          (fun t _ => by simp only [Function.comp_apply,
            continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply])
      let L₀ : F →L[ℝ] E [×0]→L[ℝ] F :=
        (continuousMultilinearCurryFin0 ℝ E F).symm
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using
        (L₀.intervalIntegral_comp_comm hR.intervalIntegrable).symm
  | succ n ih =>
      letI : NormedAddCommGroup (E [×n]→L[ℝ] F) :=
        ContinuousMultilinearMap.normedAddCommGroup'
      letI : CompleteSpace (E [×n]→L[ℝ] F) :=
        ContinuousMultilinearMap.instCompleteSpace
      letI : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] F) :=
        ContinuousLinearMap.toNormedAddCommGroup
      letI : SecondCountableTopologyEither ℝ
          (E →L[ℝ] E [×n]→L[ℝ] F) :=
        secondCountableTopologyEither_of_left ℝ _
      let L : (E →L[ℝ] E [×n]→L[ℝ] F) →L[ℝ] E [×(n + 1)]→L[ℝ] F :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm
      let H : E → ℝ → E [×n]→L[ℝ] F :=
        fun y t => iteratedFDeriv ℝ n (R t) y
      let H' : E → ℝ → (E →L[ℝ] E [×n]→L[ℝ] F) :=
        fun y t => fderiv ℝ (iteratedFDeriv ℝ n (R t)) y
      have hnle : n ≤ n + 1 := Nat.le_succ n
      have hnext := hRjet (n + 1) le_rfl
      have hH' : ContinuousOn (fun p : ℝ × E => H' p.2 p.1) (J ×ˢ V) := by
        have hc :=
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (n + 1) => E) F).continuous.comp_continuousOn hnext
        exact hc.congr fun _ _ => rfl
      obtain ⟨C, hC⟩ := tube_bound_on
        (E := E) (Φ := fun p : ℝ × E => H' p.2 p.1)
        (J := J) (V := V) hV hH' hab hx
      have hHcont (y : E) (hy : y ∈ V) :
          ContinuousOn (H y) (uIcc a b) :=
        jet_time_cont (hRjet n hnle) hab hy
      have hH'cont (y : E) (hy : y ∈ V) :
          ContinuousOn (H' y) (uIcc a b) :=
        hH'.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun t ht => ⟨hab ht, hy⟩)
      have hparam : HasFDerivAt
          (fun y => ∫ t in a..b, H y t) (∫ t in a..b, H' x t) x := by
        apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
          (s := {y : E | y ∈ V ∧ ∀ t ∈ uIcc a b, ‖H' y t‖ ≤ C}) hC
        · filter_upwards [hV.mem_nhds hx] with y hy
          exact ((hHcont y hy).mono uIoc_subset_uIcc).aestronglyMeasurable
            measurableSet_uIoc
        · exact (hHcont x hx).intervalIntegrable
        · exact ((hH'cont x hx).mono uIoc_subset_uIcc).aestronglyMeasurable
            measurableSet_uIoc
        · exact ae_of_all _ fun t ht y hy => hy.2 t (uIoc_subset_uIcc ht)
        · exact intervalIntegrable_const
        · exact ae_of_all _ fun t ht y hy =>
            ((hRs t (hab (uIoc_subset_uIcc ht))).contDiffAt
              (hV.mem_nhds hy.1)).differentiableAt_iteratedFDeriv (by
                show (n : WithTop ℕ∞) < ∞
                exact_mod_cast ENat.coe_lt_top n)
              |>.hasFDerivAt
      have hEq :
          iteratedFDeriv ℝ n (fun y => ∫ t in a..b, R t y) =ᶠ[nhds x]
            fun y => ∫ t in a..b, H y t := by
        filter_upwards [hV.mem_nhds hx] with y hy
        exact ih (fun m hm => hRjet m (hm.trans hnle)) hy
      have hH'int : IntervalIntegrable (H' x) volume a b :=
        (hH'cont x hx).intervalIntegrable
      have hL (f : E →L[ℝ] E [×n]→L[ℝ] F) : L f = f.uncurryLeft := by
        rfl
      have hcomm : L (∫ t in a..b, H' x t) = ∫ t in a..b, L (H' x t) := by
        simp only [hL]
        ext v
        simp only [ContinuousLinearMap.uncurryLeft_apply]
        rw [ContinuousLinearMap.intervalIntegral_apply hH'int (v 0)]
        let ev : (E [×n]→L[ℝ] F) →L[ℝ] F :=
          ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F (Fin.tail v)
        let evFull : (E [×(n + 1)]→L[ℝ] F) →L[ℝ] F :=
          ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) => E) F v
        have hevInt : IntervalIntegrable (fun t => H' x t (v 0)) volume a b :=
          ((hH'cont x hx).clm_apply continuousOn_const).intervalIntegrable
        have huncInt : IntervalIntegrable
            (fun t => ContinuousLinearMap.uncurryLeft
              (Ei := fun _ : Fin (n + 1) => E) (H' x t)) volume a b := by
          have hLInt : IntervalIntegrable (fun t => L (H' x t)) volume a b :=
            (L.continuous.comp_continuousOn (hH'cont x hx)).intervalIntegrable
          simpa only [hL] using hLInt
        calc
          (∫ t in a..b, H' x t (v 0)) (Fin.tail v) =
              ∫ t in a..b, H' x t (v 0) (Fin.tail v) :=
            (ev.intervalIntegral_comp_comm hevInt).symm
          _ = ∫ t in a..b, (H' x t).uncurryLeft v := by
            apply intervalIntegral.integral_congr
            intro t _
            rfl
          _ = (∫ t in a..b, (H' x t).uncurryLeft) v :=
            evFull.intervalIntegral_comp_comm huncInt
      calc
        iteratedFDeriv ℝ (n + 1) (fun y => ∫ t in a..b, R t y) x =
            L (fderiv ℝ (iteratedFDeriv ℝ n
              (fun y => ∫ t in a..b, R t y)) x) := rfl
        _ = L (fderiv ℝ (fun y => ∫ t in a..b, H y t) x) := by
          rw [hEq.fderiv_eq]
        _ = L (∫ t in a..b, H' x t) := by rw [hparam.fderiv]
        _ = ∫ t in a..b, L (H' x t) := hcomm
        _ = ∫ t in a..b, iteratedFDeriv ℝ (n + 1) (R t) x := by
          apply intervalIntegral.integral_congr
          intro t _
          rfl

theorem hasDerivAt_iterF
    {G R : ℝ → E → F}
    {J : Set ℝ} {V : Set E}
    (hJ : IsOpen J) (hV : IsOpen V)
    (r : ℕ)
    (hGs : ∀ t ∈ J, ContDiffOn ℝ ∞ (G t) V)
    (hRs : ∀ t ∈ J, ContDiffOn ℝ ∞ (R t) V)
    (hpde : ∀ t ∈ J, ∀ x ∈ V,
      HasDerivAt (fun s => G s x) (R t x) t)
    (hRjet : ∀ m ≤ r,
      ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ m (R p.1) p.2)
        (J ×ˢ V))
    {t : ℝ} (ht : t ∈ J)
    {x : E} (hx : x ∈ V) :
    HasDerivAt
      (fun s => iteratedFDeriv ℝ r (G s) x)
      (iteratedFDeriv ℝ r (R t) x)
      t := by
  obtain ⟨a, b, htab, hI_nhds, hI⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds ht)
  have hab : a ≤ b := htab.1.trans htab.2
  have hRtime : ContinuousOn
      (fun s => iteratedFDeriv ℝ r (R s) x) J := by
    exact (hRjet r le_rfl).comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs => ⟨hs, hx⟩)
  have hRint : IntervalIntegrable
      (fun s => iteratedFDeriv ℝ r (R s) x) volume a t := by
    apply (hRtime.mono ?_).intervalIntegrable
    intro s hs
    have hs' : s ∈ Icc a t := by simpa [uIcc_of_le htab.1] using hs
    exact hI ⟨hs'.1, hs'.2.trans htab.2⟩
  have hRcont : ContinuousAt (fun s => iteratedFDeriv ℝ r (R s) x) t :=
    hRtime.continuousAt (hJ.mem_nhds ht)
  have hprim : HasDerivAt
      (fun s => ∫ u in a..s, iteratedFDeriv ℝ r (R u) x)
      (iteratedFDeriv ℝ r (R t) x) t :=
    intervalIntegral.integral_hasDerivAt_right hRint
      (ContinuousOn.stronglyMeasurableAtFilter hJ hRtime t ht) hRcont
  have heq :
      (fun s => iteratedFDeriv ℝ r (G s) x) =ᶠ[nhds t]
        fun s => iteratedFDeriv ℝ r (G a) x +
          ∫ u in a..s, iteratedFDeriv ℝ r (R u) x := by
    filter_upwards [hI_nhds] with s hs
    have has : a ≤ s := hs.1
    have hsb : s ≤ b := hs.2
    have hsub : uIcc a s ⊆ J := by
      intro u hu
      rw [uIcc_of_le has] at hu
      exact hI ⟨hu.1, hu.2.trans hsb⟩
    have hdiff : (fun y => ∫ u in a..s, R u y) =ᶠ[nhds x]
        fun y => G s y - G a y := by
      filter_upwards [hV.mem_nhds hx] with y hy
      have hRslice : ContinuousOn (fun u => R u y) (uIcc a s) :=
        ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
          (jet_time_cont (hRjet 0 (Nat.zero_le r)) hsub hy)).congr
            (fun u _ => by simp only [Function.comp_apply,
              continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply])
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hpde u (hsub hu) y hy)
        hRslice.intervalIntegrable
    have hjet := (Filter.EventuallyEq.iteratedFDeriv ℝ hdiff r).eq_of_nhds
    have hGsAt : ContDiffAt ℝ r (G s) x :=
      ((hGs s (hI hs)).contDiffAt (hV.mem_nhds hx)).of_le
        (by exact_mod_cast le_top)
    have hGaAt : ContDiffAt ℝ r (G a) x :=
      ((hGs a (hI ⟨le_rfl, hab⟩)).contDiffAt (hV.mem_nhds hx)).of_le
        (by exact_mod_cast le_top)
    have hsubJet : iteratedFDeriv ℝ r (fun y => G s y - G a y) x =
        iteratedFDeriv ℝ r (G s) x - iteratedFDeriv ℝ r (G a) x := by
      simpa only [Pi.sub_apply] using iteratedFDeriv_sub_apply hGsAt hGaAt
    have hintJet := iterF_integral hJ hV hRs r hRjet hsub hx
    rw [← hintJet]
    rw [hjet, hsubJet]
    abel
  exact (hprim.const_add (iteratedFDeriv ℝ r (G a) x)).congr_of_eventuallyEq heq

theorem hasDerivIcc_of_int
    {f f' : ℝ → F} {a b t : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContinuousOn f' (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt f (f' s) s)
    (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt f (f' t) (Set.Icc a b) t := by
  let g : ℝ → F := fun s => f a + ∫ u in a..s, f' u
  have hint : IntervalIntegrable f' volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le hf'
  have hrepr : ∀ s ∈ Set.Icc a b, f s = g s := by
    intro s hs
    have hsub : Set.Icc a s ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc le_rfl hs.2
    have hFTC : ∫ u in a..s, f' u = f s - f a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
        (hf.mono hsub)
        (fun u hu => hderiv u
          ⟨hu.1, lt_of_lt_of_le hu.2 hs.2⟩)
        (hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
          (by simpa only [Set.uIcc_of_le hab.le] using hs)))
    dsimp only [g]
    rw [hFTC]
    abel
  letI : Fact (t ∈ Set.Icc a b) := ⟨ht⟩
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hintT : IntervalIntegrable f' volume a t :=
    (hf'.mono (Set.uIcc_subset_Icc ha ht)).intervalIntegrable
  have hprim :
      HasDerivWithinAt
        (fun s => ∫ u in a..s, f' u) (f' t) (Set.Icc a b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hintT
      (hf'.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hf' t ht)
  have heq : f =ᶠ[nhdsWithin t (Set.Icc a b)] g := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hrepr s hs
  exact ((hprim.const_add (f a)).congr_of_eventuallyEq heq) (hrepr t ht)

theorem hasDerivWithin_iterF
    {G R : ℝ → E → F}
    {a b : ℝ} {V : Set E}
    (hV : IsOpen V)
    (r : ℕ)
    (hGs : ∀ t ∈ Set.Icc a b, ContDiffOn ℝ ∞ (G t) V)
    (hRs : ∀ t ∈ Set.Icc a b, ContDiffOn ℝ ∞ (R t) V)
    (hpde : ∀ t ∈ Set.Icc a b, ∀ x ∈ V,
      HasDerivWithinAt (fun s => G s x) (R t x) (Set.Icc a b) t)
    (hRjet : ∀ m ≤ r,
      ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ m (R p.1) p.2)
        (Set.Icc a b ×ˢ V))
    {t : ℝ} (ht : t ∈ Set.Icc a b)
    {x : E} (hx : x ∈ V) :
    HasDerivWithinAt
      (fun s => iteratedFDeriv ℝ r (G s) x)
      (iteratedFDeriv ℝ r (R t) x)
      (Set.Icc a b) t := by
  have hab : a ≤ b := ht.1.trans ht.2
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hRtime : ContinuousOn
      (fun s => iteratedFDeriv ℝ r (R s) x) (Set.Icc a b) := by
    exact (hRjet r le_rfl).comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs => ⟨hs, hx⟩)
  have hRint : IntervalIntegrable
      (fun s => iteratedFDeriv ℝ r (R s) x) volume a t :=
    (hRtime.mono (Set.uIcc_subset_Icc ha ht)).intervalIntegrable
  have : Fact (t ∈ Set.Icc a b) := ⟨ht⟩
  have hprim : HasDerivWithinAt
      (fun s => ∫ u in a..s, iteratedFDeriv ℝ r (R u) x)
      (iteratedFDeriv ℝ r (R t) x) (Set.Icc a b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hRint
      (hRtime.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hRtime t ht)
  have heq :
      (fun s => iteratedFDeriv ℝ r (G s) x) =ᶠ[nhdsWithin t (Set.Icc a b)]
        fun s => iteratedFDeriv ℝ r (G a) x +
          ∫ u in a..s, iteratedFDeriv ℝ r (R u) x := by
    change ∀ᶠ s in nhdsWithin t (Set.Icc a b),
      iteratedFDeriv ℝ r (G s) x =
        iteratedFDeriv ℝ r (G a) x +
          ∫ u in a..s, iteratedFDeriv ℝ r (R u) x
    rw [eventually_nhdsWithin_iff]
    exact Filter.Eventually.of_forall fun s hs => by
      have has : a ≤ s := hs.1
      have hsub : uIcc a s ⊆ Set.Icc a b := Set.uIcc_subset_Icc ha hs
      have hdiff : (fun y => ∫ u in a..s, R u y) =ᶠ[nhds x]
          fun y => G s y - G a y := by
        filter_upwards [hV.mem_nhds hx] with y hy
        have hRslice : ContinuousOn (fun u => R u y) (uIcc a s) :=
          ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
            (jet_time_cont (hRjet 0 (Nat.zero_le r)) hsub hy)).congr
              (fun u _ => by simp only [Function.comp_apply,
                continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply])
        have hGcont : ContinuousOn (fun u => G u y) (uIcc a s) :=
          HasDerivWithinAt.continuousOn fun u hu =>
            (hpde u (hsub hu) y hy).mono hsub
        exact intervalIntegral.integral_eq_sub_of_hasDeriv_right hGcont
          (fun u hu => by
            have hu' : u ∈ Set.Ioo a s := by
              simpa only [min_eq_left has, max_eq_right has] using hu
            exact (hpde u
              ⟨le_trans ha.1 (le_of_lt hu'.1),
                le_of_lt (lt_of_lt_of_le hu'.2 hs.2)⟩ y hy
                ).mono_of_mem_nhdsWithin
                  (Icc_mem_nhdsGT_of_mem
                    ⟨le_of_lt hu'.1, lt_of_lt_of_le hu'.2 hs.2⟩))
          hRslice.intervalIntegrable
      have hjet := (Filter.EventuallyEq.iteratedFDeriv ℝ hdiff r).eq_of_nhds
      have hGsAt : ContDiffAt ℝ r (G s) x :=
        ((hGs s hs).contDiffAt (hV.mem_nhds hx)).of_le
          (by exact_mod_cast le_top)
      have hGaAt : ContDiffAt ℝ r (G a) x :=
        ((hGs a ha).contDiffAt (hV.mem_nhds hx)).of_le
          (by exact_mod_cast le_top)
      have hsubJet : iteratedFDeriv ℝ r (fun y => G s y - G a y) x =
          iteratedFDeriv ℝ r (G s) x - iteratedFDeriv ℝ r (G a) x := by
        simpa only [Pi.sub_apply] using iteratedFDeriv_sub_apply hGsAt hGaAt
      have hintJet := iterF_integral_Icc hV hRs r hRjet hsub hx
      rw [← hintJet]
      rw [hjet, hsubJet]
      abel
  exact (hprim.const_add (iteratedFDeriv ℝ r (G a) x)).congr_of_eventuallyEq_of_mem heq ht

end Analysis
end DifferentialGeometry
