import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPoleAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Analysis.Calculus.Cutoff.SingularBarrier
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.WithTop

/-!
# S-CH11-FIX4 port of `Surgery.LGeometry.Action.PhysicalWeightedMinimum` (`PortC11P`)

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (3 errors).  Three elaboration-level repairs:
* `hshift` / `hbase` (donor line 188): `rw [mul_div_assoc]` before `linarith`, so the atom
  `2 * v ^ 2 / r ^ 2` is read as `2 * (v ^ 2 / r ^ 2)` and `hratio` applies.
* `hsubDist` (donor lines 236-237): the composite `dist ∘ Subtype.val` is named `hcomp` with its
  type and `ContinuousAt.comp` is given `f`, `x` explicitly (the first-order approximation
  otherwise picks `f := dist`, `x := ↑y`).
* `hLaction` (donor line 322): `(mul_le_mul_left h).mp hh` (an iff in the donor Mathlib) becomes
  `le_of_mul_le_mul_left hh h`.
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.PhysicalWeightedMinimum` is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

/-- The cutoff objective preserves infinity at unreachable and exterior endpoints. -/
noncomputable def physicalWeightedCost
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B r A v : ℝ) (p : (H.stage last).Carrier) (O q : (H.stage first).Carrier) :
    WithTop ℝ :=
  let g := H.stageMetric first (T - v ^ 2)
  let shift := A * (1 - 2 * v ^ 2 / r ^ 2)
  let arg := (riemannianEDistOf g O q).toReal / r - shift
  if riemannianEDistOf g O q < ENNReal.ofReal (r * (shift + 1 / 10)) then
    WithTop.map (fun L : ℝ => DifferentialGeometry.Analysis.SingularBarrier.value arg *
      (2 * v * L + 2 * r * v)) (H.regularizedCost first last hle T B 0 v p q)
  else ⊤

private theorem lowerSemicontinuous_positive_affine_map
    {X : Type*} [TopologicalSpace X]
    (f : X → WithTop ℝ) (hf : LowerSemicontinuous f)
    (w : X → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (v r : ℝ) (hv : 0 < v) :
    LowerSemicontinuous (fun x =>
      WithTop.map (fun L : ℝ => w x * (2 * v * L + 2 * r * v)) (f x)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro b
  cases b using WithTop.recTopCoe with
  | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
  | coe b =>
    have hepi : IsClosed {z : X × WithTop ℝ | f z.1 ≤ z.2} :=
      lowerSemicontinuous_iff_isClosed_epigraph.mp hf
    have hden : ∀ x, 0 < 2 * v * w x := fun x => by
      exact mul_pos (mul_pos (by norm_num) hv) (hwpos x)
    have hbnd : Continuous (fun x => b / (2 * v * w x) - r) :=
      (continuous_const.div (continuous_const.mul hw) (fun x => (hden x).ne')).sub
        continuous_const
    have hpair : Continuous (fun x : X =>
        (x, ((b / (2 * v * w x) - r : ℝ) : WithTop ℝ))) :=
      continuous_id.prodMk (WithTop.continuous_coe.comp hbnd)
    convert hepi.preimage hpair using 1
    ext x
    change WithTop.map (fun L : ℝ => w x * (2 * v * L + 2 * r * v)) (f x) ≤
      (b : WithTop ℝ) ↔ f x ≤ ((b / (2 * v * w x) - r : ℝ) : WithTop ℝ)
    cases f x using WithTop.recTopCoe with
    | top => simp only [WithTop.map_top, WithTop.not_top_le_coe]
    | coe L =>
      simp only [WithTop.map_coe, WithTop.coe_le_coe]
      rw [le_sub_iff_add_le, le_div_iff₀ (hden x)]
      constructor <;> intro h <;> nlinarith only [h]

private theorem two_lt_cutoff_inner :
    (2 : ℝ) < DifferentialGeometry.Analysis.SingularBarrier.value (1 / 12) := by
  change (2 : ℝ) < ((1 - (max (20 * (1 / 12 : ℝ) - 1) 0) ^ 4) ^ 4)⁻¹
  norm_num

private theorem physicalWeightedCost_eq_coe
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B r A v : ℝ) (p : (H.stage last).Carrier) (O q : (H.stage first).Carrier)
    (L : ℝ)
    (hinside : riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost first last hle T B 0 v p q = (L : WithTop ℝ)) :
    H.physicalWeightedCost first last hle T B r A v p O q =
      ((DifferentialGeometry.Analysis.SingularBarrier.value
        ((riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q).toReal / r -
          A * (1 - 2 * v ^ 2 / r ^ 2)) * (2 * v * L + 2 * r * v) : ℝ) : WithTop ℝ) := by
  simp only [physicalWeightedCost, if_pos hinside, hcost, WithTop.map_coe]

private theorem physicalWeightedCost_eq_top_of_cost
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B r A v : ℝ) (p : (H.stage last).Carrier) (O q : (H.stage first).Carrier)
    (hcost : H.regularizedCost first last hle T B 0 v p q = ⊤) :
    H.physicalWeightedCost first last hle T B r A v p O q = ⊤ := by
  simp only [physicalWeightedCost, hcost, WithTop.map_top, ite_self]

/-- The original controlled trace supplies a finite plateau competitor. Its comparison
localizes a genuine extended-cost minimum uniformly through small positive clocks. -/
theorem exists_seeded_physicalWeightedCost_minimum_of_cutoff_records
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hscalar : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (A : ℝ) (hA : 1 ≤ A)
    (t a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r v : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hrsmall : r ≤ min 1 (a₀ / 3))
    (hv : 0 < v) (hvr : v ≤ r / 2)
    (hclock : (a : ℝ) = (t : ℝ) - v ^ 2) :
    ∃ trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) p,
      trace.isRmControlled (hat := hat) r ∧
      let first := H.activeStage a
      let last := H.activeStage t
      let hle := H.activeStage_mono hat
      let O := trace.point first le_rfl hle
      let g := H.stageMetric first ((t : ℝ) - v ^ 2)
      let shift := A * (1 - 2 * v ^ 2 / r ^ 2)
      let phi := DifferentialGeometry.Analysis.SingularBarrier.value
      let W := H.physicalWeightedCost first last hle t (3 / a₀) r A v p O
      ∃ action : ℝ,
        (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle t (3 / a₀) 0 v p O ∧
        H.regularizedCost first last hle t (3 / a₀) 0 v p O ≤ (action : WithTop ℝ) ∧
        action ≤ 6 * v ^ 3 / r ^ 2 ∧ action ≤ 3 * v / 2 ∧
        ∃ (q : (H.stage first).Carrier) (L : ℝ),
          H.regularizedCost first last hle t (3 / a₀) 0 v p q = (L : WithTop ℝ) ∧
          riemannianEDistOf g O q < ENNReal.ofReal (r * (shift + 1 / 12)) ∧
          L ≤ action ∧ L < 1 ∧
          (11 / 6 : ℝ) * v * r ≤ 2 * v * L + 2 * r * v ∧
          let m := phi ((riemannianEDistOf g O q).toReal / r - shift) *
            (2 * v * L + 2 * r * v)
          W q = (m : WithTop ℝ) ∧ 0 < m ∧
          m ≤ 2 * v * action + 2 * r * v ∧
          ∀ y : (H.stage first).Carrier, W q ≤ W y := by
  classical
  have hr : 0 < r := hball.1
  have hrone : r ≤ 1 := hrsmall.trans (min_le_left _ _)
  have hra : r ≤ a₀ / 3 := hrsmall.trans (min_le_right _ _)
  let B : ℝ := 3 / a₀
  have hB : 0 < B := div_pos (by norm_num) ha₀
  have hBr : B * r ≤ 1 := by
    dsimp only [B]
    rw [div_mul_eq_mul_div, div_le_one ha₀]
    nlinarith
  have hr2 : r ^ 2 ≤ r := by
    nlinarith only [mul_le_mul_of_nonneg_left hrone hr.le]
  have hBr2 : B * r ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hr2 hB.le).trans hBr
  have hv2 : v ^ 2 ≤ r ^ 2 / 4 := by
    have hh := pow_le_pow_left₀ hv.le hvr 2
    norm_num [div_pow] at hh
    exact hh
  have hv3 : v ^ 3 ≤ r ^ 3 / 8 := by
    have hh := pow_le_pow_left₀ hv.le hvr 3
    norm_num [div_pow] at hh
    exact hh
  have hroom : (2 * B / 3) * v ^ 3 ≤ r / 12 := by
    have hh := mul_le_mul_of_nonneg_left hv3 (by positivity : 0 ≤ 2 * B / 3)
    have hh' := mul_le_mul_of_nonneg_right hBr2 hr.le
    nlinarith only [hh, hh']
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  have hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ z : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) z := by
    intro j s hs z
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num) ha₀ (le_add_of_nonneg_right htime)
    have hneg : -B ≤ -3 / (a₀ + s) := by
      simpa only [B, neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve.1 j s hs z).2
  obtain ⟨a', hat', hclock', trace, htrace, action, hmem, hseed, haction, hred, _⟩ :=
    H.exists_short_regularizedCost_upper_bound_of_parabolicallyRmControlledBall
      t p hball B hfloor v hv hvr
  have haa : a' = a := Subtype.ext (hclock'.trans hclock.symm)
  subst a'
  have haction' : action ≤ 3 * v / 2 := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * v)).mp hred
    nlinarith only [hh]
  let first := H.activeStage a
  let last := H.activeStage t
  let hle := H.activeStage_mono hat
  let O := trace.point first le_rfl hle
  let g := H.stageMetric first ((t : ℝ) - v ^ 2)
  let shift := A * (1 - 2 * v ^ 2 / r ^ 2)
  let C := H.regularizedCost first last hle t B 0 v p
  let dist := fun y : (H.stage first).Carrier => riemannianEDistOf g O y
  let arg := fun y : (H.stage first).Carrier => (dist y).toReal / r - shift
  let weight := fun y : (H.stage first).Carrier =>
    DifferentialGeometry.Analysis.SingularBarrier.value (arg y)
  let W := H.physicalWeightedCost first last hle t B r A v p O
  have hshift : (1 / 2 : ℝ) ≤ shift := by
    have hratio : v ^ 2 / r ^ 2 ≤ 1 / 4 :=
      (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith only [hv2])
    have hbase : (1 / 2 : ℝ) ≤ 1 - 2 * v ^ 2 / r ^ 2 := by
      rw [mul_div_assoc]
      linarith
    have hh := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1 - 2 * v ^ 2 / r ^ 2)
    dsimp only [shift]
    nlinarith only [hbase, hh]
  let Rinner := r * (shift + 1 / 12)
  let Router := r * (shift + 1 / 10)
  have hRinner : 0 < Rinner := mul_pos hr (by linarith)
  have hRouter : 0 < Router := mul_pos hr (by linarith)
  have hRlt : Rinner < Router := by
    dsimp only [Rinner, Router]
    nlinarith only [hr]
  let K : Set (H.stage first).Carrier := {y | dist y ≤ ENNReal.ofReal Rinner}
  have hdist : Continuous dist :=
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g O
  have hKclosed : IsClosed K := isClosed_le hdist continuous_const
  have hKcompact : IsCompact K := hKclosed.isCompact
  have hOK : O ∈ K := by simp only [K, dist, mem_setOf_eq, riemannianEDistOf_self, zero_le]
  have hfinite (y : (H.stage first).Carrier) (hy : y ∈ K) : dist y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
  have hargK (y : (H.stage first).Carrier) (hy : y ∈ K) : arg y ≤ 1 / 12 := by
    have hh := ENNReal.toReal_le_of_le_ofReal hRinner.le hy
    dsimp only [arg, Rinner] at *
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hr).mpr
    nlinarith only [hh]
  have hinsideK (y : (H.stage first).Carrier) (hy : y ∈ K) : dist y < ENNReal.ofReal Router :=
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hRouter).mpr hRlt)
  have hargInside (y : (H.stage first).Carrier) (hy : dist y < ENNReal.ofReal Router) :
      arg y < 1 / 10 := by
    have hh := ENNReal.toReal_lt_of_lt_ofReal hy
    dsimp only [arg, Router] at *
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith only [hh]
  have hinner_of_arg (y : (H.stage first).Carrier) (hyfinite : dist y ≠ ⊤)
      (hy : arg y < 1 / 12) : dist y < ENNReal.ofReal Rinner := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hyfinite).mpr
    have hh := (div_lt_iff₀ hr).mp ((sub_lt_iff_lt_add).mp hy)
    dsimp only [Rinner]
    nlinarith only [hh]
  have hcostLsc : LowerSemicontinuous C :=
    H.lowerSemicontinuous_regularizedCost first last hle t B 0 v
      (by simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t)
      (fun j s hs z => hfloor j.val ((t : ℝ) - s ^ 2)
        (H.mapsTo_regularizedStage_Ioo t 0 v j.val hs) z) p
  have hsubDist : Continuous (fun y : K => (dist y).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hcomp : ContinuousAt (fun y : K => dist (y : (H.stage first).Carrier)) y :=
      hdist.continuousAt.comp continuous_subtype_val.continuousAt
    exact (ENNReal.continuousAt_toReal (hfinite y y.property)).comp
      (f := fun y : K => dist (y : (H.stage first).Carrier)) (x := y) hcomp
  have hsubArg : Continuous (fun y : K => arg y) :=
    (hsubDist.div_const r).sub continuous_const
  have hsubWeight : Continuous (fun y : K => weight y) :=
    DifferentialGeometry.Analysis.SingularBarrier.contDiffOn.continuousOn.comp_continuous
      hsubArg (fun y => (hargK y y.property).trans_lt (by norm_num : (1 / 12 : ℝ) < 1 / 10))
  have hsubPos : ∀ y : K, 0 < weight y := fun y =>
    DifferentialGeometry.Analysis.SingularBarrier.pos (hargInside y (hinsideK y y.property))
  have hsubLsc : LowerSemicontinuous (fun y : K => W y) := by
    have hh := lowerSemicontinuous_positive_affine_map (fun y : K => C y)
      (hcostLsc.comp continuous_subtype_val) (fun y : K => weight y) hsubWeight hsubPos v r hv
    convert hh using 1
    funext y
    dsimp only [W, physicalWeightedCost, C, weight, arg, dist, shift, g]
    rw [if_pos (hinsideK y y.property)]
  have hWon : LowerSemicontinuousOn W K :=
    lowerSemicontinuous_restrict_iff.mp hsubLsc
  obtain ⟨q, hqK, hminK⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨O, hOK⟩ hKcompact hWon
  have hseedFinite : C O ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hseed
  obtain ⟨Lseed, hLseed⟩ := WithTop.ne_top_iff_exists.mp hseedFinite
  have hseedReal : Lseed ≤ action := WithTop.coe_le_coe.mp (hLseed.trans_le hseed)
  have hweightO : weight O = 1 := by
    apply DifferentialGeometry.Analysis.SingularBarrier.one_of_le
    dsimp only [arg, dist]
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, zero_div, zero_sub]
    linarith
  have hWO : W O = ((2 * v * Lseed + 2 * r * v : ℝ) : WithTop ℝ) := by
    have hh := H.physicalWeightedCost_eq_coe first last hle t B r A v p O O Lseed
      (hinsideK O hOK) hLseed.symm
    change W O = ((weight O * (2 * v * Lseed + 2 * r * v) : ℝ) : WithTop ℝ) at hh
    simpa only [hweightO, one_mul] using hh
  have hWseed : W O ≤ ((2 * v * action + 2 * r * v : ℝ) : WithTop ℝ) := by
    rw [hWO]
    apply WithTop.coe_le_coe.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hseedReal (by positivity : 0 ≤ 2 * v)]
  have hqseed := (hminK hOK).trans hWseed
  have hqWfinite : W q ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hqseed
  have hqfinite : C q ≠ ⊤ := by
    intro hh
    exact hqWfinite (H.physicalWeightedCost_eq_top_of_cost first last hle t B r A v p O q hh)
  obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hqfinite
  have hWq : W q = ((weight q * (2 * v * L + 2 * r * v) : ℝ) : WithTop ℝ) :=
    H.physicalWeightedCost_eq_coe first last hle t B r A v p O q L (hinsideK q hqK) hL.symm
  have hmseed : weight q * (2 * v * L + 2 * r * v) ≤ 2 * v * action + 2 * r * v :=
    WithTop.coe_le_coe.mp (hWq.symm.trans_le hqseed)
  have hshifted (y : (H.stage first).Carrier) (ell : ℝ) (hell : C y = (ell : WithTop ℝ)) :
      (11 / 6 : ℝ) * v * r ≤ 2 * v * ell + 2 * r * v := by
    have hh := H.regularizedCost_ge first last hle t B 0 v p y
    change ((-(2 * B / 3) * (v ^ 3 - 0 ^ 3) : ℝ) : WithTop ℝ) ≤ C y at hh
    rw [hell] at hh
    have hlow : -(2 * B / 3) * v ^ 3 ≤ ell := by
      simpa only [zero_pow (by decide : 3 ≠ 0), sub_zero] using WithTop.coe_le_coe.mp hh
    have hlow' : -r / 12 ≤ ell := by nlinarith only [hlow, hroom]
    have hh' := mul_le_mul_of_nonneg_left hlow' (by positivity : 0 ≤ 2 * v)
    nlinarith only [hh']
  have hZq := hshifted q L hL.symm
  have hzfloor : 0 < (11 / 6 : ℝ) * v * r := by positivity
  have hZqpos : 0 < 2 * v * L + 2 * r * v := hzfloor.trans_le hZq
  have hseedNumber : 2 * v * action + 2 * r * v ≤ (7 / 2 : ℝ) * v * r := by
    have hh := mul_le_mul_of_nonneg_left haction' (by positivity : 0 ≤ 2 * v)
    have hh' := mul_le_mul_of_nonneg_left hvr hv.le
    nlinarith only [hh, hh']
  have hbarrier (y : (H.stage first).Carrier) (hy : dist y < ENNReal.ofReal Router)
      (hyarg : 1 / 12 ≤ arg y) (ell : ℝ) (hell : C y = (ell : WithTop ℝ)) :
      2 * v * action + 2 * r * v < weight y * (2 * v * ell + 2 * r * v) := by
    have htwo : 2 < weight y := two_lt_cutoff_inner.trans_le
      (DifferentialGeometry.Analysis.SingularBarrier.monotoneOn
        (by norm_num : (1 / 12 : ℝ) ∈ Iio (1 / 10)) (hargInside y hy) hyarg)
    have hz := hshifted y ell hell
    have hzpos := hzfloor.trans_le hz
    calc
      2 * v * action + 2 * r * v ≤ (7 / 2 : ℝ) * v * r := hseedNumber
      _ < 2 * ((11 / 6 : ℝ) * v * r) := by nlinarith only [mul_pos hv hr]
      _ ≤ 2 * (2 * v * ell + 2 * r * v) := mul_le_mul_of_nonneg_left hz (by norm_num)
      _ < weight y * (2 * v * ell + 2 * r * v) := mul_lt_mul_of_pos_right htwo hzpos
  have hqarg : arg q < 1 / 12 := by
    by_contra hh
    exact (not_lt_of_ge hmseed) (hbarrier q (hinsideK q hqK) (le_of_not_gt hh) L hL.symm)
  have hqinner := hinner_of_arg q (hfinite q hqK) hqarg
  have honeq : 1 ≤ weight q :=
    DifferentialGeometry.Analysis.SingularBarrier.one_le (hargInside q (hinsideK q hqK))
  have hZle : 2 * v * L + 2 * r * v ≤ weight q * (2 * v * L + 2 * r * v) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right honeq hZqpos.le
  have hLaction : L ≤ action := by
    have hh : 2 * v * L ≤ 2 * v * action := by linarith [hZle.trans hmseed]
    exact le_of_mul_le_mul_left hh (by positivity : 0 < 2 * v)
  have hLone : L < 1 := by
    have hh : action ≤ 3 / 4 := by linarith [hvr, hrone]
    linarith only [hLaction, hh]
  have hmpos : 0 < weight q * (2 * v * L + 2 * r * v) :=
    mul_pos (lt_of_lt_of_le zero_lt_one honeq) hZqpos
  have hglobal (y : (H.stage first).Carrier) : W q ≤ W y := by
    by_cases hyK : y ∈ K
    · exact hminK hyK
    by_cases hyinside : dist y < ENNReal.ofReal Router
    · by_cases hycost : C y = ⊤
      · rw [show W y = ⊤ from
          H.physicalWeightedCost_eq_top_of_cost first last hle t B r A v p O y hycost]
        exact le_top
      obtain ⟨ell, hell⟩ := WithTop.ne_top_iff_exists.mp hycost
      have hyarg : 1 / 12 ≤ arg y := by
        by_contra hh
        exact hyK (hinner_of_arg y (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hyinside.le)
          (lt_of_not_ge hh)).le
      have hlarge := hbarrier y hyinside hyarg ell hell.symm
      have hWy : W y = ((weight y * (2 * v * ell + 2 * r * v) : ℝ) : WithTop ℝ) :=
        H.physicalWeightedCost_eq_coe first last hle t B r A v p O y ell hyinside hell.symm
      rw [hWq, hWy]
      exact WithTop.coe_le_coe.mpr (hmseed.trans hlarge.le)
    · have hWy : W y = ⊤ := by
        dsimp only [W, physicalWeightedCost]
        exact if_neg hyinside
      rw [hWy]
      exact le_top
  refine ⟨trace, htrace, ?_⟩
  dsimp only
  exact ⟨action, hmem, hseed, haction, haction', q, L, hL.symm, hqinner,
    hLaction, hLone, hZq, hWq, hmpos, hmseed, hglobal⟩

/-- Untopping is used only after this same support proves nearby costs finite. -/
theorem isLocalMin_physical_weighted_of_extended_minimum_and_same_support
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B r A : ℝ) {v : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier) (O q : (H.stage first).Carrier)
    (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ)
    (hU : IsOpen U) (hqU : (q, v) ∈ U)
    (hupper : ∀ z ∈ U,
      H.regularizedCost first last hle T B 0 z.2 p z.1 ≤ (F z : WithTop ℝ))
    (hinside : riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)))
    (hminimum : ∀ y : (H.stage first).Carrier,
      H.physicalWeightedCost first last hle T B r A v p O q ≤
        H.physicalWeightedCost first last hle T B r A v p O y) :
    (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle T B 0 v p y ≠ ⊤) ∧
    let t0 := T - v ^ 2
    let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
        A * (1 - 2 * ((T - s) / r ^ 2))
    let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
      DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
      (2 * Real.sqrt (T - s) *
        (H.regularizedCost first last hle T B 0 (Real.sqrt (T - s)) p y).untopD 0 +
        2 * r * Real.sqrt (T - s))
    IsLocalMin (actualWeighted t0) q := by
  have hslice : ∀ᶠ y in 𝓝 q, (y, v) ∈ U :=
    (hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hqU
  have hfinite : ∀ᶠ y in 𝓝 q,
      H.regularizedCost first last hle T B 0 v p y ≠ ⊤ := by
    filter_upwards [hslice] with y hy
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (hupper (y, v) hy)
  have hqfinite : H.regularizedCost first last hle T B 0 v p q ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hupper (q, v) hqU)
  let g := H.stageMetric first (T - v ^ 2)
  have hdist : Continuous (fun y => riemannianEDistOf g O y) :=
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g O
  have hinsideNear : ∀ᶠ y in 𝓝 q, riemannianEDistOf g O y <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) :=
    (isOpen_lt hdist continuous_const).mem_nhds hinside
  have hvalue (y : (H.stage first).Carrier)
      (hyinside : riemannianEDistOf g O y <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)))
      (hyfinite : H.regularizedCost first last hle T B 0 v p y ≠ ⊤) :
      H.physicalWeightedCost first last hle T B r A v p O y =
        ((DifferentialGeometry.Analysis.SingularBarrier.value
          ((riemannianEDistOf g O y).toReal / r - A * (1 - 2 * v ^ 2 / r ^ 2)) *
          (2 * v * (H.regularizedCost first last hle T B 0 v p y).untopD 0 +
            2 * r * v) : ℝ) : WithTop ℝ) := by
    obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hyfinite
    dsimp only [physicalWeightedCost]
    rw [if_pos hyinside, ← hL, WithTop.map_coe, WithTop.untopD_coe]
  refine ⟨hfinite, ?_⟩
  dsimp only
  have hclock : T - (T - v ^ 2) = v ^ 2 := by ring
  rw [hclock, Real.sqrt_sq hv.le]
  simp only [← mul_div_assoc]
  filter_upwards [hfinite, hinsideNear] with y hyfinite hyinside
  have hcompare := hminimum y
  rw [hvalue q hinside hqfinite, hvalue y hyinside hyfinite] at hcompare
  exact WithTop.coe_le_coe.mp hcompare

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
