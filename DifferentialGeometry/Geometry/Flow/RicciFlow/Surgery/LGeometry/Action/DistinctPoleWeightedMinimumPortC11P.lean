import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.RecentScalarCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Surgery.LGeometry.Action.DistinctPoleWeightedMinimum`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (6 errors).  Elaboration-level repairs:
* `exists_pos_clock_distance_lt_of_terminal_distance_lt` (donor l.119): `simpa only [G, S,
  H.closedPrefixAt_metric] using hs` becomes `have hs' : riemannianEDistOf
  ((H.closedPrefixAt t hpole).flow.base.metric s) p x < ENNReal.ofReal R := hs`,
  `rw [H.closedPrefixAt_metric t hpole s] at hs'`, `exact hs'`.
* `hsubDist` (donor l.209-211): `hcomp` named with its type, `ContinuousAt.comp` given
  `(f := ..) (x := y)` (same repair as `PhysicalWeightedMinimum`).
* `hshifted` (donor l.270): `hneg : -2 * v ^ 3 / r ^ 2 = -(2 * v ^ 3 / r ^ 2) := by ring` added to
  the `linarith only` list (the two quotients are different atoms).
* `hLaction` (donor l.303): `(mul_le_mul_left h).mp hh` becomes `le_of_mul_le_mul_left hh h`.
* `hlower` (donor l.341-348): `rw [← hL] at hh` becomes `rw [show H.regularizedCost .. q = ↑L from
  hL.symm] at hh` (the let-bound `C q` is not matched syntactically); the final `nlinarith` is
  replaced by `h1 : (2 * r - 4 * v ^ 3 / r ^ 2) * v = 2 * r * v + 2 * v * (-2 * v ^ 3 / r ^ 2)`
  (`by ring`), `rw [h1]`, `linarith only [hlowmul, hZle]`.
* `hhi'` (donor l.579): `h12 : 12 * v ^ 3 / rho ^ 2 = 2 * (6 * v ^ 3 / rho ^ 2)` (`by ring`) and
  `linarith only [hhi, haction, h12]` instead of `nlinarith only [hhi, haction]`.
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.DistinctPoleWeightedMinimum` is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

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

noncomputable def tracedPhysicalWeightedMinimum
    (H : ObservedHistory.{u}) (aSeed t : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (p x : (H.stageAt t).Carrier)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (B r A v : ℝ) : WithTop ℝ :=
  if htime : (aSeed : ℝ) ≤ (t : ℝ) - v ^ 2 then
    let a : Icc (0 : ℝ) H.horizon :=
      ⟨(t : ℝ) - v ^ 2, aSeed.property.1.trans htime,
        (sub_le_self (t : ℝ) (sq_nonneg v)).trans t.property.2⟩
    let hat : a ≤ t := sub_le_self (t : ℝ) (sq_nonneg v)
    let has : aSeed ≤ a := htime
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    sInf (Set.range (H.physicalWeightedCost first last hle t B r A v x O))
  else ⊤

theorem exists_pos_clock_distance_lt_of_terminal_distance_lt
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (hpole : H.time (H.activeStage t) < (t : ℝ))
    (p x : (H.stageAt t).Carrier) (R : ℝ)
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal R) :
    ∃ e : ℝ, 0 < e ∧ e ^ 2 < (t : ℝ) - H.time (H.activeStage t) ∧
      ∀ v : ℝ, 0 < v → v < e →
        riemannianEDistOf (H.stageMetric (H.activeStage t) ((t : ℝ) - v ^ 2)) p x <
          ENNReal.ofReal R := by
  let S := H.closedPrefixAt t hpole
  let G := S.restrictIncoming le_rfl S.lt le_rfl
  let L := S.endpointTerminalLimitMetric (H.stageAt t)
  let p' : G.terminalRegularOpen := ⟨p, by
    change p ∈ G.terminalRegularRegion
    rw [S.terminalRegularRegion_eq_univ]
    exact mem_univ _⟩
  let x' : G.terminalRegularOpen := ⟨x, by
    change x ∈ G.terminalRegularRegion
    rw [S.terminalRegularRegion_eq_univ]
    exact mem_univ _⟩
  have hxy : riemannianEDistOf L.metric p' x' < ENNReal.ofReal R := by
    rw [S.riemannianEDistOf_endpointTerminalLimitMetric p' x']
    simpa only [S, H.closedPrefixAt_metric] using hdist
  have hnear : ∀ᶠ s in 𝓝[<] (t : ℝ),
      riemannianEDistOf (H.stageMetric (H.activeStage t) s) p x < ENNReal.ofReal R := by
    filter_upwards [L.eventually_riemannianEDistOf_lt p' x' hxy] with s hs
    have hs' : riemannianEDistOf ((H.closedPrefixAt t hpole).flow.base.metric s) p x <
        ENNReal.ofReal R := hs
    rw [H.closedPrefixAt_metric t hpole s] at hs'
    exact hs'
  obtain ⟨d, hd, hbound⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hpole).mp hnear
  let e : ℝ := Real.sqrt (((t : ℝ) - d) / 2)
  have hed : 0 < ((t : ℝ) - d) / 2 := by linarith only [hd.2]
  have he : 0 < e := Real.sqrt_pos.mpr hed
  have he2 : e ^ 2 = ((t : ℝ) - d) / 2 := Real.sq_sqrt hed.le
  refine ⟨e, he, ?_, ?_⟩
  · linarith only [he2, hd.1, hd.2]
  · intro v hv hve
    have hv2 : v ^ 2 < e ^ 2 := (sq_lt_sq₀ hv.le he.le).mpr hve
    exact hbound ⟨by linarith only [hv2, he2, hd.2],
      sub_lt_self _ (sq_pos_of_pos hv)⟩

theorem exists_physicalWeightedCost_minimum_of_plateau_competitor
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B r A v : ℝ) (x : (H.stage last).Carrier) (O y : (H.stage first).Carrier)
    (hr : 0 < r) (hv : 0 < v)
    (hshift : 0 ≤ A * (1 - 2 * v ^ 2 / r ^ 2))
    (hroom : 2 * v ^ 3 / r ^ 2 ≤ r / 4)
    (hcostLSC : LowerSemicontinuous (H.regularizedCost first last hle T B 0 v x))
    (hcostLower : ∀ z : (H.stage first).Carrier,
      ((-2 * v ^ 3 / r ^ 2 : ℝ) : WithTop ℝ) ≤
        H.regularizedCost first last hle T B 0 v x z)
    (action : ℝ)
    (hcompetitor : (action : WithTop ℝ) ∈
      H.regularizedActionValues first last hle T B 0 v x y)
    (haction : action ≤ r / 4)
    (hplateau : riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O y <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 20))) :
    ∃ (q : (H.stage first).Carrier) (L m : ℝ),
      H.regularizedCost first last hle T B 0 v x q = (L : WithTop ℝ) ∧
      riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 12)) ∧
      L ≤ action ∧ 3 * r / 4 ≤ L + r ∧
      H.physicalWeightedCost first last hle T B r A v x O q = (m : WithTop ℝ) ∧
      sInf (Set.range (H.physicalWeightedCost first last hle T B r A v x O)) =
        (m : WithTop ℝ) ∧
      0 < m ∧ 2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v ∧ m / v ≤ 2 * r + 2 * action ∧
      ∀ z : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle T B r A v x O q ≤
          H.physicalWeightedCost first last hle T B r A v x O z := by
  classical
  let g := H.stageMetric first (T - v ^ 2)
  let shift := A * (1 - 2 * v ^ 2 / r ^ 2)
  let C := H.regularizedCost first last hle T B 0 v x
  let dist := fun z : (H.stage first).Carrier => riemannianEDistOf g O z
  let arg := fun z : (H.stage first).Carrier => (dist z).toReal / r - shift
  let weight := fun z : (H.stage first).Carrier =>
    DifferentialGeometry.Analysis.SingularBarrier.value (arg z)
  let W := H.physicalWeightedCost first last hle T B r A v x O
  change 0 ≤ shift at hshift
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
      (hcostLSC.comp continuous_subtype_val) (fun y : K => weight y) hsubWeight hsubPos v r hv
    convert hh using 1
    funext y
    dsimp only [W, physicalWeightedCost, C, weight, arg, dist, shift, g]
    rw [if_pos (hinsideK y y.property)]
  have hWon : LowerSemicontinuousOn W K :=
    lowerSemicontinuous_restrict_iff.mp hsubLsc
  obtain ⟨q, hqK, hminK⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨O, hOK⟩ hKcompact hWon
  have hyK : y ∈ K := by
    have hsmall : r * (shift + 1 / 20) < Rinner := by
      dsimp only [Rinner]
      nlinarith only [hr]
    exact hplateau.le.trans (ENNReal.ofReal_le_ofReal hsmall.le)
  have hseed : C y ≤ (action : WithTop ℝ) :=
    H.regularizedCost_le_of_competitor first last hle T B 0 v x y hcompetitor
  have hseedFinite : C y ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hseed
  obtain ⟨Lseed, hLseed⟩ := WithTop.ne_top_iff_exists.mp hseedFinite
  have hseedReal : Lseed ≤ action := WithTop.coe_le_coe.mp (hLseed.trans_le hseed)
  have hweightY : weight y = 1 := by
    apply DifferentialGeometry.Analysis.SingularBarrier.one_of_le
    have hh := ENNReal.toReal_lt_of_lt_ofReal hplateau
    dsimp only [arg, dist, g, shift] at hh ⊢
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hr).mpr
    nlinarith only [hh]
  have hWY : W y = ((2 * v * Lseed + 2 * r * v : ℝ) : WithTop ℝ) := by
    have hh := H.physicalWeightedCost_eq_coe first last hle T B r A v x O y Lseed
      (hinsideK y hyK) hLseed.symm
    change W y = ((weight y * (2 * v * Lseed + 2 * r * v) : ℝ) : WithTop ℝ) at hh
    simpa only [hweightY, one_mul] using hh
  have hWseed : W y ≤ ((2 * v * action + 2 * r * v : ℝ) : WithTop ℝ) := by
    rw [hWY]
    apply WithTop.coe_le_coe.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hseedReal (by positivity : 0 ≤ 2 * v)]
  have hqseed := (hminK hyK).trans hWseed
  have hqWfinite : W q ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hqseed
  have hqfinite : C q ≠ ⊤ := by
    intro hh
    exact hqWfinite (H.physicalWeightedCost_eq_top_of_cost first last hle T B r A v x O q hh)
  obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hqfinite
  have hWq : W q = ((weight q * (2 * v * L + 2 * r * v) : ℝ) : WithTop ℝ) :=
    H.physicalWeightedCost_eq_coe first last hle T B r A v x O q L (hinsideK q hqK) hL.symm
  have hmseed : weight q * (2 * v * L + 2 * r * v) ≤ 2 * v * action + 2 * r * v :=
    WithTop.coe_le_coe.mp (hWq.symm.trans_le hqseed)
  have hshifted (z : (H.stage first).Carrier) (ell : ℝ) (hell : C z = (ell : WithTop ℝ)) :
      3 * r / 4 ≤ ell + r := by
    have hh := hcostLower z
    rw [show H.regularizedCost first last hle T B 0 v x z = (ell : WithTop ℝ) from hell] at hh
    have hlow : -2 * v ^ 3 / r ^ 2 ≤ ell := WithTop.coe_le_coe.mp hh
    have hneg : -2 * v ^ 3 / r ^ 2 = -(2 * v ^ 3 / r ^ 2) := by ring
    linarith only [hlow, hroom, hneg]
  have hLr := hshifted q L hL.symm
  have hZq : (3 / 2 : ℝ) * v * r ≤ 2 * v * L + 2 * r * v := by
    nlinarith only [mul_le_mul_of_nonneg_left hLr hv.le]
  have hzfloor : 0 < (3 / 2 : ℝ) * v * r := by positivity
  have hZqpos : 0 < 2 * v * L + 2 * r * v := hzfloor.trans_le hZq
  have hseedNumber : 2 * v * action + 2 * r * v ≤ (5 / 2 : ℝ) * v * r := by
    nlinarith only [mul_le_mul_of_nonneg_left haction hv.le]
  have hbarrier (z : (H.stage first).Carrier) (hz : dist z < ENNReal.ofReal Router)
      (hzarg : 1 / 12 ≤ arg z) (ell : ℝ) (hell : C z = (ell : WithTop ℝ)) :
      2 * v * action + 2 * r * v < weight z * (2 * v * ell + 2 * r * v) := by
    have htwo : 2 < weight z := two_lt_cutoff_inner.trans_le
      (DifferentialGeometry.Analysis.SingularBarrier.monotoneOn
        (by norm_num : (1 / 12 : ℝ) ∈ Iio (1 / 10)) (hargInside z hz) hzarg)
    have hzr := hshifted z ell hell
    have hzlow : (3 / 2 : ℝ) * v * r ≤ 2 * v * ell + 2 * r * v := by
      nlinarith only [mul_le_mul_of_nonneg_left hzr hv.le]
    have hzpos := hzfloor.trans_le hzlow
    calc
      2 * v * action + 2 * r * v ≤ (5 / 2 : ℝ) * v * r := hseedNumber
      _ < 2 * ((3 / 2 : ℝ) * v * r) := by nlinarith only [mul_pos hv hr]
      _ ≤ 2 * (2 * v * ell + 2 * r * v) := mul_le_mul_of_nonneg_left hzlow (by norm_num)
      _ < weight z * (2 * v * ell + 2 * r * v) := mul_lt_mul_of_pos_right htwo hzpos
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
  let m : ℝ := weight q * (2 * v * L + 2 * r * v)
  have hmpos : 0 < m := mul_pos (lt_of_lt_of_le zero_lt_one honeq) hZqpos
  have hglobal (z : (H.stage first).Carrier) : W q ≤ W z := by
    by_cases hzK : z ∈ K
    · exact hminK hzK
    by_cases hzinside : dist z < ENNReal.ofReal Router
    · by_cases hzcost : C z = ⊤
      · rw [show W z = ⊤ from
          H.physicalWeightedCost_eq_top_of_cost first last hle T B r A v x O z hzcost]
        exact le_top
      obtain ⟨ell, hell⟩ := WithTop.ne_top_iff_exists.mp hzcost
      have hzarg : 1 / 12 ≤ arg z := by
        by_contra hh
        exact hzK (hinner_of_arg z (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hzinside.le)
          (lt_of_not_ge hh)).le
      have hlarge := hbarrier z hzinside hzarg ell hell.symm
      have hWz : W z = ((weight z * (2 * v * ell + 2 * r * v) : ℝ) : WithTop ℝ) :=
        H.physicalWeightedCost_eq_coe first last hle T B r A v x O z ell hzinside hell.symm
      rw [hWq, hWz]
      exact WithTop.coe_le_coe.mpr (hmseed.trans hlarge.le)
    · have hWz : W z = ⊤ := by
        dsimp only [W, physicalWeightedCost]
        exact if_neg hzinside
      rw [hWz]
      exact le_top
  have hBdd : BddBelow (Set.range W) := ⟨W q, by
    rintro _ ⟨z, rfl⟩
    exact hglobal z⟩
  have hInf : sInf (Set.range W) = W q := le_antisymm
    (csInf_le hBdd (Set.mem_range_self q))
    (le_csInf ⟨W q, Set.mem_range_self q⟩ (by rintro _ ⟨z, rfl⟩; exact hglobal z))
  have hlower : 2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v := by
    have hh := hcostLower q
    rw [show H.regularizedCost first last hle T B 0 v x q = (L : WithTop ℝ) from hL.symm] at hh
    have hlow : -2 * v ^ 3 / r ^ 2 ≤ L := WithTop.coe_le_coe.mp hh
    apply (le_div_iff₀ hv).mpr
    dsimp only [m]
    have hlowmul := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 * v)
    have h1 : (2 * r - 4 * v ^ 3 / r ^ 2) * v =
        2 * r * v + 2 * v * (-2 * v ^ 3 / r ^ 2) := by ring
    rw [h1]
    linarith only [hlowmul, hZle]
  have hupper : m / v ≤ 2 * r + 2 * action := by
    apply (div_le_iff₀ hv).mpr
    dsimp only [m]
    nlinarith only [hmseed]
  exact ⟨q, L, m, hL.symm, hqinner, hLaction, hLr, hWq,
    hInf.trans hWq, hmpos, hlower, hupper, hglobal⟩

theorem exists_distinct_pole_initial_weighted_minimum_and_limit
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ z, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ z)
    (hscalar : ∀ z, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) z)
    (aSeed t : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (p x : (H.stageAt t).Carrier) (r rho A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A)
    (hSeedClock : (aSeed : ℝ) = (t : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hPoleTest : H.isParabolicallyRmControlledBall t x rho)
    (hrecent : 2 * r ^ 2 < (t : ℝ))
    (hpole : H.time (H.activeStage t) < (t : ℝ))
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r)) :
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    (∃ e : ℝ, 0 < e ∧ e ≤ r / 4 ∧ e ≤ rho / 2 ∧
      e ^ 2 < (t : ℝ) - H.time (H.activeStage t) ∧ 6 * e ^ 3 / rho ^ 2 ≤ r / 4 ∧
      ∀ v : ℝ, 0 < v → v < e →
        ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - v ^ 2 ∧
          H.activeStage a = H.activeStage t ∧
          let first := H.activeStage a
          let last := H.activeStage t
          let hle := H.activeStage_mono hat
          let O := seedTrace.point first (H.activeStage_mono has) hle
          ∃ poleTrace : BackwardPointTrace H first last hle x,
            poleTrace.isRmControlled (hat := hat) rho ∧
            let y := poleTrace.point first le_rfl hle
            riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
              ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) ∧
            ∃ action : ℝ,
              action ∈ H.regularizedC1ActionValues first last hle t 0 v x y ∧
              (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle t (3 / a₀) 0 v x y ∧
              H.regularizedCost first last hle t (3 / a₀) 0 v x y ≤ (action : WithTop ℝ) ∧
              action ≤ 6 * v ^ 3 / rho ^ 2 ∧
              ∃ (q : (H.stage first).Carrier) (L m : ℝ),
                H.regularizedCost first last hle t (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
                riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O q <
                  ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 12)) ∧
                L ≤ action ∧ 3 * r / 4 ≤ L + r ∧
                H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q = (m : WithTop ℝ) ∧
                M v = (m : WithTop ℝ) ∧ 0 < m ∧
                2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v ∧
                m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 ∧
                ∀ z : (H.stage first).Carrier,
                  H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q ≤
                    H.physicalWeightedCost first last hle t (3 / a₀) r A v x O z) ∧
    (∀ᶠ v in 𝓝[>] (0 : ℝ), M v ≠ ⊤) ∧
    Tendsto (fun v : ℝ => (M v).untopD 0 / v) (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
  classical
  intro M
  obtain ⟨hrho, aPole, hPoleTime, hPoleClock, hPoleTraces⟩ := hPoleTest
  have hxball : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) x rho := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) x x < ENNReal.ofReal rho
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hrho
  obtain ⟨fullPoleTrace, hFullPoleTrace⟩ := hPoleTraces x hxball
  obtain ⟨R, hdR, hRAr⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hdist)
  have hR : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal R := (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hdist)).mpr hdR
  obtain ⟨eD, heD, heDage, hD⟩ :=
    H.exists_pos_clock_distance_lt_of_terminal_distance_lt t hpole p x R hR
  have hgapCont : Continuous (fun w : ℝ => r * (A * (1 - 2 * w ^ 2 / r ^ 2))) := by
    fun_prop
  have hgap0 : R < r * (A * (1 - 2 * (0 : ℝ) ^ 2 / r ^ 2)) := by
    simpa only [zero_pow two_ne_zero, mul_zero, zero_div, sub_zero, mul_one, mul_comm r A]
      using hRAr
  have hgap : ∀ᶠ w in 𝓝 (0 : ℝ), R < r * (A * (1 - 2 * w ^ 2 / r ^ 2)) :=
    hgapCont.continuousAt.eventually (Ioi_mem_nhds hgap0)
  have hcubeCont : Continuous (fun w : ℝ => 6 * w ^ 3 / rho ^ 2) := by fun_prop
  have hcube0 : 6 * (0 : ℝ) ^ 3 / rho ^ 2 < r / 4 := by
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div] using
      (div_pos hr (by norm_num : (0 : ℝ) < 4))
  have hcubeNear : ∀ᶠ w in 𝓝 (0 : ℝ), 6 * w ^ 3 / rho ^ 2 < r / 4 :=
    hcubeCont.continuousAt.eventually (Iio_mem_nhds hcube0)
  obtain ⟨d, hd, hsmall⟩ := Metric.eventually_nhds_iff.mp (hgap.and hcubeNear)
  let e : ℝ := min eD (min (r / 4) (min (rho / 2) (d / 2)))
  have he : 0 < e := lt_min heD (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have heeD : e ≤ eD := min_le_left _ _
  have her : e ≤ r / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have herho : e ≤ rho / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hed : e < d := lt_of_le_of_lt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (half_lt_self hd)
  have heage : e ^ 2 < (t : ℝ) - H.time (H.activeStage t) :=
    (pow_le_pow_left₀ he.le heeD 2).trans_lt heDage
  have heDist : dist e (0 : ℝ) < d := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using hed
  have hecube : 6 * e ^ 3 / rho ^ 2 ≤ r / 4 := (hsmall heDist).2.le
  have hHI := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  have hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ z : (H.stage j).Carrier, -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) z := by
    intro j s hs z
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num) ha₀ (le_add_of_nonneg_right htime)
    exact (show -(3 / a₀) ≤ -3 / (a₀ + s) by
      simpa only [neg_div] using neg_le_neg hratio).trans (hHI.1 j s hs z).2
  have hlocal : ∀ v : ℝ, 0 < v → v < e →
      ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
        (a : ℝ) = (t : ℝ) - v ^ 2 ∧
        H.activeStage a = H.activeStage t ∧
        let first := H.activeStage a
        let last := H.activeStage t
        let hle := H.activeStage_mono hat
        let O := seedTrace.point first (H.activeStage_mono has) hle
        ∃ poleTrace : BackwardPointTrace H first last hle x,
          poleTrace.isRmControlled (hat := hat) rho ∧
          let y := poleTrace.point first le_rfl hle
          riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
            ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) ∧
          ∃ action : ℝ,
            action ∈ H.regularizedC1ActionValues first last hle t 0 v x y ∧
            (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle t (3 / a₀) 0 v x y ∧
            H.regularizedCost first last hle t (3 / a₀) 0 v x y ≤ (action : WithTop ℝ) ∧
            action ≤ 6 * v ^ 3 / rho ^ 2 ∧
            ∃ (q : (H.stage first).Carrier) (L m : ℝ),
              H.regularizedCost first last hle t (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
              riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O q <
                ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 12)) ∧
              L ≤ action ∧ 3 * r / 4 ≤ L + r ∧
              H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q = (m : WithTop ℝ) ∧
              M v = (m : WithTop ℝ) ∧ 0 < m ∧
              2 * r - 4 * v ^ 3 / r ^ 2 ≤ m / v ∧
              m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 ∧
              ∀ z : (H.stage first).Carrier,
                H.physicalWeightedCost first last hle t (3 / a₀) r A v x O q ≤
                  H.physicalWeightedCost first last hle t (3 / a₀) r A v x O z := by
    intro v hv hve
    have hvr : v ≤ r / 4 := hve.le.trans her
    have hvrHalf : v ≤ r / 2 := by linarith
    have hvrho : v ≤ rho / 2 := hve.le.trans herho
    have hv2r : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv.le (by linarith : v ≤ r) 2
    have hv2rho : v ^ 2 ≤ rho ^ 2 :=
      pow_le_pow_left₀ hv.le (by linarith : v ≤ rho) 2
    have hasTime : (aSeed : ℝ) ≤ (t : ℝ) - v ^ 2 := by
      rw [hSeedClock]
      linarith only [hv2r]
    let a : Icc (0 : ℝ) H.horizon :=
      ⟨(t : ℝ) - v ^ 2, aSeed.property.1.trans hasTime,
        (sub_le_self (t : ℝ) (sq_nonneg v)).trans t.property.2⟩
    have has : aSeed ≤ a := hasTime
    have hat : a ≤ t := sub_le_self (t : ℝ) (sq_nonneg v)
    have hPoleA : aPole ≤ a := by
      change (aPole : ℝ) ≤ (t : ℝ) - v ^ 2
      rw [hPoleClock]
      linarith only [hv2rho]
    have hstage : H.activeStage a = H.activeStage t := by
      apply le_antisymm (H.activeStage_mono hat) (H.le_activeStage a (H.activeStage t) ?_)
      change H.time (H.activeStage t) ≤ (t : ℝ) - v ^ 2
      have hh := (pow_le_pow_left₀ hv.le hve.le 2).trans_lt heage
      linarith only [hh]
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    let poleTrace : BackwardPointTrace H first last hle x :=
      fullPoleTrace.restrictFirst (H.activeStage_mono hPoleA) hle
    have hpTrace : poleTrace.isRmControlled (hat := hat) rho :=
      hFullPoleTrace.restrictFirst fullPoleTrace hrho.le le_rfl hPoleA hat
    let y := poleTrace.point first le_rfl hle
    have hpair (j : Fin (H.eventCount + 1)) (hs : H.activeStage aSeed ≤ j)
        (hx : first ≤ j) (hj : j ≤ last) (heq : j = last) :
        riemannianEDistOf (H.stageMetric j ((t : ℝ) - v ^ 2))
          (seedTrace.point j hs hj) (poleTrace.point j hx hj) =
            riemannianEDistOf (H.stageMetric last ((t : ℝ) - v ^ 2)) p x := by
      subst j
      rw [seedTrace.endpoint_eq, poleTrace.endpoint_eq]
    have hvDist : dist v (0 : ℝ) < d := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hv] using hve.trans hed
    have hsmallv := hsmall hvDist
    have hplateau : riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2))) := by
      rw [show riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y =
          riemannianEDistOf (H.stageMetric last ((t : ℝ) - v ^ 2)) p x from
        hpair first (H.activeStage_mono has) le_rfl hle hstage]
      exact (hD v hv (hve.trans_le heeD)).trans_le
        (ENNReal.ofReal_le_ofReal hsmallv.1.le)
    obtain ⟨action, hC1, haction⟩ :=
      poleTrace.exists_regularizedC1ActionValues_le_of_isRmControlled hrho hv.le rfl hpTrace
    have hAC : (action : WithTop ℝ) ∈
        H.regularizedActionValues first last hle t (3 / a₀) 0 v x y :=
      H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle
        (fun j w hw z => hfloor j.val ((t : ℝ) - w ^ 2)
          (H.mapsTo_regularizedStage_Ioo t 0 v j.val hw) z) x y hC1
    have hcostle := H.regularizedCost_le_of_competitor first last hle t (3 / a₀) 0 v x y hAC
    have hhalf : v ^ 2 ≤ r ^ 2 / 2 := by
      have hh := pow_le_pow_left₀ hv.le hvrHalf 2
      nlinarith only [hh, sq_nonneg r]
    have hshift : 0 ≤ A * (1 - 2 * v ^ 2 / r ^ 2) := by
      apply mul_nonneg (by linarith only [hA])
      have hh : 2 * v ^ 2 / r ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hr)).mpr (by linarith)
      linarith only [hh]
    have hroom : 2 * v ^ 3 / r ^ 2 ≤ r / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      have hh := pow_le_pow_left₀ hv.le hvrHalf 3
      nlinarith only [hh]
    have hLsc : LowerSemicontinuous (H.regularizedCost first last hle t (3 / a₀) 0 v x) :=
      H.lowerSemicontinuous_regularizedCost first last hle t (3 / a₀) 0 v
        (by simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t)
        (fun j w hw z => hfloor j.val ((t : ℝ) - w ^ 2)
          (H.mapsTo_regularizedStage_Ioo t 0 v j.val hw) z) x
    have hLower (z : (H.stage first).Carrier) :
        ((-2 * v ^ 3 / r ^ 2 : ℝ) : WithTop ℝ) ≤
          H.regularizedCost first last hle t (3 / a₀) 0 v x z :=
      H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀ hfixed hscalar
        first last hle hr hv.le hhalf hrecent x z
    have hactionSmall : action ≤ r / 4 := haction.trans hsmallv.2.le
    have hplateau' : riemannianEDistOf (H.stageMetric first ((t : ℝ) - v ^ 2)) O y <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 20)) :=
      hplateau.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith only [hr]))
    obtain ⟨q, L, m, hcost, hinner, hLact, hLr, hW, hInf, hmpos, hlo, hhi, hglobal⟩ :=
      H.exists_physicalWeightedCost_minimum_of_plateau_competitor first last hle t (3 / a₀)
        r A v x O y hr hv hshift hroom hLsc hLower action hAC hactionSmall hplateau'
    have hM : M v = (m : WithTop ℝ) := by
      dsimp only [M, tracedPhysicalWeightedMinimum]
      rw [dif_pos hasTime]
      exact hInf
    have hhi' : m / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 := by
      have h12 : 12 * v ^ 3 / rho ^ 2 = 2 * (6 * v ^ 3 / rho ^ 2) := by ring
      linarith only [hhi, haction, h12]
    refine ⟨a, has, hat, rfl, hstage, poleTrace, hpTrace, hplateau,
      action, hC1, hAC, hcostle, haction, q, L, m,
      hcost, hinner, hLact, hLr, hW, hM, hmpos, hlo, hhi', hglobal⟩
  have hbds : ∀ᶠ v in 𝓝[>] (0 : ℝ),
      M v ≠ ⊤ ∧ 2 * r - 4 * v ^ 3 / r ^ 2 ≤ (M v).untopD 0 / v ∧
        (M v).untopD 0 / v ≤ 2 * r + 12 * v ^ 3 / rho ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT he] with v hv
    obtain ⟨a, has, hat, hclock, hstage, trace, htrace, hplateau, action, hC1, hAC,
      hcostle, haction, q, L, m, hcost, hinner, hLact, hLr, hW, hM, hmpos, hlo, hhi, hglobal⟩ :=
      hlocal v hv.1 hv.2
    rw [hM, WithTop.untopD_coe]
    exact ⟨WithTop.coe_ne_top, hlo, hhi⟩
  have hlowLimit : Tendsto (fun v : ℝ => 2 * r - 4 * v ^ 3 / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
    have hc : Continuous (fun v : ℝ => 2 * r - 4 * v ^ 3 / r ^ 2) := by fun_prop
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, sub_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hhighLimit : Tendsto (fun v : ℝ => 2 * r + 12 * v ^ 3 / rho ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
    have hc : Continuous (fun v : ℝ => 2 * r + 12 * v ^ 3 / rho ^ 2) := by fun_prop
    simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨⟨e, he, her, herho, heage, hecube, hlocal⟩,
    hbds.mono (fun _ h => h.1),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowLimit hhighLimit
      (hbds.mono (fun _ h => h.2.1)) (hbds.mono (fun _ h => h.2.2))⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
