import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarOpen
import DifferentialGeometry.Geometry.Hyperbolic.Truncation

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint GC.GraphManifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- The half-line point `max s 0`. -/
def hpt_LTP1 (s : ℝ) : EuclideanHalfSpace 1 := halfPoint (max s 0) (le_max_right _ _)

theorem hpt_val_LTP1 (s : ℝ) : (hpt_LTP1 s).val 0 = max s 0 := rfl

theorem hpt_of_nonneg_LTP1 {s : ℝ} (hs : 0 ≤ s) : hpt_LTP1 s = halfPoint s hs := by
  apply Subtype.ext
  change WithLp.toLp 2 (fun _ => max s 0) = WithLp.toLp 2 (fun _ => s)
  rw [max_eq_left hs]

theorem hpt_zero_LTP1 : hpt_LTP1 0 = halfZero := hpt_of_nonneg_LTP1 le_rfl

theorem continuous_hpt_LTP1 : Continuous hpt_LTP1 := by
  refine Continuous.subtype_mk ?_ _
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id.max continuous_const)

theorem halfPoint_injective_LTP1 {s s' : ℝ} {hs : 0 ≤ s} {hs' : 0 ≤ s'}
    (h : halfPoint s hs = halfPoint s' hs') : s = s' := by
  have := congrArg (fun p : EuclideanHalfSpace 1 => p.val 0) h
  exact this

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) (q : Fin T.count)

/-- Inner (core-side) half of the bicollar, for `-1 < s`. -/
def bcInner_LTP1 (p : Torus × ℝ) : H.Carrier :=
  T.inclusion (T.boundary.collar q (p.1, hpt_LTP1 (-p.2)))

/-- Outer (cusp-side) half of the bicollar. -/
def bcOuter_LTP1 (p : Torus × ℝ) : H.Carrier :=
  T.cuspMap q (p.1, hpt_LTP1 p.2)

/-- The glued two-sided collar map (before restriction to `-1 < s < 1`). -/
def bcFun_LTP1 (p : Torus × ℝ) : H.Carrier :=
  if p.2 ≤ 0 then bcInner_LTP1 T q p else bcOuter_LTP1 T q p

def bcSource_LTP1 : Set (Torus × ℝ) := {p | -1 < p.2 ∧ p.2 < 1}

theorem isOpen_bcSource_LTP1 : IsOpen bcSource_LTP1 :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

theorem collar_mem_source_LTP1 {p : Torus × ℝ} (hp : -1 < p.2) :
    (p.1, hpt_LTP1 (-p.2)) ∈ (T.boundary.collar q).source := by
  rw [T.boundary.source_eq]
  change (hpt_LTP1 (-p.2)).val 0 < 1
  rw [hpt_val_LTP1]
  exact max_lt (by linarith) one_pos

theorem continuousOn_bcInner_LTP1 : ContinuousOn (bcInner_LTP1 T q) {p | -1 < p.2} := by
  have h1 : ContinuousOn (fun p : Torus × ℝ => (p.1, hpt_LTP1 (-p.2))) {p | -1 < p.2} := by
    apply Continuous.continuousOn
    exact continuous_fst.prodMk (continuous_hpt_LTP1.comp continuous_snd.neg)
  exact T.inclusion.continuous.comp_continuousOn
    ((T.boundary.collar q).toOpenPartialHomeomorph.continuousOn.comp h1 (fun p hp => collar_mem_source_LTP1 T q hp))

theorem continuous_bcOuter_LTP1 : Continuous (bcOuter_LTP1 T q) :=
  (T.cuspEmbedding q).isEmbedding.continuous.comp
    (continuous_fst.prodMk (continuous_hpt_LTP1.comp continuous_snd))

theorem bcInner_zero_LTP1 (t : Torus) :
    bcInner_LTP1 T q (t, 0) = T.inclusion (T.boundary.torusMap q t) := by
  simp only [bcInner_LTP1, neg_zero, hpt_zero_LTP1]
  rfl

theorem bcOuter_zero_LTP1 (t : Torus) :
    bcOuter_LTP1 T q (t, 0) = T.inclusion (T.boundary.torusMap q t) := by
  simp only [bcOuter_LTP1, hpt_zero_LTP1]
  exact T.cusp_zero q t

theorem bcFun_of_nonpos_LTP1 {p : Torus × ℝ} (h : p.2 ≤ 0) : bcFun_LTP1 T q p = bcInner_LTP1 T q p :=
  by simp [bcFun_LTP1, h]

theorem bcFun_of_pos_LTP1 {p : Torus × ℝ} (h : 0 < p.2) : bcFun_LTP1 T q p = bcOuter_LTP1 T q p :=
  by simp [bcFun_LTP1, not_le.2 h]

theorem bcFun_of_nonneg_LTP1 {p : Torus × ℝ} (h : 0 ≤ p.2) : bcFun_LTP1 T q p = bcOuter_LTP1 T q p := by
  rcases h.lt_or_eq with h | h
  · exact bcFun_of_pos_LTP1 T q h
  · rw [bcFun_of_nonpos_LTP1 T q h.symm.le]
    rcases p with ⟨t, s⟩
    have h' : s = 0 := h.symm
    subst h'
    rw [bcInner_zero_LTP1, bcOuter_zero_LTP1]

theorem continuousOn_bcFun_LTP1 : ContinuousOn (bcFun_LTP1 T q) bcSource_LTP1 := by
  intro p hp
  have hin : ContinuousAt (bcInner_LTP1 T q) p :=
    (continuousOn_bcInner_LTP1 T q).continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp.1)
  have hout : ContinuousAt (bcOuter_LTP1 T q) p := (continuous_bcOuter_LTP1 T q).continuousAt
  apply ContinuousAt.continuousWithinAt
  rcases lt_trichotomy p.2 0 with h | h | h
  · refine hin.congr ?_
    have : {x : Torus × ℝ | x.2 < 0} ∈ 𝓝 p := (isOpen_lt continuous_snd continuous_const).mem_nhds h
    filter_upwards [this] with x hx using (bcFun_of_nonpos_LTP1 T q (le_of_lt hx)).symm
  · have h1 : ContinuousWithinAt (bcFun_LTP1 T q) {x : Torus × ℝ | x.2 ≤ 0} p :=
      hin.continuousWithinAt.congr (fun x hx => bcFun_of_nonpos_LTP1 T q hx)
        (bcFun_of_nonpos_LTP1 T q h.le)
    have h2 : ContinuousWithinAt (bcFun_LTP1 T q) {x : Torus × ℝ | 0 ≤ x.2} p :=
      hout.continuousWithinAt.congr (fun x hx => bcFun_of_nonneg_LTP1 T q hx)
        (bcFun_of_nonneg_LTP1 T q h.ge)
    have := h1.union h2
    rw [show {x : Torus × ℝ | x.2 ≤ 0} ∪ {x : Torus × ℝ | 0 ≤ x.2} = univ from by
      ext x; simp [le_total], continuousWithinAt_univ] at this
    exact this
  · refine hout.congr ?_
    have : {x : Torus × ℝ | 0 < x.2} ∈ 𝓝 p := (isOpen_lt continuous_const continuous_snd).mem_nhds h
    filter_upwards [this] with x hx using (bcFun_of_pos_LTP1 T q hx).symm

end GC.LongTime.CuspP1
