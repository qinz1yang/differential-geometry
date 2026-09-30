import DifferentialGeometry.Topology.Order.SemicontinuousInsertion.Insertion
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Group.Continuity

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology Filter

theorem lowerHemicontinuous_Icc {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : UpperSemicontinuous f) (hg : LowerSemicontinuous g) (hfg : ∀ x, f x ≤ g x) :
    LowerHemicontinuous (fun x => Icc (f x) (g x)) := by
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨y, hyfg, hyU⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y hyU
  have hfn := (hf.isOpen_preimage (y + ε)).mem_nhds (show f x < y + ε by linarith [hyfg.1])
  have hgn := (hg.isOpen_preimage (y - ε)).mem_nhds (show y - ε < g x by linarith [hyfg.2])
  filter_upwards [hfn, hgn] with z hfz hgz
  let w := max (f z) (min y (g z))
  refine ⟨w, ⟨le_max_left _ _, max_le (hfg z) (min_le_right _ _)⟩, hεU ?_⟩
  rw [mem_ball, Real.dist_eq, abs_lt]
  have hlo : y - ε < w := (lt_min (by linarith) hgz).trans_le (le_max_right _ _)
  have hhi : w < y + ε := max_lt hfz ((min_le_left _ _).trans_lt (by linarith))
  constructor <;> linarith

theorem exists_continuous_between {X : Type*} [TopologicalSpace X]
    [NormalSpace X] [ParacompactSpace X] {f g : X → ℝ}
    (hf : UpperSemicontinuous f) (hg : LowerSemicontinuous g) (hfg : ∀ x, f x ≤ g x) :
    ∃ h : X → ℝ, Continuous h ∧ ∀ x, f x ≤ h x ∧ h x ≤ g x :=
  (lowerHemicontinuous_Icc hf hg hfg).exists_continuous_selection
    (fun x => nonempty_Icc.mpr (hfg x)) (fun x => convex_Icc (f x) (g x))
    (fun _ => isClosed_Icc)

theorem exists_continuous_minorant_pos {X : Type*} [MetricSpace X] {q : X → ℝ}
    (hq : LowerSemicontinuous q) (hq₀ : ∀ x, 0 ≤ q x) :
    ∃ δ : X → ℝ, Continuous δ ∧ (∀ x, 0 ≤ δ x ∧ δ x ≤ q x) ∧
      ∀ x, 0 < q x → 0 < δ x := by
  classical
  let D : Set X := {x | 0 < q x}
  have hD : IsOpen D := hq.isOpen_preimage 0
  by_cases hDu : D = univ
  · have hqp (x : X) : 0 < q x := by
      change x ∈ D
      rw [hDu]
      trivial
    obtain ⟨δ, hδ, hδq⟩ := exists_continuous_between_strict
      continuous_const.upperSemicontinuous hq hqp
    exact ⟨δ, hδ, fun x => ⟨(hδq x).1.le, (hδq x).2.le⟩, fun x _ => (hδq x).1⟩
  have hDc : Dᶜ.Nonempty := nonempty_compl.mpr hDu
  obtain ⟨u, hu, huq⟩ := exists_continuous_between_strict
    (f := fun _ : D => (0 : ℝ)) continuous_const.upperSemicontinuous
    (hq.comp continuous_subtype_val) (fun x => x.2)
  let δ : X → ℝ := fun x => if hx : x ∈ D then min (u ⟨x, hx⟩) (infDist x Dᶜ) else 0
  have hδ₀ (x : X) : 0 ≤ δ x := by
    dsimp [δ]
    split_ifs with hx
    · exact le_min (huq ⟨x, hx⟩).1.le infDist_nonneg
    · rfl
  have hδdist (x : X) : δ x ≤ infDist x Dᶜ := by
    dsimp [δ]
    split_ifs
    · exact min_le_right _ _
    · exact infDist_nonneg
  have hδD : ContinuousOn δ D := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hu.min ((continuous_infDist_pt Dᶜ).comp continuous_subtype_val) using 1
    funext x
    exact dite_eq_left x.2
  have hδ : Continuous δ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ D
    · exact (hδD x hx).continuousAt (hD.mem_nhds hx)
    · change Tendsto δ (𝓝 x) (𝓝 (δ x))
      rw [show δ x = 0 from dite_eq_right hx]
      exact squeeze_zero hδ₀ hδdist (by
        simpa only [infDist_zero_of_mem (show x ∈ Dᶜ from hx)] using
          (continuous_infDist_pt Dᶜ).tendsto x)
  refine ⟨δ, hδ, fun x => ⟨hδ₀ x, ?_⟩, ?_⟩
  · dsimp [δ]
    split_ifs with hx
    · exact (min_le_left _ _).trans (huq ⟨x, hx⟩).2.le
    · exact hq₀ x
  · intro x hx
    have hxD : x ∈ D := hx
    rw [show δ x = min (u ⟨x, hxD⟩) (infDist x Dᶜ) from dite_eq_left hxD]
    exact lt_min (huq ⟨x, hxD⟩).1
      ((hD.isClosed_compl.notMem_iff_infDist_pos hDc).mp (not_not.mpr hxD))

theorem exists_continuous_between_strict_where_lt {X : Type*} [MetricSpace X] {f g : X → ℝ}
    (hf : UpperSemicontinuous f) (hg : LowerSemicontinuous g) (hfg : ∀ x, f x ≤ g x) :
    ∃ h : X → ℝ, Continuous h ∧ (∀ x, f x ≤ h x ∧ h x ≤ g x) ∧
      ∀ x, f x < g x → f x < h x ∧ h x < g x := by
  have hgap : LowerSemicontinuous (fun x => g x - f x) := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using hg.add hf.neg
  obtain ⟨δ, hδ, hδbound, hδpos⟩ :=
    exists_continuous_minorant_pos hgap (fun x => sub_nonneg.mpr (hfg x))
  have hε : Continuous (fun x => δ x / 3) := hδ.div_const 3
  have hleft : UpperSemicontinuous (fun x => f x + δ x / 3) :=
    hf.add hε.upperSemicontinuous
  have hright : LowerSemicontinuous (fun x => g x - δ x / 3) := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using hg.add hε.neg.lowerSemicontinuous
  obtain ⟨h, hh, hbetween⟩ := exists_continuous_between hleft hright (fun x => by
    have hb := hδbound x
    linarith)
  refine ⟨h, hh, ?_, ?_⟩
  · intro x
    have hb := hbetween x
    have hnonneg := (hδbound x).1
    constructor <;> linarith
  · intro x hx
    have hb := hbetween x
    have hpos := hδpos x (sub_pos.mpr hx)
    constructor <;> linarith

end DifferentialGeometry.Topology.Engulfing
