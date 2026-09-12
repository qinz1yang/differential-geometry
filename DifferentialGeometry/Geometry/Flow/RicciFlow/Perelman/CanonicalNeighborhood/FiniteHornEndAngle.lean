import DifferentialGeometry.Geometry.Comparison.Toponogov.AngleKernel
import DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {W : Type u} [MetricSpace W]

def endRayFamily (E : UniformSpace.Completion W) :
    EndRay E → ℝ → UniformSpace.Completion W :=
  fun a s => (a.point s : UniformSpace.Completion W)

def endRayLength (E : UniformSpace.Completion W) (d : ℝ) (a : EndRay E) : ℝ :=
  min a.length d

theorem endRayFamily_isRadialFamily (E : UniformSpace.Completion W) (d : ℝ) :
    IsRadialFamily E (endRayLength E d) (endRayFamily E) :=
  fun a s hs => by
    rw [endRayFamily, dist_comm]
    exact a.radial s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩

theorem radialComparisonAngle_endRay {E : UniformSpace.Completion W}
    (a b : EndRay E) (s t : ℝ) :
    radialComparisonAngle (endRayFamily E) a b s t = endComparisonAngle a b s t := by
  simp only [radialComparisonAngle, endRayFamily, endComparisonAngle, comparisonAngle,
    comparisonCosine, UniformSpace.Completion.dist_eq]

theorem endComparisonAngle_eq_zero_of_dist_eq_abs {E : UniformSpace.Completion W}
    (a b : EndRay E) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : dist (a.point s) (b.point t) = |s - t|) : endComparisonAngle a b s t = 0 := by
  have hcos : (s ^ 2 + t ^ 2 - dist (a.point s) (b.point t) ^ 2) / (2 * s * t) = 1 := by
    rw [h, sq_abs]
    field_simp
    ring
  simp only [endComparisonAngle, hcos, Real.arccos_one]

theorem radialComparisonAngle_eq_zero_of_dist_eq_abs {E : UniformSpace.Completion W}
    (a b : EndRay E) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : dist (a.point s) (b.point t) = |s - t|) :
    radialComparisonAngle (endRayFamily E) a b s t = 0 := by
  rw [radialComparisonAngle_endRay]
  exact endComparisonAngle_eq_zero_of_dist_eq_abs a b hs ht h

def endRayAngle (E : UniformSpace.Completion W) (d : ℝ) (a b : EndRay E) : ℝ :=
  limitingRadialAngle (endRayLength E d) (endRayFamily E) a b

variable [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
variable {g : SmoothRiemannianMetric I3 W}

theorem endRayAngle_mem_Icc (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (a b : EndRay H.endpoint) : endRayAngle H.endpoint d a b ∈ Icc 0 Real.pi :=
  limitingRadialAngle_mem_Icc (endRayFamily H.endpoint)
    (by simpa only [endRayLength] using lt_min a.length_pos hd)
    (by simpa only [endRayLength] using lt_min b.length_pos hd)

theorem tendsto_endRayAngle (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a b : EndRay H.endpoint) :
    Tendsto (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (endRayAngle H.endpoint d a b)) := by
  have h := tendsto_limitingRadialAngle (endRayFamily H.endpoint)
    (by simpa only [endRayLength] using lt_min a.length_pos hd)
    (by simpa only [endRayLength] using lt_min b.length_pos hd) (hmono a b)
  simpa only [radialComparisonAngle_endRay, endRayAngle] using h

theorem endRayAngle_self (H : FiniteHorn g) {d : ℝ} (hd : 0 < d) (a : EndRay H.endpoint) :
    endRayAngle H.endpoint d a a = 0 := by
  have hpos : 0 < endRayLength H.endpoint d a := by
    simpa only [endRayLength] using lt_min a.length_pos hd
  have hset : positiveRectangleValues (endRayLength H.endpoint d a) (endRayLength H.endpoint d a)
      (radialComparisonAngle (endRayFamily H.endpoint) a a) = {0} := by
    ext z
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine radialComparisonAngle_eq_zero_of_dist_eq_abs a a hs.1 ht.1 ?_
      exact a.minimizing s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩ t
        ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
    · intro hz
      rw [mem_singleton_iff] at hz
      subst hz
      exact ⟨endRayLength H.endpoint d a, ⟨hpos, le_rfl⟩, endRayLength H.endpoint d a,
        ⟨hpos, le_rfl⟩, (radialComparisonAngle_eq_zero_of_dist_eq_abs a a hpos hpos
          (by simp)).symm⟩
  rw [endRayAngle, limitingRadialAngle, hset, csSup_singleton]

theorem endRayAngle_comm (H : FiniteHorn g) (d : ℝ) (a b : EndRay H.endpoint) :
    endRayAngle H.endpoint d a b = endRayAngle H.endpoint d b a :=
  limitingRadialAngle_comm (endRayLength H.endpoint d) (endRayFamily H.endpoint) a b

theorem endRayAngle_triangle (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a b c : EndRay H.endpoint) :
    endRayAngle H.endpoint d a c ≤ endRayAngle H.endpoint d a b +
      endRayAngle H.endpoint d b c := by
  rcases eq_or_ne a b with hab | hab
  · subst hab
    rw [endRayAngle_self H hd, zero_add]
  rcases eq_or_ne b c with hbc | hbc
  · subst hbc
    rw [endRayAngle_self H hd, add_zero]
  rcases eq_or_ne a c with hac | hac
  · subst hac
    rw [endRayAngle_self H hd]
    exact add_nonneg (endRayAngle_mem_Icc H hd a b).1 (endRayAngle_mem_Icc H hd b a).1
  · exact limitingRadialAngle_triangle H.endpoint (endRayLength H.endpoint d)
      (endRayFamily H.endpoint) (fun a => by
        simpa only [endRayLength] using lt_min a.length_pos hd)
      (endRayFamily_isRadialFamily H.endpoint d) (fun i j _ => hmono i j) hab hbc hac

theorem endRayAngle_limit (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (a b : EndRay H.endpoint) {eta : ℝ} (heta : 0 < eta) :
    ∃ d' : ℝ, 0 < d' ∧ d' ≤ min a.length b.length ∧
      ∀ s ∈ Ioc (0 : ℝ) d', ∀ t ∈ Ioc (0 : ℝ) d',
        |endComparisonAngle a b s t - endRayAngle H.endpoint d a b| < eta := by
  have h := tendsto_endRayAngle H hd hmono a b
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
      |endComparisonAngle a b p.1 p.2 - endRayAngle H.endpoint d a b| < eta := by
    refine (h.eventually (Metric.ball_mem_nhds (endRayAngle H.endpoint d a b) heta)).mono ?_
    intro y hy
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
  obtain ⟨pa, hpa, pb, hpb, hmain⟩ := Filter.eventually_prod_iff.mp hev
  obtain ⟨u, hu, hU'⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hpa
  obtain ⟨v, hv, hV'⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hpb
  refine ⟨min (min u v) (min a.length b.length), ?_,
    min_le_right _ _, ?_⟩
  · exact lt_min (lt_min hu hv) (lt_min a.length_pos b.length_pos)
  · intro s hs t ht
    exact hmain (hU' ⟨hs.1, hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩)
      (hV' ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩)

theorem endRayAngle_eq_zero_of_eventuallyEqual (H : FiniteHorn g) {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    {a b : EndRay H.endpoint} (heq : a.EventuallyEqual b) :
    endRayAngle H.endpoint d a b = 0 := by
  have h := tendsto_endRayAngle H hd hmono a b
  have hzero : (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2) =ᶠ[
      𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    obtain ⟨e, he, hemin, hee⟩ := heq
    have hU : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ∈ Ioc (0 : ℝ) e := Ioc_mem_nhdsGT he
    filter_upwards [hU.prod_mk hU] with p hp
    refine endComparisonAngle_eq_zero_of_dist_eq_abs a b hp.1.1 hp.2.1 ?_
    rw [hee p.1 ⟨hp.1.1, hp.1.2⟩,
      b.minimizing p.1 ⟨hp.1.1, (hp.1.2.trans hemin).trans (min_le_right _ _)⟩ p.2
        ⟨hp.2.1, (hp.2.2.trans hemin).trans (min_le_right _ _)⟩]
  have h0 : Tendsto (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Filter.Tendsto.congr' hzero.symm tendsto_const_nhds
  exact tendsto_nhds_unique h h0

theorem finite_horn_end_angle_of_monotone (H : FiniteHorn g) (d : ℝ) (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b)) :
    Nonempty (EndAngles H) := by
  have hself : ∀ a : EndRay H.endpoint, endRayAngle H.endpoint d a a = 0 :=
    endRayAngle_self H hd
  have hsymm : ∀ a b : EndRay H.endpoint, endRayAngle H.endpoint d a b =
      endRayAngle H.endpoint d b a := endRayAngle_comm H d
  have htri : ∀ a b c : EndRay H.endpoint, endRayAngle H.endpoint d a c ≤
      endRayAngle H.endpoint d a b + endRayAngle H.endpoint d b c :=
    endRayAngle_triangle H hd hmono
  let K : AngleKernel (EndRay H.endpoint) :=
    { angle := endRayAngle H.endpoint d
      nonneg := fun a b => (endRayAngle_mem_Icc H hd a b).1
      self := hself
      symm := hsymm
      triangle := htri }
  have hmonoField : ∀ a b : EndRay H.endpoint, ∃ d' : ℝ, 0 < d' ∧
      d' ≤ min a.length b.length ∧ ∀ s s' t t', 0 < s → s ≤ s' → s' ≤ d' →
        0 < t → t ≤ t' → t' ≤ d' → endComparisonAngle a b s' t' ≤ endComparisonAngle a b s t := by
    intro a b
    refine ⟨min (endRayLength H.endpoint d a) (endRayLength H.endpoint d b),
      lt_min (by simpa only [endRayLength] using lt_min a.length_pos hd)
        (by simpa only [endRayLength] using lt_min b.length_pos hd),
      le_min ((min_le_left _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
    intro s s' t t' hs hss' hs'd ht htt' ht'd
    have hsI : s ∈ Ioc (0 : ℝ) (endRayLength H.endpoint d a) :=
      ⟨hs, hss'.trans (hs'd.trans (min_le_left _ _))⟩
    have hs'I : s' ∈ Ioc (0 : ℝ) (endRayLength H.endpoint d a) :=
      ⟨lt_of_lt_of_le hs hss', hs'd.trans (min_le_left _ _)⟩
    have htI : t ∈ Ioc (0 : ℝ) (endRayLength H.endpoint d b) :=
      ⟨ht, htt'.trans (ht'd.trans (min_le_right _ _))⟩
    have ht'I : t' ∈ Ioc (0 : ℝ) (endRayLength H.endpoint d b) :=
      ⟨lt_of_lt_of_le ht htt', ht'd.trans (min_le_right _ _)⟩
    have h₁ := (hmono a b).1 hsI hs'I htI hss'
    have h₂ := (hmono a b).2 hs'I htI ht'I htt'
    simpa only [radialComparisonAngle_endRay] using h₂.trans h₁
  have hevField : ∀ a b : EndRay H.endpoint, a.EventuallyEqual b →
      K.classOf a = K.classOf b := by
    intro a b hab
    exact Quotient.sound (endRayAngle_eq_zero_of_eventuallyEqual H hd hmono hab)
  let F : EndAngles H :=
    { angle := K.angle
      range := fun a b => endRayAngle_mem_Icc H hd a b
      limit := fun a b eta heta => endRayAngle_limit H hd hmono a b heta
      monotone := hmonoField
      self := hself
      symm := hsymm
      triangle := htri
      quotient := Quotient K.setoid
      metric := K.metricSpace
      classOf := K.classOf
      onto := K.classOf_surjective
      distance := fun a b => K.dist_mk a b
      eventual_eq := hevField }
  exact ⟨F⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
