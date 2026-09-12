import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornIntrinsicRays
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornAnnulusCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndRayLocality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayUniqueness
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngleMonotone

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Toponogov

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] EndAngles.metric

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

def conePoint {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} (angles : EndAngles H)
    (r : ℝ) (γ : EndRay H.endpoint) : ℝ × UniformSpace.Completion angles.quotient :=
  (r, angles.classOf γ)

def hornAnnulusRelation {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (angles : EndAngles H) (d : ℕ → ℝ) (a b : ℝ) (i : ℕ) :
    Set ((ℝ × UniformSpace.Completion angles.quotient) × W) :=
  {p | ∃ (r : ℝ) (γ : EndRay H.endpoint), r ∈ Set.Icc a b ∧
      r * d i ∈ Set.Ioc 0 γ.length ∧ p.1 = conePoint angles r γ ∧
      p.2 = γ.point (r * d i)}

structure ConeAnnulusRealization {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop where
  angles_le : ∃ D : ℝ, 0 < D ∧ ∀ (γ γ' : EndRay H.endpoint) (s t : ℝ),
    s ∈ Set.Ioc 0 (min γ.length D) → t ∈ Set.Ioc 0 (min γ'.length D) →
      endComparisonAngle γ γ' s t ≤ angles.angle γ γ'
  lower : ∀ a b : ℝ, 0 < a → a < b → ∃ err : ℕ → ℝ, (∀ i, 0 < err i) ∧
    Filter.Tendsto err Filter.atTop (nhds 0) ∧ ∀ᶠ i in Filter.atTop,
      ∀ (γ γ' : EndRay H.endpoint) (r r' : ℝ), r ∈ Set.Icc a b → r' ∈ Set.Icc a b →
        r * d i ∈ Set.Ioc 0 γ.length → r' * d i ∈ Set.Ioc 0 γ'.length →
        openConeDistance (conePoint angles r γ) (conePoint angles r' γ') ≤
          dist (γ.point (r * d i)) (γ'.point (r' * d i)) / d i + err i
  dense : ∀ a b : ℝ, 0 < a → a < b → ∃ err : ℕ → ℝ, (∀ i, 0 < err i) ∧
    Filter.Tendsto err Filter.atTop (nhds 0) ∧ ∀ᶠ i in Filter.atTop,
      ∀ r ∈ Set.Icc a b, ∀ q : UniformSpace.Completion angles.quotient,
        ∃ γ : EndRay H.endpoint, r * d i ∈ Set.Ioc 0 γ.length ∧
          openConeDistance (r, q) (conePoint angles r γ) < err i

omit [SigmaCompactSpace W] in
theorem dist_div_le_openConeDistance {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g}
    (angles : EndAngles H) {γ γ' : EndRay H.endpoint} {s t q : ℝ}
    (hs : s ∈ Set.Ioc 0 γ.length) (ht : t ∈ Set.Ioc 0 γ'.length) (hq : 0 < q)
    (hcmp : endComparisonAngle γ γ' s t ≤ angles.angle γ γ') :
    dist (γ.point s) (γ'.point t) / q ≤
      openConeDistance (conePoint angles (s / q) γ) (conePoint angles (t / q) γ') := by
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := ht.1
  obtain ⟨hθ0, hθπ⟩ := angles.range γ γ'
  have hside₁ : |s - t| ≤ dist (γ.point s) (γ'.point t) := by
    have h := abs_dist_sub_le (γ.point s : UniformSpace.Completion W)
      (γ'.point t : UniformSpace.Completion W) H.endpoint
    rw [γ.radial s hs, γ'.radial t ht, UniformSpace.Completion.dist_eq] at h
    exact h
  have hside₂ : dist (γ.point s) (γ'.point t) ≤ s + t := by
    have h := dist_triangle (γ.point s : UniformSpace.Completion W) H.endpoint
      (γ'.point t : UniformSpace.Completion W)
    rw [γ.radial s hs, UniformSpace.Completion.dist_eq] at h
    have h₂ : dist H.endpoint (γ'.point t : UniformSpace.Completion W) = t := by
      rw [dist_comm, γ'.radial t ht]
    rw [h₂] at h
    exact h
  have hmain : dist (γ.point s) (γ'.point t) ^ 2 ≤
      s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (angles.angle γ γ') :=
    DifferentialGeometry.Toponogov.sq_le_cos_of_comparisonAngle_le hs0 ht0 hside₁ hside₂ hθπ hcmp
  have hnonneg : 0 ≤ s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (angles.angle γ γ') :=
    le_trans (sq_nonneg _) hmain
  have hsqrt : dist (γ.point s) (γ'.point t) ≤
      Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (angles.angle γ γ')) := by
    have h := Real.sqrt_le_sqrt hmain
    rwa [Real.sqrt_sq (dist_nonneg)] at h
  have hcone : openConeDistance (conePoint angles (s / q) γ) (conePoint angles (t / q) γ') =
      Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (angles.angle γ γ')) / q := by
    have hdist : dist (angles.classOf γ : UniformSpace.Completion angles.quotient)
        (angles.classOf γ' : UniformSpace.Completion angles.quotient) = angles.angle γ γ' := by
      rw [UniformSpace.Completion.dist_eq, angles.distance]
    have harg : (s / q) ^ 2 + (t / q) ^ 2 - 2 * (s / q) * (t / q) *
        Real.cos (angles.angle γ γ') =
        (s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (angles.angle γ γ')) / q ^ 2 := by
      field_simp
    have hmin : min Real.pi (dist (angles.classOf γ : UniformSpace.Completion angles.quotient)
        (angles.classOf γ' : UniformSpace.Completion angles.quotient)) = angles.angle γ γ' := by
      rw [hdist, min_eq_right hθπ]
    rw [show conePoint angles (s / q) γ =
        ((s / q : ℝ), (angles.classOf γ : UniformSpace.Completion angles.quotient)) from rfl,
      show conePoint angles (t / q) γ' =
        ((t / q : ℝ), (angles.classOf γ' : UniformSpace.Completion angles.quotient)) from rfl]
    rw [openConeDistance, hmin, harg]
    rw [Real.sqrt_div' (x := s ^ 2 + t ^ 2 - 2 * s * t * Real.cos (angles.angle γ γ'))
      (y := q ^ 2) (by positivity)]
    rw [Real.sqrt_sq hq.le]
  rw [hcone]
  exact (div_le_div_iff_of_pos_right hq).mpr hsqrt

theorem finiteHorn_eventually_exists_endRay_through (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (d : ℕ → ℝ) (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    {b : ℝ} :
    ∀ᶠ i in Filter.atTop, ∀ w : W,
      dist (w : UniformSpace.Completion W) H.endpoint ≤ b * d i →
      ∃ γ : EndRay H.endpoint,
        γ.point (dist (w : UniformSpace.Completion W) H.endpoint) = w ∧
        γ.length = dist (w : UniformSpace.Completion W) H.endpoint := by
  obtain ⟨j, hrays⟩ := finiteHorn_intrinsic_rays g H
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H j
  have hbd : ∀ᶠ i in Filter.atTop, b * d i < delta := by
    have h0 : Filter.Tendsto (fun i => b * d i) Filter.atTop (nhds 0) := by
      simpa using hzero.const_mul b
    exact h0.eventually (eventually_lt_nhds hdelta)
  filter_upwards [hbd] with i hi w hw
  have hx : w ∈ H.subend j := hball w (lt_of_le_of_lt hw hi)
  obtain ⟨a, ha⟩ := hrays w hx
  have hlen : a.length = dist (w : UniformSpace.Completion W) H.endpoint := by
    rw [← ha]
    exact (a.radial a.length ⟨a.length_pos, le_rfl⟩).symm
  exact ⟨a, by rw [← hlen]; exact ha, hlen⟩

omit [SigmaCompactSpace W] in
theorem finiteHorn_isCompact_scaled_radial_annulus (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length) (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    {a b : ℝ} (ha : 0 < a) :
    ∀ᶠ i in Filter.atTop, IsCompact {w : W |
      a ≤ dist (w : UniformSpace.Completion W) H.endpoint / d i ∧
      dist (w : UniformSpace.Completion W) H.endpoint / d i ≤ b} := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H 0
  let r : ℝ := delta / 2
  have hr : 0 < r := half_pos hdelta
  have hsub : Metric.closedBall H.endpoint r ⊆
      closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend 0) := by
    intro z hz
    change dist z H.endpoint ≤ delta / 2 at hz
    refine Metric.mem_closure_iff.mpr ?_
    intro eta heta
    obtain ⟨x, hx⟩ := (UniformSpace.Completion.denseRange_coe (α := W)).exists_dist_lt z
      (lt_min heta (half_pos hdelta))
    have hxd : dist (x : UniformSpace.Completion W) z < delta / 2 := by
      rw [dist_comm]
      exact hx.trans_le (min_le_right _ _)
    have hxend : dist (x : UniformSpace.Completion W) H.endpoint < delta := by
      have htri := dist_triangle (x : UniformSpace.Completion W) z H.endpoint
      linarith
    exact ⟨(x : UniformSpace.Completion W), ⟨x, hball x hxend, rfl⟩,
      hx.trans_le (min_le_left _ _)⟩
  have hcompactBall : IsCompact (Metric.closedBall H.endpoint r) :=
    (finiteHorn_isCompact_closure_subend g H 0).of_isClosed_subset Metric.isClosed_closedBall hsub
  have hev : ∀ᶠ i in Filter.atTop, b * d i ≤ r := by
    have h0 : Filter.Tendsto (fun i => b * d i) Filter.atTop (nhds 0) := by
      simpa using hzero.const_mul b
    exact (h0.eventually (eventually_lt_nhds hr)).mono (fun i hi => hi.le)
  refine hev.mono (fun i hi => ?_)
  have hc : 0 < d i := (hd i).1
  let S : Set (UniformSpace.Completion W) :=
    {z | a * d i ≤ dist z H.endpoint ∧ dist z H.endpoint ≤ b * d i}
  have hcont : Continuous (fun z : UniformSpace.Completion W => dist z H.endpoint) :=
    continuous_id.dist continuous_const
  have hSclosed : IsClosed S :=
    (isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const)
  have hSsub : S ⊆ Metric.closedBall H.endpoint r := by
    intro z hz
    change dist z H.endpoint ≤ r
    exact hz.2.trans hi
  have hScompact : IsCompact S := hcompactBall.of_isClosed_subset hSclosed hSsub
  have hSrange : S ⊆ range (fun x : W => (x : UniformSpace.Completion W)) := by
    intro z hz
    have hpos : 0 < dist z H.endpoint := lt_of_lt_of_le (mul_pos ha hc) hz.1
    refine finiteHorn_mem_range_of_mem_closure_subend g H 0 (hsub (hSsub hz)) ?_
    intro heq
    rw [heq, dist_self] at hpos
    exact lt_irrefl 0 hpos
  have hpre : IsCompact ((fun x : W => (x : UniformSpace.Completion W)) ⁻¹' S) :=
    ((UniformSpace.Completion.isUniformInducing_coe W).isInducing.isCompact_preimage_iff
      hSrange).mpr hScompact
  have hset : {w : W | a ≤ dist (w : UniformSpace.Completion W) H.endpoint / d i ∧
      dist (w : UniformSpace.Completion W) H.endpoint / d i ≤ b} =
      (fun x : W => (x : UniformSpace.Completion W)) ⁻¹' S := by
    ext w
    change (a ≤ dist (w : UniformSpace.Completion W) H.endpoint / d i ∧
        dist (w : UniformSpace.Completion W) H.endpoint / d i ≤ b) ↔
      (a * d i ≤ dist (w : UniformSpace.Completion W) H.endpoint ∧
        dist (w : UniformSpace.Completion W) H.endpoint ≤ b * d i)
    exact ⟨fun h => ⟨(le_div_iff₀ hc).mp h.1, (div_le_iff₀ hc).mp h.2⟩,
      fun h => ⟨(le_div_iff₀ hc).mpr h.1, (div_le_iff₀ hc).mpr h.2⟩⟩
  rw [hset]
  exact hpre

theorem EndAngles.classOf_eq_of_common_point {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g}
    (angles : EndAngles H) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint, ∀ t : ℝ, 0 < t → t < min a.length d →
      t ≤ b.length → a.point t = b.point t → angles.classOf a = angles.classOf b := by
  obtain ⟨d, hd, hunique⟩ := finiteHorn_endRay_unique_inward g H
  refine ⟨d, hd, ?_⟩
  intro a b t ht htd htb hcontact
  refine (EndAngles.classOf_eq_iff_eventuallyEqual angles a b).mpr ⟨t, ht, ?_, ?_⟩
  · exact le_min ((le_of_lt htd).trans (min_le_left _ _)) htb
  · intro s hs
    exact hunique a b t ht htd htb hcontact s hs

theorem nonempty_annularConvergence_of_coneAnnulusRealization
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hreal : ConeAnnulusRealization H angles ray d) :
    Nonempty (AnnularConvergence H angles ray d) := by
  classical
  have hpos : ∀ i, 0 < d i := fun i => (hd i).1
  obtain ⟨Dang, hDang, hangle⟩ := hreal.angles_le
  choose el helpos heltend helev using fun a b (ha : 0 < a) (hab : a < b) =>
    hreal.lower a b ha hab
  choose ed hedpos hedtend hedev using fun a b (ha : 0 < a) (hab : a < b) =>
    hreal.dense a b ha hab
  let err : ℝ → ℝ → ℕ → ℝ := fun a b i =>
    if h : 0 < a ∧ a < b then
      el a b h.1 h.2 i + ed a b h.1 h.2 i + 1 / ((i : ℝ) + 1)
    else 1
  have err_eq : ∀ a b (ha : 0 < a) (hab : a < b) i,
      err a b i = el a b ha hab i + ed a b ha hab i + 1 / ((i : ℝ) + 1) := by
    intro a b ha hab i
    simp only [err]
    rw [dif_pos ⟨ha, hab⟩]
  have herrpos : ∀ a b i, 0 < err a b i := by
    intro a b i
    by_cases h : 0 < a ∧ a < b
    · rw [err_eq a b h.1 h.2 i]
      have h2 := helpos a b h.1 h.2 i
      have h3 := hedpos a b h.1 h.2 i
      have h4 : 0 < 1 / ((i : ℝ) + 1) := by positivity
      linarith
    · have herr : err a b i = 1 := by
        simp only [err]
        rw [dif_neg h]
      rw [herr]
      norm_num
  have herrtend : ∀ a b, 0 < a → a < b → Filter.Tendsto (err a b) Filter.atTop (nhds 0) := by
    intro a b ha hab
    have hslack : Filter.Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hsum : Filter.Tendsto (fun i : ℕ =>
        el a b ha hab i + ed a b ha hab i + 1 / ((i : ℝ) + 1))
        Filter.atTop (nhds 0) := by
      have h := (heltend a b ha hab).add ((hedtend a b ha hab).add hslack)
      simpa [add_assoc] using h
    refine hsum.congr' ?_
    filter_upwards with i
    rw [err_eq a b ha hab i]
  have herr_gt_el : ∀ a b (ha : 0 < a) (hab : a < b) i, el a b ha hab i < err a b i := by
    intro a b ha hab i
    rw [err_eq a b ha hab i]
    have h1 := hedpos a b ha hab i
    have h2 : 0 < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  have herr_gt_ed : ∀ a b (ha : 0 < a) (hab : a < b) i, ed a b ha hab i < err a b i := by
    intro a b ha hab i
    rw [err_eq a b ha hab i]
    have h1 := helpos a b ha hab i
    have h2 : 0 < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  have herr_ge_ed : ∀ a b (ha : 0 < a) (hab : a < b) i, ed a b ha hab i ≤ err a b i :=
    fun a b ha hab i => (herr_gt_ed a b ha hab i).le
  refine ⟨⟨hornAnnulusRelation H angles d, err, herrpos, herrtend, ?_⟩⟩
  intro a b ha hab
  have hcomp := finiteHorn_isCompact_scaled_radial_annulus g H ray d hd hzero (b := b) ha
  have hray := finiteHorn_eventually_exists_endRay_through g H d hzero (b := b)
  have hevD : ∀ᶠ i in Filter.atTop, b * d i ≤ Dang := by
    have h0 : Filter.Tendsto (fun i => b * d i) Filter.atTop (nhds 0) := by
      simpa using hzero.const_mul b
    exact (h0.eventually (eventually_lt_nhds hDang)).mono (fun i hi => hi.le)
  filter_upwards [helev a b ha hab, hedev a b ha hab, hcomp, hray, hevD] with
    i hl hdense hci hrayi hiD
  refine ⟨hci, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨r₀, q₀⟩ w ⟨r, γ, hr, hrlen, hp1, hp2⟩
    have hx : (r₀, q₀) = conePoint angles r γ := hp1
    have hw : w = γ.point (r * d i) := hp2
    have hxr : (r₀, q₀).1 = r := by rw [hx]; rfl
    constructor
    · rw [hxr]
      exact hr
    · have hdist : dist (w : UniformSpace.Completion W) H.endpoint = r * d i := by
        rw [hw]
        exact γ.radial (r * d i) hrlen
      rw [hdist, mul_div_cancel_right₀ r (ne_of_gt (hpos i))]
      exact hr
  · rintro x hx
    obtain ⟨r, q⟩ := x
    obtain ⟨γ, hlen, hclose⟩ := hdense r hx q
    exact ⟨conePoint angles r γ, γ.point (r * d i), ⟨r, γ, hx, hlen, rfl, rfl⟩,
      hclose.trans_le (herr_ge_ed a b ha hab i)⟩
  · intro w hw
    have hw' : dist (w : UniformSpace.Completion W) H.endpoint ≤ b * d i :=
      (div_le_iff₀ (hpos i)).mp hw.2
    obtain ⟨γ, hγpt, hγlen⟩ := hrayi w hw'
    have hdiv : dist (w : UniformSpace.Completion W) H.endpoint / d i * d i =
        dist (w : UniformSpace.Completion W) H.endpoint :=
      div_mul_cancel₀ _ (ne_of_gt (hpos i))
    have hrlen : dist (w : UniformSpace.Completion W) H.endpoint / d i * d i ∈
        Set.Ioc 0 γ.length := by
      refine ⟨?_, ?_⟩
      · rw [hdiv]
        exact dist_pos.mpr (H.endpoint_missing w)
      · rw [hdiv, hγlen]
    have hpt : γ.point (dist (w : UniformSpace.Completion W) H.endpoint / d i * d i) = w := by
      rw [hdiv]
      exact hγpt
    refine ⟨conePoint angles (dist (w : UniformSpace.Completion W) H.endpoint / d i) γ, w,
      ⟨_, γ, hw, hrlen, rfl, hpt.symm⟩, ?_⟩
    · rw [dist_self, zero_div]
      exact herrpos a b i
  · rintro ⟨r₀, q₀⟩ w ⟨r₁, q₁⟩ z ⟨r, γ, hr, hrlen, hp1, hp2⟩
      ⟨r', γ', hr', hr'len, hp1', hp2'⟩
    have hx : (r₀, q₀) = conePoint angles r γ := hp1
    have hw : w = γ.point (r * d i) := hp2
    have hy : (r₁, q₁) = conePoint angles r' γ' := hp1'
    have hz : z = γ'.point (r' * d i) := hp2'
    have hl' := hl γ γ' r r' hr hr' hrlen hr'len
    have hsD : r * d i ∈ Set.Ioc 0 (min γ.length Dang) :=
      ⟨mul_pos (lt_of_lt_of_le ha hr.1) (hpos i),
        le_min hrlen.2 ((mul_le_mul_of_nonneg_right hr.2 (le_of_lt (hpos i))).trans hiD)⟩
    have htD : r' * d i ∈ Set.Ioc 0 (min γ'.length Dang) :=
      ⟨mul_pos (lt_of_lt_of_le ha hr'.1) (hpos i),
        le_min hr'len.2 ((mul_le_mul_of_nonneg_right hr'.2 (le_of_lt (hpos i))).trans hiD)⟩
    have hupp : dist (γ.point (r * d i)) (γ'.point (r' * d i)) / d i ≤
        openConeDistance (conePoint angles r γ) (conePoint angles r' γ') := by
      have h := dist_div_le_openConeDistance angles hrlen hr'len (hpos i)
        (hangle γ γ' (r * d i) (r' * d i) hsD htD)
      rwa [mul_div_cancel_right₀ r (ne_of_gt (hpos i)),
        mul_div_cancel_right₀ r' (ne_of_gt (hpos i))] at h
    rw [hx, hy, hw, hz]
    rw [abs_lt]
    refine ⟨by linarith [hupp, herrpos a b i],
      by linarith [hl', herr_gt_el a b ha hab i]⟩
  · rintro ⟨r₀, q₀⟩ w ⟨r, γ, hr, hrlen, hp1, hp2⟩
    have hx : (r₀, q₀) = conePoint angles r γ := hp1
    have hw : w = γ.point (r * d i) := hp2
    have hxr : (r₀, q₀).1 = r := by rw [hx]; rfl
    have hdist : dist (w : UniformSpace.Completion W) H.endpoint = r * d i := by
      rw [hw]
      exact γ.radial (r * d i) hrlen
    rw [hxr, hdist, mul_div_cancel_right₀ r (ne_of_gt (hpos i)), sub_self, abs_zero]
    exact herrpos a b i
  · intro ha1 hb1
    refine ⟨1, ray, ⟨ha1.le, hb1.le⟩, by simpa using hd i, rfl, ?_⟩
    simp

theorem finite_horn_cone_convergence_of_coneAnnulusRealization
    (h : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        ConeAnnulusRealization H angles ray d) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        Nonempty (AnnularConvergence H angles ray d) := by
  obtain ⟨H₀, hH₀, hcone⟩ := h
  exact ⟨H₀, hH₀, fun g H hdepth angles ray d hd hzero =>
    nonempty_annularConvergence_of_coneAnnulusRealization H angles ray d hd hzero
      (hcone g H hdepth angles ray d hd hzero)⟩

structure ConeDistanceRealization {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop where
  lower : ∀ a b : ℝ, 0 < a → a < b → ∃ err : ℕ → ℝ, (∀ i, 0 < err i) ∧
    Filter.Tendsto err Filter.atTop (nhds 0) ∧ ∀ᶠ i in Filter.atTop,
      ∀ (γ γ' : EndRay H.endpoint) (r r' : ℝ), r ∈ Set.Icc a b → r' ∈ Set.Icc a b →
        r * d i ∈ Set.Ioc 0 γ.length → r' * d i ∈ Set.Ioc 0 γ'.length →
        openConeDistance (conePoint angles r γ) (conePoint angles r' γ') ≤
          dist (γ.point (r * d i)) (γ'.point (r' * d i)) / d i + err i
  dense : ∀ a b : ℝ, 0 < a → a < b → ∃ err : ℕ → ℝ, (∀ i, 0 < err i) ∧
    Filter.Tendsto err Filter.atTop (nhds 0) ∧ ∀ᶠ i in Filter.atTop,
      ∀ r ∈ Set.Icc a b, ∀ q : UniformSpace.Completion angles.quotient,
        ∃ γ : EndRay H.endpoint, r * d i ∈ Set.Ioc 0 γ.length ∧
          openConeDistance (r, q) (conePoint angles r γ) < err i

omit [SigmaCompactSpace W] in
theorem endComparisonAngle_le_endRayAngle {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (d : ℝ) (a b : EndRay H.endpoint) {s t : ℝ}
    (hs : s ∈ Set.Ioc 0 (min a.length d)) (ht : t ∈ Set.Ioc 0 (min b.length d)) :
    endComparisonAngle a b s t ≤ endRayAngle H.endpoint d a b := by
  rw [endRayAngle, limitingRadialAngle, ← radialComparisonAngle_endRay]
  exact le_csSup (positiveRectangleValues_radial_bddAbove (endRayLength H.endpoint d)
    (endRayFamily H.endpoint) a b) ⟨s, hs, t, ht, rfl⟩

omit [SigmaCompactSpace W] in
theorem endRayAngle_eq_of_endAngles {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (angles : EndAngles H) (a b : EndRay H.endpoint) :
    angles.angle a b = endRayAngle H.endpoint d a b := by
  have hlim : Filter.Tendsto (fun p : ℝ × ℝ => endComparisonAngle a b p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (nhds (angles.angle a b)) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    obtain ⟨d', hd'pos, -, hmain⟩ := angles.limit a b eta heta
    rw [Filter.eventually_prod_iff]
    refine ⟨fun s => s ∈ Set.Ioc (0 : ℝ) d', Ioc_mem_nhdsGT hd'pos,
      fun t => t ∈ Set.Ioc (0 : ℝ) d', Ioc_mem_nhdsGT hd'pos, ?_⟩
    intro s hs t ht
    simpa only [Real.dist_eq] using hmain s hs t ht
  exact tendsto_nhds_unique hlim (tendsto_endRayAngle H hd hmono a b)

omit [SigmaCompactSpace W] in
theorem exists_d_endComparisonAngle_le_angle {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    {d : ℝ} (hd : 0 < d)
    (hmono : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
        (radialComparisonAngle (endRayFamily H.endpoint) a b))
    (angles : EndAngles H) :
    ∃ D : ℝ, 0 < D ∧ ∀ (γ γ' : EndRay H.endpoint) (s t : ℝ),
      s ∈ Set.Ioc 0 (min γ.length D) → t ∈ Set.Ioc 0 (min γ'.length D) →
        endComparisonAngle γ γ' s t ≤ angles.angle γ γ' := by
  refine ⟨d, hd, ?_⟩
  intro γ γ' s t hs ht
  rw [endRayAngle_eq_of_endAngles H hd hmono angles γ γ']
  exact endComparisonAngle_le_endRayAngle H d γ γ' hs ht

theorem finite_horn_endComparisonAngle_le_angle :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H,
      ∃ D : ℝ, 0 < D ∧ ∀ (γ γ' : EndRay H.endpoint) (s t : ℝ),
        s ∈ Set.Ioc 0 (min γ.length D) → t ∈ Set.Ioc 0 (min γ'.length D) →
          endComparisonAngle γ γ' s t ≤ angles.angle γ γ' := by
  obtain ⟨H₀, hH₀, hmono⟩ := finite_horn_end_angle_monotone (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth angles
  obtain ⟨d, hd, hmonoH⟩ := hmono g H hdepth
  exact exists_d_endComparisonAngle_le_angle H hd hmonoH angles

omit [SigmaCompactSpace W] in
theorem coneAnnulusRealization_of_coneDistanceRealization
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
    {ray : EndRay H.endpoint} {d : ℕ → ℝ}
    (hangle : ∃ D : ℝ, 0 < D ∧ ∀ (γ γ' : EndRay H.endpoint) (s t : ℝ),
      s ∈ Set.Ioc 0 (min γ.length D) → t ∈ Set.Ioc 0 (min γ'.length D) →
        endComparisonAngle γ γ' s t ≤ angles.angle γ γ')
    (h : ConeDistanceRealization H angles ray d) : ConeAnnulusRealization H angles ray d :=
  ⟨hangle, h.lower, h.dense⟩

theorem finite_horn_cone_convergence_of_coneDistanceRealization
    (h : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        ConeDistanceRealization H angles ray d) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        Nonempty (AnnularConvergence H angles ray d) := by
  obtain ⟨H₀, hH₀, hcone⟩ := h
  obtain ⟨H₁, hH₁, hangle⟩ := finite_horn_endComparisonAngle_le_angle (W := W)
  refine ⟨max H₀ H₁, lt_max_of_lt_left hH₀, ?_⟩
  intro g H hdepth angles ray d hd hzero
  have hdepth₀ : H₀ ≤ H.collar_depth := (le_max_left H₀ H₁).trans hdepth
  have hdepth₁ : H₁ ≤ H.collar_depth := (le_max_right H₀ H₁).trans hdepth
  exact nonempty_annularConvergence_of_coneAnnulusRealization H angles ray d hd hzero
    (coneAnnulusRealization_of_coneDistanceRealization (hangle g H hdepth₁ angles)
      (hcone g H hdepth₀ angles ray d hd hzero))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
