import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled

/-!
# Curvature-scale balls

Elementary toolkit for the curvature scale `R_p = curvatureRadius g p`
(`Geometry/Collapse/CurvatureScale.lean`), the supremum of the radii `r > 0` such that every
point of the open Riemannian ball `B(p, r)` has sectional curvature at least `-r⁻²`.

* T1: below the curvature scale the defining sectional bound holds, strictly
  (`sectionalBoundedBelowAt_of_lt_curvatureRadius`) and at the attained radius `R_p` when it
  is finite (`sectionalBoundedBelowAt_of_curvatureRadius_ne_top`, by the closed limit `r ↑ R_p`;
  no continuity of `curvatureRadius` is used).
* T2: `R_p ≤ R_q + d(p, q)` in `ℝ≥0∞` (`curvatureRadius_le_add_riemannianEDistOf`), with no
  finiteness or connectedness hypothesis.
* T3: on a compact manifold the curvature scale has a uniform positive floor
  (`exists_pos_le_curvatureRadius`).
* T4: `R_p(c g) = √c R_p(g)` (`curvatureRadius_scaleMetric`).
* T5: the real curvature scale is `1`-Lipschitz for the Riemannian distance on a connected
  manifold whose curvature scales are all finite (`abs_toReal_curvatureRadius_sub_le`).

Paper proof of T2: if `r ≤ d(p, q)` there is nothing to show; otherwise
`B(q, r - d) ⊆ B(p, r)` and `-r⁻² ≥ -(r - d)⁻²`, so `r - d ≤ R_q`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open Filter Set
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Unpacking the supremum -/

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- A radius at which the defining sectional bound holds is at most the curvature scale. -/
theorem ofReal_le_curvatureRadius (g : SmoothRiemannianMetric I M) {p : M} {r : ℝ}
    (hr : 0 < r)
    (hP : ∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) :
    ENNReal.ofReal r ≤ curvatureRadius g p := by
  unfold curvatureRadius
  exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hP le_rfl))

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- Upper bounds for the curvature scale are checked on the admissible radii. -/
theorem curvatureRadius_le_iff {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ≥0∞} :
    curvatureRadius g p ≤ a ↔
      ∀ r : ℝ, 0 < r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
          ENNReal.ofReal r ≤ a := by
  unfold curvatureRadius
  simp only [iSup_le_iff]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- A real radius strictly below the curvature scale is dominated by an admissible radius. -/
theorem exists_admissible_gt_of_ofReal_lt_curvatureRadius (g : SmoothRiemannianMetric I M)
    {p : M} {r : ℝ} (hR : ENNReal.ofReal r < curvatureRadius g p) :
    ∃ s : ℝ, r < s ∧ 0 < s ∧
      ∀ q ∈ riemannianBallOf g p s, SectionalBoundedBelowAt g q (-(s ^ 2)⁻¹) := by
  unfold curvatureRadius at hR
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hR
  obtain ⟨hspos, hs⟩ := lt_iSup_iff.mp hs
  obtain ⟨hP, hs⟩ := lt_iSup_iff.mp hs
  exact ⟨s, (ENNReal.ofReal_lt_ofReal_iff hspos).mp hs, hspos, hP⟩

/-! ### T1: the sectional bound below the curvature scale -/

omit [SigmaCompactSpace M] in
/-- T1 (attained). When the curvature scale is finite, the defining bound holds on the ball of
radius exactly `R_p`, with constant `-R_p⁻²`. The proof passes to the closed limit `r ↑ R_p`
pointwise in the two tangent vectors; no continuity of `curvatureRadius` is used. -/
theorem sectionalBoundedBelowAt_of_curvatureRadius_ne_top (g : SmoothRiemannianMetric I M)
    {p : M} (hfin : curvatureRadius g p ≠ ⊤) :
    ∀ q ∈ riemannianBallOf g p (curvatureRadius g p).toReal,
      SectionalBoundedBelowAt g q (-(((curvatureRadius g p).toReal) ^ 2)⁻¹) := by
  have hRpos : 0 < (curvatureRadius g p).toReal :=
    ENNReal.toReal_pos (curvatureRadius_pos g p).ne' hfin
  intro q hq v w
  have hqlt : riemannianEDistOf (I := I) g p q <
      ENNReal.ofReal (curvatureRadius g p).toReal := hq
  have hd : riemannianEDistOf (I := I) g p q ≠ ⊤ := ne_top_of_lt hqlt
  have hd0 : 0 ≤ (riemannianEDistOf (I := I) g p q).toReal := ENNReal.toReal_nonneg
  have hdR : (riemannianEDistOf (I := I) g p q).toReal < (curvatureRadius g p).toReal := by
    rw [← ENNReal.ofReal_toReal hd] at hqlt
    exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mp hqlt
  have hev : ∀ᶠ r in 𝓝[<] (curvatureRadius g p).toReal,
      -(r ^ 2)⁻¹ * (g.inner q v v * g.inner q w w - g.inner q v w ^ 2) ≤
        metricRm04StandardAt (I := I) (M := M) g q v w w v := by
    filter_upwards [Ioo_mem_nhdsLT hdR] with r hr
    have hrpos : 0 < r := lt_of_le_of_lt hd0 hr.1
    have hlt : ENNReal.ofReal r < curvatureRadius g p := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hr.2
    have hqr : q ∈ riemannianBallOf g p r := by
      change riemannianEDistOf (I := I) g p q < ENNReal.ofReal r
      rw [← ENNReal.ofReal_toReal hd]
      exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hr.1
    exact sectionalBoundedBelowAt_of_lt_curvatureRadius g hlt hqr v w
  have hcont : ContinuousAt
      (fun r : ℝ => -(r ^ 2)⁻¹ * (g.inner q v v * g.inner q w w - g.inner q v w ^ 2))
      (curvatureRadius g p).toReal := by
    have hne : (curvatureRadius g p).toReal ^ 2 ≠ 0 := by positivity
    exact (((continuousAt_id.pow 2).inv₀ hne).neg).mul continuousAt_const
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev

/-! ### T2: the curvature scale is `1`-Lipschitz in `ℝ≥0∞` -/

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- T2. `R_p ≤ R_q + d(p, q)`; no finiteness or connectedness is needed. -/
theorem curvatureRadius_le_add_riemannianEDistOf (g : SmoothRiemannianMetric I M) (p q : M) :
    curvatureRadius g p ≤ curvatureRadius g q + riemannianEDistOf (I := I) g p q := by
  refine curvatureRadius_le_iff.mpr fun r hr hP => ?_
  by_cases hle : ENNReal.ofReal r ≤ riemannianEDistOf (I := I) g p q
  · exact hle.trans le_add_self
  · rw [not_le] at hle
    have hd : riemannianEDistOf (I := I) g p q ≠ ⊤ := ne_top_of_lt hle
    have hdeq : riemannianEDistOf (I := I) g p q =
        ENNReal.ofReal (riemannianEDistOf (I := I) g p q).toReal :=
      (ENNReal.ofReal_toReal hd).symm
    have hd0 : 0 ≤ (riemannianEDistOf (I := I) g p q).toReal := ENNReal.toReal_nonneg
    have hdr : (riemannianEDistOf (I := I) g p q).toReal < r := by
      rw [hdeq] at hle
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hle
    have hs : 0 < r - (riemannianEDistOf (I := I) g p q).toReal := sub_pos.mpr hdr
    have hP' : ∀ x ∈ riemannianBallOf g q (r - (riemannianEDistOf (I := I) g p q).toReal),
        SectionalBoundedBelowAt g x
          (-((r - (riemannianEDistOf (I := I) g p q).toReal) ^ 2)⁻¹) := by
      intro x hx
      have hxq : riemannianEDistOf (I := I) g q x <
          ENNReal.ofReal (r - (riemannianEDistOf (I := I) g p q).toReal) := hx
      have hxp : x ∈ riemannianBallOf g p r := by
        change riemannianEDistOf (I := I) g p x < ENNReal.ofReal r
        calc riemannianEDistOf (I := I) g p x
            ≤ riemannianEDistOf (I := I) g p q + riemannianEDistOf (I := I) g q x :=
              riemannianEDistOf_triangle g p q x
          _ < riemannianEDistOf (I := I) g p q +
              ENNReal.ofReal (r - (riemannianEDistOf (I := I) g p q).toReal) :=
              ENNReal.add_lt_add_left hd hxq
          _ = ENNReal.ofReal (riemannianEDistOf (I := I) g p q).toReal +
              ENNReal.ofReal (r - (riemannianEDistOf (I := I) g p q).toReal) := by
              rw [ENNReal.ofReal_toReal hd]
          _ = ENNReal.ofReal r := by
              rw [← ENNReal.ofReal_add hd0 hs.le]
              congr 1
              ring
      refine (hP x hxp).mono ?_
      have hpow : (r - (riemannianEDistOf (I := I) g p q).toReal) ^ 2 ≤ r ^ 2 :=
        pow_le_pow_left₀ hs.le (by linarith) 2
      have hinv : (r ^ 2)⁻¹ ≤ ((r - (riemannianEDistOf (I := I) g p q).toReal) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hpow
      linarith
    have hq := ofReal_le_curvatureRadius g hs hP'
    calc ENNReal.ofReal r
        = ENNReal.ofReal (r - (riemannianEDistOf (I := I) g p q).toReal) +
            ENNReal.ofReal (riemannianEDistOf (I := I) g p q).toReal := by
          rw [← ENNReal.ofReal_add hs.le hd0]
          congr 1
          ring
      _ ≤ curvatureRadius g q + riemannianEDistOf (I := I) g p q := by
          rw [← hdeq]
          exact add_le_add hq le_rfl

/-! ### T3: a uniform floor on compact manifolds -/

/-- T3. On a compact manifold the curvature scale has a uniform positive lower bound.
Each point has a radius `r_p > 0` with `2 r_p < R_p`; by T2 every point of `B(p, r_p)` has
curvature scale at least `r_p`; a finite subcover gives the floor. -/
theorem exists_pos_le_curvatureRadius [CompactSpace M] (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p : M, ENNReal.ofReal ρ ≤ curvatureRadius g p := by
  have hloc : ∀ p : M, ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (2 * r) < curvatureRadius g p := by
    intro p
    obtain ⟨s, hs0, hs, hsR⟩ := ENNReal.lt_iff_exists_real_btwn.mp (curvatureRadius_pos g p)
    have hspos : 0 < s := ENNReal.ofReal_pos.mp hs
    refine ⟨s / 2, by positivity, ?_⟩
    rwa [mul_div_cancel₀ s two_ne_zero]
  choose r hr0 hrR using hloc
  have hball : ∀ p q : M, q ∈ riemannianBallOf g p (r p) →
      ENNReal.ofReal (r p) ≤ curvatureRadius g q := by
    intro p q hq
    have hq' : riemannianEDistOf (I := I) g p q < ENNReal.ofReal (r p) := hq
    have hsum : ENNReal.ofReal (r p) + ENNReal.ofReal (r p) <
        curvatureRadius g q + ENNReal.ofReal (r p) :=
      calc ENNReal.ofReal (r p) + ENNReal.ofReal (r p) = ENNReal.ofReal (2 * r p) := by
            rw [← ENNReal.ofReal_add (hr0 p).le (hr0 p).le, two_mul]
        _ < curvatureRadius g p := hrR p
        _ ≤ curvatureRadius g q + riemannianEDistOf (I := I) g p q :=
            curvatureRadius_le_add_riemannianEDistOf g p q
        _ ≤ curvatureRadius g q + ENNReal.ofReal (r p) := add_le_add le_rfl hq'.le
    exact ((ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hsum).le
  have hself : ∀ p : M, p ∈ riemannianBallOf g p (r p) := by
    intro p
    change riemannianEDistOf (I := I) g p p < ENNReal.ofReal (r p)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (hr0 p)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun p : M => riemannianBallOf g p (r p))
    (fun p _ => (isOpen_riemannianBallOf g p (r p)).mem_nhds (hself p))
  rcases t.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun p => ?_⟩
    have hp := ht (mem_univ p)
    simp [hempty] at hp
  · obtain ⟨p₀, hp₀, hmin⟩ := t.exists_min_image r hne
    refine ⟨r p₀, hr0 p₀, fun q => ?_⟩
    obtain ⟨p, hp, hq⟩ := mem_iUnion₂.mp (ht (mem_univ q))
    exact (ENNReal.ofReal_le_ofReal (hmin p hp)).trans (hball p q hq)

/-! ### T4: scaling -/

omit [SigmaCompactSpace M] in
/-- The sectional lower bound of `c g` with constant `K` is the sectional lower bound of `g`
with constant `K c`. -/
theorem sectionalBoundedBelowAt_scaleMetric_iff {c : ℝ} (hc : 0 < c)
    {g : SmoothRiemannianMetric I M} {x : M} {K : ℝ} :
    SectionalBoundedBelowAt (scaleMetric c hc g) x K ↔ SectionalBoundedBelowAt g x (K * c) := by
  constructor
  · intro h v w
    have h1 := h v w
    simp only [scaleMetric_inner,
      PDE.RicciFlow.metricRm04StandardAt_scaleMetric c hc g x v w w v] at h1
    have heq : K * (c * g.inner x v v * (c * g.inner x w w) - (c * g.inner x v w) ^ 2) =
        c * (K * c * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) := by
      ring
    rw [heq] at h1
    exact le_of_mul_le_mul_left h1 hc
  · intro h
    have h1 := PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric h c hc
    rwa [mul_div_cancel_right₀ K hc.ne'] at h1

omit [SigmaCompactSpace M] in
/-- One half of T4: `R_p(c g) ≤ √c R_p(g)`. -/
theorem curvatureRadius_scaleMetric_le (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (p : M) :
    curvatureRadius (scaleMetric c hc g) p ≤
      ENNReal.ofReal (Real.sqrt c) * curvatureRadius g p := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine curvatureRadius_le_iff.mpr fun s hs hP => ?_
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, s = Real.sqrt c * r :=
    ⟨s / Real.sqrt c, by field_simp⟩
  have hr : 0 < r := (mul_pos_iff_of_pos_left hsc).mp hs
  have hPg : ∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
    intro q hq
    have hq' : q ∈ riemannianBallOf (scaleMetric c hc g) p (Real.sqrt c * r) := by
      rw [riemannianBallOf_scaleMetric]
      exact hq
    have h1 := (sectionalBoundedBelowAt_scaleMetric_iff hc).mp (hP q hq')
    have hK : -((Real.sqrt c * r) ^ 2)⁻¹ * c = -(r ^ 2)⁻¹ := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      field_simp
    rwa [hK] at h1
  calc ENNReal.ofReal (Real.sqrt c * r)
      = ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal r := ENNReal.ofReal_mul hsc.le
    _ ≤ ENNReal.ofReal (Real.sqrt c) * curvatureRadius g p :=
        mul_le_mul' le_rfl (ofReal_le_curvatureRadius g hr hPg)

/-! ### T5: the real form under finite scales -/

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- T5. On a connected manifold whose curvature scales are all finite, the real curvature scale
is `1`-Lipschitz for the Riemannian distance. -/
theorem abs_toReal_curvatureRadius_sub_le [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hfin : ∀ p, curvatureRadius g p ≠ ⊤) (p q : M) :
    |(curvatureRadius g p).toReal - (curvatureRadius g q).toReal| ≤
      (riemannianEDistOf (I := I) g p q).toReal := by
  have key : ∀ a b : M, (curvatureRadius g a).toReal ≤
      (curvatureRadius g b).toReal + (riemannianEDistOf (I := I) g a b).toReal := by
    intro a b
    have hd : riemannianEDistOf (I := I) g a b ≠ ⊤ := riemannianEDistOf_ne_top g a b
    rw [← ENNReal.toReal_add (hfin b) hd]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin b, hd⟩)
      (curvatureRadius_le_add_riemannianEDistOf g a b)
  rw [abs_sub_le_iff]
  constructor
  · linarith [key p q]
  · have h := key q p
    rw [riemannianEDistOf_comm] at h
    linarith

end DifferentialGeometry.Geometry.Collapse
