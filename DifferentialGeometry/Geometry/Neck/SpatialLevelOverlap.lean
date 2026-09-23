import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem abs_height_lt_of_scaled_difference
    {r₀ r₁ σ s₀ s₁ v E : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hsqrt : r₁ ≤ 2 * r₀) (hσ : σ = 1 ∨ σ = -1)
    (hs₀ : |s₀| ≤ 1 / 8) (hs₁ : |s₁| ≤ 1 / 8)
    (hE : 0 ≤ E) (hCeps : E ≤ 1 / 64)
    (hestq : |0 - σ * (r₁⁻¹ * v) - (r₀⁻¹ * s₀ - σ * (r₁⁻¹ * s₁))| ≤ E / r₀) :
    |v| < 1 / 2 := by
  have hscaled : |(-σ * v) - (r₁ / r₀ * s₀ - σ * s₁)| ≤ 2 * E := by
    have hh := mul_le_mul_of_nonneg_left hestq hr₁.le
    have hid : r₁ * (0 - σ * (r₁⁻¹ * v) - (r₀⁻¹ * s₀ - σ * (r₁⁻¹ * s₁))) =
        (-σ * v) - (r₁ / r₀ * s₀ - σ * s₁) := by
      field_simp
      ring
    have habsmul : |r₁ * (0 - σ * (r₁⁻¹ * v) -
        (r₀⁻¹ * s₀ - σ * (r₁⁻¹ * s₁)))| =
        r₁ * |0 - σ * (r₁⁻¹ * v) - (r₀⁻¹ * s₀ - σ * (r₁⁻¹ * s₁))| := by
      rw [abs_mul, abs_of_pos hr₁]
    rw [← habsmul, hid] at hh
    apply hh.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hr₀).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsqrt hE]
  have hratio_pos : 0 ≤ r₁ / r₀ := (div_pos hr₁ hr₀).le
  have hratio_le : r₁ / r₀ ≤ 2 := (div_le_iff₀ hr₀).mpr hsqrt
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp hs₀).1 hratio_pos
  have hhi := mul_le_mul_of_nonneg_left (abs_le.mp hs₀).2 hratio_pos
  have hvabs : |v| < 1 / 2 := by
    have hl := (abs_le.mp hscaled).1
    have hu := (abs_le.mp hscaled).2
    rcases hσ with rfl | rfl <;> rw [abs_lt] <;>
      constructor <;> nlinarith [(abs_le.mp hs₁).1, (abs_le.mp hs₁).2]
  exact hvabs

theorem exists_spatial_neck_level_slab_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (u₀ u₁ : Sphere 2) (a b s₀ s₁ : ℝ),
          |a| ≤ 3 → |b| ≤ 3 → |s₀| ≤ 1 / 8 → |s₁| ≤ 1 / 8 →
          nk₀.map (u₀, a + s₀) = nk₁.map (u₁, b + s₁) →
          (nk₀.map '' (univ ×ˢ Icc (a - 1) (a + 1)) ⊆
            nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) ∧
          ∀ q : Sphere 2, |(nk₁.map.symm (nk₀.map (q, a))).2 - b| < 1 / 2 := by
  obtain ⟨eta₀, C, heta₀, hsmall₀, hC, hbound⟩ :=
    exists_spatial_neck_anchored_overlap_estimates.{u}
  obtain ⟨eta₁, heta₁, _, hintersection⟩ := exists_spatial_neck_intersection_tolerance.{u}
  let eta : ℝ := min (eta₀ / 13000)
    (min (eta₁ / 13000) (min (1 / 156000) (1 / (832000 * C))))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ u₀ u₁ a b s₀ s₁ ha hb hs₀ hs₁ hmeet
  let alpha : ℝ := 13000 * eps
  have halpha₀ : alpha ≤ eta₀ := by
    have h := heps.trans (min_le_left _ _)
    dsimp only [alpha]
    linarith
  have halpha₁ : alpha ≤ eta₁ := by
    have h := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp only [alpha]
    linarith
  have hepssmall : eps ≤ 1 / 156000 :=
    heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hCeps : C * alpha ≤ 1 / 64 := by
    have h := heps.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hh := (le_div_iff₀ (show 0 < 832000 * C by positivity)).mp h
    dsimp only [alpha]
    nlinarith
  have hasmall : alpha < 1 / 11 := by dsimp only [alpha]; linarith
  obtain ⟨out₀, _, hm₀⟩ := nk₀.exists_at_coordinate hasmall le_rfl u₀
    (ha.trans (by norm_num))
  obtain ⟨out₁, _, hm₁⟩ := nk₁.exists_at_coordinate hasmall le_rfl u₁
    (hb.trans (by norm_num))
  have hmap₀ := nk₀.translated_map_apply u₀ out₀ hm₀
  have hmap₁ := nk₁.translated_map_apply u₁ out₁ hm₁
  have hmeet' : out₀.map (u₀, s₀) = out₁.map (u₁, s₁) := by
    rw [hmap₀, hmap₁]
    exact hmeet
  let z : M := out₀.map (u₀, s₀)
  have hz₀ : z ∈ out₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(u₀, s₀), ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hs₀).1,
      (abs_le.mp hs₀).2]⟩, rfl⟩
  have hz₁ : z ∈ out₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(u₁, s₁), ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hs₁).1,
      (abs_le.mp hs₁).2]⟩, hmeet'.symm⟩
  have hlen : (1 : ℝ) < alpha⁻¹ :=
    (one_lt_inv₀ out₀.eps_pos).mpr (out₀.eps_small.trans (by norm_num))
  have hunit : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆
      univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ := by
    intro v hv
    exact ⟨hv.1, (neg_lt_neg hlen).trans_le hv.2.1, hv.2.2.trans_lt hlen⟩
  obtain ⟨_, _, _, hsub, _⟩ := hintersection alpha halpha₁ M g _ _ out₀ out₁
    ⟨z, hz₀, hz₁⟩
  obtain ⟨σ, hσ, hest⟩ := hbound alpha halpha₀ M g _ _ out₀ out₁ z hz₀ hz₁
  have hratio := out₁.scalar_ratio_of_common_point out₀ (halpha₀.trans_lt hsmall₀)
    ((image_mono hunit) hz₁) ((image_mono hunit) hz₀)
  have hQ : metricScalarAt g (nk₁.map (u₁, b)) ≤
      4 * metricScalarAt g (nk₀.map (u₀, a)) := by
    apply (div_le_iff₀ out₀.Q_pos).mp
    have hh := (abs_le.mp hratio).2
    linarith [halpha₀.trans_lt hsmall₀]
  let r₀ := Real.sqrt (metricScalarAt g (nk₀.map (u₀, a)))
  let r₁ := Real.sqrt (metricScalarAt g (nk₁.map (u₁, b)))
  have hr₀ : 0 < r₀ := Real.sqrt_pos.mpr out₀.Q_pos
  have hr₁ : 0 < r₁ := Real.sqrt_pos.mpr out₁.Q_pos
  have hsqrt : r₁ ≤ 2 * r₀ := by
    dsimp only [r₀, r₁]
    nlinarith [Real.sq_sqrt out₀.Q_pos.le, Real.sq_sqrt out₁.Q_pos.le,
      Real.sqrt_nonneg (metricScalarAt g (nk₀.map (u₀, a))),
      Real.sqrt_nonneg (metricScalarAt g (nk₁.map (u₁, b)))]
  have hax₀ (v : Cylinder) (hv : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) :
      out₀.cylindricalChart.axial (out₀.map v) = r₀⁻¹ * v.2 :=
    out₀.cylindricalChart.axial_chart ⟨v, hv⟩
  have hax₁ (v : Cylinder) (hv : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) :
      out₁.cylindricalChart.axial (out₁.map v) = r₁⁻¹ * v.2 :=
    out₁.cylindricalChart.axial_chart ⟨v, hv⟩
  have hzax₀ : out₀.cylindricalChart.axial z = r₀⁻¹ * s₀ :=
    hax₀ _ (hunit ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hs₀).1,
      (abs_le.mp hs₀).2]⟩)
  have hzax₁ : out₁.cylindricalChart.axial z = r₁⁻¹ * s₁ := by
    change out₁.cylindricalChart.axial (out₀.map (u₀, s₀)) = _
    rw [hmeet']
    exact hax₁ _ (hunit ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hs₁).1,
      (abs_le.mp hs₁).2]⟩)
  have hfit : 4 + alpha⁻¹ < eps⁻¹ := by
    have hap : 0 < alpha := out₀.eps_pos
    have hp : 0 < 4 + alpha⁻¹ := by positivity
    apply (lt_inv_comm₀ hp nk₀.eps_pos).mpr
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hp).mpr
    have hc : eps * alpha⁻¹ = 1 / 13000 := by
      dsimp only [alpha]
      field_simp [nk₀.eps_pos.ne']
    nlinarith
  have htranslate (v : Cylinder) (hv : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) :
      (v.1, b + v.2) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    exact ⟨mem_univ _, by linarith [(abs_le.mp hb).1, hv.2.1],
      by linarith [(abs_le.mp hb).2, hv.2.2]⟩
  constructor
  · rintro x ⟨v, hv, rfl⟩
    have ht : (v.1, v.2 - a) ∈ univ ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨mem_univ _, by constructor <;> linarith [hv.2.1, hv.2.2]⟩
    obtain ⟨w, hw, heq⟩ := hsub (Or.inl ⟨(v.1, v.2 - a), ht, rfl⟩)
    have hwfull : w ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ :=
      ⟨hw.1, by constructor <;> linarith [hw.2.1, hw.2.2]⟩
    refine ⟨(w.1, b + w.2), htranslate w hwfull, ?_⟩
    rw [← hmap₁, heq, hmap₀, add_sub_cancel]
  intro q
  have hq : out₀.map (q, 0) ∈ out₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  obtain ⟨v, hv, heq⟩ := hsub (Or.inl hq)
  have hvfull : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ :=
    ⟨hv.1, by constructor <;> linarith [hv.2.1, hv.2.2]⟩
  have hestq := (hest (out₀.map (q, 0)) (Or.inl hq)).1
  rw [hax₀ _ (hunit ⟨mem_univ _, by norm_num⟩), mul_zero,
    hzax₀, hzax₁, ← heq, hax₁ _ hvfull] at hestq
  change |0 - σ * (r₁⁻¹ * v.2) - (r₀⁻¹ * s₀ - σ * (r₁⁻¹ * s₁))| ≤
    C * alpha / r₀ at hestq
  have hvabs : |v.2| < 1 / 2 := abs_height_lt_of_scaled_difference
    hr₀ hr₁ hsqrt hσ hs₀ hs₁ (mul_nonneg hC.le out₀.eps_pos.le) hCeps hestq
  have hsource := nk₁.domain (htranslate v hvfull)
  have hmap : nk₁.map (v.1, b + v.2) = nk₀.map (q, a) := by
    rw [← hmap₁, heq, hmap₀, add_zero]
  have hinv := nk₁.map.left_inv hsource
  change nk₁.map.symm (nk₁.map (v.1, b + v.2)) = (v.1, b + v.2) at hinv
  rw [← hmap, hinv]
  simpa only [add_sub_cancel_left] using hvabs

private theorem abs_height_lt_of_small_scaled_difference
    {r₀ r₁ σ s t v E : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hsqrt : r₁ ≤ 2 * r₀) (hσ : σ = 1 ∨ σ = -1)
    (hs : |s| ≤ 1 / 100) (ht : |t| ≤ 1 / 100)
    (hE : 0 ≤ E) (hsmall : E ≤ 1 / 64)
    (hest : |r₀⁻¹ * t - σ * (r₁⁻¹ * v) - r₀⁻¹ * s| ≤ E / r₀) :
    |v| < 1 / 8 := by
  have hscaled : |r₁ / r₀ * (t - s) - σ * v| ≤ 2 * E := by
    have hh := mul_le_mul_of_nonneg_left hest hr₁.le
    have hid : r₁ * (r₀⁻¹ * t - σ * (r₁⁻¹ * v) - r₀⁻¹ * s) =
        r₁ / r₀ * (t - s) - σ * v := by
      field_simp
      ring
    have habsmul : |r₁ * (r₀⁻¹ * t - σ * (r₁⁻¹ * v) - r₀⁻¹ * s)| =
        r₁ * |r₀⁻¹ * t - σ * (r₁⁻¹ * v) - r₀⁻¹ * s| := by
      rw [abs_mul, abs_of_pos hr₁]
    rw [← habsmul, hid] at hh
    apply hh.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hr₀).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsqrt hE]
  have hratio_pos : 0 ≤ r₁ / r₀ := (div_pos hr₁ hr₀).le
  have hratio_le : r₁ / r₀ ≤ 2 := (div_le_iff₀ hr₀).mpr hsqrt
  have htslo : -(1 / 50 : ℝ) ≤ t - s := by
    linarith [(abs_le.mp ht).1, (abs_le.mp hs).2]
  have htshi : t - s ≤ (1 / 50 : ℝ) := by
    linarith [(abs_le.mp ht).2, (abs_le.mp hs).1]
  have hlo := mul_le_mul_of_nonneg_left htslo hratio_pos
  have hhi := mul_le_mul_of_nonneg_left htshi hratio_pos
  have hl := (abs_le.mp hscaled).1
  have hu := (abs_le.mp hscaled).2
  rcases hσ with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith

theorem exists_spatial_neck_thin_level_slab_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (u₀ u₁ : Sphere 2) (a b s₀ : ℝ),
          |a| ≤ 3 → |b| ≤ 3 → |s₀| ≤ 1 / 100 →
          nk₀.map (u₀, a + s₀) = nk₁.map (u₁, b) →
          nk₀.map '' (univ ×ˢ Icc (a - 1 / 100) (a + 1 / 100)) ⊆
            nk₁.map '' (univ ×ˢ Ioo (b - 1 / 8) (b + 1 / 8)) := by
  obtain ⟨eta₀, C, heta₀, hsmall₀, hC, hbound⟩ :=
    exists_spatial_neck_anchored_overlap_estimates.{u}
  obtain ⟨eta₁, heta₁, _, hintersection⟩ := exists_spatial_neck_intersection_tolerance.{u}
  let eta : ℝ := min (eta₀ / 13000)
    (min (eta₁ / 13000) (min (1 / 156000) (1 / (832000 * C))))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ u₀ u₁ a b s₀ ha hb hs₀ hmeet
  let alpha : ℝ := 13000 * eps
  have halpha₀ : alpha ≤ eta₀ := by
    have h := heps.trans (min_le_left _ _)
    dsimp only [alpha]
    linarith
  have halpha₁ : alpha ≤ eta₁ := by
    have h := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp only [alpha]
    linarith
  have hepssmall : eps ≤ 1 / 156000 :=
    heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hCeps : C * alpha ≤ 1 / 64 := by
    have h := heps.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hh := (le_div_iff₀ (show 0 < 832000 * C by positivity)).mp h
    dsimp only [alpha]
    nlinarith
  have hasmall : alpha < 1 / 11 := by dsimp only [alpha]; linarith
  obtain ⟨out₀, _, hm₀⟩ := nk₀.exists_at_coordinate hasmall le_rfl u₀
    (ha.trans (by norm_num))
  obtain ⟨out₁, _, hm₁⟩ := nk₁.exists_at_coordinate hasmall le_rfl u₁
    (hb.trans (by norm_num))
  have hmap₀ := nk₀.translated_map_apply u₀ out₀ hm₀
  have hmap₁ := nk₁.translated_map_apply u₁ out₁ hm₁
  have hmeet' : out₀.map (u₀, s₀) = out₁.map (u₁, 0) := by
    rw [hmap₀, hmap₁, add_zero]
    exact hmeet
  let z : M := out₀.map (u₀, s₀)
  have hz₀ : z ∈ out₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(u₀, s₀), ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hs₀).1,
      (abs_le.mp hs₀).2]⟩, rfl⟩
  have hz₁ : z ∈ out₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(u₁, 0), ⟨mem_univ _, by norm_num⟩, hmeet'.symm⟩
  have hlen : (1 : ℝ) < alpha⁻¹ :=
    (one_lt_inv₀ out₀.eps_pos).mpr (out₀.eps_small.trans (by norm_num))
  have hunit : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆
      univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ := by
    intro v hv
    exact ⟨hv.1, (neg_lt_neg hlen).trans_le hv.2.1, hv.2.2.trans_lt hlen⟩
  obtain ⟨_, _, _, hsub, _⟩ := hintersection alpha halpha₁ M g _ _ out₀ out₁
    ⟨z, hz₀, hz₁⟩
  obtain ⟨σ, hσ, hest⟩ := hbound alpha halpha₀ M g _ _ out₀ out₁ z hz₀ hz₁
  have hratio := out₁.scalar_ratio_of_common_point out₀ (halpha₀.trans_lt hsmall₀)
    ((image_mono hunit) hz₁) ((image_mono hunit) hz₀)
  have hQ : metricScalarAt g (nk₁.map (u₁, b)) ≤
      4 * metricScalarAt g (nk₀.map (u₀, a)) := by
    apply (div_le_iff₀ out₀.Q_pos).mp
    have hh := (abs_le.mp hratio).2
    linarith [halpha₀.trans_lt hsmall₀]
  let r₀ := Real.sqrt (metricScalarAt g (nk₀.map (u₀, a)))
  let r₁ := Real.sqrt (metricScalarAt g (nk₁.map (u₁, b)))
  have hr₀ : 0 < r₀ := Real.sqrt_pos.mpr out₀.Q_pos
  have hr₁ : 0 < r₁ := Real.sqrt_pos.mpr out₁.Q_pos
  have hsqrt : r₁ ≤ 2 * r₀ := by
    dsimp only [r₀, r₁]
    nlinarith [Real.sq_sqrt out₀.Q_pos.le, Real.sq_sqrt out₁.Q_pos.le,
      Real.sqrt_nonneg (metricScalarAt g (nk₀.map (u₀, a))),
      Real.sqrt_nonneg (metricScalarAt g (nk₁.map (u₁, b)))]
  have hax₀ (v : Cylinder) (hv : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) :
      out₀.cylindricalChart.axial (out₀.map v) = r₀⁻¹ * v.2 :=
    out₀.cylindricalChart.axial_chart ⟨v, hv⟩
  have hax₁ (v : Cylinder) (hv : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) :
      out₁.cylindricalChart.axial (out₁.map v) = r₁⁻¹ * v.2 :=
    out₁.cylindricalChart.axial_chart ⟨v, hv⟩
  have hzax₀ : out₀.cylindricalChart.axial z = r₀⁻¹ * s₀ :=
    hax₀ _ (hunit ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hs₀).1,
      (abs_le.mp hs₀).2]⟩)
  have hzax₁ : out₁.cylindricalChart.axial z = 0 := by
    change out₁.cylindricalChart.axial (out₀.map (u₀, s₀)) = _
    rw [hmeet', hax₁ _ (hunit ⟨mem_univ _, by norm_num⟩), mul_zero]
  rintro x ⟨⟨q, t⟩, ht, rfl⟩
  have htoff : |t - a| ≤ 1 / 100 := by
    rw [abs_le]
    constructor <;> linarith [ht.2.1, ht.2.2]
  have hqmem : (q, t - a) ∈ univ ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩
  have hq : out₀.map (q, t - a) ∈ out₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(q, t - a), hqmem, rfl⟩
  obtain ⟨v, hv, heq⟩ := hsub (Or.inl hq)
  have hvfull : v ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ :=
    ⟨hv.1, by constructor <;> linarith [hv.2.1, hv.2.2]⟩
  have hestq := (hest (out₀.map (q, t - a)) (Or.inl hq)).1
  rw [hax₀ _ (hunit hqmem), hzax₀, hzax₁, mul_zero, sub_zero,
    ← heq, hax₁ _ hvfull] at hestq
  change |r₀⁻¹ * (t - a) - σ * (r₁⁻¹ * v.2) - r₀⁻¹ * s₀| ≤
    C * alpha / r₀ at hestq
  have hvabs : |v.2| < 1 / 8 := abs_height_lt_of_small_scaled_difference
    hr₀ hr₁ hsqrt hσ hs₀ htoff (mul_nonneg hC.le out₀.eps_pos.le) hCeps hestq
  refine ⟨(v.1, b + v.2), ⟨mem_univ _, ?_, ?_⟩, ?_⟩
  · linarith [(abs_lt.mp hvabs).1]
  · linarith [(abs_lt.mp hvabs).2]
  · rw [← hmap₁, heq, hmap₀, add_sub_cancel]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
