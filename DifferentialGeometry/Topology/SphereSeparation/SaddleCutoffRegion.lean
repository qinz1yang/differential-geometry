import DifferentialGeometry.Topology.PlanarJordan.ArcCollar
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Embedding.ArcGluing
import DifferentialGeometry.Topology.Embedding.LevelArcCollar
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle
import DifferentialGeometry.Topology.PlanarJordan.SaddleCapSides
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import DifferentialGeometry.Topology.PlanarJordan.SmoothArc
import DifferentialGeometry.External.Schoenflies.Concatenate
import DifferentialGeometry.Topology.PlanarJordan.Regions
import DifferentialGeometry.Topology.Embedding.GraphChartNeighborhood
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Topology.Diffeomorph.QuadraticCapProjection
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleCutoffProjection

open Set Filter Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE (saddleBandCurve saddleBandCurve_zero quadraticLevelScaling)
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

private noncomputable def lowerSaddleArm (s a τ σ v : ℝ) : ℝ × ℝ :=
  (τ * Real.sqrt ((v ^ 2 - 2 * a) / (v ^ 2 + 2 * s)), σ * v)

private theorem lowerSaddleArm_properties {s a τ σ : ℝ}
    (hs : 0 < s) (ha : a < 0) (hτ : τ ^ 2 = 1) (hσ : σ ^ 2 = 1) :
    ContDiff ℝ ∞ (lowerSaddleArm s a τ σ) ∧
      Function.Injective (lowerSaddleArm s a τ σ) ∧
      ∀ v, 0 < τ * (lowerSaddleArm s a τ σ v).1 ∧
        σ * (lowerSaddleArm s a τ σ v).2 = v ∧
        (1 - (lowerSaddleArm s a τ σ v).1 ^ 2) *
          ((lowerSaddleArm s a τ σ v).2 ^ 2 + 2 * s) / 2 - s = a := by
  have hden (v : ℝ) : 0 < v ^ 2 + 2 * s := by positivity
  have hnum (v : ℝ) : 0 < v ^ 2 - 2 * a := by nlinarith [sq_nonneg v]
  have hrad (v : ℝ) : 0 < (v ^ 2 - 2 * a) / (v ^ 2 + 2 * s) :=
    div_pos (hnum v) (hden v)
  have hσne : σ ≠ 0 := by intro heq; rw [heq] at hσ; norm_num at hσ
  refine ⟨?_, ?_, ?_⟩
  · unfold lowerSaddleArm
    apply ContDiff.prodMk
    · exact contDiff_const.mul ((((contDiff_id.pow 2).sub contDiff_const).div
        ((contDiff_id.pow 2).add contDiff_const) (fun v => (hden v).ne')).sqrt
        (fun v => (hrad v).ne'))
    · fun_prop
  · intro v w heq
    have he := congrArg Prod.snd heq
    exact mul_left_cancel₀ hσne he
  · intro v
    have hroot := Real.sq_sqrt (hrad v).le
    refine ⟨?_, ?_, ?_⟩
    · change τ * (τ * Real.sqrt _) > 0
      rw [← mul_assoc, ← pow_two, hτ, one_mul]
      exact Real.sqrt_pos.mpr (hrad v)
    · change σ * (σ * v) = v
      rw [← mul_assoc, ← pow_two, hσ, one_mul]
    · simp only [lowerSaddleArm, mul_pow, hτ, hσ, one_mul, hroot]
      field_simp [(hden v).ne']
      ring

private theorem lowerSaddleArm_width_iff {s a τ σ k v : ℝ}
    (hs : 0 < s) (ha : a < 0) (hτ : τ ^ 2 = 1) (hk : 0 ≤ k) (hk1 : k < 1) :
    |(lowerSaddleArm s a τ σ v).1| ≤ k ↔
      v ^ 2 ≤ 2 * (a + s * k ^ 2) / (1 - k ^ 2) := by
  have hden : 0 < v ^ 2 + 2 * s := by positivity
  have hnum : 0 < v ^ 2 - 2 * a := by nlinarith [sq_nonneg v]
  have hkden : 0 < 1 - k ^ 2 := by nlinarith
  have habsτ : |τ| = 1 := by
    rcases sq_eq_one_iff.mp hτ with rfl | rfl <;> norm_num
  simp only [lowerSaddleArm, abs_mul, habsτ, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_le_iff, and_iff_right hk, div_le_iff₀ hden, le_div_iff₀ hkden]
  constructor <;> intro h <;> nlinarith

private theorem lowerSaddleArm_mem_half_band
    {s a j τ σ k v₀ v₁ v : ℝ} (hs : 0 < s) (ha : a < 0)
    (hτ : τ ^ 2 = 1) (hσ : σ ^ 2 = 1) (hk : 0 ≤ k) (hk1 : k < 1)
    (hv₀₁ : v₀ ≤ v₁)
    (hvk : v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2)) (haj : a ≤ j)
    (hv : v ∈ Icc (-v₀) v₁) :
    let z := lowerSaddleArm s a τ σ v
    |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j := by
  have hprops := (lowerSaddleArm_properties hs ha hτ hσ).2.2 v
  dsimp only
  refine ⟨?_, by simpa only [hprops.2.1] using hv.1, ?_, ?_⟩
  · apply (lowerSaddleArm_width_iff hs ha hτ hk hk1).mpr
    rw [← hvk]
    nlinarith [hv.1, hv.2]
  · exact hprops.2.2.ge
  · exact hprops.2.2.le.trans haj

private theorem lowerSaddleArm_right_endpoint {s a τ σ k v₁ : ℝ}
    (hs : 0 < s) (hk : 0 ≤ k) (hk1 : k < 1)
    (hvk : v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2)) :
    lowerSaddleArm s a τ σ v₁ = (τ * k, σ * v₁) := by
  have hden : v₁ ^ 2 + 2 * s ≠ 0 := ne_of_gt (by positivity)
  have hkden : 1 - k ^ 2 ≠ 0 := ne_of_gt (by nlinarith : 0 < 1 - k ^ 2)
  have hmul : v₁ ^ 2 * (1 - k ^ 2) = 2 * (a + s * k ^ 2) :=
    (eq_div_iff hkden).mp hvk
  have hratio : (v₁ ^ 2 - 2 * a) / (v₁ ^ 2 + 2 * s) = k ^ 2 := by
    apply (div_eq_iff hden).mpr
    nlinarith
  simp only [lowerSaddleArm, hratio, Real.sqrt_sq hk]

private theorem lower_saddle_boundary_parameters
    {s a j σ k v₀ : ℝ} (hs : 0 < s) (ha : a < 0) (hσ : σ ^ 2 = 1)
    (hk : 0 < k) (hk1 : k < 1) (hak : 0 < a + s * k ^ 2)
    (hv₀ : 0 < v₀) (hv₀j : v₀ ^ 2 / 2 < j)
    (hside : ∀ z : ℝ × ℝ, |z.1| ≤ k → -v₀ ≤ σ * z.2 →
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j →
      |z.1| = k → 0 < σ * z.2) :
    let v₁ := Real.sqrt (2 * (a + s * k ^ 2) / (1 - k ^ 2))
    let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    0 < v₁ ∧ v₀ < v₁ ∧ 0 < u₀ ∧ u₀ < k ∧
      v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2) ∧
      u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s) := by
  let v₁ := Real.sqrt (2 * (a + s * k ^ 2) / (1 - k ^ 2))
  let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
  have hkden : 0 < 1 - k ^ 2 := by nlinarith
  have hv₁ : 0 < v₁ := Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hak) hkden)
  have hv₁sq : v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2) :=
    Real.sq_sqrt (div_pos (mul_pos (by norm_num) hak) hkden).le
  have hlevel : (1 - k ^ 2) * (v₁ ^ 2 + 2 * s) / 2 - s = a := by
    have hm := (eq_div_iff hkden.ne').mp hv₁sq
    nlinarith
  have hσmul (v : ℝ) : σ * (σ * v) = v := by rw [← mul_assoc, ← pow_two, hσ, one_mul]
  have hv₀₁ : v₀ < v₁ := by
    by_contra hn
    have hle : v₁ ≤ v₀ := le_of_not_gt hn
    have hpos := hside (k, -(σ * v₁)) (by simp only [abs_of_pos hk, le_refl])
      (by simp only [mul_neg, hσmul]; linarith)
      (by simp only [neg_sq, mul_pow, hσ, one_mul, hlevel, le_refl])
      (by simp only [neg_sq, mul_pow, hσ, one_mul, hlevel]; nlinarith)
      (by simp only [abs_of_pos hk])
    simp only [mul_neg, hσmul] at hpos
    linarith
  have hden : 0 < v₀ ^ 2 + 2 * s := by positivity
  have hnum : 0 < v₀ ^ 2 - 2 * a := by nlinarith [sq_nonneg v₀]
  have hu₀ : 0 < u₀ := Real.sqrt_pos.mpr (div_pos hnum hden)
  have hu₀sq : u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s) :=
    Real.sq_sqrt (div_pos hnum hden).le
  have hu₀k : u₀ < k := by
    have hmul := (eq_div_iff hden.ne').mp hu₀sq
    have hvk := (eq_div_iff hkden.ne').mp hv₁sq
    have hsq : v₀ ^ 2 < v₁ ^ 2 := by nlinarith
    have hprod := mul_pos hkden (sub_pos.mpr hsq)
    have hcomp : (u₀ ^ 2 - k ^ 2) * (v₀ ^ 2 + 2 * s) < 0 := by nlinarith
    by_contra hn
    have hh : 0 ≤ u₀ ^ 2 - k ^ 2 := by nlinarith [le_of_not_gt hn]
    exact (not_lt_of_ge (mul_nonneg hh hden.le)) hcomp
  exact ⟨hv₁, hv₀₁, hu₀, hu₀k, hv₁sq, hu₀sq⟩

private theorem negative_edge_mem_half_band
    {s a j σ k v₀ u₀ u : ℝ} (hs : 0 < s) (hσ : σ ^ 2 = 1)
    (hv₀j : v₀ ^ 2 / 2 ≤ j) (hu₀k : u₀ ≤ k)
    (hu₀sq : u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (hu : u ∈ Icc (-u₀) u₀) :
    let z : ℝ × ℝ := (u, -(σ * v₀))
    |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j := by
  have hden : 0 < v₀ ^ 2 + 2 * s := by positivity
  have hm := (eq_div_iff hden.ne').mp hu₀sq
  have husq : u ^ 2 ≤ u₀ ^ 2 := by nlinarith [hu.1, hu.2]
  have hmul := mul_le_mul_of_nonneg_right husq hden.le
  have hσmul : σ * (-(σ * v₀)) = -v₀ := by
    rw [mul_neg, ← mul_assoc, ← pow_two, hσ, one_mul]
  dsimp only
  refine ⟨(abs_le.mpr hu).trans hu₀k, hσmul.ge, ?_, ?_⟩
  · simp only [neg_sq, mul_pow, hσ, one_mul]
    nlinarith
  · simp only [neg_sq, mul_pow, hσ, one_mul]
    have hp := mul_nonneg (sq_nonneg u) hden.le
    nlinarith

private theorem isArcBetween_image_interval {P : (ℝ × ℝ) → Schoenflies.Plane}
    {f : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (P ∘ f) (Icc a b))
    (hinj : InjOn (P ∘ f) (Icc a b)) :
    Schoenflies.IsArcBetween (P '' (f '' Icc a b)) (P (f a)) (P (f b)) := by
  have hmap : MapsTo (Schoenflies.reparam a b) (Icc (0 : ℝ) 1) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using (Schoenflies.mapsTo_reparam (a := a) (b := b))
  refine ⟨Schoenflies.subarc (P ∘ f) a b,
    hcont.comp Schoenflies.continuous_reparam.continuousOn hmap,
    Schoenflies.injOn_subarc (by simpa only [uIcc_of_le hab.le] using hinj) hab.ne, ?_,
    Schoenflies.subarc_zero, Schoenflies.subarc_one⟩
  rw [Schoenflies.subarc_image, uIcc_of_le hab.le, image_comp]

private theorem isCutPair_lower_saddle_boundary
    (P : (ℝ × ℝ) → Schoenflies.Plane) (hP : Continuous P)
    {s a j σ k v₀ v₁ u₀ : ℝ}
    (hs : 0 < s) (ha : a < 0) (hσ : σ ^ 2 = 1)
    (hk : 0 < k) (hk1 : k < 1) (hv₀ : 0 < v₀) (hv₀₁ : v₀ < v₁)
    (hv₀j : v₀ ^ 2 / 2 ≤ j) (hu₀ : 0 < u₀) (hu₀k : u₀ < k)
    (hv₁sq : v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2))
    (hu₀def : u₀ = Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s)))
    (hu₀sq : u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (hinj : InjOn P {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j})
    {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsArcBetween C (P (-k, σ * v₁)) (P (k, σ * v₁)))
    (hcontact : ∀ z : ℝ × ℝ, |z.1| ≤ k → -v₀ ≤ σ * z.2 →
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j →
      P z ∈ C → z = (-k, σ * v₁) ∨ z = (k, σ * v₁)) :
    let N := P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀)
    let Bottom := ((P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁)) ∪ C ∪
          (P '' (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁)))
    Schoenflies.IsCutPair (N ∪ Bottom) (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀))) N Bottom := by
  let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
    a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
    (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
  have haj : a ≤ j := by nlinarith [sq_nonneg v₀]
  have hτleft : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have hτright : (1 : ℝ) ^ 2 = 1 := by norm_num
  have harm (τ : ℝ) (hτ : τ ^ 2 = 1) (v : ℝ) (hv : v ∈ Icc (-v₀) v₁) :
      lowerSaddleArm s a τ σ v ∈ R :=
    lowerSaddleArm_mem_half_band hs ha hτ hσ hk.le hk1 hv₀₁.le hv₁sq haj hv
  have hedge (u : ℝ) (hu : u ∈ Icc (-u₀) u₀) : (u, -(σ * v₀)) ∈ R :=
    negative_edge_mem_half_band hs hσ hv₀j hu₀k.le hu₀sq hu
  have hbottom (τ : ℝ) : lowerSaddleArm s a τ σ (-v₀) = (τ * u₀, -(σ * v₀)) := by
    simp only [lowerSaddleArm, neg_sq, mul_neg, hu₀def]
  have htop (τ : ℝ) : lowerSaddleArm s a τ σ v₁ = (τ * k, σ * v₁) :=
    lowerSaddleArm_right_endpoint hs hk.le hk1 hv₁sq
  have hArc (τ : ℝ) (hτ : τ ^ 2 = 1) :
      Schoenflies.IsArcBetween (P '' (lowerSaddleArm s a τ σ '' Icc (-v₀) v₁))
        (P (τ * u₀, -(σ * v₀))) (P (τ * k, σ * v₁)) := by
    have hp := lowerSaddleArm_properties hs ha hτ hσ
    have hh := isArcBetween_image_interval (show -v₀ < v₁ by linarith)
      (hP.comp hp.1.continuous).continuousOn
      (fun v hv w hw heq => hp.2.1 (hinj (harm τ hτ v hv) (harm τ hτ w hw) heq))
    simpa only [hbottom, htop] using hh
  have hL := hArc (-1) hτleft
  have hR := hArc 1 hτright
  simp only [neg_one_mul, one_mul] at hL hR
  have hN : Schoenflies.IsArcBetween
      (P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀))
      (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀))) :=
    isArcBetween_image_interval (by linarith)
      (hP.comp (by fun_prop)).continuousOn
      (fun u hu v hv heq => congrArg Prod.fst (hinj (hedge u hu) (hedge v hv) heq))
  have hmeetLC : ∀ x ∈ P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁),
      x ∈ C → x = P (-k, σ * v₁) := by
    rintro x ⟨z, ⟨v, hv, rfl⟩, rfl⟩ hxC
    have hz := harm (-1) hτleft v hv
    rcases hcontact _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hxC with heq | heq
    · exact congrArg P heq
    · have hsign := (lowerSaddleArm_properties hs ha hτleft hσ).2.2 v |>.1
      rw [heq] at hsign
      norm_num at hsign
      linarith
  have hLC := hL.concatenate hC hmeetLC
  have hmeetRLC : ∀ x ∈ (P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁)) ∪ C,
      x ∈ P '' (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁) → x = P (k, σ * v₁) := by
    rintro x hx ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    have hz := harm 1 hτright v hv
    rcases hx with ⟨w, ⟨u, hu, rfl⟩, heq⟩ | hxC
    · have hzw := hinj (harm (-1) hτleft u hu) hz heq
      have hneg := (lowerSaddleArm_properties hs ha hτleft hσ).2.2 u |>.1
      have hpos := (lowerSaddleArm_properties hs ha hτright hσ).2.2 v |>.1
      rw [hzw] at hneg
      norm_num at hneg hpos
      linarith
    · rcases hcontact _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hxC with heq | heq
      · have hsign := (lowerSaddleArm_properties hs ha hτright hσ).2.2 v |>.1
        rw [heq] at hsign
        norm_num at hsign
        linarith
      · exact congrArg P heq
  have hB := hLC.concatenate hR.reverse hmeetRLC
  have hmeet : ∀ x ∈ P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀),
      x ∈ (P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁)) ∪ C ∪
        (P '' (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁)) →
      x = P (-u₀, -(σ * v₀)) ∨ x = P (u₀, -(σ * v₀)) := by
    rintro x ⟨z, ⟨u, hu, rfl⟩, rfl⟩ hx
    have hz := hedge u hu
    have hnotC : P (u, -(σ * v₀)) ∉ C := by
      intro hxC
      rcases hcontact _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hxC with heq | heq <;>
        have he := congrArg Prod.fst heq <;> dsimp only at he <;> linarith [hu.1, hu.2]
    have hσne : σ ≠ 0 := by intro heq; rw [heq] at hσ; norm_num at hσ
    have hmeetArm (τ : ℝ) (hτ : τ ^ 2 = 1)
        (hxA : P (u, -(σ * v₀)) ∈ P '' (lowerSaddleArm s a τ σ '' Icc (-v₀) v₁)) :
        (u, -(σ * v₀)) = (τ * u₀, -(σ * v₀)) := by
      obtain ⟨z, ⟨v, hv, rfl⟩, heq⟩ := hxA
      have hp := hinj (harm τ hτ v hv) hz heq
      have hv' : v = -v₀ := by
        have he := congrArg Prod.snd hp
        change σ * v = -(σ * v₀) at he
        rw [← mul_neg] at he
        exact mul_left_cancel₀ hσne he
      rw [hv', hbottom] at hp
      exact hp.symm
    rcases hx with (hxL | hxC) | hxR
    · exact Or.inl (congrArg P (by simpa only [neg_one_mul] using hmeetArm (-1) hτleft hxL))
    · exact (hnotC hxC).elim
    · exact Or.inr (congrArg P (by simpa only [one_mul] using hmeetArm 1 hτright hxR))
  refine ⟨hN, hB, rfl, ?_⟩
  apply Subset.antisymm
  · intro x hx
    exact (hmeet x hx.1 hx.2).elim (fun h => Or.inl h) (fun h => Or.inr h)
  · rintro x (rfl | hx)
    · exact ⟨hN.left_mem, hB.left_mem⟩
    · obtain rfl := mem_singleton_iff.mp hx
      exact ⟨hN.right_mem, hB.right_mem⟩


private theorem isArcBetween_reference_circle_compl_selected
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s t₀ σ k r : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀) (hk : 0 < k) (hk1 : k < 1)
    (hr : 0 < r)
    (hcurve : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-k) k) ⊆ G '' Metric.sphere 0 r) :
    Schoenflies.IsArcBetween
      (G '' Metric.sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-k) k))
      (B (saddleBandLevelCurve s t₀ σ (-k))) (B (saddleBandLevelCurve s t₀ σ k)) := by
  let A := B '' (saddleBandLevelCurve s t₀ σ '' Icc (-k) k)
  let p := B (saddleBandLevelCurve s t₀ σ (-k))
  let q := B (saddleBandLevelCurve s t₀ σ k)
  have hA : Schoenflies.IsArcBetween A p q :=
    PlanarJordan.isArcBetween_image_saddleBandLevelCurve B.continuous B.injective hs ht₀ hk hk1
  have hpq : p ≠ q := by
    intro heq
    have h := congrArg Prod.fst (B.injective heq)
    change -k = k at h
    linarith
  obtain ⟨A₀, A₁, hcut⟩ := Schoenflies.exists_isCutPair
    (PlanarJordan.isJordanCurve_image_sphere G.toHomeomorph 0 hr)
    (hcurve hA.left_mem) (hcurve hA.right_mem) hpq
  have hpair : ∃ D, Schoenflies.IsCutPair (G '' Metric.sphere 0 r) p q A D := by
    rcases hA.eq_fst_or_eq_snd_of_subset hcurve hcut with heq | heq
    · exact ⟨A₁, heq.symm ▸ hcut⟩
    · exact ⟨A₀, heq.symm ▸ hcut.symm⟩
  obtain ⟨D, hD⟩ := hpair
  have hopen : B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-k) k) = A \ {p, q} := by
    ext y
    constructor
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨⟨_, ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩, rfl⟩, ?_⟩
      rintro (heq | heq)
      · have h := congrArg Prod.fst (B.injective heq)
        exact hu.1.ne' h
      · have h := congrArg Prod.fst (B.injective (mem_singleton_iff.mp heq))
        exact hu.2.ne h
    · rintro ⟨⟨z, ⟨u, hu, rfl⟩, rfl⟩, hn⟩
      refine ⟨_, ⟨u, ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · apply lt_of_le_of_ne hu.1
        intro heq
        apply hn
        exact Or.inl (by rw [← heq])
      · apply lt_of_le_of_ne hu.2
        intro heq
        apply hn
        exact Or.inr (by rw [heq]; rfl)
  have heq : G '' Metric.sphere 0 r \ (A \ {p, q}) = D := by
    ext y
    constructor
    · rintro ⟨hy, hn⟩
      rcases hD.union_eq.symm ▸ hy with hA | hB
      · have hpq' : y ∈ ({p, q} : Set Schoenflies.Plane) := by
          by_contra hnot
          exact hn ⟨hA, hnot⟩
        rcases hpq' with rfl | hpq'
        · exact hD.snd.left_mem
        · exact (mem_singleton_iff.mp hpq') ▸ hD.snd.right_mem
      · exact hB
    · intro hy
      refine ⟨hD.snd_subset hy, ?_⟩
      rintro ⟨hA, hn⟩
      exact hn (hD.inter_eq ▸ ⟨hA, hy⟩)
  rw [hopen, heq]
  exact hD.snd

private theorem isCutPair_cutoff_lower_boundary
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (θ : ℝ × ℝ → ℝ)
    {s a j ℓ t₀ δ σ h k ρ r v₀ : ℝ}
    (hs : 0 < s) (ha : a < 0) (ht₀ : 0 < t₀) (ht₀δ : t₀ < δ)
    (hσ : σ ^ 2 = 1) (hk : 0 < k) (hkh : k < h) (hh1 : h < 1)
    (hak : 0 < a + s * k ^ 2) (hr : 0 < r) (hv₀ : 0 < v₀)
    (hv₀j : v₀ ^ 2 / 2 < j) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hθ : ∀ t u, k ≤ |u| → θ (t, u) = 1)
    (hcurve : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-k) k) ⊆ G '' sphere 0 r)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ b < t₀, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + b}) ⊆
          (G '' closedBall 0 r)ᶜ) :
    let q : (ℝ × ℝ) → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-k) k)
    let S := ((fun z => ((T (B z, ℓ + q z)).1, q z)) '' R) ∪ C ×ˢ Icc a j
    let P : (ℝ × ℝ) → Schoenflies.Plane := fun z => (Q (T (B z, ℓ + q z))).1
    let v₁ := Real.sqrt (2 * (a + s * k ^ 2) / (1 - k ^ 2))
    let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (∀ z ∈ R, |z.1| = k → 0 < σ * z.2) →
    (∀ z ∈ R, T (B z, ℓ + q z) =
      (B (saddleBandCurve z (θ (q z, z.1) * (t₀ - q z))), ℓ + q z)) →
    (∀ z ∈ R, -v₀ ≤ σ * (B.symm (T (B z, ℓ + q z)).1).2) →
    (∀ z ∈ R, (1 - (B.symm (T (B z, ℓ + q z)).1).1 ^ 2) *
      ((B.symm (T (B z, ℓ + q z)).1).2 ^ 2 + 2 * s) / 2 ≤ s + t₀) →
    InjOn (fun p : Schoenflies.Plane × ℝ => (Q (p.1, ℓ + p.2)).1) S →
    let N := P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀)
    let Bottom := ((P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁)) ∪
          ((fun y => (Q (y, ℓ + a)).1) '' C) ∪
          (P '' (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁)))
    Schoenflies.IsCutPair (N ∪ Bottom) (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀))) N Bottom := by
  intro q R C S P v₁ u₀ hside hmodel hbottom henergy hproj
  have hk1 : k < 1 := hkh.trans hh1
  have haj : a ≤ j := by nlinarith [sq_nonneg v₀]
  have hparams := lower_saddle_boundary_parameters hs ha hσ hk hk1 hak hv₀ hv₀j
    (fun z hz hv ha hj heq => hside z ⟨hz, hv, ha, hj⟩ heq)
  change 0 < v₁ ∧ v₀ < v₁ ∧ 0 < u₀ ∧ u₀ < k ∧
    v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2) ∧
      u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s) at hparams
  obtain ⟨hv₁, hv₀₁, hu₀, hu₀k, hv₁sq, hu₀sq⟩ := hparams
  let f : (ℝ × ℝ) → Schoenflies.Plane × ℝ := fun z => ((T (B z, ℓ + q z)).1, q z)
  let H : Schoenflies.Plane → Schoenflies.Plane := fun y => (Q (y, ℓ + a)).1
  have hfS {z : ℝ × ℝ} (hz : z ∈ R) : f z ∈ S := Or.inl ⟨z, hz, rfl⟩
  have hcS {y : Schoenflies.Plane} (hy : y ∈ C) : (y, a) ∈ S :=
    Or.inr ⟨hy, le_rfl, haj⟩
  have hheight {z : ℝ × ℝ} (hz : z ∈ R) : (T (B z, ℓ + q z)).2 = ℓ + q z := by
    rw [hmodel z hz]
  have hP {z : ℝ × ℝ} (hz : z ∈ R) : P z = (Q ((f z).1, ℓ + (f z).2)).1 := by
    apply congrArg (fun p : Schoenflies.Plane × ℝ => (Q p).1)
    exact Prod.ext rfl (hheight hz)
  have hinj : InjOn P R := by
    intro z hz w hw heq
    have hf := hproj (hfS hz) (hfS hw) ((hP hz).symm.trans (heq.trans (hP hw)))
    have ht : T (B z, ℓ + q z) = T (B w, ℓ + q w) := by
      apply Prod.ext
      · change (f z).1 = (f w).1
        exact congrArg Prod.fst hf
      · rw [hheight hz, hheight hw]
        exact congrArg (fun x : ℝ => ℓ + x) (congrArg Prod.snd hf)
    exact B.injective (congrArg Prod.fst (T.injective ht))
  have hHinj : InjOn H C := by
    intro y hy z hz heq
    exact congrArg Prod.fst (hproj (hcS hy) (hcS hz) heq)
  have hH : Continuous H := (Q.continuous.comp (continuous_id.prodMk continuous_const)).fst
  have hC := isArcBetween_reference_circle_compl_selected B G hs.le ht₀ hk hk1 hr hcurve
  have hHC := hC.image_of_injOn Subset.rfl hH.continuousOn hHinj
  have hend (τ : ℝ) (hτ : τ = -1 ∨ τ = 1) :
      H (B (saddleBandLevelCurve s t₀ σ (τ * k))) = P (τ * k, σ * v₁) := by
    have hτsq : τ ^ 2 = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have habsτ : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have htop := lowerSaddleArm_right_endpoint (τ := τ) (σ := σ) hs hk.le hk1 hv₁sq
    have hz : (τ * k, σ * v₁) ∈ R := by
      rw [← htop]
      exact lowerSaddleArm_mem_half_band hs ha hτsq hσ hk.le hk1 hv₀₁.le hv₁sq haj
        ⟨by linarith, le_rfl⟩
    have hqa : q (τ * k, σ * v₁) = a := by
      rw [← htop]
      exact (lowerSaddleArm_properties hs ha hτsq hσ).2.2 v₁ |>.2.2
    have hunit : τ * k ∈ Ioo (-1 : ℝ) 1 := by
      rcases hτ with rfl | rfl <;> constructor <;> simp only [neg_one_mul, one_mul] <;> linarith
    have hcur : saddleBandLevelCurve s a σ (τ * k) = (τ * k, σ * v₁) := by
      simp only [saddleBandLevelCurve, mul_pow, hτsq, one_mul]
      rfl
    have hrad : 0 < a + s * (τ * k) ^ 2 := by simpa only [mul_pow, hτsq, one_mul] using hak
    have hshift := saddleBandCurve_saddleBandLevelCurve hrad
      (add_pos_of_pos_of_nonneg ht₀ (mul_nonneg hs.le (sq_nonneg (τ * k)))).le hσ hunit
    rw [hcur] at hshift
    dsimp only [P, H]
    rw [hmodel _ hz, hqa, hθ a (τ * k) (by simp only [abs_mul, habsτ, one_mul, abs_of_pos hk, le_refl]),
      one_mul, hshift]
  have hCactual : Schoenflies.IsArcBetween (H '' C) (P (-k, σ * v₁)) (P (k, σ * v₁)) := by
    have hl := hend (-1) (Or.inl rfl)
    have hr := hend 1 (Or.inr rfl)
    simp only [neg_one_mul, one_mul] at hl hr
    simpa only [hl, hr] using hHC
  let E : Set (ℝ × ℝ) := (fun z => B.symm (T (B z, ℓ + q z)).1) '' R
  have hcoord (z : ℝ × ℝ) (hz : z ∈ R) :
      (B.symm (T (B z, ℓ + q z)).1).1 = z.1 := by
    rw [hmodel z hz, B.symm_apply_apply]
    rfl
  have hcapInter := saddle_lower_band_inter_cap_circle_subset B G hs.le ht₀ ht₀δ hσ hh1 hkh
    hv₀.le hv₀t hupper hclear (K := E)
    (by rintro z ⟨w, hw, rfl⟩; rw [hcoord w hw]; exact hw.1)
    (by rintro z ⟨w, hw, rfl⟩; exact hbottom w hw)
    (by rintro z ⟨w, hw, rfl⟩; exact henergy w hw)
  have hcontact : ∀ z : ℝ × ℝ, |z.1| ≤ k → -v₀ ≤ σ * z.2 →
      a ≤ q z → q z ≤ j → P z ∈ H '' C →
        z = (-k, σ * v₁) ∨ z = (k, σ * v₁) := by
    intro z hzwidth hzbottom hzlower hzupper hzC
    have hz : z ∈ R := ⟨hzwidth, hzbottom, hzlower, hzupper⟩
    obtain ⟨y, hy, heq⟩ := hzC
    have hfeq := hproj (hfS hz) (hcS hy) ((hP hz).symm.trans heq.symm)
    have hfy : (T (B z, ℓ + q z)).1 = y := congrArg Prod.fst hfeq
    have hqa : q z = a := congrArg Prod.snd hfeq
    have hyE : y ∈ B '' E := by
      refine ⟨B.symm y, ?_, B.apply_symm_apply y⟩
      exact ⟨z, hz, congrArg B.symm hfy⟩
    obtain ⟨w, ⟨u, hu, huw⟩, hwy⟩ := hcapInter ⟨hyE, hy.1⟩
    have huy : B (saddleBandLevelCurve s t₀ σ u) = y := by rw [huw]; exact hwy
    have hzu : z.1 = u := by
      have he : B.symm y = saddleBandLevelCurve s t₀ σ u := by rw [← huy, B.symm_apply_apply]
      have hc := hcoord z hz
      rw [hfy, he] at hc
      exact hc.symm
    have hn : u ∉ Ioo (-k) k := by
      intro huopen
      exact hy.2 ⟨_, ⟨u, huopen, rfl⟩, huy⟩
    have huend : u = -k ∨ u = k := by
      by_cases hl : u = -k
      · exact Or.inl hl
      · right
        by_contra hr
        exact hn ⟨lt_of_le_of_ne hu.1 (Ne.symm hl), lt_of_le_of_ne hu.2 hr⟩
    have hwidth : |z.1| = k := by
      rw [hzu]
      rcases huend with rfl | rfl <;> simp only [abs_neg, abs_of_pos hk]
    have hpos := hside z hz hwidth
    have hunit : z.1 ∈ Ioo (-1 : ℝ) 1 := by
      have hh := abs_le.mp hzwidth
      constructor <;> linarith [hh.1, hh.2]
    have hden : 1 - z.1 ^ 2 ≠ 0 := by nlinarith [hunit.1, hunit.2]
    have hcur := saddleBandCurve_eq_saddleBandLevelCurve (s := s) (t := 0) hσ hden hpos (by simp)
    simp only [saddleBandCurve_zero, add_zero] at hcur
    change z = saddleBandLevelCurve s (q z) σ z.1 at hcur
    rw [hqa, hzu] at hcur
    rcases huend with rfl | rfl
    · left
      simpa only [saddleBandLevelCurve, neg_sq] using hcur
    · right
      exact hcur
  exact isCutPair_lower_saddle_boundary P (by dsimp only [P, q]; fun_prop)
    hs ha hσ hk hk1 hv₀ hv₀₁ hv₀j.le hu₀ hu₀k hv₁sq rfl hu₀sq hinj
    hCactual hcontact

private theorem saddle_half_band_lower_faces
    {s a j σ k v₀ v₁ u₀ : ℝ} (hs : 0 < s) (ha : a < 0) (hσ : σ ^ 2 = 1)
    (hv₁ : 0 ≤ v₁) (hu₀ : 0 ≤ u₀)
    (hv₁sq : v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2))
    (hu₀sq : u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (hk : 0 ≤ k) (hk1 : k < 1)
    {z : ℝ × ℝ}
    (hz : |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j)
    : ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = a →
      z ∈ (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁) ∪
        (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁)) ∧
      (σ * z.2 = -v₀ → z ∈ (fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀) := by
  have hσmul : σ * (σ * z.2) = z.2 := by rw [← mul_assoc, ← pow_two, hσ, one_mul]
  constructor
  · intro hlevel
    have hden : 0 < (σ * z.2) ^ 2 + 2 * s := by positivity
    have hratio : ((σ * z.2) ^ 2 - 2 * a) / ((σ * z.2) ^ 2 + 2 * s) = z.1 ^ 2 := by
      apply (div_eq_iff hden.ne').mpr
      simp only [mul_pow, hσ, one_mul]
      nlinarith
    have hwidth : (σ * z.2) ^ 2 ≤ v₁ ^ 2 := by
      rw [hv₁sq]
      apply (lowerSaddleArm_width_iff hs ha (σ := σ) (τ := 1) (by norm_num) hk hk1).mp
      simpa only [lowerSaddleArm, one_mul, hratio, Real.sqrt_sq_eq_abs, abs_abs] using hz.1
    have hv : σ * z.2 ∈ Icc (-v₀) v₁ := ⟨hz.2.1, by nlinarith⟩
    by_cases hu : z.1 < 0
    · left
      refine ⟨σ * z.2, hv, ?_⟩
      simp only [lowerSaddleArm, hratio, Real.sqrt_sq_eq_abs, abs_of_neg hu, neg_mul,
        one_mul, neg_neg, hσmul]
    · right
      refine ⟨σ * z.2, hv, ?_⟩
      simp only [lowerSaddleArm, hratio, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (le_of_not_gt hu), one_mul, hσmul]
  · intro hnegative
    have hv : z.2 = -(σ * v₀) := by
      have he := congrArg (σ * ·) hnegative
      rw [hσmul, mul_neg] at he
      exact he
    have hden : 0 < v₀ ^ 2 + 2 * s := by positivity
    have hm := (eq_div_iff hden.ne').mp hu₀sq
    have hl := hz.2.2.1
    rw [hv] at hl
    simp only [neg_sq, mul_pow, hσ, one_mul] at hl
    have hsq : z.1 ^ 2 ≤ u₀ ^ 2 := by
      by_contra hn
      have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hden
      nlinarith
    refine ⟨z.1, ⟨by nlinarith, by nlinarith⟩, ?_⟩
    exact Prod.ext rfl hv.symm

private theorem actual_lower_boundary_application
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (θ : ℝ × ℝ → ℝ) {V : Set (ℝ × (ℝ × ℝ))}
    {c s h ε d t₀ δ j σ ρ r v₀ : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1) (hε : 0 < ε)
    (hεh : ε < s * h ^ 2 / 16) (ht₀ : 0 < t₀) (ht₀δ : t₀ < δ)
    (ht₀d : t₀ < d) (hj : j ∈ Ioo (t₀ / 2) t₀)
    (hσ : σ ^ 2 = 1) (hr : 0 < r) (hv₀ : 0 < v₀) (hv₀t : v₀ ^ 2 / 2 < t₀ / 4)
    (hθ01 : ∀ q, 0 ≤ θ q ∧ θ q ≤ 1)
    (hθ1 : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    (hcurve : ∀ u ∈ Ioo (-h) h, B (saddleBandLevelCurve s t₀ σ u) ∈ G '' sphere 0 r)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ b < t₀, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + b}) ⊆
          (G '' closedBall 0 r)ᶜ)
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hVreg : ∀ q ∈ V, θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
      (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (t₀ - q.1)) / q.2.2 ^ 2))
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1)) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))
    let S := ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ C ×ˢ Icc (-ε / 2) j
    let P : (ℝ × ℝ) → Schoenflies.Plane := fun z =>
      (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
    let v₁ := Real.sqrt (2 * (-ε / 2 + s * (5 * h / 8) ^ 2) / (1 - (5 * h / 8) ^ 2))
    let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * (-ε / 2)) / (v₀ ^ 2 + 2 * s))
    (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) →
    (∀ p ∈ J '' R, -v₀ ≤ σ * p.1.2) →
    InjOn (fun q : Schoenflies.Plane × ℝ => (Q (q.1, c + s + q.2)).1) S →
    let N := P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀)
    let Bottom := ((P '' (lowerSaddleArm s (-ε / 2) (-1) σ '' Icc (-v₀) v₁)) ∪
          ((fun y => (Q (y, c + s + (-ε / 2))).1) '' C) ∪
          (P '' (lowerSaddleArm s (-ε / 2) 1 σ '' Icc (-v₀) v₁)))
    Schoenflies.IsCutPair (N ∪ Bottom) (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀))) N Bottom := by
  intro R J C S P v₁ u₀ hside hbottom hproj
  have hcertificate := saddle_cutoff_half_band_coordinates_and_height B T hh.le hε.le
    (hj.2.trans ht₀d).le hj.2.le (fun q => (hθ01 q).2) hKV hVreg hTmodel
    (v₀ := v₀) (σ := σ)
  have hc (u v : ℝ) :
      c + s + ((1 - u ^ 2) * (v ^ 2 + 2 * s) / 2 - s) =
        c + (1 - u ^ 2) * (v ^ 2 + 2 * s) / 2 := by ring
  have hmodel (z : ℝ × ℝ) (hz : z ∈ R) :
      T (B z, c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) =
        (B (saddleBandCurve z
          (θ (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z.1) *
            (t₀ - ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))),
          c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) := by
    apply hTmodel (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z)
    exact hKV ⟨⟨by linarith [hz.2.2.1], hz.2.2.2.trans (hj.2.trans ht₀d).le⟩,
      hz.1.trans (by linarith), by ring⟩
  have hS : ((fun z : ℝ × ℝ =>
      ((T (B z, c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) '' R) ∪ C ×ˢ Icc (-ε / 2) j = S := by
    change _ = ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ _
    rw [image_image]
    congr 1
    apply image_congr
    intro z _
    simp only [J, B.apply_symm_apply, hc]
  have h := isCutPair_cutoff_lower_boundary B G T Q θ hs (by linarith) ht₀ ht₀δ hσ
    (k := 5 * h / 8) (a := -ε / 2) (j := j) (ℓ := c + s)
    (by positivity) (by linarith) hh1
    (by nlinarith [mul_pos hs (sq_pos_of_pos hh)]) hr hv₀ (by linarith [hj.1]) (by linarith)
    (fun t u hu => hθ1 t u (by linarith))
    (by rintro _ ⟨z, ⟨u, hu, rfl⟩, rfl⟩; exact hcurve u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    hupper hclear hside hmodel
    (fun z hz => by simpa only [hc] using hbottom (J z) ⟨z, hz, rfl⟩)
    (fun z hz => by simpa only [hc] using (hcertificate z hz).2)
    (hS ▸ hproj)
  simpa only [hc] using h

private theorem image_interior_subset_interior_image_of_partialDiffeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    {R : Set E} (hR : R ⊆ χ.source) :
    χ '' interior R ⊆ interior (χ '' R) := by
  have hopen : IsOpen (χ '' interior R) :=
    χ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
      (interior_subset.trans hR)
  exact interior_maximal (image_mono interior_subset) hopen

private theorem source_projection_interior
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : E ≃ₘ[ℝ] F) (T Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {U : Set E} (hU : IsOpen U)
    {S : Set (F × ℝ)} (hsource : ∀ z ∈ U, T (B z, q z) ∈ S)
    {g : F → ℝ} {O : Set F} (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g O)
    {W : Set (F × ℝ)} (hW : IsOpen W) (hWO : W ⊆ {p | p.1 ∈ O})
    (hgraph : W ∩ Q '' S = W ∩ {p | p.2 = g p.1})
    {R : Set E} (hRU : R ⊆ U) (hRW : (fun z => Q (T (B z, q z))) '' R ⊆ W) :
    (fun z => (Q (T (B z, q z))).1) '' interior R ⊆
      interior ((fun z => (Q (T (B z, q z))).1) '' R) := by
  obtain ⟨χ, hχsource, hχ, _⟩ :=
    exists_partialDiffeomorph_projection_of_graph_neighborhood B (T.trans Q) hq hU hO hg hW hWO
      (fun z hz hzw => by
        have hw : Q (T (B z, q z)) ∈ W ∩ Q '' S :=
          ⟨hzw, mem_image_of_mem Q (hsource z hz)⟩
        rw [hgraph] at hw
        exact hw.2)
  have hRχ : R ⊆ χ.source := by
    rw [hχsource]
    exact fun z hz => ⟨hRU hz, hRW (mem_image_of_mem _ hz)⟩
  simpa only [hχ, Diffeomorph.coe_trans, Function.comp_apply] using
    image_interior_subset_interior_image_of_partialDiffeomorph χ hRχ

private theorem saddle_half_band_strict_subset_interior {s a j σ k v₀ : ℝ} :
    {z : ℝ × ℝ | |z.1| < k ∧ -v₀ < σ * z.2 ∧
      a < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s < j} ⊆
    interior {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j} := by
  apply interior_maximal
  · exact fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩
  · have hc : Continuous (fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) := by
      fun_prop
    exact (isOpen_lt continuous_fst.abs continuous_const).inter
      ((isOpen_lt continuous_const (continuous_const.mul continuous_snd)).inter
        ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)))

private theorem saddle_half_band_boundary_faces {s a j σ k v₀ : ℝ}
    {z : ℝ × ℝ}
    (hz : |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j)
    (hn : z ∉ interior {w : ℝ × ℝ | |w.1| ≤ k ∧ -v₀ ≤ σ * w.2 ∧
      a ≤ (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2 - s ≤ j}) :
    |z.1| = k ∨ σ * z.2 = -v₀ ∨
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = a ∨
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = j := by
  by_contra h
  push Not at h
  apply hn
  apply saddle_half_band_strict_subset_interior
  exact ⟨lt_of_le_of_ne hz.1 h.1,
    lt_of_le_of_ne hz.2.1 h.2.1.symm, lt_of_le_of_ne hz.2.2.1 h.2.2.1.symm,
    lt_of_le_of_ne hz.2.2.2 h.2.2.2⟩

private theorem actual_source_projection_interior {M : Type*} (e : M → Schoenflies.Plane × ℝ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {c s : ℝ}
    (hgraph : ∀ z ∈ U, e (β z) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hTheight : ∀ q, (T q).2 = q.2) {R : Set (ℝ × ℝ)}
    (hRU : R ⊆ U) (hzeroR : (0, 0) ∈ interior R)
    {C : Set Schoenflies.Plane} {a j : ℝ} {Ucap : Set (Schoenflies.Plane × ℝ)}
    {OQ : Set Schoenflies.Plane} (hOQ : IsOpen OQ)
    {gQ : Schoenflies.Plane → ℝ} (hgQ : ContDiffOn ℝ ∞ gQ OQ)
    {WQ : Set (Schoenflies.Plane × ℝ)} (hWQ : IsOpen WQ)
    (hWQO : WQ ⊆ {q | q.1 ∈ OQ})
    (hWQeq : WQ ∩ Q '' range (T ∘ e) = WQ ∩ {q | q.2 = gQ q.1}) :
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let S : Set (Schoenflies.Plane × ℝ) :=
      ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ C ×ˢ Icc a j
    let K := ((fun q : Schoenflies.Plane × ℝ => (q.1, c + s + q.2)) '' S) ∪ Ucap
    let P := fun z : ℝ × ℝ => (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
    Q '' K ⊆ WQ →
      P '' interior R ⊆ interior (Prod.fst '' (Q '' K)) ∧
      (interior (Prod.fst '' (Q '' K))).Nonempty := by
  intro J S K P hKWQ
  let q : (ℝ × ℝ) → ℝ := fun z => c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have hsource (z : ℝ × ℝ) (hz : z ∈ U) : T (B z, q z) ∈ range (T ∘ e) := by
    refine ⟨β z, ?_⟩
    change T (e (β z)) = T (B z, q z)
    rw [hgraph z hz]
  have hraw (z : ℝ × ℝ) (hz : z ∈ R) : T (B z, q z) ∈ K := by
    apply Or.inl
    refine ⟨(B (J z).1, (J z).2), Or.inl ⟨J z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
    apply Prod.ext
    · exact B.apply_symm_apply _
    · change c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) = (T (B z, q z)).2
      rw [hTheight]
      dsimp only [q]
      ring
  have hRW : (fun z => Q (T (B z, q z))) '' R ⊆ WQ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hKWQ (mem_image_of_mem Q (hraw z hz))
  have hPint := source_projection_interior B T Q hq hU hsource hOQ hgQ hWQ hWQO hWQeq hRU hRW
  have hPK : P '' R ⊆ Prod.fst '' (Q '' K) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨Q (T (B z, q z)), mem_image_of_mem Q (hraw z hz), rfl⟩
  have hfinal : P '' interior R ⊆ interior (Prod.fst '' (Q '' K)) :=
    hPint.trans (interior_mono hPK)
  exact ⟨hfinal, ⟨P (0, 0), hfinal (mem_image_of_mem P hzeroR)⟩⟩

private theorem actual_reference_cylinder_application
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (T : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {s c h ε j v₀ σ d τ : ℝ} {C : Set F}
    (hs : 0 ≤ s) (hh : 0 < h) (hh1 : h < 1) (hτ : 0 < τ)
    (hv₀ : 0 ≤ v₀) (hσ : σ ^ 2 = 1) (hε : 0 < ε)
    (hεh : ε < s * h ^ 2 / 16) (hjd : j ≤ d)
    {θ : ℝ × ℝ → ℝ}
    (hθ : ∀ t u, τ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1)
    {V : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (τ - q.1))), c + s + q.1)) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let S := ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪
      (C \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc (-ε / 2) j
    {p : F × ℝ | p.1 ∈ C ∧ p.2 ∈ Icc (-ε / 2) j ∧
      (τ / 2 ≤ p.2 ∨ p.1 ∉ B '' (saddleBandLevelCurve s τ σ '' Icc (-(h / 2)) (h / 2)))} ⊆ S := by
  intro R J S
  have hmodel : ∀ z : ℝ × ℝ, |z.1| ≤ 5 * h / 8 → -v₀ ≤ σ * z.2 →
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j →
      T (B z, c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) =
        (B (saddleBandCurve z (θ (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z.1) *
          (τ - ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))),
          c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) := by
    intro z hz _ hza hzj
    apply hTmodel (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z)
    exact hKV ⟨⟨by linarith only [hza, hε], hzj.trans hjd⟩,
      hz.trans (by linarith only [hh]), by ring⟩
  have hsub := reference_cylinder_subset_image_saddle_cutoff_half_band (B : (ℝ × ℝ) → F) (T : F × ℝ → F × ℝ) hs hh.le hτ
    (k := 5 * h / 8) (by linarith only [hh, hh1]) hv₀ hσ hεh hθ hmodel (C := C)
  have hS : S =
      ((fun z : ℝ × ℝ =>
        ((T (B z, c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1,
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) '' R) ∪
        (C \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))) ×ˢ Icc (-ε / 2) j := by
    dsimp only [S]
    rw [image_image]
    congr 1
    apply image_congr
    intro z _
    dsimp only [J, Function.comp_apply]
    rw [B.apply_symm_apply]
    rw [show c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) =
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 by ring]
  rw [hS]
  exact hsub

private theorem frontier_projection_saddle_patch_subset
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ)) (ψ : ℝ ≃ ℝ)
    {s τ σ h k v₀ a j ℓ b m r : ℝ}
    (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hh1 : h < 1)
    (hk : h / 2 < k) (hkh : k < h) (ha : a < 0) (hj : j ∈ Ioo (τ / 2) τ)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ) (hbaseb : ℓ + τ < b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    {Ucap : Set (Schoenflies.Plane × ℝ)}
    (hQcap : Q '' Ucap = {z : Schoenflies.Plane × ℝ | b ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2})
    (hcurve : ∀ u ∈ Ioo (-h) h, B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ} {κ A : ℝ → ℝ}
    (hκ : ∀ u, h / 2 ≤ |u| → κ u = 0) (hAj : A j = 0) :
    let q := fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R := {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-k) k)
    let S := ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ C ×ˢ Icc a j
    let K := ((fun p : Schoenflies.Plane × ℝ => (p.1, ℓ + p.2)) '' S) ∪
      ((G '' sphere 0 r) ×ˢ Icc (ℓ + j) b ∪ Ucap)
    let P := fun z : ℝ × ℝ => (Q (B (J z).1, ℓ + (J z).2)).1
    let Y := (fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K
    IsCompact K →
    (∀ z ∈ R, (J z).1.1 = z.1 ∧ (J z).2 = q z ∧ -v₀ ≤ σ * (J z).1.2 ∧
      (1 - (J z).1.1 ^ 2) * ((J z).1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ (J z).1.1 * A (q z) = 0) →
    ({p : Schoenflies.Plane × ℝ | p.1 ∈ G '' sphere 0 r ∧ p.2 ∈ Icc a j ∧
      (τ / 2 ≤ p.2 ∨ p.1 ∉ B '' (saddleBandLevelCurve s τ σ '' Icc (-(h / 2)) (h / 2)))} ⊆ S) →
    P '' interior R ⊆ interior Y →
    frontier Y ⊆
      P '' {z ∈ R | q z = a ∨ σ * z.2 = -v₀} ∪
        (fun y => (Q (y, ℓ + a)).1) '' C := by
  intro q R C S K P Y hK hJ hwall hinner
  let C₀ := G '' sphere 0 r
  let A₀ := B '' (saddleBandLevelCurve s τ σ '' Icc (-(h / 2)) (h / 2))
  have hA₀ : IsClosed A₀ :=
    ((isCompact_Icc.image_of_continuousOn
      ((contDiffOn_saddleBandLevelCurve hs hτ σ).continuousOn.mono
        (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩))).image B.continuous).isClosed
  have hCsub : C ⊆ C₀ \ A₀ := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
    exact hy.2 ⟨_, ⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩, heq⟩
  have hlow : (C₀ \ A₀) ×ˢ Ioo (ℓ + a) (ℓ + j) ⊆ K := by
    intro z hz
    refine Or.inl ⟨(z.1, z.2 - ℓ), ?_, by ext <;> simp⟩
    apply hwall
    exact ⟨hz.1.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩, Or.inr hz.1.2⟩
  have hlowOpen : IsOpen ((fun p : Schoenflies.Plane × ℝ => (Q p).1) ''
      ((C₀ \ A₀) ×ˢ Ioo (ℓ + a) (ℓ + j))) :=
    Diffeomorph.isOpen_image_projection_reference_cylinder Q G.toEquiv ψ
      (by linarith [hj.2]) hbm hr hrsq hψ hψb hQfull hA₀
  have hlowInterior : (fun p : Schoenflies.Plane × ℝ => (Q p).1) ''
      ((C₀ \ A₀) ×ˢ Ioo (ℓ + a) (ℓ + j)) ⊆ interior Y :=
    interior_maximal (image_mono hlow) hlowOpen
  let j' := (τ / 2 + j) / 2
  have hj' : τ / 2 < j' ∧ j' < j := by dsimp only [j']; constructor <;> linarith [hj.1]
  have hhigh : (C₀ ×ˢ Icc (ℓ + j') b) ∪ Ucap ⊆ K := by
    rintro z (hz | hz)
    · by_cases hzt : ℓ + j ≤ z.2
      · exact Or.inr (Or.inl ⟨hz.1, hzt, hz.2.2⟩)
      · refine Or.inl ⟨(z.1, z.2 - ℓ), ?_, by ext <;> simp⟩
        apply hwall
        exact ⟨hz.1, ⟨by linarith [hz.2.1, hj'.1], by linarith [not_le.mp hzt]⟩,
          Or.inl (by linarith [hz.2.1, hj'.1])⟩
    · exact Or.inr (Or.inr hz)
  have hhighImage := Diffeomorph.image_reference_cylinder_union_cap Q G.toEquiv ψ hbm hr hrsq
    (j := ℓ + j') (by linarith [hj'.2, hj.2]) hψ hψb hQfull hQcap
  have hopenCap : IsOpen {y : Schoenflies.Plane | ψ (ℓ + j') < m - ‖y‖ ^ 2 / 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have hcapInterior : {y : Schoenflies.Plane | ψ (ℓ + j') < m - ‖y‖ ^ 2 / 2} ⊆ interior Y := by
    apply interior_maximal _ hopenCap
    intro y hy
    obtain ⟨z, hz, heq⟩ := hhighImage.symm.subset
      (show (y, m - ‖y‖ ^ 2 / 2) ∈ {p : Schoenflies.Plane × ℝ |
        ψ (ℓ + j') ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2} from ⟨hy.le, rfl⟩)
    exact ⟨z, hhigh hz, congrArg Prod.fst heq⟩
  have hcapPoint (z : Schoenflies.Plane × ℝ)
      (hz : z ∈ C₀ ×ˢ Icc (ℓ + j) b ∪ Ucap) : (Q z).1 ∈ interior Y := by
    have himage := Diffeomorph.image_reference_cylinder_union_cap Q G.toEquiv ψ hbm hr hrsq
      (j := ℓ + j) (by linarith [hj.2]) hψ hψb hQfull hQcap
    have hp := himage.subset (mem_image_of_mem Q hz)
    apply hcapInterior
    change ψ (ℓ + j') < m - ‖(Q z).1‖ ^ 2 / 2
    rw [← hp.2]
    exact (hψ (by linarith [hj'.2])).trans_le hp.1
  have hseam (z : ℝ × ℝ) (hz : z ∈ R) (hf : |z.1| = k ∨ q z = j) :
      (J z).1 = saddleBandLevelCurve s τ σ z.1 := by
    have he := (hJ z hz).2.2.2
    have hzκ : κ (J z).1.1 * A (q z) = 0 := by
      rcases hf with hw | ht
      · rw [hκ _ (by rw [(hJ z hz).1, hw]; exact hk.le), zero_mul]
      · rw [ht, hAj, mul_zero]
    rw [hzκ, add_zero] at he
    have hroot := eq_saddleBandLevelCurve_of_height_eq_of_lower_bound hs hσ hv₀ hv₀τ
      (hJ z hz).2.2.1 (by linarith only [he])
    simpa only [(hJ z hz).1] using hroot
  have hseamCircle (z : ℝ × ℝ) (hz : z ∈ R) (hf : |z.1| = k ∨ q z = j) :
      B (J z).1 ∈ C₀ := by
    rw [hseam z hz hf]
    exact hcurve z.1 (abs_lt.mp (hz.1.trans_lt hkh))
  have hseamInterior (z : ℝ × ℝ) (hz : z ∈ R) (hf : |z.1| = k ∨ q z = j)
      (hza : a < q z) : P z ∈ interior Y := by
    by_cases ht : q z = j
    · apply hcapPoint (B (J z).1, ℓ + (J z).2)
      exact Or.inl ⟨hseamCircle z hz hf, by rw [(hJ z hz).2.1, ht], by
        rw [(hJ z hz).2.1, ht]; linarith [hj.2]⟩
    · have hw : |z.1| = k := hf.resolve_right ht
      apply hlowInterior
      refine ⟨(B (J z).1, ℓ + (J z).2), ⟨⟨hseamCircle z hz hf, ?_⟩, ?_⟩, rfl⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
        have heu := congrArg Prod.fst (B.injective heq)
        change u = (J z).1.1 at heu
        rw [(hJ z hz).1] at heu
        have habs : |z.1| ≤ h / 2 := by rw [← heu]; exact abs_le.mpr hu
        rw [hw] at habs
        exact (not_le_of_gt hk) habs
      · rw [(hJ z hz).2.1]
        exact ⟨by linarith, by linarith [lt_of_le_of_ne hz.2.2.2 ht]⟩
  have hYclosed : IsClosed Y := (hK.image (Q.continuous.fst)).isClosed
  intro y hy
  have hyK : y ∈ Y := hYclosed.closure_eq ▸ frontier_subset_closure hy
  have hyn : y ∉ interior Y := hy.2
  obtain ⟨z, hz, rfl⟩ := hyK
  rcases hz with ⟨w, hw, rfl⟩ | hz
  · rcases hw with ⟨_, ⟨v, hv, rfl⟩, rfl⟩ | hw
    · change P v ∈ _
      by_cases hvi : v ∈ interior R
      · exact (hyn (hinner (mem_image_of_mem P hvi))).elim
      have hf := saddle_half_band_boundary_faces hv hvi
      rcases hf with hw | hn | ha' | hj'
      · by_cases hqa : q v = a
        · exact Or.inl ⟨v, ⟨hv, Or.inl hqa⟩, rfl⟩
        · exact (hyn (hseamInterior v hv (Or.inl hw) (lt_of_le_of_ne hv.2.2.1 (fun heq => hqa heq.symm)))).elim
      · exact Or.inl ⟨v, ⟨hv, Or.inr hn⟩, rfl⟩
      · exact Or.inl ⟨v, ⟨hv, Or.inl ha'⟩, rfl⟩
      · exact (hyn (hseamInterior v hv (Or.inr hj') (by change q v = j at hj'; rw [hj']; linarith [hj.1]))).elim
    · by_cases hwa : w.2 = a
      · exact Or.inr ⟨w.1, hw.1, by dsimp only; rw [hwa]⟩
      · by_cases hwj : w.2 = j
        · exact (hyn (hcapPoint (w.1, ℓ + w.2)
            (Or.inl ⟨hw.1.1, by rw [hwj], by rw [hwj]; linarith [hj.2]⟩))).elim
        · apply False.elim
          apply hyn
          apply hlowInterior
          exact ⟨(w.1, ℓ + w.2), ⟨hCsub hw.1, by
            constructor <;> linarith [lt_of_le_of_ne hw.2.1 (fun heq => hwa heq.symm), lt_of_le_of_ne hw.2.2 hwj]⟩, rfl⟩
  · exact (hyn (hcapPoint z hz)).elim

private theorem saddle_half_band_lower_faces_eq
    {s a j σ k v₀ v₁ u₀ : ℝ} (hs : 0 < s) (ha : a < 0) (hσ : σ ^ 2 = 1)
    (hk : 0 ≤ k) (hk1 : k < 1) (hv₁ : 0 ≤ v₁) (hu₀ : 0 ≤ u₀)
    (hv₀₁ : v₀ ≤ v₁) (hv₀j : v₀ ^ 2 / 2 ≤ j) (haj : a ≤ j) (hu₀k : u₀ ≤ k)
    (hv₁sq : v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2))
    (hu₀sq : u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s)) :
    let R := {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    {z ∈ R | σ * z.2 = -v₀} = (fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀ ∧
      {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = a} =
        (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁) ∪
          (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁) := by
  intro R
  constructor
  · ext z
    constructor
    · intro hz
      exact (saddle_half_band_lower_faces hs ha hσ hv₁ hu₀ hv₁sq hu₀sq hk hk1 hz.1).2 hz.2
    · rintro ⟨u, hu, rfl⟩
      refine ⟨negative_edge_mem_half_band hs hσ hv₀j hu₀k hu₀sq hu, ?_⟩
      change σ * -(σ * v₀) = -v₀
      rw [mul_neg, ← mul_assoc, ← pow_two, hσ, one_mul]
  · ext z
    constructor
    · intro hz
      exact (saddle_half_band_lower_faces hs ha hσ hv₁ hu₀ hv₁sq hu₀sq hk hk1 hz.1).1 hz.2
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact ⟨lowerSaddleArm_mem_half_band hs ha (by norm_num) hσ hk hk1 hv₀₁ hv₁sq haj hv,
          ((lowerSaddleArm_properties hs ha (by norm_num) hσ).2.2 v).2.2⟩
      · exact ⟨lowerSaddleArm_mem_half_band hs ha (by norm_num) hσ hk hk1 hv₀₁ hv₁sq haj hv,
          ((lowerSaddleArm_properties hs ha (by norm_num) hσ).2.2 v).2.2⟩

private theorem eq_lowerSaddleArm_of_level
    {s a ξ σ : ℝ} (hs : 0 < s) (hξ : ξ ^ 2 = 1) (hσ : σ ^ 2 = 1)
    {z : ℝ × ℝ} (hsgn : 0 < ξ * z.1)
    (hq : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = a) :
    z = lowerSaddleArm s a ξ σ (σ * z.2) := by
  have hden : 0 < z.2 ^ 2 + 2 * s := by positivity
  have hratio : ((σ * z.2) ^ 2 - 2 * a) / ((σ * z.2) ^ 2 + 2 * s) = z.1 ^ 2 := by
    rw [mul_pow, hσ, one_mul]
    apply (div_eq_iff hden.ne').mpr
    nlinarith only [hq]
  have hξabs : |ξ| = 1 := by rcases sq_eq_one_iff.mp hξ with rfl | rfl <;> norm_num
  have hξu : ξ * |z.1| = z.1 := by
    have habs : |ξ * z.1| = ξ * z.1 := abs_of_pos hsgn
    rw [abs_mul, hξabs, one_mul] at habs
    rw [habs, ← mul_assoc, ← pow_two, hξ, one_mul]
  apply Prod.ext
  · simp only [lowerSaddleArm, hratio, Real.sqrt_sq_eq_abs, hξu]
  · simp only [lowerSaddleArm, ← mul_assoc, ← pow_two, hσ, one_mul]

private theorem saddle_bottom_arm_projection_has_smooth_left_inverse
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (A : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    (ψ : ℝ → ℝ) (hA : ∀ p, (A p).2 = ψ p.2)
    {s a ξ σ ell : ℝ} (hs : 0 < s) (ha : a < 0) (hξ : ξ ^ 2 = 1)
    (hσ : σ ^ 2 = 1) :
    let α : ℝ → F := fun v => (A (B (lowerSaddleArm s a ξ σ v), ell + a)).1
    let R : F → ℝ := fun y => σ * (B.symm (A.symm (y, ψ (ell + a))).1).2
    ContDiff ℝ ∞ α ∧ ContDiff ℝ ∞ R ∧ Function.LeftInverse R α ∧
      ∀ v, deriv α v ≠ 0 := by
  intro α R
  have ha₀ := (lowerSaddleArm_properties hs ha hξ hσ).1
  have hα : ContDiff ℝ ∞ α :=
    contDiff_fst.comp (A.contMDiff.contDiff.comp
      ((B.contMDiff.contDiff.comp ha₀).prodMk contDiff_const))
  have hR : ContDiff ℝ ∞ R := by
    exact contDiff_const.mul (contDiff_snd.comp (B.symm.contMDiff.contDiff.comp
      (contDiff_fst.comp (A.symm.contMDiff.contDiff.comp
        (contDiff_id.prodMk contDiff_const)))))
  have hleft : Function.LeftInverse R α := by
    intro v
    have he : (α v, ψ (ell + a)) = A (B (lowerSaddleArm s a ξ σ v), ell + a) :=
      Prod.ext rfl (hA (B (lowerSaddleArm s a ξ σ v), ell + a)).symm
    dsimp only [R]
    rw [he, A.symm_apply_apply, B.symm_apply_apply]
    exact ((lowerSaddleArm_properties hs ha hξ hσ).2.2 v).2.1
  refine ⟨hα, hR, hleft, ?_⟩
  intro v hv
  have hd := ((hR.differentiable (by simp)) (α v)).hasFDerivAt.comp_hasDerivAt v
    ((hα.differentiable (by simp)) v).hasDerivAt
  have hid : HasDerivAt (fun t => R (α t)) 1 v := by
    have he : (fun t => R (α t)) = id := funext hleft
    rw [he]
    exact hasDerivAt_id v
  have he := hd.unique hid
  rw [hv, map_zero] at he
  exact zero_ne_one he

private theorem saddle_bottom_reference_arc_seam_germ
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (ψ : ℝ → ℝ) (hQ : ∀ p, (Q p).2 = ψ p.2)
    {s a τ ξ σ ell r u₀ x₀ : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hξ : ξ ^ 2 = 1) (hσ : σ ^ 2 = 1)
    (hr : 0 < r) (hu₀ : u₀ ∈ Ioo (-1 : ℝ) 1) (hξu : 0 < ξ * u₀)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcurveV : saddleBandLevelCurve s τ σ u₀ ∈ V)
    (hside : ∀ z ∈ V, B z ∈ G '' Metric.closedBall 0 r ↔
      s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hseam : (a, u₀) ∈ O)
    (hOunit : ∀ p ∈ O, p.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < p.1 + s * p.2 ^ 2)
    (hmodel : ∀ p ∈ O, T (B (saddleBandLevelCurve s p.1 σ p.2), ell + p.1) =
      (B (saddleBandLevelCurve s τ σ p.2), ell + p.1))
    {f : ℝ → Schoenflies.Plane} (hf : Continuous f)
    (hf₀ : f x₀ = B (saddleBandLevelCurve s τ σ u₀))
    (hfC : ∀ x, f x ∈ G '' Metric.sphere 0 r) :
    let A := T.trans Q
    let α : ℝ → Schoenflies.Plane :=
      fun v => (A (B (lowerSaddleArm s a ξ σ v), ell + a)).1
    let R : Schoenflies.Plane → ℝ :=
      fun y => σ * (B.symm (A.symm (y, ψ (ell + a))).1).2
    let β : ℝ → Schoenflies.Plane := fun x => (Q (f x, ell + a)).1
    β =ᶠ[𝓝 x₀] fun x => α (R (β x)) := by
  intro A α R β
  let z : ℝ → ℝ × ℝ := fun x => B.symm (f x)
  have hz : Continuous z := B.symm.continuous.comp hf
  have hz₀ : z x₀ = saddleBandLevelCurve s τ σ u₀ := by
    dsimp only [z]
    rw [hf₀, B.symm_apply_apply]
  have hvpos : 0 < σ * (z x₀).2 := by
    rw [hz₀]
    change 0 < σ * (σ * Real.sqrt (2 * (τ + s * u₀ ^ 2) / (1 - u₀ ^ 2)))
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
    apply Real.sqrt_pos.mpr
    exact div_pos (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hτ (by positivity)))
      (by nlinarith only [hu₀.1, hu₀.2])
  have hzV : ∀ᶠ x in 𝓝 x₀, z x ∈ V := hz.continuousAt.preimage_mem_nhds
    (hV.mem_nhds (hz₀.symm ▸ hcurveV))
  have hzO : ∀ᶠ x in 𝓝 x₀, (a, (z x).1) ∈ O :=
    (continuous_const.prodMk hz.fst).continuousAt.preimage_mem_nhds
      (hO.mem_nhds (by simpa only [hz₀, saddleBandLevelCurve] using hseam))
  have hzξ : ∀ᶠ x in 𝓝 x₀, 0 < ξ * (z x).1 :=
    (continuous_const.mul hz.fst).continuousAt.eventually (Ioi_mem_nhds
      (by simpa only [Pi.mul_apply, hz₀, saddleBandLevelCurve] using hξu))
  have hzσ : ∀ᶠ x in 𝓝 x₀, 0 < σ * (z x).2 :=
    (continuous_const.mul hz.snd).continuousAt.eventually (Ioi_mem_nhds hvpos)
  filter_upwards [hzV, hzO, hzξ, hzσ] with x hxV hxO hxξ hxσ
  have hu := hOunit (a, (z x).1) hxO
  have hc : B (z x) ∈ G '' Metric.sphere 0 r := by
    simpa only [z, B.apply_symm_apply] using hfC x
  have hq := PlanarJordan.cap_circle_height_eq_on_side_neighborhood
    B.toHomeomorph G.toHomeomorph hr hV hside hxV hc
  have hzcurve : z x = saddleBandLevelCurve s τ σ (z x).1 :=
    eq_saddleBandLevelCurve_of_height_eq_of_lower_bound hs.le hσ
      (v₀ := 0) le_rfl (by nlinarith only [hτ]) (by simpa only [neg_zero] using hxσ.le) hq
  let w := saddleBandLevelCurve s a σ (z x).1
  have hwq : (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2 - s = a := by
    have he := saddleBandLevelCurve_height_of_nonneg hu.2.le hσ hu.1 (0 : ℝ)
    change (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2 - s = a
    linarith only [he]
  have hwarm : w = lowerSaddleArm s a ξ σ (σ * w.2) :=
    eq_lowerSaddleArm_of_level hs hξ hσ hxξ hwq
  have hTw : T (B w, ell + a) = (f x, ell + a) := by
    have he := hmodel (a, (z x).1) hxO
    change T (B w, ell + a) = (B (saddleBandLevelCurve s τ σ (z x).1), ell + a) at he
    rw [← hzcurve] at he
    simpa only [z, B.apply_symm_apply] using he
  have hQa : (β x, ψ (ell + a)) = Q (f x, ell + a) :=
    Prod.ext rfl (hQ (f x, ell + a)).symm
  have hAw : A (B w, ell + a) = (β x, ψ (ell + a)) := by
    change Q (T (B w, ell + a)) = _
    rw [hTw, hQa]
  have hRw : R (β x) = σ * w.2 := by
    dsimp only [R]
    rw [← hAw, A.symm_apply_apply, B.symm_apply_apply]
  dsimp only [α]
  rw [hRw, ← hwarm, hAw]

private theorem exists_smooth_parameter_saddle_bottom_boundary
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (ψ : ℝ → ℝ) (hT : ∀ p, (T p).2 = p.2) (hQ : ∀ p, (Q p).2 = ψ p.2)
    {s a τ σ ell r k v₀ v₁ : ℝ}
    (hs : 0 < s) (ha : a < 0) (hτ : 0 < τ) (hσ : σ ^ 2 = 1)
    (hr : 0 < r) (hk : 0 < k) (hk1 : k < 1) (hv₀₁ : -v₀ < v₁)
    {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsArcBetween C (B (saddleBandLevelCurve s τ σ (-k)))
      (B (saddleBandLevelCurve s τ σ k))) (hCC : C ⊆ G '' Metric.sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcurveV : ∀ ξ ∈ ({-1, 1} : Set ℝ), saddleBandLevelCurve s τ σ (ξ * k) ∈ V)
    (hside : ∀ z ∈ V, B z ∈ G '' Metric.closedBall 0 r ↔
      s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hseam : ∀ ξ ∈ ({-1, 1} : Set ℝ), (a, ξ * k) ∈ O)
    (hOunit : ∀ p ∈ O, p.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < p.1 + s * p.2 ^ 2)
    (hmodel : ∀ p ∈ O, T (B (saddleBandLevelCurve s p.1 σ p.2), ell + p.1) =
      (B (saddleBandLevelCurve s τ σ p.2), ell + p.1)) :
    let A := T.trans Q
    let α : ℝ → ℝ → Schoenflies.Plane :=
      fun ξ v => (A (B (lowerSaddleArm s a ξ σ v), ell + a)).1
    let H : Schoenflies.Plane → Schoenflies.Plane := fun y => (Q (y, ell + a)).1
    (∀ ξ ∈ ({-1, 1} : Set ℝ), H (B (saddleBandLevelCurve s τ σ (ξ * k))) = α ξ v₁) →
    (∀ ξ ∈ ({-1, 1} : Set ℝ), ∀ v ∈ Icc (-v₀) v₁, α ξ v ∈ H '' C → v = v₁) →
    ∃ g : ℝ → Schoenflies.Plane, ∃ u v : ℝ,
      u < 0 ∧ 1 < v ∧ ContDiff ℝ ∞ g ∧ (∀ t, deriv g t ≠ 0) ∧
      InjOn g (Icc u v) ∧ g u = α (-1) (-v₀) ∧ g v = α 1 (-v₀) ∧
      g '' Icc u v = α (-1) '' Icc (-v₀) v₁ ∪ H '' C ∪ α 1 '' Icc (-v₀) v₁ ∧
      (∃ D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ, StrictMono D₀ ∧ StrictAnti D₁ ∧
        D₀ u = -v₀ ∧ D₁ v = -v₀ ∧
        g =ᶠ[𝓝 u] (fun t => α (-1) (D₀ t)) ∧
        g =ᶠ[𝓝 v] (fun t => α 1 (D₁ t))) := by
  intro A α H hend hcontact
  let R : Schoenflies.Plane → ℝ := fun y =>
    σ * (B.symm (A.symm (y, ψ (ell + a))).1).2
  have hA : ∀ p, (A p).2 = ψ p.2 := by
    intro p
    change (Q (T p)).2 = ψ p.2
    rw [hQ, hT]
  have hαL := saddle_bottom_arm_projection_has_smooth_left_inverse B A ψ hA
    hs ha (by norm_num : (-1 : ℝ) ^ 2 = 1) hσ (ell := ell)
  have hαR := saddle_bottom_arm_projection_has_smooth_left_inverse B A ψ hA
    hs ha (by norm_num : (1 : ℝ) ^ 2 = 1) hσ (ell := ell)
  change ContDiff ℝ ∞ (α (-1)) ∧ ContDiff ℝ ∞ R ∧ Function.LeftInverse R (α (-1)) ∧
    (∀ v, deriv (α (-1)) v ≠ 0) at hαL
  change ContDiff ℝ ∞ (α 1) ∧ ContDiff ℝ ∞ R ∧ Function.LeftInverse R (α 1) ∧
    (∀ v, deriv (α 1) v ≠ 0) at hαR
  obtain ⟨γ, hγ, hγrange⟩ := exists_isSmoothEmbedding_addCircle_range_eq_sphere
    (E := Schoenflies.Plane) (by simp) 0 hr
  have hGγ := hγ.diffeomorph_comp G
  have hGγrange : range (G ∘ γ) = G '' Metric.sphere 0 r := by rw [range_comp, hγrange]
  obtain ⟨f, hf, hdf, hfC, hfinj, hf₀, hf₁, hfimage⟩ :=
    PlanarJordan.exists_smooth_parameter_of_arc_subset_circle hGγ hC (hGγrange.symm ▸ hCC)
  have hfC' : ∀ t, f t ∈ G '' Metric.sphere 0 r := fun t => hGγrange ▸ hfC t
  let β : ℝ → Schoenflies.Plane := H ∘ f
  have hH : ContDiff ℝ ∞ H := contDiff_fst.comp
    (Q.contMDiff.contDiff.comp (contDiff_id.prodMk contDiff_const))
  have hβ : ContDiff ℝ ∞ β := hH.comp hf
  let I : Schoenflies.Plane → Schoenflies.Plane := fun y => (Q.symm (y, ψ (ell + a))).1
  have hI : ContDiff ℝ ∞ I := contDiff_fst.comp
    (Q.symm.contMDiff.contDiff.comp (contDiff_id.prodMk contDiff_const))
  have hIH : Function.LeftInverse I H := by
    intro y
    have he : (H y, ψ (ell + a)) = Q (y, ell + a) := Prod.ext rfl (hQ (y, ell + a)).symm
    dsimp only [I]
    rw [he, Q.symm_apply_apply]
  have hβder (t : ℝ) : deriv β t ≠ 0 := by
    intro hzero
    have hd := ((hI.differentiable (by simp)) (β t)).hasFDerivAt.comp_hasDerivAt t
      ((hβ.differentiable (by simp)) t).hasDerivAt
    have he : I ∘ β = f := funext (fun t => hIH (f t))
    rw [he, hzero, map_zero] at hd
    exact hdf t hd.deriv
  have hβinj : InjOn β (Icc 0 1) := by
    intro t ht u hu he
    exact hfinj ht hu (hIH.injective he)
  have hβ₀ : β 0 = α (-1) v₁ := by
    change H (f 0) = _
    rw [hf₀]
    simpa only [neg_one_mul] using hend (-1) (by simp)
  have hβ₁ : β 1 = α 1 v₁ := by
    change H (f 1) = _
    rw [hf₁]
    simpa only [one_mul] using hend 1 (by simp)
  have hβimage : β '' Icc 0 1 = H '' C := by rw [image_comp, hfimage]
  have hgerm₀ : β =ᶠ[𝓝 0] fun t => α (-1) (R (β t)) := by
    exact saddle_bottom_reference_arc_seam_germ B G T Q ψ hQ hs hτ (by norm_num) hσ hr
      (u₀ := -k) ⟨by linarith only [hk1], by linarith only [hk]⟩
      (by simpa using hk) hV (by simpa using hcurveV (-1) (by simp)) hside hO
      (by simpa using hseam (-1) (by simp)) hOunit hmodel hf.continuous hf₀ hfC'
  have hgerm₁ : β =ᶠ[𝓝 1] fun t => α 1 (R (β t)) := by
    exact saddle_bottom_reference_arc_seam_germ B G T Q ψ hQ hs hτ (by norm_num) hσ hr
      (u₀ := k) ⟨by linarith only [hk], hk1⟩ (by simpa using hk) hV
      (by simpa using hcurveV 1 (by simp)) hside hO
      (by simpa using hseam 1 (by simp)) hOunit hmodel hf.continuous hf₁ hfC'
  have hmeet₀ : ∀ v ∈ Icc (-v₀) v₁, ∀ t ∈ Icc (0 : ℝ) 1,
      α (-1) v = β t → t = 0 := by
    intro v hv t ht heq
    have hv₁ := hcontact (-1) (by simp) v hv (heq.symm ▸ (hβimage ▸ mem_image_of_mem β ht))
    apply hβinj ht (by constructor <;> norm_num)
    rw [← heq, hv₁, hβ₀]
  have hmeet₁ : ∀ v ∈ Icc (-v₀) v₁, ∀ t ∈ Icc (0 : ℝ) 1,
      α 1 v = β t → t = 1 := by
    intro v hv t ht heq
    have hv₁ := hcontact 1 (by simp) v hv (heq.symm ▸ (hβimage ▸ mem_image_of_mem β ht))
    apply hβinj ht (by constructor <;> norm_num)
    rw [← heq, hv₁, hβ₁]
  have hdisjoint : ∀ v ∈ Icc (-v₀) v₁, ∀ w ∈ Icc (-v₀) v₁, α (-1) v ≠ α 1 w := by
    intro v _ w _ heq
    have heA : A (B (lowerSaddleArm s a (-1) σ v), ell + a) =
        A (B (lowerSaddleArm s a 1 σ w), ell + a) := by
      apply Prod.ext heq
      rw [hA, hA]
    have he := congrArg Prod.fst (B.injective (congrArg Prod.fst (A.injective heA)))
    change -1 * Real.sqrt _ = 1 * Real.sqrt _ at he
    have hpos : 0 < Real.sqrt ((v ^ 2 - 2 * a) / (v ^ 2 + 2 * s)) :=
      Real.sqrt_pos.mpr (div_pos (by nlinarith [sq_nonneg v]) (by positivity))
    have hn := Real.sqrt_nonneg ((w ^ 2 - 2 * a) / (w ^ 2 + 2 * s))
    nlinarith only [he, hpos, hn]
  obtain ⟨g, u, v, hu, hv, hg, hdg, hinj, hgu, hgv, himage, hgerm⟩ :=
    exists_smooth_arc_attaching_ends hv₀₁ hβ hβder hβinj hαL.1 hαR.1 hαL.2.1 hαR.2.1
      hαL.2.2.1 hαR.2.2.1 hβ₀ hβ₁ hgerm₀ hgerm₁ hmeet₀ hmeet₁ hdisjoint
  exact ⟨g, u, v, hu, hv, hg, hdg, hinj, hgu, hgv, hβimage ▸ himage, hgerm⟩

private theorem saddle_cutoff_outer_level_germ
    {F : Type*} (B : (ℝ × ℝ) → F) (T : F × ℝ → F × ℝ)
    {c s h ε d τ σ : ℝ} (hs : 0 ≤ s) (hh1 : h < 1) (hτ : 0 ≤ τ)
    (hσ : σ ^ 2 = 1) {θ : ℝ × ℝ → ℝ}
    (hθ : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    {V : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (τ - q.1))), c + s + q.1)) :
    let O : Set (ℝ × ℝ) := {p | -ε < p.1 ∧ p.1 < d ∧ h / 2 < |p.2| ∧
      |p.2| < h ∧ 0 < p.1 + s * p.2 ^ 2}
    IsOpen O ∧ ∀ p ∈ O,
      T (B (saddleBandLevelCurve s p.1 σ p.2), c + s + p.1) =
        (B (saddleBandLevelCurve s τ σ p.2), c + s + p.1) := by
  intro O
  have hO : IsOpen O :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd.abs).inter
          ((isOpen_lt continuous_snd.abs continuous_const).inter
            (isOpen_lt continuous_const (show Continuous (fun p : ℝ × ℝ => p.1 + s * p.2 ^ 2) by fun_prop)))))
  refine ⟨hO, ?_⟩
  rintro ⟨t, u⟩ ⟨htlo, hthi, huouter, huwidth, hrad⟩
  have hu : u ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (huwidth.trans hh1)
  have hlevel : (1 - (saddleBandLevelCurve s t σ u).1 ^ 2) *
      ((saddleBandLevelCurve s t σ u).2 ^ 2 + 2 * s) / 2 = s + t := by
    simpa only [zero_add] using saddleBandLevelCurve_height_of_nonneg hrad.le hσ hu (0 : ℝ)
  have hzV : (t, saddleBandLevelCurve s t σ u) ∈ V := hKV ⟨⟨htlo.le, hthi.le⟩, huwidth.le, hlevel⟩
  have heq := hTmodel (t, saddleBandLevelCurve s t σ u) hzV
  change T (B (saddleBandLevelCurve s t σ u), c + s + t) =
    (B (saddleBandCurve (saddleBandLevelCurve s t σ u) (θ (t, u) * (τ - t))), c + s + t) at heq
  rw [hθ t u huouter.le, one_mul,
    saddleBandCurve_saddleBandLevelCurve hrad (add_nonneg hτ (mul_nonneg hs (sq_nonneg u))) hσ hu] at heq
  exact heq

private theorem exists_smooth_saddle_cutoff_bottom_arc
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (θ : ℝ × ℝ → ℝ) (ψ : ℝ → ℝ)
    (hT : ∀ p, (T p).2 = p.2) (hQ : ∀ p, (Q p).2 = ψ p.2)
    {s a j ℓ t₀ δ σ h k ρ r v₀ ε d : ℝ}
    (hs : 0 < s) (ha : a < 0) (ht₀ : 0 < t₀) (ht₀δ : t₀ < δ)
    (hσ : σ ^ 2 = 1) (hk : 0 < k) (hhalfk : h / 2 < k) (hkh : k < h) (hh1 : h < 1)
    (hεa : -ε < a) (had : a < d)
    (hak : 0 < a + s * k ^ 2) (hr : 0 < r) (hv₀ : 0 < v₀)
    (hv₀j : v₀ ^ 2 / 2 < j) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hθ : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    (hcurve : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-k) k) ⊆ G '' sphere 0 r)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ b < t₀, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + b}) ⊆
          (G '' closedBall 0 r)ᶜ)
    {Vside : Set (ℝ × ℝ)} (hVside : IsOpen Vside)
    (hcurveVside : ∀ ξ ∈ ({-1, 1} : Set ℝ), saddleBandLevelCurve s t₀ σ (ξ * k) ∈ Vside)
    (hcapSide : ∀ z ∈ Vside, B z ∈ G '' closedBall 0 r ↔
      s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {Vraw : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ Vraw)
    (hTraw : ∀ q ∈ Vraw, T (B q.2, ℓ + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), ℓ + q.1)) :
    let q : (ℝ × ℝ) → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-k) k)
    let S := ((fun z => ((T (B z, ℓ + q z)).1, q z)) '' R) ∪ C ×ˢ Icc a j
    let P : (ℝ × ℝ) → Schoenflies.Plane := fun z => (Q (T (B z, ℓ + q z))).1
    let v₁ := Real.sqrt (2 * (a + s * k ^ 2) / (1 - k ^ 2))
    let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (∀ z ∈ R, |z.1| = k → 0 < σ * z.2) →
    (∀ z ∈ R, T (B z, ℓ + q z) =
      (B (saddleBandCurve z (θ (q z, z.1) * (t₀ - q z))), ℓ + q z)) →
    (∀ z ∈ R, -v₀ ≤ σ * (B.symm (T (B z, ℓ + q z)).1).2) →
    (∀ z ∈ R, (1 - (B.symm (T (B z, ℓ + q z)).1).1 ^ 2) *
      ((B.symm (T (B z, ℓ + q z)).1).2 ^ 2 + 2 * s) / 2 ≤ s + t₀) →
    InjOn (fun p : Schoenflies.Plane × ℝ => (Q (p.1, ℓ + p.2)).1) S →
    let Bottom := ((P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁)) ∪
          ((fun y => (Q (y, ℓ + a)).1) '' C) ∪
          (P '' (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁)))
    ∃ g : ℝ → Schoenflies.Plane, ∃ u v : ℝ,
      u < 0 ∧ 1 < v ∧ ContDiff ℝ ∞ g ∧ (∀ t, deriv g t ≠ 0) ∧
      InjOn g (Icc u v) ∧ g u = P (-u₀, -(σ * v₀)) ∧
      g v = P (u₀, -(σ * v₀)) ∧ g '' Icc u v = Bottom ∧
      (∃ D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ, StrictMono D₀ ∧ StrictAnti D₁ ∧
        D₀ u = -v₀ ∧ D₁ v = -v₀ ∧
        g =ᶠ[𝓝 u] (fun t => P (lowerSaddleArm s a (-1) σ (D₀ t))) ∧
        g =ᶠ[𝓝 v] (fun t => P (lowerSaddleArm s a 1 σ (D₁ t)))) := by
  intro q R C S P v₁ u₀ hside hmodel hbottom henergy hproj
  let O : Set (ℝ × ℝ) := {p | -ε < p.1 ∧ p.1 < d ∧ h / 2 < |p.2| ∧
    |p.2| < h ∧ 0 < p.1 + s * p.2 ^ 2}
  have hTraw' : ∀ q ∈ Vraw, T (B q.2, (ℓ - s) + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), (ℓ - s) + s + q.1) := by
    simpa only [sub_add_cancel] using hTraw
  obtain ⟨hO, hOmodel'⟩ := saddle_cutoff_outer_level_germ B T hs.le hh1 ht₀.le hσ hθ hKV hTraw'
  change IsOpen O at hO
  have hOmodel : ∀ p ∈ O, T (B (saddleBandLevelCurve s p.1 σ p.2), ℓ + p.1) =
      (B (saddleBandLevelCurve s t₀ σ p.2), ℓ + p.1) := by
    simpa only [sub_add_cancel] using hOmodel'
  have hOunit : ∀ p ∈ O, p.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < p.1 + s * p.2 ^ 2 := by
    intro p hp
    exact ⟨abs_lt.mp (hp.2.2.2.1.trans hh1), hp.2.2.2.2⟩
  have hseam : ∀ ξ ∈ ({-1, 1} : Set ℝ), (a, ξ * k) ∈ O := by
    intro ξ hξ
    have hξsq : ξ ^ 2 = 1 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hξ
      rcases hξ with rfl | rfl <;> norm_num
    have hξabs : |ξ| = 1 := by rcases sq_eq_one_iff.mp hξsq with rfl | rfl <;> norm_num
    have habs : |ξ * k| = k := by rw [abs_mul, hξabs, one_mul, abs_of_pos hk]
    refine ⟨hεa, had, ?_, ?_, ?_⟩
    · rwa [habs]
    · rwa [habs]
    · simpa only [mul_pow, hξsq, one_mul] using hak
  have hθk : ∀ t u, k ≤ |u| → θ (t, u) = 1 := fun t u hu => hθ t u (hhalfk.le.trans hu)
  have hk1 : k < 1 := hkh.trans hh1
  have haj : a ≤ j := by nlinarith [sq_nonneg v₀]
  have hparams := lower_saddle_boundary_parameters hs ha hσ hk hk1 hak hv₀ hv₀j
    (fun z hz hv ha hj heq => hside z ⟨hz, hv, ha, hj⟩ heq)
  change 0 < v₁ ∧ v₀ < v₁ ∧ 0 < u₀ ∧ u₀ < k ∧
    v₁ ^ 2 = 2 * (a + s * k ^ 2) / (1 - k ^ 2) ∧
      u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s) at hparams
  obtain ⟨hv₁, hv₀₁, hu₀, hu₀k, hv₁sq, hu₀sq⟩ := hparams
  let f : (ℝ × ℝ) → Schoenflies.Plane × ℝ := fun z => ((T (B z, ℓ + q z)).1, q z)
  let H : Schoenflies.Plane → Schoenflies.Plane := fun y => (Q (y, ℓ + a)).1
  have hfS {z : ℝ × ℝ} (hz : z ∈ R) : f z ∈ S := Or.inl ⟨z, hz, rfl⟩
  have hcS {y : Schoenflies.Plane} (hy : y ∈ C) : (y, a) ∈ S :=
    Or.inr ⟨hy, le_rfl, haj⟩
  have hheight {z : ℝ × ℝ} (hz : z ∈ R) : (T (B z, ℓ + q z)).2 = ℓ + q z := by
    rw [hmodel z hz]
  have hP {z : ℝ × ℝ} (hz : z ∈ R) : P z = (Q ((f z).1, ℓ + (f z).2)).1 := by
    apply congrArg (fun p : Schoenflies.Plane × ℝ => (Q p).1)
    exact Prod.ext rfl (hheight hz)
  have hinj : InjOn P R := by
    intro z hz w hw heq
    have hf := hproj (hfS hz) (hfS hw) ((hP hz).symm.trans (heq.trans (hP hw)))
    have ht : T (B z, ℓ + q z) = T (B w, ℓ + q w) := by
      apply Prod.ext
      · change (f z).1 = (f w).1
        exact congrArg Prod.fst hf
      · rw [hheight hz, hheight hw]
        exact congrArg (fun x : ℝ => ℓ + x) (congrArg Prod.snd hf)
    exact B.injective (congrArg Prod.fst (T.injective ht))
  have hHinj : InjOn H C := by
    intro y hy z hz heq
    exact congrArg Prod.fst (hproj (hcS hy) (hcS hz) heq)
  have hH : Continuous H := (Q.continuous.comp (continuous_id.prodMk continuous_const)).fst
  have hC := isArcBetween_reference_circle_compl_selected B G hs.le ht₀ hk hk1 hr hcurve
  have hHC := hC.image_of_injOn Subset.rfl hH.continuousOn hHinj
  have hend (τ : ℝ) (hτ : τ = -1 ∨ τ = 1) :
      H (B (saddleBandLevelCurve s t₀ σ (τ * k))) = P (τ * k, σ * v₁) := by
    have hτsq : τ ^ 2 = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have habsτ : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have htop := lowerSaddleArm_right_endpoint (τ := τ) (σ := σ) hs hk.le hk1 hv₁sq
    have hz : (τ * k, σ * v₁) ∈ R := by
      rw [← htop]
      exact lowerSaddleArm_mem_half_band hs ha hτsq hσ hk.le hk1 hv₀₁.le hv₁sq haj
        ⟨by linarith, le_rfl⟩
    have hqa : q (τ * k, σ * v₁) = a := by
      rw [← htop]
      exact (lowerSaddleArm_properties hs ha hτsq hσ).2.2 v₁ |>.2.2
    have hunit : τ * k ∈ Ioo (-1 : ℝ) 1 := by
      rcases hτ with rfl | rfl <;> constructor <;> simp only [neg_one_mul, one_mul] <;> linarith
    have hcur : saddleBandLevelCurve s a σ (τ * k) = (τ * k, σ * v₁) := by
      simp only [saddleBandLevelCurve, mul_pow, hτsq, one_mul]
      rfl
    have hrad : 0 < a + s * (τ * k) ^ 2 := by simpa only [mul_pow, hτsq, one_mul] using hak
    have hshift := saddleBandCurve_saddleBandLevelCurve hrad
      (add_pos_of_pos_of_nonneg ht₀ (mul_nonneg hs.le (sq_nonneg (τ * k)))).le hσ hunit
    rw [hcur] at hshift
    dsimp only [P, H]
    rw [hmodel _ hz, hqa, hθk a (τ * k) (by simp only [abs_mul, habsτ, one_mul, abs_of_pos hk, le_refl]),
      one_mul, hshift]
  have hCactual : Schoenflies.IsArcBetween (H '' C) (P (-k, σ * v₁)) (P (k, σ * v₁)) := by
    have hl := hend (-1) (Or.inl rfl)
    have hr := hend 1 (Or.inr rfl)
    simp only [neg_one_mul, one_mul] at hl hr
    simpa only [hl, hr] using hHC
  let E : Set (ℝ × ℝ) := (fun z => B.symm (T (B z, ℓ + q z)).1) '' R
  have hcoord (z : ℝ × ℝ) (hz : z ∈ R) :
      (B.symm (T (B z, ℓ + q z)).1).1 = z.1 := by
    rw [hmodel z hz, B.symm_apply_apply]
    rfl
  have hcapInter := saddle_lower_band_inter_cap_circle_subset B G hs.le ht₀ ht₀δ hσ hh1 hkh
    hv₀.le hv₀t hupper hclear (K := E)
    (by rintro z ⟨w, hw, rfl⟩; rw [hcoord w hw]; exact hw.1)
    (by rintro z ⟨w, hw, rfl⟩; exact hbottom w hw)
    (by rintro z ⟨w, hw, rfl⟩; exact henergy w hw)
  have hcontact : ∀ z : ℝ × ℝ, |z.1| ≤ k → -v₀ ≤ σ * z.2 →
      a ≤ q z → q z ≤ j → P z ∈ H '' C →
        z = (-k, σ * v₁) ∨ z = (k, σ * v₁) := by
    intro z hzwidth hzbottom hzlower hzupper hzC
    have hz : z ∈ R := ⟨hzwidth, hzbottom, hzlower, hzupper⟩
    obtain ⟨y, hy, heq⟩ := hzC
    have hfeq := hproj (hfS hz) (hcS hy) ((hP hz).symm.trans heq.symm)
    have hfy : (T (B z, ℓ + q z)).1 = y := congrArg Prod.fst hfeq
    have hqa : q z = a := congrArg Prod.snd hfeq
    have hyE : y ∈ B '' E := by
      refine ⟨B.symm y, ?_, B.apply_symm_apply y⟩
      exact ⟨z, hz, congrArg B.symm hfy⟩
    obtain ⟨w, ⟨u, hu, huw⟩, hwy⟩ := hcapInter ⟨hyE, hy.1⟩
    have huy : B (saddleBandLevelCurve s t₀ σ u) = y := by rw [huw]; exact hwy
    have hzu : z.1 = u := by
      have he : B.symm y = saddleBandLevelCurve s t₀ σ u := by rw [← huy, B.symm_apply_apply]
      have hc := hcoord z hz
      rw [hfy, he] at hc
      exact hc.symm
    have hn : u ∉ Ioo (-k) k := by
      intro huopen
      exact hy.2 ⟨_, ⟨u, huopen, rfl⟩, huy⟩
    have huend : u = -k ∨ u = k := by
      by_cases hl : u = -k
      · exact Or.inl hl
      · right
        by_contra hr
        exact hn ⟨lt_of_le_of_ne hu.1 (Ne.symm hl), lt_of_le_of_ne hu.2 hr⟩
    have hwidth : |z.1| = k := by
      rw [hzu]
      rcases huend with rfl | rfl <;> simp only [abs_neg, abs_of_pos hk]
    have hpos := hside z hz hwidth
    have hunit : z.1 ∈ Ioo (-1 : ℝ) 1 := by
      have hh := abs_le.mp hzwidth
      constructor <;> linarith [hh.1, hh.2]
    have hden : 1 - z.1 ^ 2 ≠ 0 := by nlinarith [hunit.1, hunit.2]
    have hcur := saddleBandCurve_eq_saddleBandLevelCurve (s := s) (t := 0) hσ hden hpos (by simp)
    simp only [saddleBandCurve_zero, add_zero] at hcur
    change z = saddleBandLevelCurve s (q z) σ z.1 at hcur
    rw [hqa, hzu] at hcur
    rcases huend with rfl | rfl
    · left
      simpa only [saddleBandLevelCurve, neg_sq] using hcur
    · right
      exact hcur
  let A := T.trans Q
  let α : ℝ → ℝ → Schoenflies.Plane :=
    fun ξ v => (A (B (lowerSaddleArm s a ξ σ v), ℓ + a)).1
  have hαP (ξ : ℝ) (hξ : ξ ∈ ({-1, 1} : Set ℝ)) (v : ℝ) :
      α ξ v = P (lowerSaddleArm s a ξ σ v) := by
    have hξsq : ξ ^ 2 = 1 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hξ
      rcases hξ with rfl | rfl <;> norm_num
    have he := ((lowerSaddleArm_properties hs ha hξsq hσ).2.2 v).2.2
    change q (lowerSaddleArm s a ξ σ v) = a at he
    dsimp only [α, A, P]
    rw [he]
    rfl
  have hends : ∀ ξ ∈ ({-1, 1} : Set ℝ),
      H (B (saddleBandLevelCurve s t₀ σ (ξ * k))) = α ξ v₁ := by
    intro ξ hξ
    rw [hαP ξ hξ, lowerSaddleArm_right_endpoint (τ := ξ) (σ := σ) hs hk.le hk1 hv₁sq]
    exact hend ξ (by simpa only [mem_insert_iff, mem_singleton_iff] using hξ)
  have hcontactarm : ∀ ξ ∈ ({-1, 1} : Set ℝ), ∀ v ∈ Icc (-v₀) v₁,
      α ξ v ∈ H '' C → v = v₁ := by
    intro ξ hξ v hv hmem
    have hξsq : ξ ^ 2 = 1 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hξ
      rcases hξ with rfl | rfl <;> norm_num
    have hz := lowerSaddleArm_mem_half_band hs ha hξsq hσ hk.le hk1 hv₀₁.le hv₁sq haj hv
    change lowerSaddleArm s a ξ σ v ∈ R at hz
    rw [hαP ξ hξ] at hmem
    have hc := hcontact _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hmem
    have hread := ((lowerSaddleArm_properties hs ha hξsq hσ).2.2 v).2.1
    rcases hc with hc | hc <;>
      have he := congrArg (fun z : ℝ × ℝ => σ * z.2) hc <;>
      simpa only [hread, ← mul_assoc, ← pow_two, hσ, one_mul] using he
  obtain ⟨g, u, v, hu, hv, hg, hdg, hinj, hgu, hgv, himage, D₀, D₁,
      hm₀, hm₁, hDu, hDv, hgerm₀, hgerm₁⟩ :=
    exists_smooth_parameter_saddle_bottom_boundary B G T Q ψ hT hQ hs ha ht₀ hσ hr hk hk1
      (by linarith only [hv₀, hv₀₁]) hC (fun _ hy => hy.1)
      hVside hcurveVside hcapSide hO hseam hOunit hOmodel hends hcontactarm
  have hleft : α (-1) (-v₀) = P (-u₀, -(σ * v₀)) := by
    rw [hαP (-1) (by simp)]
    congr 1
    simp only [lowerSaddleArm, neg_sq, neg_one_mul, mul_neg, u₀]
  have hright : α 1 (-v₀) = P (u₀, -(σ * v₀)) := by
    rw [hαP 1 (by simp)]
    congr 1
    simp only [lowerSaddleArm, neg_sq, one_mul, mul_neg, u₀]
  have hαL : (α (-1) : ℝ → Schoenflies.Plane) = P ∘ lowerSaddleArm s a (-1) σ :=
    funext (hαP (-1) (by simp))
  have hαR : (α 1 : ℝ → Schoenflies.Plane) = P ∘ lowerSaddleArm s a 1 σ :=
    funext (hαP 1 (by simp))
  refine ⟨g, u, v, hu, hv, hg, hdg, hinj, hgu.trans hleft, hgv.trans hright, ?_,
    D₀, D₁, hm₀, hm₁, hDu, hDv, ?_, ?_⟩
  · change g '' Icc u v = α (-1) '' Icc (-v₀) v₁ ∪ H '' C ∪ α 1 '' Icc (-v₀) v₁ at himage
    simpa only [hαL, hαR, image_comp] using himage
  · change g =ᶠ[𝓝 u] (fun t => α (-1) (D₀ t)) at hgerm₀
    simpa only [hαL, Function.comp_def] using hgerm₀
  · change g =ᶠ[𝓝 v] (fun t => α 1 (D₁ t)) at hgerm₁
    simpa only [hαR, Function.comp_def] using hgerm₁
private theorem hasDerivAt_negative_saddle_level_second
    {s a u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) (hrad : 0 < a + s * u ^ 2) :
    HasDerivAt (fun x => -Real.sqrt (2 * (a + s * x ^ 2) / (1 - x ^ 2)))
      (-(4 * u * (s + a) / (1 - u ^ 2) ^ 2) /
        (2 * Real.sqrt (2 * (a + s * u ^ 2) / (1 - u ^ 2)))) u := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith only [hu.1, hu.2]
  have hr : 0 < 2 * (a + s * u ^ 2) / (1 - u ^ 2) :=
    div_pos (mul_pos (by norm_num) hrad) hden
  have hn : HasDerivAt (fun x : ℝ => 2 * (a + s * x ^ 2)) (4 * s * u) u := by
    exact ((((hasDerivAt_id u).pow 2).const_mul s).const_add a |>.const_mul 2).congr_deriv
      (by simp only [id_eq, Nat.cast_ofNat, mul_one]; ring)
  have hd : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * u) u := by
    exact (((hasDerivAt_id u).pow 2).const_sub 1).congr_deriv
      (by simp only [id_eq, Nat.cast_ofNat, mul_one]; ring)
  have hdiv : HasDerivAt (fun x : ℝ => 2 * (a + s * x ^ 2) / (1 - x ^ 2))
      (4 * u * (s + a) / (1 - u ^ 2) ^ 2) u :=
    (hn.div hd hden.ne').congr_deriv (by congr 1; ring)
  exact ((hdiv.sqrt hr.ne').neg).congr_deriv (by rw [neg_div])

private theorem negative_saddle_level_second_endpoint_data
    {s a v₀ u₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀)
    (hu₀ : 0 < u₀) (hu₀1 : u₀ < 1)
    (hlevel : (1 - u₀ ^ 2) * (v₀ ^ 2 + 2 * s) / 2 - s = a) :
    let V : Set ℝ := {u | u ∈ Ioo (-1 : ℝ) 1 ∧ 0 < a + s * u ^ 2}
    let f : ℝ → ℝ := fun u => -Real.sqrt (2 * (a + s * u ^ 2) / (1 - u ^ 2))
    IsOpen V ∧ -u₀ ∈ V ∧ u₀ ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
      f (-u₀) = -v₀ ∧ f u₀ = -v₀ ∧
      0 < deriv f (-u₀) ∧ deriv f u₀ < 0 := by
  intro V f
  have hden : 0 < 1 - u₀ ^ 2 := by nlinarith only [hu₀, hu₀1]
  have hsa : 0 < s + a := by nlinarith only [hlevel, mul_pos hden (by positivity : 0 < v₀ ^ 2 + 2 * s)]
  have hrad : 0 < a + s * u₀ ^ 2 := by
    have hp := mul_pos hden (sq_pos_of_pos hv₀)
    nlinarith only [hlevel, hp]
  have huunit : u₀ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [hu₀], hu₀1⟩
  have hnegunit : -u₀ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [hu₀1], by linarith only [hu₀]⟩
  have hneg : -u₀ ∈ V := ⟨hnegunit, by simpa only [neg_sq] using hrad⟩
  have hpos : u₀ ∈ V := ⟨huunit, hrad⟩
  have hV : IsOpen V := isOpen_Ioo.inter
    (isOpen_lt continuous_const (show Continuous (fun u : ℝ => a + s * u ^ 2) by fun_prop))
  have hdenV : ∀ u ∈ V, 0 < 1 - u ^ 2 := by
    intro u hu
    nlinarith only [hu.1.1, hu.1.2]
  have hradV : ∀ u ∈ V, 0 < 2 * (a + s * u ^ 2) / (1 - u ^ 2) :=
    fun u hu => div_pos (mul_pos (by norm_num) hu.2) (hdenV u hu)
  have hf : ContDiffOn ℝ ∞ f V := by
    apply ContDiffOn.neg
    apply ContDiffOn.sqrt
    · exact (contDiffOn_const.mul (contDiffOn_const.add
        (contDiffOn_const.mul (contDiffOn_id.pow 2)))).div
        (contDiffOn_const.sub (contDiffOn_id.pow 2)) (fun u hu => (hdenV u hu).ne')
    · exact fun u hu => (hradV u hu).ne'
  have hratio : 2 * (a + s * u₀ ^ 2) / (1 - u₀ ^ 2) = v₀ ^ 2 := by
    apply (div_eq_iff hden.ne').mpr
    nlinarith only [hlevel]
  have hfpos : f u₀ = -v₀ := by
    dsimp only [f]
    rw [hratio, Real.sqrt_sq hv₀.le]
  have hfneg : f (-u₀) = -v₀ := by simpa only [f, neg_sq] using hfpos
  have hdl := hasDerivAt_negative_saddle_level_second hnegunit hneg.2
  have hdr := hasDerivAt_negative_saddle_level_second huunit hrad
  refine ⟨hV, hneg, hpos, hf, hfneg, hfpos, ?_, ?_⟩
  · rw [hdl.deriv]
    have hn : 4 * (-u₀) * (s + a) / (1 - (-u₀) ^ 2) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith only [hu₀]) hsa)
        (sq_pos_of_ne_zero (hdenV _ hneg).ne')
    exact div_pos (neg_pos.mpr hn) (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hradV _ hneg)))
  · rw [hdr.deriv]
    have hn : 0 < 4 * u₀ * (s + a) / (1 - u₀ ^ 2) ^ 2 :=
      div_pos (mul_pos (by positivity) hsa) (sq_pos_of_ne_zero hden.ne')
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hn)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hradV _ hpos)))
private theorem negative_saddle_level_eq_bottom_arm
    {s a ξ σ u : ℝ} (hs : 0 < s) (hξ : ξ ^ 2 = 1) (hσ : σ ^ 2 = 1)
    (hu : u ∈ Ioo (-1 : ℝ) 1) (hrad : 0 < a + s * u ^ 2) (hsgn : 0 < ξ * u) :
    saddleBandLevelCurve s a (-σ) u = lowerSaddleArm s a ξ σ
      (-Real.sqrt (2 * (a + s * u ^ 2) / (1 - u ^ 2))) := by
  have hσneg : (-σ) ^ 2 = 1 := by simpa only [neg_sq] using hσ
  have hlevel := saddleBandLevelCurve_height_of_nonneg hrad.le hσneg hu (0 : ℝ)
  simp only [zero_add] at hlevel
  have he := eq_lowerSaddleArm_of_level (a := a) hs hξ hσ
    (z := saddleBandLevelCurve s a (-σ) u) hsgn (by linarith only [hlevel])
  have hsecond : σ * (saddleBandLevelCurve s a (-σ) u).2 =
      -Real.sqrt (2 * (a + s * u ^ 2) / (1 - u ^ 2)) := by
    simp only [saddleBandLevelCurve, mul_neg, ← mul_assoc, ← pow_two, hσ, neg_one_mul]
  rw [hsecond] at he
  exact he

private theorem exists_smooth_bottom_arc_eq_negative_level
    {P : (ℝ × ℝ) → Schoenflies.Plane} {g : ℝ → Schoenflies.Plane}
    {s a σ v₀ u₀ u v : ℝ} (hs : 0 < s) (hσ : σ ^ 2 = 1)
    (hv₀ : 0 < v₀) (hu₀ : 0 < u₀) (hu₀1 : u₀ < 1)
    (hlevel : (1 - u₀ ^ 2) * (v₀ ^ 2 + 2 * s) / 2 - s = a)
    (huv : u < v) (hg : ContDiff ℝ ∞ g) (hgd : ∀ t, deriv g t ≠ 0)
    (hginj : InjOn g (Icc u v))
    (D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ) (hm₀ : StrictMono D₀) (hm₁ : StrictAnti D₁)
    (hD₀ : D₀ u = -v₀) (hD₁ : D₁ v = -v₀)
    (hg₀ : g =ᶠ[𝓝 u] (fun t => P (lowerSaddleArm s a (-1) σ (D₀ t))))
    (hg₁ : g =ᶠ[𝓝 v] (fun t => P (lowerSaddleArm s a 1 σ (D₁ t)))) :
    ∃ β : ℝ → Schoenflies.Plane, ContDiff ℝ ∞ β ∧ (∀ t, deriv β t ≠ 0) ∧
      InjOn β (Icc (-u₀) u₀) ∧ β '' Icc (-u₀) u₀ = g '' Icc u v ∧
      β =ᶠ[𝓝 (-u₀)] (fun x => P (saddleBandLevelCurve s a (-σ) x)) ∧
      β =ᶠ[𝓝 u₀] (fun x => P (saddleBandLevelCurve s a (-σ) x)) := by
  obtain ⟨hV, haV, hbV, hf, hfa, hfb, hd₀, hd₁⟩ :=
    negative_saddle_level_second_endpoint_data hs hv₀ hu₀ hu₀1 hlevel
  obtain ⟨β, hβ, hβd, hβinj, hβimage, hβa, hβb⟩ :=
    DifferentialGeometry.Topology.exists_smooth_arc_eq_endpoint_parameters
      (α₀ := fun t => P (lowerSaddleArm s a (-1) σ t))
      (α₁ := fun t => P (lowerSaddleArm s a 1 σ t))
      (show -u₀ < u₀ by linarith only [hu₀]) huv hg hgd hginj D₀ D₁ hm₀ hm₁
      hV haV hbV hf (hfa.trans hD₀.symm) (hfb.trans hD₁.symm) hd₀ hd₁ hg₀ hg₁
  refine ⟨β, hβ, hβd, hβinj, hβimage, ?_, ?_⟩
  · filter_upwards [hβa, hV.mem_nhds haV,
      (isOpen_Iio.mem_nhds (show -u₀ < (0 : ℝ) by linarith only [hu₀]))] with x hx hVx hneg
    exact hx.trans (congrArg P (negative_saddle_level_eq_bottom_arm hs (by norm_num)
      hσ hVx.1 hVx.2 (by simpa only [neg_one_mul, neg_pos, mem_Iio] using hneg)).symm)
  · filter_upwards [hβb, hV.mem_nhds hbV,
      (isOpen_Ioi.mem_nhds hu₀)] with x hx hVx hpos
    exact hx.trans (congrArg P (negative_saddle_level_eq_bottom_arm hs (by norm_num)
      hσ hVx.1 hVx.2 (by simpa only [one_mul, mem_Ioi] using hpos)).symm)
private theorem actual_saddle_cutoff_bottom_collar
    {P : (ℝ × ℝ) → Schoenflies.Plane} {g : ℝ → Schoenflies.Plane}
    (Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (ψ : ℝ ≃ₘ[ℝ] ℝ) {K : Set (Schoenflies.Plane × ℝ)} (hK : IsCompact K)
    {Cboundary : Set Schoenflies.Plane}
    (hfrontier : frontier ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) = Cboundary)
    {OQ : Set Schoenflies.Plane} (hOQ : IsOpen OQ) {gQ : Schoenflies.Plane → ℝ}
    (hgQ : ContDiffOn ℝ ∞ gQ OQ) {WQ : Set (Schoenflies.Plane × ℝ)}
    (hKW : Q '' K ⊆ WQ) (hWQO : WQ ⊆ {p | p.1 ∈ OQ})
    {s a σ v₀ ell k j u v : ℝ} (hs : 0 < s) (ha : a < 0) (hσ : σ ^ 2 = 1)
    (hv₀ : 0 < v₀) (hk : 0 < k) (hk1 : k < 1) (hak : 0 < a + s * k ^ 2)
    (hv₀j : v₀ ^ 2 / 2 < j) (huv : u < v)
    (hg : ContDiff ℝ ∞ g) (hgd : ∀ t, deriv g t ≠ 0) (hginj : InjOn g (Icc u v))
    (hgC : g '' Icc u v ⊆ Cboundary)
    (hbottom : ∀ x ∈ g '' Icc u v, gQ x = ψ (ell + a) ∧ fderiv ℝ gQ x ≠ 0)
    (D₀ D₁ : ℝ ≃ₘ[ℝ] ℝ) (hm₀ : StrictMono D₀) (hm₁ : StrictAnti D₁)
    (hD₀ : D₀ u = -v₀) (hD₁ : D₁ v = -v₀)
    (hg₀ : g =ᶠ[𝓝 u] (fun t => P (lowerSaddleArm s a (-1) σ (D₀ t))))
    (hg₁ : g =ᶠ[𝓝 v] (fun t => P (lowerSaddleArm s a 1 σ (D₁ t)))) :
    let q : (ℝ × ℝ) → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (∀ z ∈ R, |z.1| = k → 0 < σ * z.2) →
    ∀ χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane)
        (ℝ × ℝ) Schoenflies.Plane ∞,
    (fun z : ℝ × ℝ => (q z, z.1)) '' {z ∈ R | σ * z.2 = -v₀} ⊆ χ.source →
    (χ : (ℝ × ℝ) → Schoenflies.Plane) =
      (fun p => P (saddleBandLevelCurve s p.1 (-σ) p.2)) →
    (∀ p ∈ χ.source, gQ (χ p) = ψ (ell + p.1)) →
    ∃ β : ℝ → Schoenflies.Plane,
      ContDiff ℝ ∞ β ∧ (∀ t, deriv β t ≠ 0) ∧ InjOn β (Icc (-u₀) u₀) ∧
      β '' Icc (-u₀) u₀ = g '' Icc u v ∧
      ∃ D : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane)
          (ℝ × ℝ) Schoenflies.Plane ∞,
        {a} ×ˢ Icc (-u₀) u₀ ⊆ D.source ∧ D.target ⊆ OQ ∧
        (∀ x ∈ Icc (-u₀) u₀, D (a, x) = β x) ∧
        (∀ p ∈ D.source, gQ (D p) = ψ (ell + p.1)) ∧
        ∀ x ∈ ({-u₀, u₀} : Set ℝ), (D : (ℝ × ℝ) → Schoenflies.Plane) =ᶠ[𝓝 (a, x)] χ := by
  intro q R u₀ hside χ hχsource hχformula hχheight
  obtain ⟨_, _, hu₀, hu₀k, _, hu₀sq⟩ := lower_saddle_boundary_parameters hs ha hσ hk hk1 hak hv₀ hv₀j
    (fun z hz hv hl hj he => hside z ⟨hz, hv, hl, hj⟩ he)
  change 0 < u₀ at hu₀
  change u₀ < k at hu₀k
  change u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s) at hu₀sq
  have hden : 0 < v₀ ^ 2 + 2 * s := by positivity
  have hlevel : (1 - u₀ ^ 2) * (v₀ ^ 2 + 2 * s) / 2 - s = a := by
    have hm := (eq_div_iff hden.ne').mp hu₀sq
    nlinarith only [hm]
  obtain ⟨β, hβ, hβd, hβinj, hβimage, hβleft, hβright⟩ :=
    exists_smooth_bottom_arc_eq_negative_level hs hσ hv₀ hu₀ (hu₀k.trans hk1)
      hlevel huv hg hgd hginj D₀ D₁ hm₀ hm₁ hD₀ hD₁ hg₀ hg₁
  have hYclosed : IsClosed ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) :=
    (hK.image (Q.continuous.fst)).isClosed
  have hβO (x : ℝ) (hx : x ∈ Icc (-u₀) u₀) : β x ∈ OQ := by
    have hxg : β x ∈ g '' Icc u v := hβimage ▸ mem_image_of_mem β hx
    have hxf : β x ∈ frontier ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) :=
      hfrontier.symm ▸ hgC hxg
    have hxY : β x ∈ (fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K :=
      hYclosed.closure_eq ▸ frontier_subset_closure hxf
    obtain ⟨p, hp, hpx⟩ := hxY
    rw [← hpx]
    exact hWQO (hKW (mem_image_of_mem Q hp))
  have hβbottom (x : ℝ) (hx : x ∈ Icc (-u₀) u₀) :
      gQ (β x) = ψ (ell + a) ∧ fderiv ℝ gQ (β x) ≠ 0 :=
    hbottom (β x) (hβimage ▸ mem_image_of_mem β hx)
  have hcorners (x : ℝ) (hx : x ∈ ({-u₀, u₀} : Set ℝ)) :
      (a, x) ∈ χ.source ∧ β =ᶠ[𝓝 x] (fun y => χ (a, y)) := by
    have hxabs : |x| = u₀ := by
      rcases mem_insert_iff.mp hx with rfl | hh
      · exact abs_of_neg (neg_neg_of_pos hu₀) |>.trans (neg_neg u₀)
      · have hh' : x = u₀ := hh; subst x; exact abs_of_pos hu₀
    have hxsq : x ^ 2 = u₀ ^ 2 := by
      rw [← sq_abs x, hxabs]
    have hσv : σ * (-(σ * v₀)) = -v₀ := by
      rw [mul_neg, ← mul_assoc, ← pow_two, hσ, one_mul]
    have hq : q (x, -(σ * v₀)) = a := by
      simp only [q, hxsq, neg_sq, mul_pow, hσ, one_mul, hlevel]
    have hzin : (x, -(σ * v₀)) ∈ R := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |x| ≤ k; rw [hxabs]; exact hu₀k.le
      · change -v₀ ≤ σ * (-(σ * v₀)); rw [hσv]
      · exact hq.ge
      · rw [hq]; nlinarith only [ha, hv₀j, sq_nonneg v₀]
    refine ⟨hχsource ⟨(x, -(σ * v₀)), ⟨hzin, hσv⟩, Prod.ext hq rfl⟩, ?_⟩
    have hgerm : β =ᶠ[𝓝 x] (fun y => P (saddleBandLevelCurve s a (-σ) y)) := by
      rcases mem_insert_iff.mp hx with rfl | hh
      · exact hβleft
      · have hh' : x = u₀ := hh; subst x; exact hβright
    simpa only [hχformula] using hgerm
  obtain ⟨D, hDs, hDt, hDb, hDh, hDχ⟩ := exists_partialDiffeomorph_height_arc_eq_corner_chart
    (by simp [Schoenflies.Plane]) ψ hOQ hgQ (show -u₀ < u₀ by linarith only [hu₀])
    hβ (fun x _ => hβd x) hβinj hβO hβbottom χ hχheight hcorners
  exact ⟨β, hβ, hβd, hβinj, hβimage, D, hDs, hDt, hDb, hDh, hDχ⟩


theorem projection_saddle_cutoff_region_eq_closure_inside
    {M : Type*} (e : M → Schoenflies.Plane × ℝ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ)) (ψ : ℝ ≃ ℝ)
    (θ : ℝ × ℝ → ℝ) (κ : ContDiffBump (0 : ℝ))
    {β : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {V : Set (ℝ × (ℝ × ℝ))} {c s h ε d τ δ j σ ρ r v₀ b m : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1) (hε : 0 < ε)
    (hεh : ε < s * h ^ 2 / 16) (hτ : 0 < τ) (hτδ : τ < δ) (hτd : τ < d)
    (hj : j ∈ Ioo (τ / 2) τ) (hσ : σ ^ 2 = 1) (hr : 0 < r)
    (hv₀ : 0 < v₀) (hv₀τ : v₀ ^ 2 / 2 < τ / 4) (hκout : κ.rOut = h / 2)
    (hgraph : ∀ z ∈ U, e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hTheight : ∀ q, (T q).2 = q.2)
    (hθ01 : ∀ q, 0 ≤ θ q ∧ θ q ≤ 1)
    (hθ1 : ∀ t u, τ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1)
    (hcurve : ∀ u ∈ Ioo (-h) h, B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ a < τ, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆ (G '' closedBall 0 r)ᶜ)
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hVreg : ∀ q ∈ V, θ (q.1, q.2.1) * (τ - q.1) = 0 ∨
      (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ * (θ (q.1, q.2.1) * (τ - q.1)) / q.2.2 ^ 2))
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (τ - q.1))), c + s + q.1))
    (hbaseb : c + s + τ < b) (hbm : b < m) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    {Ucap : Set (Schoenflies.Plane × ℝ)}
    (hQcap : Q '' Ucap = {z : Schoenflies.Plane × ℝ | b ≤ z.2 ∧ z.2 = m - ‖z.1‖ ^ 2 / 2})
    {OQ : Set Schoenflies.Plane} (hOQ : IsOpen OQ)
    {gQ : Schoenflies.Plane → ℝ} (hgQ : ContDiffOn ℝ ∞ gQ OQ)
    {WQ : Set (Schoenflies.Plane × ℝ)} (hWQ : IsOpen WQ)
    (hWQO : WQ ⊆ {q | q.1 ∈ OQ})
    (hWQeq : WQ ∩ Q '' range (T ∘ e) = WQ ∩ {q | q.2 = gQ q.1}) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-(5 * h / 8)) (5 * h / 8))
    let S := ((fun p : (ℝ × ℝ) × ℝ => (B p.1, p.2)) '' (J '' R)) ∪ C ×ˢ Icc (-ε / 2) j
    let K := ((fun p : Schoenflies.Plane × ℝ => (p.1, c + s + p.2)) '' S) ∪
      ((G '' sphere 0 r) ×ˢ Icc (c + s + j) b ∪ Ucap)
    let P := fun z : ℝ × ℝ => (Q (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))).1
    let Cboundary := P '' {z ∈ R | σ * z.2 = -v₀ ∨
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
      (fun y => (Q (y, c + s + (-ε / 2))).1) '' C
    IsCompact K → R ⊆ U →
    (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) →
    (∀ p ∈ J '' R, -v₀ ≤ σ * p.1.2 ∧
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0) →
    InjOn (fun q : Schoenflies.Plane × ℝ => (Q (q.1, c + s + q.2)).1) S →
    Q '' K ⊆ WQ →
    Schoenflies.IsJordanCurve Cboundary ∧
      (fun q : Schoenflies.Plane × ℝ => (Q q).1) '' K = closure (Schoenflies.inside Cboundary) ∧
      frontier ((fun q : Schoenflies.Plane × ℝ => (Q q).1) '' K) = Cboundary ∧
      let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * (-ε / 2)) / (v₀ ^ 2 + 2 * s))
      Schoenflies.IsCutPair Cboundary (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀)))
        (P '' {z ∈ R | σ * z.2 = -v₀})
        (P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
          (fun y => (Q (y, c + s + (-ε / 2))).1) '' C) := by
  intro R J C S K P Cboundary hK hRU hside hpoints hproj hKW
  have hzeroR : (0, 0) ∈ interior R := by
    apply saddle_half_band_strict_subset_interior
    norm_num
    exact ⟨by positivity, hv₀, by linarith only [hε], (half_pos hτ).trans hj.1⟩
  have hcoord (z : ℝ × ℝ) (hz : z ∈ R) : (J z).1.1 = z.1 :=
    (saddle_cutoff_half_band_coordinates_and_height B T hh.le hε.le
      (hj.2.trans hτd).le hj.2.le (fun q => (hθ01 q).2) hKV hVreg hTmodel z hz).1
  let v₁ := Real.sqrt (2 * (-ε / 2 + s * (5 * h / 8) ^ 2) / (1 - (5 * h / 8) ^ 2))
  let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * (-ε / 2)) / (v₀ ^ 2 + 2 * s))
  let Cexplicit := (P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀)) ∪
      ((P '' (lowerSaddleArm s (-ε / 2) (-1) σ '' Icc (-v₀) v₁)) ∪
        ((fun y => (Q (y, c + s + (-ε / 2))).1) '' C) ∪
        (P '' (lowerSaddleArm s (-ε / 2) 1 σ '' Icc (-v₀) v₁)))
  have hcut := actual_lower_boundary_application B G T Q θ hs hh hh1 hε hεh hτ hτδ hτd hj hσ hr hv₀ hv₀τ
    hθ01 (fun t u hu => hθ1 t u (Or.inr hu)) hcurve hupper hclear hKV hVreg hTmodel hside
    (fun p hp => (hpoints p hp).1) hproj
  change Schoenflies.IsCutPair Cexplicit (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀))) _ _ at hcut
  have hJord : Schoenflies.IsJordanCurve Cexplicit := by
    rw [← hcut.union_eq]
    exact Schoenflies.isJordanCurve_union hcut.fst hcut.snd (fun x hx hy => by
      have hm := hcut.inter_eq.subset ⟨hx, hy⟩
      simpa only [mem_insert_iff, mem_singleton_iff] using hm)
  have hwall := actual_reference_cylinder_application B T hs.le hh hh1 hτ hv₀.le hσ hε hεh
    (hj.2.trans hτd).le hθ1 hKV hTmodel (C := G '' sphere 0 r)
  have hinner := actual_source_projection_interior e B T Q hU hgraph hTheight hRU hzeroR
    hOQ hgQ hWQ hWQO hWQeq (C := C) (a := -ε / 2) (j := j)
    (Ucap := (G '' sphere 0 r) ×ˢ Icc (c + s + j) b ∪ Ucap) hKW
  change P '' interior R ⊆ interior (Prod.fst '' (Q '' K)) ∧
    (interior (Prod.fst '' (Q '' K))).Nonempty at hinner
  rw [image_image] at hinner
  change P '' interior R ⊆ interior ((fun q : Schoenflies.Plane × ℝ => (Q q).1) '' K) ∧
    (interior ((fun q : Schoenflies.Plane × ℝ => (Q q).1) '' K)).Nonempty at hinner
  have hP (z : ℝ × ℝ) : (Q (B (J z).1, c + s + (J z).2)).1 = P z := by
    apply congrArg (fun w : Schoenflies.Plane × ℝ => (Q w).1)
    apply Prod.ext
    · exact B.apply_symm_apply _
    · rw [hTheight]
      dsimp only [J]
      ring
  let A : ℝ → ℝ := fun t => (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)
  have hAj : A j = 0 := by
    change (1 - Real.smoothTransition ((j - τ / 4) / (τ / 4))) * (τ - j) = 0
    rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by linarith : 0 < τ / 4)).mpr (by linarith [hj.1])), sub_self, zero_mul]
  have hκzero (u : ℝ) (hu : h / 2 ≤ |u|) : κ u = 0 := by
    apply κ.zero_of_le_dist
    simpa only [hκout, dist_zero_right, Real.norm_eq_abs] using hu
  have hfront := frontier_projection_saddle_patch_subset B G Q ψ hs.le hτ hσ hh1
    (k := 5 * h / 8) (a := -ε / 2) (ℓ := c + s) (by linarith) (by linarith)
    (by linarith) hj hv₀.le (by nlinarith) hbaseb hbm hr.le hrsq hψ hψb hQfull hQcap hcurve hκzero hAj
    (J := J) hK
    (fun z hz => ⟨hcoord z hz, rfl, (hpoints (J z) ⟨z, hz, rfl⟩).1,
      (hpoints (J z) ⟨z, hz, rfl⟩).2⟩) hwall
    (by simpa only [hP] using hinner.1)
  have hparams := lower_saddle_boundary_parameters hs (by linarith : -ε / 2 < 0) hσ
    (k := 5 * h / 8) (by positivity) (by linarith) (by nlinarith [mul_pos hs (sq_pos_of_pos hh)])
    hv₀ (by linarith [hj.1]) (fun z hz hv ha hj heq => hside z ⟨hz, hv, ha, hj⟩ heq)
  change 0 < v₁ ∧ v₀ < v₁ ∧ 0 < u₀ ∧ u₀ < 5 * h / 8 ∧
    v₁ ^ 2 = 2 * (-ε / 2 + s * (5 * h / 8) ^ 2) / (1 - (5 * h / 8) ^ 2) ∧
    u₀ ^ 2 = (v₀ ^ 2 - 2 * (-ε / 2)) / (v₀ ^ 2 + 2 * s) at hparams
  have hboundary : frontier ((fun q : Schoenflies.Plane × ℝ => (Q q).1) '' K) ⊆ Cexplicit := by
    intro y hy
    rcases hfront hy with ⟨z, ⟨hz, hface⟩, rfl⟩ | hc
    · dsimp only
      rw [hP]
      have hf := saddle_half_band_lower_faces hs (by linarith : -ε / 2 < 0) hσ
        hparams.1.le hparams.2.2.1.le hparams.2.2.2.2.1 hparams.2.2.2.2.2
        (by positivity : 0 ≤ 5 * h / 8) (by linarith : 5 * h / 8 < 1) hz
      have hfaces' := hface.elim (fun h => Or.inr (hf.1 h)) (fun h => Or.inl (hf.2 h))
      rcases hfaces' with hf | hf | hf
      · exact Or.inl (mem_image_of_mem P hf)
      · exact Or.inr (Or.inl (Or.inl (mem_image_of_mem P hf)))
      · exact Or.inr (Or.inr (mem_image_of_mem P hf))
    · exact Or.inr (Or.inl (Or.inr hc))
  have hne : (interior ((fun q : Schoenflies.Plane × ℝ => (Q q).1) '' K)).Nonempty := by
    exact hinner.2
  have heq := PlanarJordan.eq_closure_inside_of_isCompact_of_frontier_subset
    (hK.image Q.continuous.fst) hJord hne hboundary
  have hfaces := saddle_half_band_lower_faces_eq (j := j) hs (by linarith : -ε / 2 < 0) hσ
    (by positivity : 0 ≤ 5 * h / 8) (by linarith : 5 * h / 8 < 1)
    hparams.1.le hparams.2.2.1.le hparams.2.1.le (by linarith [hj.1])
    (by linarith [hj.1]) hparams.2.2.2.1.le hparams.2.2.2.2.1 hparams.2.2.2.2.2
  have hnegativeEq : P '' {z ∈ R | σ * z.2 = -v₀} =
      P '' ((fun u : ℝ => (u, -(σ * v₀))) '' Icc (-u₀) u₀) := congrArg (P '' ·) hfaces.1
  have hbottomEq :
      P '' {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} ∪
        (fun y => (Q (y, c + s + (-ε / 2))).1) '' C =
      (P '' (lowerSaddleArm s (-ε / 2) (-1) σ '' Icc (-v₀) v₁)) ∪
        ((fun y => (Q (y, c + s + (-ε / 2))).1) '' C) ∪
        (P '' (lowerSaddleArm s (-ε / 2) 1 σ '' Icc (-v₀) v₁)) := by
    rw [hfaces.2, image_union]
    exact union_right_comm _ _ _
  have hboundaryEq : Cexplicit = Cboundary := by
    have hsplit : {z ∈ R | σ * z.2 = -v₀ ∨
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} =
        {z ∈ R | σ * z.2 = -v₀} ∪
          {z ∈ R | (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = -ε / 2} := by
      ext z
      simp only [mem_ofPred_eq, mem_union]
      tauto
    dsimp only [Cboundary]
    rw [hsplit, image_union, union_assoc, hnegativeEq, hbottomEq]
  rw [hboundaryEq] at hJord heq hcut
  refine ⟨hJord, heq, by rw [heq]; exact (Schoenflies.jordan_curve_theorem hJord).frontier_closure_inside, ?_⟩
  dsimp only
  rw [hnegativeEq, hbottomEq]
  exact hcut

theorem exists_partialDiffeomorph_saddle_cutoff_boundary
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (T Q : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (θ : ℝ × ℝ → ℝ) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (hT : ∀ p, (T p).2 = p.2) (hQ : ∀ p, (Q p).2 = ψ p.2)
    {s a j ℓ t₀ δ σ h k ρ r v₀ ε d : ℝ}
    (hs : 0 < s) (ha : a < 0) (ht₀ : 0 < t₀) (ht₀δ : t₀ < δ)
    (hσ : σ ^ 2 = 1) (hk : 0 < k) (hhalfk : h / 2 < k) (hkh : k < h) (hh1 : h < 1)
    (hεa : -ε < a) (had : a < d)
    (hak : 0 < a + s * k ^ 2) (hr : 0 < r) (hv₀ : 0 < v₀)
    (hv₀j : v₀ ^ 2 / 2 < j) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hθ : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    (hcurve : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-k) k) ⊆ G '' sphere 0 r)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    (hclear : ∀ b < t₀, ∃ η > 0, cthickening η
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + b}) ⊆
          (G '' closedBall 0 r)ᶜ)
    {Vside : Set (ℝ × ℝ)} (hVside : IsOpen Vside)
    (hcurveVside : ∀ ξ ∈ ({-1, 1} : Set ℝ), saddleBandLevelCurve s t₀ σ (ξ * k) ∈ Vside)
    (hcapSide : ∀ z ∈ Vside, B z ∈ G '' closedBall 0 r ↔
      s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
    {Vraw : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ Vraw)
    (hTraw : ∀ q ∈ Vraw, T (B q.2, ℓ + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), ℓ + q.1))
    {K : Set (Schoenflies.Plane × ℝ)} (hK : IsCompact K)
    {OQ : Set Schoenflies.Plane} (hOQ : IsOpen OQ) {gQ : Schoenflies.Plane → ℝ}
    (hgQ : ContDiffOn ℝ ∞ gQ OQ) {WQ : Set (Schoenflies.Plane × ℝ)}
    (hKW : Q '' K ⊆ WQ) (hWQO : WQ ⊆ {p | p.1 ∈ OQ})
    (hKgraph : ∀ p ∈ K, (Q p).2 = gQ (Q p).1)
    (hKheight : ∀ p ∈ K, ℓ + a ≤ p.2) :
    let q : (ℝ × ℝ) → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧ a ≤ q z ∧ q z ≤ j}
    let C := G '' sphere 0 r \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-k) k)
    let S := ((fun z => ((T (B z, ℓ + q z)).1, q z)) '' R) ∪ C ×ˢ Icc a j
    let P : (ℝ × ℝ) → Schoenflies.Plane := fun z => (Q (T (B z, ℓ + q z))).1
    let u₀ := Real.sqrt ((v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s))
    (∀ z ∈ R, |z.1| = k → 0 < σ * z.2) →
    (∀ z ∈ R, T (B z, ℓ + q z) =
      (B (saddleBandCurve z (θ (q z, z.1) * (t₀ - q z))), ℓ + q z)) →
    (∀ z ∈ R, -v₀ ≤ σ * (B.symm (T (B z, ℓ + q z)).1).2) →
    (∀ z ∈ R, (1 - (B.symm (T (B z, ℓ + q z)).1).1 ^ 2) *
      ((B.symm (T (B z, ℓ + q z)).1).2 ^ 2 + 2 * s) / 2 ≤ s + t₀) →
    InjOn (fun p : Schoenflies.Plane × ℝ => (Q (p.1, ℓ + p.2)).1) S →
    let Bottom := P '' {z ∈ R | q z = a} ∪ (fun y => (Q (y, ℓ + a)).1) '' C
    let N := P '' {z ∈ R | σ * z.2 = -v₀}
    let Cboundary := N ∪ Bottom
    (fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K =
      closure (Schoenflies.inside Cboundary) →
    Schoenflies.IsCutPair Cboundary (P (-u₀, -(σ * v₀))) (P (u₀, -(σ * v₀))) N Bottom →
    (∀ x ∈ Bottom, gQ x = ψ (ℓ + a) ∧ fderiv ℝ gQ x ≠ 0) →
    ∀ χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane)
        (ℝ × ℝ) Schoenflies.Plane ∞,
    (fun z : ℝ × ℝ => (q z, z.1)) '' {z ∈ R | σ * z.2 = -v₀} ⊆ χ.source →
    (χ : (ℝ × ℝ) → Schoenflies.Plane) =
      (fun p => P (saddleBandLevelCurve s p.1 (-σ) p.2)) →
    (∀ p ∈ χ.source, gQ (χ p) = ψ (ℓ + p.1)) →
    χ.toOpenPartialHomeomorph.IsImage
      {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2}
      ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) →
    ∃ β : ℝ → Schoenflies.Plane,
      ContDiff ℝ ∞ β ∧ (∀ t, deriv β t ≠ 0) ∧ InjOn β (Icc (-u₀) u₀) ∧
      β '' Icc (-u₀) u₀ = Bottom ∧
      β (-u₀) = P (-u₀, -(σ * v₀)) ∧ β u₀ = P (u₀, -(σ * v₀)) ∧
      ∃ D : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane)
          (ℝ × ℝ) Schoenflies.Plane ∞,
        {a} ×ˢ Icc (-u₀) u₀ ⊆ D.source ∧ D.target ⊆ OQ ∧
        (∀ x ∈ Icc (-u₀) u₀, D (a, x) = β x) ∧
        (∀ p ∈ D.source, gQ (D p) = ψ (ℓ + p.1)) ∧
        D.toOpenPartialHomeomorph.IsImage
          {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2}
          ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) ∧
        (∀ x ∈ ({-u₀, u₀} : Set ℝ), (D : (ℝ × ℝ) → Schoenflies.Plane) =ᶠ[𝓝 (a, x)] χ) ∧
        ∃ η : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane)
            (ℝ × ℝ) Schoenflies.Plane ∞,
          let K₀ := (fun u : ℝ => (v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * u ^ 2, u)) '' Icc (-u₀) u₀
          let K₁ := {a} ×ˢ Icc (-u₀) u₀
          K₀ ∪ K₁ ⊆ η.source ∧ η '' (K₀ ∪ K₁) = Cboundary ∧
          η.toOpenPartialHomeomorph.IsImage
            {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * p.2 ^ 2}
            ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) ∧
          (∀ p ∈ η.source, gQ (η p) = ψ (ℓ + p.1)) ∧
          (∀ p ∈ K₀, (η : (ℝ × ℝ) → Schoenflies.Plane) =ᶠ[𝓝 p] χ) ∧
          (∀ p ∈ K₁, (η : (ℝ × ℝ) → Schoenflies.Plane) =ᶠ[𝓝 p] D) := by
  intro q R C S P u₀ hside hmodel hbottom henergy hproj Bottom N Cboundary
    hregion hcut hreg χ hχsource hχformula hχheight hχimage
  let v₁ := Real.sqrt (2 * (a + s * k ^ 2) / (1 - k ^ 2))
  have hk1 : k < 1 := hkh.trans hh1
  obtain ⟨hv₁, hv₀₁, hu₀, hu₀k, hv₁sq, hu₀sq⟩ :=
    lower_saddle_boundary_parameters hs ha hσ hk hk1 hak hv₀ hv₀j
      (fun z hz hv hl hj he => hside z ⟨hz, hv, hl, hj⟩ he)
  change 0 < u₀ at hu₀
  change u₀ < k at hu₀k
  change u₀ ^ 2 = (v₀ ^ 2 - 2 * a) / (v₀ ^ 2 + 2 * s) at hu₀sq
  have hfaces := saddle_half_band_lower_faces_eq hs ha hσ hk.le hk1 hv₁.le hu₀.le
    hv₀₁.le hv₀j.le (by nlinarith only [ha, hv₀j, sq_nonneg v₀]) hu₀k.le hv₁sq hu₀sq
  have hBottom : Bottom =
      (P '' (lowerSaddleArm s a (-1) σ '' Icc (-v₀) v₁)) ∪
        ((fun y => (Q (y, ℓ + a)).1) '' C) ∪
        (P '' (lowerSaddleArm s a 1 σ '' Icc (-v₀) v₁)) := by
    change P '' {z ∈ R | q z = a} ∪ _ = _
    rw [hfaces.2, image_union]
    exact union_right_comm _ _ _
  obtain ⟨g, u, v, hu, hv, hg, hgd, hginj, _, _, hgimage,
      D₀, D₁, hm₀, hm₁, hD₀, hD₁, hg₀, hg₁⟩ :=
    exists_smooth_saddle_cutoff_bottom_arc B G T Q θ ψ hT hQ hs ha ht₀ ht₀δ hσ
      hk hhalfk hkh hh1 hεa had hak hr hv₀ hv₀j hv₀t hθ hcurve hupper hclear
      hVside hcurveVside hcapSide hKV hTraw hside hmodel hbottom henergy hproj
  change g '' Icc u v = _ at hgimage
  have hgBottom : g '' Icc u v = Bottom := hgimage.trans hBottom.symm
  have hJord : Schoenflies.IsJordanCurve Cboundary := by
    rw [← hcut.union_eq]
    exact Schoenflies.isJordanCurve_union hcut.fst hcut.snd (fun x hx hy => by
      have hm := hcut.inter_eq.subset ⟨hx, hy⟩
      simpa only [mem_insert_iff, mem_singleton_iff] using hm)
  have hfrontier : frontier ((fun p : Schoenflies.Plane × ℝ => (Q p).1) '' K) = Cboundary := by
    rw [hregion]
    exact (Schoenflies.jordan_curve_theorem hJord).frontier_closure_inside
  obtain ⟨β, hβ, hβd, hβinj, hβimage, D, hDs, hDt, hDb, hDh, hDχ⟩ :=
    actual_saddle_cutoff_bottom_collar Q ψ hK hfrontier hOQ hgQ hKW hWQO
      hs ha hσ hv₀ hk hk1 hak hv₀j (by linarith only [hu, hv]) hg hgd hginj
      (hgBottom.symm ▸ hcut.snd_subset) (hgBottom.symm ▸ hreg)
      D₀ D₁ hm₀ hm₁ hD₀ hD₁ hg₀ hg₁ hside χ hχsource hχformula hχheight
  have hβBottom : β '' Icc (-u₀) u₀ = Bottom := hβimage.trans hgBottom
  have hden : 0 < v₀ ^ 2 + 2 * s := by positivity
  have hlevel : (1 - u₀ ^ 2) * (v₀ ^ 2 + 2 * s) / 2 - s = a := by
    have hm := (eq_div_iff hden.ne').mp hu₀sq
    nlinarith only [hm]
  have hcorners (x : ℝ) (hx : x ∈ ({-u₀, u₀} : Set ℝ)) :
      (a, x) ∈ χ.source ∧ β x = P (x, -(σ * v₀)) := by
    have hxabs : |x| = u₀ := by
      rcases hx with rfl | hx
      · simp only [abs_neg, abs_of_pos hu₀]
      · have he : x = u₀ := hx; subst x; exact abs_of_pos hu₀
    have hxsq : x ^ 2 = u₀ ^ 2 := by rw [← sq_abs x, hxabs]
    have hxI : x ∈ Icc (-u₀) u₀ := abs_le.mp hxabs.le
    have hσv : σ * (-(σ * v₀)) = -v₀ := by
      rw [mul_neg, ← mul_assoc, ← pow_two, hσ, one_mul]
    have hq : q (x, -(σ * v₀)) = a := by
      simp only [q, hxsq, neg_sq, mul_pow, hσ, one_mul, hlevel]
    have hz : (x, -(σ * v₀)) ∈ R := negative_edge_mem_half_band hs hσ hv₀j.le
      hu₀k.le hu₀sq hxI
    refine ⟨hχsource ⟨(x, -(σ * v₀)), ⟨hz, hσv⟩, Prod.ext hq rfl⟩, ?_⟩
    rw [← hDb x hxI, (hDχ x hx).self_of_nhds, hχformula]
    have hdenx : 0 < 1 - x ^ 2 := by nlinarith only [hxsq, hu₀, hu₀k.trans hk1]
    have hratio : 2 * (a + s * x ^ 2) / (1 - x ^ 2) = v₀ ^ 2 := by
      rw [hxsq] at hdenx ⊢
      apply (div_eq_iff hdenx.ne').mpr
      nlinarith only [hlevel]
    simp only [saddleBandLevelCurve, hratio, Real.sqrt_sq hv₀.le, neg_mul]
  let f : Schoenflies.Plane → ℝ := fun x => ψ.symm (gQ x) - ℓ
  have hf : ContDiffOn ℝ ∞ f OQ := (ψ.symm.contDiff.comp_contDiffOn hgQ).sub contDiffOn_const
  have hDf (p) (hp : p ∈ D.source) : f (D p) = p.1 := by
    simp only [f, hDh p hp, ψ.symm_apply_apply, add_sub_cancel_left]
  have hfreg (u) (hu : u ∈ Icc (-u₀) u₀) : fderiv ℝ f (β u) ≠ 0 := by
    have hO : β u ∈ OQ := hDb u hu ▸ hDt (D.map_source (hDs ⟨rfl, hu⟩))
    have hfd := (hf.contDiffAt (hOQ.mem_nhds hO)).differentiableAt (by simp)
    have hd := (ψ.contDiff.differentiable (by simp) (f (β u) + ℓ)).hasFDerivAt.comp (β u)
      (hfd.hasFDerivAt.add_const ℓ)
    have he : (fun y => ψ (f y + ℓ)) = gQ := by
      funext y; simp only [f, sub_add_cancel, ψ.apply_symm_apply]
    intro hz
    apply (hreg (β u) (hβBottom ▸ mem_image_of_mem β hu)).2
    change HasFDerivAt (fun y => ψ (f y + ℓ))
      ((fderiv ℝ ψ (f (β u) + ℓ)).comp (fderiv ℝ f (β u))) (β u) at hd
    rw [he] at hd
    rw [hd.fderiv, hz, ContinuousLinearMap.comp_zero]
  have hsideHeight (x) (hx : x ∈ Schoenflies.inside Cboundary) : a ≤ f x := by
    obtain ⟨p, hp, rfl⟩ := hregion.symm ▸ subset_closure hx
    simp only [f, ← hKgraph p hp, hQ, ψ.symm_apply_apply]
    linarith only [hKheight p hp]
  have hβcut : Schoenflies.IsCutPair Cboundary (β (-u₀)) (β u₀) N (β '' Icc (-u₀) u₀) := by
    rw [hβBottom, (hcorners (-u₀) (by simp)).2, (hcorners u₀ (by simp)).2]
    exact hcut
  obtain ⟨E, hEs, hEsD, hEtD, hED, hEimage⟩ :=
    PlanarJordan.exists_partialDiffeomorph_isImage_level_arc D χ
      (H := fun u => v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * u ^ 2)
      (by fun_prop) (by linarith only [hu₀]) (fun u hu => by
        have hsq : u ^ 2 < u₀ ^ 2 := by nlinarith only [hu.1, hu.2]
        have hp := mul_pos (sub_pos.mpr hsq) (show 0 < s + v₀ ^ 2 / 2 by positivity)
        nlinarith only [hp, hlevel])
      (Schoenflies.jordan_curve_theorem hJord) hβcut hβinj hDs hDb hDt hf hDf hfreg hsideHeight
      (hregion ▸ hχimage) (fun u hu => ⟨(hcorners u hu).1, hDχ u hu⟩)
  let H : ℝ → ℝ := fun u => v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * u ^ 2
  let K₀ : Set (ℝ × ℝ) := (fun u => (H u, u)) '' Icc (-u₀) u₀
  let K₁ : Set (ℝ × ℝ) := {a} ×ˢ Icc (-u₀) u₀
  have hHends : H (-u₀) = a ∧ H u₀ = a := by
    dsimp only [H]
    constructor <;> nlinarith only [hlevel]
  have hqH (u : ℝ) : q (u, -(σ * v₀)) = H u := by
    simp only [q, H, neg_sq, mul_pow, hσ, one_mul]
    ring
  have hχtop (u : ℝ) (hu : u ∈ Icc (-u₀) u₀) : χ (H u, u) = P (u, -(σ * v₀)) := by
    rw [hχformula]
    have hdenu : 0 < 1 - u ^ 2 := by nlinarith only [hu.1, hu.2, hu₀, hu₀k.trans hk1]
    have hratio : 2 * (H u + s * u ^ 2) / (1 - u ^ 2) = v₀ ^ 2 := by
      apply (div_eq_iff hdenu.ne').mpr
      dsimp only [H]
      ring
    simp only [saddleBandLevelCurve, hratio, Real.sqrt_sq hv₀.le, neg_mul]
  have hχtopSource : K₀ ⊆ χ.source := by
    rintro _ ⟨u, hu, rfl⟩
    have hz := negative_edge_mem_half_band hs hσ hv₀j.le hu₀k.le hu₀sq hu
    have hσv : σ * (-(σ * v₀)) = -v₀ := by
      rw [mul_neg, ← mul_assoc, ← pow_two, hσ, one_mul]
    exact hχsource ⟨(u, -(σ * v₀)), ⟨hz, hσv⟩, Prod.ext (hqH u) rfl⟩
  have hχN : χ '' K₀ = N := by
    dsimp only [N, K₀]
    rw [hfaces.1, image_image, image_image]
    exact image_congr hχtop
  have hEBottom : E '' K₁ = Bottom := by
    rw [← hβBottom]
    ext y
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, he⟩
      have heq : t = a := ht
      subst t
      rw [hED, hDb u hu] at he
      exact ⟨u, hu, he⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(a, u), ⟨rfl, hu⟩, by rw [hED, hDb u hu]⟩
  have hχcut : Schoenflies.IsCutPair Cboundary (χ (a, -u₀)) (χ (a, u₀)) N Bottom := by
    rw [← hHends.1, hχtop (-u₀) ⟨le_rfl, by linarith only [hu₀]⟩,
      hHends.1, ← hHends.2, hχtop u₀ ⟨by linarith only [hu₀], le_rfl⟩]
    exact hcut
  obtain ⟨η, hηsource, hηboundary, hηimage, hηf, hηχ, hηE⟩ :=
    PlanarJordan.exists_partialDiffeomorph_of_band_boundary_collars χ E
      (by linarith only [hu₀]) (show Continuous H by fun_prop) hHends.1 hHends.2
      (fun u hu => by
        have hsq : u ^ 2 < u₀ ^ 2 := by nlinarith only [hu.1, hu.2]
        have hp := mul_pos (sub_pos.mpr hsq) (show 0 < s + v₀ ^ 2 / 2 by positivity)
        dsimp only [H]
        nlinarith only [hp, hlevel])
      hχcut hχtopSource hEs hχN hEBottom hχimage (hregion.symm ▸ hEimage)
      (f := f) (fun p hp => by simp only [f, hχheight p hp, ψ.symm_apply_apply, add_sub_cancel_left])
      (fun p hp => by rw [hED]; exact hDf p (hEsD hp))
      (fun x hx => hED ▸ hDχ x hx)
  have hηheight (p) (hp : p ∈ η.source) : gQ (η p) = ψ (ℓ + p.1) := by
    have he := hηf p hp
    change ψ.symm (gQ (η p)) - ℓ = p.1 at he
    have he' : ψ.symm (gQ (η p)) = ℓ + p.1 := by linarith only [he]
    rw [← he', ψ.apply_symm_apply]
  exact ⟨β, hβ, hβd, hβinj, hβBottom, (hcorners (-u₀) (by simp)).2,
    (hcorners u₀ (by simp)).2, E, hEs, hEtD.trans hDt,
    (fun x hx => by rw [hED]; exact hDb x hx),
    (fun p hp => by rw [hED]; exact hDh p (hEsD hp)), hregion.symm ▸ hEimage,
    (fun x hx => hED ▸ hDχ x hx), η, hηsource, hηboundary, hηimage, hηheight, hηχ, hηE⟩

end DifferentialGeometry.Topology.SphereSeparation
