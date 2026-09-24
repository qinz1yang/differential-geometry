import DifferentialGeometry.Topology.PlanarJordan.CutBoundaryExtension
import DifferentialGeometry.Topology.PlanarJordan.Regions
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem parabolic_lens_geometry {a A B : ℝ} (ha : a < A) (hB : 0 < B) :
    let X : Set (ℝ × ℝ) := {z | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2}
    IsCompact X ∧ Convex ℝ X ∧ (interior X).Nonempty ∧
      frontier X = {z | (a ≤ z.1 ∧ z.1 = A - B * z.2 ^ 2) ∨
        (z.1 = a ∧ a ≤ A - B * z.2 ^ 2)} := by
  let X : Set (ℝ × ℝ) := {z | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2}
  have hX : IsClosed X := (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst (continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))))
  have hstrict : {z : ℝ × ℝ | a < z.1 ∧ z.1 < A - B * z.2 ^ 2} ⊆ interior X := by
    apply interior_maximal
    · exact fun z hz => ⟨hz.1.le, hz.2.le⟩
    · exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst (continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))))
  have hne : (interior X).Nonempty := ⟨((a + A) / 2, 0), hstrict (by
    change a < (a + A) / 2 ∧ (a + A) / 2 < A - B * 0 ^ 2
    constructor <;> nlinarith)⟩
  let r := Real.sqrt ((A - a) / B)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos (sub_pos.mpr ha) hB)
  have hrsq : B * r ^ 2 = A - a := by
    rw [Real.sq_sqrt (div_pos (sub_pos.mpr ha) hB).le, mul_div_cancel₀ _ hB.ne']
  have hbound : X ⊆ Icc a A ×ˢ Icc (-r) r := by
    intro z hz
    have hzsq : z.2 ^ 2 ≤ r ^ 2 := by nlinarith [hz.1, hz.2]
    exact ⟨⟨hz.1, by nlinarith [hz.2, mul_nonneg hB.le (sq_nonneg z.2)]⟩,
      by nlinarith [sq_nonneg (z.2 + r)], by nlinarith [sq_nonneg (z.2 - r)]⟩
  refine ⟨(isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hX hbound, ?_, hne, ?_⟩
  · intro x hx y hy s t hs ht hst
    change a ≤ s * x.1 + t * y.1 ∧
      s * x.1 + t * y.1 ≤ A - B * (s * x.2 + t * y.2) ^ 2
    have hsq : (s * x.2 + t * y.2) ^ 2 ≤ s * x.2 ^ 2 + t * y.2 ^ 2 := by
      have hvariance : s * x.2 ^ 2 + t * y.2 ^ 2 - (s * x.2 + t * y.2) ^ 2 =
          s * t * (x.2 - y.2) ^ 2 := by
        calc
          _ = (s + t) * (s * x.2 ^ 2 + t * y.2 ^ 2) - (s * x.2 + t * y.2) ^ 2 := by rw [hst, one_mul]
          _ = _ := by ring
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x.2 - y.2))]
    constructor
    · have haeq : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hx.1), mul_nonneg ht (sub_nonneg.mpr hy.1)]
    · have hsx := mul_nonneg hs (sub_nonneg.mpr hx.2)
      have hty := mul_nonneg ht (sub_nonneg.mpr hy.2)
      have hAeq : s * A + t * A = A := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hsq)]
  · ext z
    constructor
    · intro hz
      have hzX : z ∈ X := hX.closure_eq ▸ hz.1
      by_cases ht : z.1 = A - B * z.2 ^ 2
      · exact Or.inl ⟨hzX.1, ht⟩
      · have haeq : z.1 = a := by
          by_contra hn
          exact hz.2 (hstrict ⟨lt_of_le_of_ne hzX.1 (Ne.symm hn), lt_of_le_of_ne hzX.2 ht⟩)
        exact Or.inr ⟨haeq, haeq ▸ hzX.2⟩
    · intro hz
      rw [frontier_eq_closure_inter_closure]
      constructor
      · apply subset_closure
        rcases hz with hz | hz
        · exact ⟨hz.1, hz.2.le⟩
        · exact ⟨hz.1.ge, hz.1.symm ▸ hz.2⟩
      · rw [Metric.mem_closure_iff]
        intro ε hε
        rcases hz with hz | hz
        · refine ⟨(z.1 + ε / 2, z.2), ?_, ?_⟩
          · change ¬ (a ≤ z.1 + ε / 2 ∧ z.1 + ε / 2 ≤ A - B * z.2 ^ 2)
            intro hh
            linarith [hh.2]
          · rw [Prod.dist_eq, dist_self, Real.dist_eq]
            simp only [show z.1 - (z.1 + ε / 2) = -(ε / 2) by ring, abs_neg,
              abs_of_pos (half_pos hε), max_eq_left (half_pos hε).le]
            linarith
        · refine ⟨(z.1 - ε / 2, z.2), ?_, ?_⟩
          · change ¬ (a ≤ z.1 - ε / 2 ∧ z.1 - ε / 2 ≤ A - B * z.2 ^ 2)
            intro hh
            linarith [hh.1]
          · rw [Prod.dist_eq, dist_self, Real.dist_eq]
            simp only [show z.1 - (z.1 - ε / 2) = ε / 2 by ring,
              abs_of_pos (half_pos hε), max_eq_left (half_pos hε).le]
            linarith


theorem interior_parabolic_lens {a A B : ℝ} (ha : a < A) (hB : 0 < B) :
    interior {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} =
      {z | a < z.1 ∧ z.1 < A - B * z.2 ^ 2} := by
  apply subset_antisymm
  · intro p hp
    have hpX := interior_subset hp
    have hpn : p ∉ frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} :=
      disjoint_left.mp disjoint_interior_frontier hp
    rw [(parabolic_lens_geometry ha hB).2.2.2] at hpn
    exact ⟨lt_of_le_of_ne hpX.1 (fun he => hpn (Or.inr ⟨he.symm, he ▸ hpX.2⟩)),
      lt_of_le_of_ne hpX.2 (fun he => hpn (Or.inl ⟨hpX.1, he⟩))⟩
  · apply interior_maximal
    · exact fun p hp => ⟨hp.1.le, hp.2.le⟩
    · exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst (continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))))

theorem frontier_parabolic_lens {a A B : ℝ} (ha : a < A) (hB : 0 < B) :
    frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} =
      (fun u : ℝ => (A - B * u ^ 2, u)) ''
        Icc (-Real.sqrt ((A - a) / B)) (Real.sqrt ((A - a) / B)) ∪
      {a} ×ˢ Icc (-Real.sqrt ((A - a) / B)) (Real.sqrt ((A - a) / B)) := by
  rw [(parabolic_lens_geometry ha hB).2.2.2]
  let r := Real.sqrt ((A - a) / B)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos (sub_pos.mpr ha) hB)
  have hrsq : B * r ^ 2 = A - a := by
    rw [Real.sq_sqrt (div_pos (sub_pos.mpr ha) hB).le, mul_div_cancel₀ _ hB.ne']
  have hmem (u : ℝ) : a ≤ A - B * u ^ 2 ↔ u ∈ Icc (-r) r := by
    constructor
    · intro hu
      have husq : u ^ 2 ≤ r ^ 2 := by nlinarith
      exact ⟨by nlinarith [sq_nonneg (u + r)], by nlinarith [sq_nonneg (u - r)]⟩
    · intro hu
      have husq : u ^ 2 ≤ r ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ u + r by linarith [hu.1]) (sub_nonneg.mpr hu.2)]
      nlinarith
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl ⟨z.2, (hmem _).mp (hz.2 ▸ hz.1), Prod.ext hz.2.symm rfl⟩
    · exact Or.inr ⟨hz.1, (hmem _).mp hz.2⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨ha, hu⟩)
    · exact Or.inl ⟨(hmem _).mpr hu, rfl⟩
    · exact Or.inr ⟨ha, (hmem _).mpr hu⟩

private theorem exists_parabolic_lens_corner_band
    (L : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {a A B : ℝ} (ha : a < A) (hB : 0 < B) :
    ∃ D : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane, ∃ δ : ℝ, 0 < δ ∧
      (∀ z : ℝ × ℝ, |z.2| < δ →
        D z = L (a + z.2, Real.sqrt ((A - a - z.2) / B) * z.1) ∧
        (D z ∈ L '' {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ A - B * p.2 ^ 2} ↔
          -1 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2)) := by
  have h0 : (0 : ℝ) ∈ Iio (A - a) := sub_pos.mpr ha
  obtain ⟨φ, hφ, hφid, hφrange⟩ :=
    DifferentialGeometry.exists_contDiff_eventuallyEq_id_range_subset (isOpen_Iio.mem_nhds h0)
  have hpos (u : ℝ) : 0 < (A - a - φ u) / B :=
    div_pos (sub_pos.mpr (hφrange ⟨u, rfl⟩)) hB
  let r := fun u => Real.sqrt ((A - a - φ u) / B)
  have hr : ContDiff ℝ ∞ r :=
    ((contDiff_const.sub hφ).div_const B).sqrt (fun u => (hpos u).ne')
  have hrpos (u : ℝ) : 0 < r u := Real.sqrt_pos.mpr (hpos u)
  let P : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := {
    toEquiv := {
      toFun z := (a + z.2, z.1)
      invFun z := (z.2, z.1 - a)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
    contMDiff_toFun := ((contDiff_const.add contDiff_snd).prodMk contDiff_fst).contMDiff
    contMDiff_invFun := (contDiff_snd.prodMk (contDiff_fst.sub contDiff_const)).contMDiff }
  let D := ((Diffeomorph.fiberwiseSmul (E := ℝ) hr (fun u => (hrpos u).ne')).trans P).trans L
  have hD (z : ℝ × ℝ) : D z = L (a + z.2, r z.2 * z.1) := rfl
  obtain ⟨δ, hδ, heq⟩ := Metric.mem_nhds_iff.mp hφid
  refine ⟨D, δ, hδ, ?_⟩
  intro z hz
  have hφz : φ z.2 = z.2 := heq (by simpa only [mem_ball, Real.dist_eq, sub_zero] using hz)
  have hrz : r z.2 = Real.sqrt ((A - a - z.2) / B) := by dsimp [r]; rw [hφz]
  have hrsq : B * r z.2 ^ 2 = A - a - z.2 := by
    dsimp [r]
    rw [Real.sq_sqrt (hpos z.2).le, mul_div_cancel₀ _ hB.ne', hφz]
  refine ⟨by rw [hD, hrz], ?_⟩
  have hLi : Function.Injective (L : (ℝ × ℝ) → Schoenflies.Plane) := L.injective
  rw [hD, hLi.mem_set_image]
  change (a ≤ a + z.2 ∧ a + z.2 ≤ A - B * (r z.2 * z.1) ^ 2) ↔ _
  have hwidth : 0 < B * r z.2 ^ 2 := mul_pos hB (sq_pos_of_pos (hrpos _))
  constructor
  · intro hh
    have hsq : z.1 ^ 2 ≤ 1 := by nlinarith [hh.2]
    exact ⟨by nlinarith [sq_nonneg (z.1 + 1)], by nlinarith [sq_nonneg (z.1 - 1)], by linarith [hh.1]⟩
  · rintro ⟨hl, hh, hv⟩
    have hsq : z.1 ^ 2 ≤ 1 := by nlinarith [mul_nonneg (show 0 ≤ z.1 + 1 by linarith) (show 0 ≤ 1 - z.1 by linarith)]
    exact ⟨by linarith, by nlinarith⟩


private theorem exists_regular_defining_function_parabolic_lens
    (L : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane) {a A B : ℝ} (ha : a < A) (hB : 0 < B)
    {q : Schoenflies.Plane}
    (hq : q ∈ L '' frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2})
    (hne : q ∉ ({L (a, -Real.sqrt ((A - a) / B)), L (a, Real.sqrt ((A - a) / B))} : Set Schoenflies.Plane)) :
    ∃ U : Set Schoenflies.Plane, ∃ f : Schoenflies.Plane → ℝ,
      IsOpen U ∧ q ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      (∀ x ∈ U, x ∈ L '' frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} ↔ f x = 0) ∧
      fderiv ℝ f q ≠ 0 := by
  let f₀ : Schoenflies.Plane →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.symm.toContinuousLinearMap
  let f₁ : Schoenflies.Plane →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.symm.toContinuousLinearMap
  have h₀ (p : ℝ × ℝ) : f₀ (L p) = p.1 := by change (L.symm (L p)).1 = p.1; rw [L.symm_apply_apply]
  have h₁ (p : ℝ × ℝ) : f₁ (L p) = p.2 := by change (L.symm (L p)).2 = p.2; rw [L.symm_apply_apply]
  obtain ⟨p, hp, rfl⟩ := hq
  have hf : ∀ x : Schoenflies.Plane,
      x ∈ L '' frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} ↔
        (a ≤ f₀ x ∧ f₀ x = A - B * (f₁ x) ^ 2) ∨
          (f₀ x = a ∧ a ≤ A - B * (f₁ x) ^ 2) := by
    intro x
    rw [Set.mem_image_iff_of_inverse L.symm_apply_apply L.apply_symm_apply,
      (parabolic_lens_geometry ha hB).2.2.2]
    rfl
  rw [(parabolic_lens_geometry ha hB).2.2.2] at hp
  have hcorner : ¬ (p.1 = a ∧ p.1 = A - B * p.2 ^ 2) := by
    rintro ⟨ht, hg⟩
    have hrsq : B * (Real.sqrt ((A - a) / B)) ^ 2 = A - a := by
      rw [Real.sq_sqrt (div_pos (sub_pos.mpr ha) hB).le, mul_div_cancel₀ _ hB.ne']
    have he : p.2 ^ 2 = (Real.sqrt ((A - a) / B)) ^ 2 := by nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with hu | hu
    · exact hne (Or.inr (congrArg L (Prod.ext ht hu)))
    · exact hne (Or.inl (congrArg L (Prod.ext ht hu)))
  by_cases ht : a < p.1
  · let U := {x : Schoenflies.Plane | a < f₀ x}
    let g := fun x : Schoenflies.Plane => f₀ x + B * (f₁ x) ^ 2 - A
    have hg : ContDiff ℝ ∞ g :=
      (f₀.contDiff.add (contDiff_const.mul (f₁.contDiff.pow 2))).sub contDiff_const
    have hd := (f₀.hasFDerivAt.add ((f₁.hasFDerivAt.pow 2).const_mul B)).sub_const A (x := L p)
    refine ⟨U, g, isOpen_lt continuous_const f₀.continuous,
      by change a < f₀ (L p); rwa [h₀], hg.contDiffOn, ?_, ?_⟩
    · intro x hx
      rw [hf]
      change a < f₀ x at hx
      dsimp [g]
      constructor
      · rintro (hh | hh)
        · linarith [hh.2]
        · exact (hx.ne' hh.1).elim
      · intro hh
        exact Or.inl ⟨hx.le, by linarith⟩
    · intro he
      have hv := congrArg (fun D : Schoenflies.Plane →L[ℝ] ℝ => D (L (1, 0))) he
      rw [show fderiv ℝ g (L p) = _ from hd.fderiv] at hv
      simp [h₀, h₁] at hv
  · have hpfirst : p.1 = a := by
      rcases hp with hp | hp
      · exact le_antisymm (le_of_not_gt ht) hp.1
      · exact hp.1
    have hptop : p.1 < A - B * p.2 ^ 2 := by
      have hle : p.1 ≤ A - B * p.2 ^ 2 := hp.elim (fun h => h.2.le) (fun h => h.1.symm ▸ h.2)
      exact lt_of_le_of_ne hle (fun he => hcorner ⟨hpfirst, he⟩)
    let U := {x : Schoenflies.Plane | f₀ x < A - B * (f₁ x) ^ 2}
    let g := fun x : Schoenflies.Plane => f₀ x - a
    have hd := f₀.hasFDerivAt.sub_const a (x := L p)
    refine ⟨U, g, isOpen_lt f₀.continuous
      (continuous_const.sub (continuous_const.mul (f₁.continuous.pow 2))),
      by change f₀ (L p) < A - B * (f₁ (L p)) ^ 2; rwa [h₀, h₁],
      (f₀.contDiff.sub contDiff_const).contDiffOn, ?_, ?_⟩
    · intro x hx
      rw [hf]
      change f₀ x < A - B * (f₁ x) ^ 2 at hx
      dsimp [g]
      constructor
      · rintro (hh | hh)
        · exact (hx.ne hh.2).elim
        · linarith [hh.1]
      · intro hh
        exact Or.inr ⟨by linarith, by linarith⟩
    · intro he
      have hv := congrArg (fun D : Schoenflies.Plane →L[ℝ] ℝ => D (L (1, 0))) he
      rw [show fderiv ℝ g (L p) = _ from hd.fderiv] at hv
      simp [h₀] at hv


theorem exists_diffeomorph_eqOn_neighborhood_of_parabolic_lens
    {a A B : ℝ} (ha : a < A) (hB : 0 < B)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane)
      (ℝ × ℝ) Schoenflies.Plane ∞)
    {J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J)
    (hsource : frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} ⊆ c.source)
    (hc : c.toOpenPartialHomeomorph.IsImage
      {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} (closure (Schoenflies.inside J))) :
    ∃ F : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane,
      F '' frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} = J ∧
      F '' {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} = closure (Schoenflies.inside J) ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧
        frontier {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2} ⊆ U ∧
        U ⊆ c.source ∧ EqOn F c U := by
  let L : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
    Complex.equivRealProdCLM.symm.trans Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let X : Set (ℝ × ℝ) := {z | a ≤ z.1 ∧ z.1 ≤ A - B * z.2 ^ 2}
  let Y := L '' X
  let J₀ := L '' frontier X
  obtain ⟨hX, hconv, hne, hfr⟩ := parabolic_lens_geometry ha hB
  have hY : IsCompact Y := hX.image L.continuous
  have hYconv : Convex ℝ Y := hconv.linear_image L.toLinearMap
  have hYne : (interior Y).Nonempty := by
    rw [show interior Y = L '' interior X from (L.toHomeomorph.image_interior X).symm]
    exact hne.image L
  obtain ⟨R, _, _, hRf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hYconv hYne hY.isBounded
  have hJfr : J₀ = frontier Y := L.toHomeomorph.image_frontier X
  have hJimage : J₀ = R.symm '' sphere 0 1 := by
    rw [← hRf, image_image]
    simp only [R.symm_apply_apply, image_id', hJfr]
  have hJ₀ : Schoenflies.IsJordanCurve J₀ := hJimage ▸ isJordanCurve_image_sphere R.symm 0 zero_lt_one
  have hYinside : Y = closure (Schoenflies.inside J₀) :=
    eq_closure_inside_of_isCompact_of_frontier_subset hY hJ₀ hYne (hJfr ▸ subset_rfl)
  let d := L.symm.toDiffeomorph.toPartialDiffeomorph.trans c
  have hdsource : J₀ ⊆ d.source := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    change L.symm (L p) ∈ c.source
    rw [L.symm_apply_apply]
    exact hsource hp
  have hd : d.toOpenPartialHomeomorph.IsImage
      (closure (Schoenflies.inside J₀)) (closure (Schoenflies.inside J)) := by
    intro x hx
    change c (L.symm x) ∈ closure (Schoenflies.inside J) ↔ x ∈ closure (Schoenflies.inside J₀)
    rw [← hYinside]
    exact (hc hx.2).trans (Set.mem_image_iff_of_inverse L.symm_apply_apply L.apply_symm_apply).symm
  obtain ⟨D, δ, hδ, hD⟩ := exists_parabolic_lens_corner_band L.toDiffeomorph ha hB
  let r := Real.sqrt ((A - a) / B)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos (sub_pos.mpr ha) hB)
  have hrsq : B * r ^ 2 = A - a := by
    rw [Real.sq_sqrt (div_pos (sub_pos.mpr ha) hB).le, mul_div_cancel₀ _ hB.ne']
  have hDleft : D (-1, 0) = L (a, -r) := by
    have hh := (hD (-1, 0) (by simpa only [abs_zero] using hδ)).1
    change D (-1, 0) = L (a + 0, Real.sqrt ((A - a - 0) / B) * (-1)) at hh
    simpa only [add_zero, sub_zero, mul_neg_one] using hh
  have hDright : D (1, 0) = L (a, r) := by
    have hh := (hD (1, 0) (by simpa only [abs_zero] using hδ)).1
    change D (1, 0) = L (a + 0, Real.sqrt ((A - a - 0) / B) * 1) at hh
    simpa only [add_zero, sub_zero, mul_one] using hh
  have hpoints : ({D (-1, 0), D (1, 0)} : Set Schoenflies.Plane) ⊆ J₀ := by
    rw [hDleft, hDright]
    apply Set.pair_subset_iff.mpr
    constructor
    · refine ⟨(a, -r), ?_, rfl⟩
      rw [hfr]
      exact Or.inr ⟨rfl, by change a ≤ A - B * (-r) ^ 2; nlinarith⟩
    · refine ⟨(a, r), ?_, rfl⟩
      rw [hfr]
      exact Or.inr ⟨rfl, by change a ≤ A - B * r ^ 2; nlinarith⟩
  have hreg : ∀ p ∈ J₀, p ∉ ({D (-1, 0), D (1, 0)} : Set Schoenflies.Plane) →
      ∃ V : Set Schoenflies.Plane, ∃ g : Schoenflies.Plane → ℝ,
        IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧
        (∀ x ∈ V, x ∈ J₀ ↔ g x = 0) ∧ fderiv ℝ g p ≠ 0 := by
    intro p hp hn
    rw [hDleft, hDright] at hn
    exact exists_regular_defining_function_parabolic_lens L ha hB hp hn
  have hprofile : ∀ b ∈ ({-1, 1} : Set ℝ),
      ∀ z ∈ Ioo (b - 1 / 2) (b + 1 / 2) ×ˢ Ioo (-δ) δ,
        D z ∈ closure (Schoenflies.inside J₀) ↔ b * z.1 ≤ 1 ∧ 0 ≤ (1 : ℝ) * z.2 := by
    intro b hb z hz
    have hhz : |z.2| < δ := abs_lt.mpr hz.2
    have hh := (hD z hhz).2
    change D z ∈ Y ↔ _ at hh
    rw [← hYinside, hh, one_mul]
    rcases hb with hb | hb
    · have hb' : b = -1 := hb
      subst b
      constructor
      · rintro ⟨hl, _, hv⟩; exact ⟨by linarith, hv⟩
      · rintro ⟨hl, hv⟩; exact ⟨by linarith, by linarith [hz.1.2], hv⟩
    · have hb' : b = 1 := hb
      subst b
      constructor
      · rintro ⟨_, hh, hv⟩; exact ⟨by linarith, hv⟩
      · rintro ⟨hh, hv⟩; exact ⟨by linarith [hz.1.1], by linarith, hv⟩
  obtain ⟨F, hFJ, hFY, U, hU, hJU, hUs, hFc⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_band_corner_curve D d
      (b := 1) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) hδ d.open_source
      (hpoints.trans hdsource) subset_rfl hJ₀ hJ hdsource hd hreg (Or.inl hprofile)
  refine ⟨L.toDiffeomorph.trans F, ?_, ?_, L ⁻¹' U, hU.preimage L.continuous, ?_, ?_, ?_⟩
  · change (F ∘ L) '' frontier X = J
    rw [image_comp]
    exact hFJ
  · change (F ∘ L) '' X = closure (Schoenflies.inside J)
    rw [image_comp]
    change F '' Y = _
    rw [hYinside]
    exact hFY
  · intro p hp
    exact hJU ⟨p, hp, rfl⟩
  · intro p hp
    have hh := (hUs hp).2
    change L.symm (L p) ∈ c.source at hh
    rwa [L.symm_apply_apply] at hh
  · intro p hp
    have hh := hFc hp
    change F (L p) = c (L.symm (L p)) at hh
    change F (L p) = c p
    simpa only [L.symm_apply_apply] using hh

end DifferentialGeometry.Topology.PlanarJordan
