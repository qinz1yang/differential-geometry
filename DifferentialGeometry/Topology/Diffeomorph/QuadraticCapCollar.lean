import DifferentialGeometry.Topology.Diffeomorph.GraphCap
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Topology.Homeomorph.LevelIsotopy
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

private theorem exists_smooth_quadratic_scaling
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (c : ℝ) :
    ∃ s : ℝ × ℝ → ℝ, ContDiff ℝ ∞ s ∧ (∀ p, 0 < s p) ∧
      (∀ t, s (0, t) = 1) ∧
      (∃ η > 0, ∀ t, |t - (c - r ^ 2 / 2)| ≤ η →
        s (1, t) = Real.sqrt ((c - t) / (r ^ 2 / 2))) ∧
      ∀ τ t, s (τ, t) ≠ 1 →
        t < c ∧ Real.sqrt (2 * (c - t)) / r ∈ Ioo (1 - δ) (1 + δ) ∧
          Real.sqrt (2 * (c - t)) / (r * s (τ, t)) ∈ Ioo (1 - δ) (1 + δ) := by
  let b := c - r ^ 2 / 2
  let d := r ^ 2 / 2
  let A : ℝ × ℝ → ℝ := fun p => 1 - p.2 * (p.1 - b) / d
  let R : ℝ → ℝ := fun t => Real.sqrt (2 * (c - t)) / r
  have hd : 0 < d := by dsimp [d]; positivity
  have hA : Continuous A := by fun_prop
  have hR : Continuous R := by fun_prop
  have hAb (u : ℝ) : A (b, u) = 1 := by simp only [A, sub_self, mul_zero, zero_div, sub_zero]
  have hRb : R b = 1 := by
    have hsq : 2 * (c - b) = r ^ 2 := by dsimp [b]; ring
    simp only [R, hsq, Real.sqrt_sq hr.le, div_self hr.ne']
  have hnb : ∀ᶠ t in 𝓝 b, ∀ u ∈ Icc (0 : ℝ) 1,
      0 < A (t, u) ∧ t < c ∧ R t ∈ Ioo (1 - δ) (1 + δ) ∧
        R t / Real.sqrt (A (t, u)) ∈ Ioo (1 - δ) (1 + δ) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u _
    have hQ : ContinuousAt (fun p : ℝ × ℝ => R p.1 / Real.sqrt (A p)) (b, u) :=
      (hR.comp continuous_fst).continuousAt.div (Real.continuous_sqrt.comp hA).continuousAt
        (by rw [hAb, Real.sqrt_one]; exact one_ne_zero)
    have hQb : R b / Real.sqrt (A (b, u)) = 1 := by rw [hRb, hAb, Real.sqrt_one, div_one]
    filter_upwards [hA.continuousAt.eventually
      (eventually_gt_nhds (by rw [hAb]; exact zero_lt_one)),
      (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ)).continuousAt.eventually
        (eventually_lt_nhds (show b < c by dsimp [b]; nlinarith [sq_pos_of_pos hr])),
      (hR.comp continuous_fst).continuousAt.eventually
        (isOpen_Ioo.mem_nhds (show R b ∈ Ioo (1 - δ) (1 + δ) by
          rw [hRb]; constructor <;> linarith)),
      hQ.eventually (isOpen_Ioo.mem_nhds
        (show R b / Real.sqrt (A (b, u)) ∈ Ioo (1 - δ) (1 + δ) by
          rw [hQb]; constructor <;> linarith))] with p hp hc hRmem hQmem
    exact ⟨hp, hc, hRmem, hQmem⟩
  obtain ⟨η, hη, hηnb⟩ := Metric.eventually_nhds_iff.mp hnb
  let χ : ContDiffBump b := ⟨η / 4, η / 2, by positivity, by linarith⟩
  let u : ℝ × ℝ → ℝ := fun p => Real.smoothTransition p.1 * χ p.2
  have hu : ContDiff ℝ ∞ u :=
    (Real.smoothTransition.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd)
  have humem (p : ℝ × ℝ) : u p ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (Real.smoothTransition.nonneg _) χ.nonneg
    · exact mul_le_one₀ (Real.smoothTransition.le_one _) χ.nonneg χ.le_one
  have hloc (p : ℝ × ℝ) (hp : χ p.2 ≠ 0) : dist p.2 b < η := by
    have hlt : dist p.2 b < η / 2 := lt_of_not_ge (fun h => hp (χ.zero_of_le_dist h))
    linarith
  have hpos (p : ℝ × ℝ) : 0 < A (p.2, u p) := by
    by_cases hp : χ p.2 = 0
    · simp only [A, u, hp, mul_zero, zero_mul, zero_div, sub_zero, zero_lt_one]
    · exact (hηnb (hloc p hp) _ (humem p)).1
  let s : ℝ × ℝ → ℝ := fun p => Real.sqrt (A (p.2, u p))
  have hAs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => A (p.2, u p)) :=
    contDiff_const.sub ((hu.mul (contDiff_snd.sub contDiff_const)).div_const d)
  refine ⟨s, hAs.sqrt (fun p => (hpos p).ne'), fun p => Real.sqrt_pos.mpr (hpos p), ?_,
    ⟨η / 4, by positivity, ?_⟩, ?_⟩
  · intro t
    simp only [s, A, u, Real.smoothTransition.zero, zero_mul, zero_div, sub_zero, Real.sqrt_one]
  · intro t ht
    have hχ : χ t = 1 := χ.one_of_mem_closedBall (by
      rw [mem_closedBall, Real.dist_eq]
      exact ht)
    simp only [s, A, u, Real.smoothTransition.one, one_mul, hχ]
    congr 1
    dsimp [b, d]
    field_simp
    ring
  · intro τ t ht
    have hχ : χ t ≠ 0 := by
      intro hχ
      apply ht
      simp only [s, A, u, hχ, mul_zero, zero_mul, zero_div, sub_zero, Real.sqrt_one]
    have h := hηnb (hloc (τ, t) hχ) _ (humem (τ, t))
    refine ⟨h.2.1, h.2.2.1, ?_⟩
    simpa only [R, s, div_div] using h.2.2.2

private theorem radial_apply_of_norm_div_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E → E) {r δ : ℝ} (hr : 0 < r)
    (hrad : ∀ y ∈ sphere (0 : E) r, ∀ a ∈ Icc (1 - δ) (1 + δ), C (a • y) = a • C y)
    {x : E} (hx : 0 < ‖x‖) (hxr : ‖x‖ / r ∈ Icc (1 - δ) (1 + δ)) :
    C x = (‖x‖ / r) • C ((r / ‖x‖) • x) := by
  have hnorm : (r / ‖x‖) • x ∈ sphere (0 : E) r := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (div_pos hr hx).le]
    exact div_mul_cancel₀ r hx.ne'
  have hscalar : ‖x‖ / r * (r / ‖x‖) = 1 := by field_simp
  have h := hrad _ hnorm _ hxr
  simpa only [smul_smul, hscalar, one_smul] using h

private theorem radial_inv_smul_of_norm_div_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E → E) {r δ s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrad : ∀ y ∈ sphere (0 : E) r, ∀ a ∈ Icc (1 - δ) (1 + δ), C (a • y) = a • C y)
    {x : E} (hx : 0 < ‖x‖)
    (hxr : ‖x‖ / r ∈ Icc (1 - δ) (1 + δ))
    (hxsr : ‖x‖ / (r * s) ∈ Icc (1 - δ) (1 + δ)) :
    C (s⁻¹ • x) = s⁻¹ • C x := by
  have hnorm : (r / ‖x‖) • x ∈ sphere (0 : E) r := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (div_pos hr hx).le]
    exact div_mul_cancel₀ r hx.ne'
  have hscalar : ‖x‖ / (r * s) * (r / ‖x‖) = s⁻¹ := by field_simp
  have h := hrad _ hnorm _ hxsr
  rw [smul_smul, hscalar] at h
  rw [h, radial_apply_of_norm_div_mem C hr hrad hx hxr, smul_smul]
  congr 1
  field_simp

theorem exists_diffeomorph_quadratic_cap_eqOn_radial_collar
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : E ≃ₘ[ℝ] E) {r δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hC : C '' closedBall 0 r = closedBall 0 r)
    (hrad : ∀ x ∈ sphere (0 : E) r, ∀ a ∈ Icc (1 - δ) (1 + δ), C (a • x) = a • C x)
    (hradi : ∀ x ∈ sphere (0 : E) r, ∀ a ∈ Icc (1 - δ) (1 + δ),
      C.symm (a • x) = a • C.symm x) :
    ∃ η > 0, ∃ F : (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
      (∀ p : E × ℝ, |p.2 - (c - r ^ 2 / 2)| ≤ η →
        let s := Real.sqrt ((c - p.2) / (r ^ 2 / 2))
        F p = (s • C (s⁻¹ • p.1), p.2)) ∧
      (∀ p : E × ℝ, c - r ^ 2 / 2 ≤ (F p).2 ↔ c - r ^ 2 / 2 ≤ p.2) ∧
      (∀ p : E × ℝ, c - r ^ 2 / 2 < (F p).2 ↔ c - r ^ 2 / 2 < p.2) ∧
      (∀ x ∈ closedBall (0 : E) r,
        F (x, c - ‖x‖ ^ 2 / 2) = (C x, c - ‖C x‖ ^ 2 / 2)) ∧
      F '' {p : E × ℝ | p.1 ∈ closedBall 0 r ∧
        c - r ^ 2 / 2 ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
        {p : E × ℝ | p.1 ∈ closedBall 0 r ∧
          c - r ^ 2 / 2 ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} := by
  let b := c - r ^ 2 / 2
  let q : E → ℝ := fun x => c - ‖x‖ ^ 2 / 2
  have hCs : C '' sphere 0 r = sphere 0 r := by
    have h := C.toHomeomorph.image_frontier (closedBall 0 r)
    change C '' frontier (closedBall 0 r) = frontier (C '' closedBall 0 r) at h
    simpa only [hC, frontier_closedBall (0 : E) hr.ne'] using h
  have hCis : C.symm '' sphere 0 r = sphere 0 r := by
    calc
      C.symm '' sphere 0 r = C.symm '' (C '' sphere 0 r) :=
        congrArg (fun s => C.symm '' s) hCs.symm
      _ = sphere 0 r := C.symm_image_image _
  have hnear (x : E) (hx : x ∈ closedBall 0 r) (hxr : r - r * δ ≤ ‖x‖) :
      ‖C.symm x‖ = ‖x‖ := by
    have hxpos : 0 < ‖x‖ := by nlinarith
    have ha : ‖x‖ / r ∈ Icc (1 - δ) (1 + δ) := by
      constructor
      · apply (le_div_iff₀ hr).mpr
        nlinarith
      · apply (div_le_iff₀ hr).mpr
        nlinarith [mem_closedBall_zero_iff.mp hx]
    rw [radial_apply_of_norm_div_mem C.symm hr hradi hxpos ha, norm_smul,
      Real.norm_of_nonneg (div_pos hxpos hr).le]
    have hy : (r / ‖x‖) • x ∈ sphere (0 : E) r := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (div_pos hr hxpos).le]
      exact div_mul_cancel₀ r hxpos.ne'
    have hz : C.symm ((r / ‖x‖) • x) ∈ sphere (0 : E) r := by
      rw [← hCis]
      exact mem_image_of_mem C.symm hy
    rw [mem_sphere_zero_iff_norm.mp hz]
    exact div_mul_cancel₀ ‖x‖ hr.ne'
  obtain ⟨ε, hε, G, _, hGslab, hGle, hGlt, hGgraph, hGsolid⟩ :=
    exists_diffeomorph_quadratic_cap_eqOn_halfspace C hr (mul_pos hr hδ) hC hnear (c := c)
  obtain ⟨s, hs, hspos, hs0, ⟨ζ, hζ, hseam⟩, hsrad⟩ :=
    exists_smooth_quadratic_scaling hr hδ c
  let P : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := C.toEquiv.prodCongr (Equiv.refl ℝ)
      contMDiff_toFun := ((C.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
      contMDiff_invFun := ((C.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
  let S (τ : ℝ) := fiberwiseSmul (E := E)
    (hs.comp (contDiff_const.prodMk contDiff_id)) (fun t => (hspos (τ, t)).ne')
  let T (τ : ℝ) := (((S τ).symm.trans P).trans (S τ)).trans P.symm
  have hT (τ : ℝ) (p : E × ℝ) :
      T τ p = (C.symm (s (τ, p.2) • C ((s (τ, p.2))⁻¹ • p.1)), p.2) := rfl
  have hTzero : T 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ := by
    apply Diffeomorph.ext
    intro p
    change T 0 p = p
    rw [hT]
    simp only [hs0, inv_one, one_smul, C.symm_apply_apply, Prod.eta]
  have hTcont : Continuous (fun z : ℝ × (E × ℝ) => T z.1 z.2) := by
    have hS : Continuous (fun z : ℝ × (E × ℝ) => s (z.1, z.2.2)) :=
      hs.continuous.comp (continuous_fst.prodMk continuous_snd.snd)
    exact (C.symm.continuous.comp
      (hS.smul (C.continuous.comp
        ((hS.inv₀ (fun z => (hspos (z.1, z.2.2)).ne')).smul continuous_snd.fst)))).prodMk
          continuous_snd.snd
  have hTgraph (τ : ℝ) (x : E) : T τ (x, q x) = (x, q x) := by
    rw [hT]
    by_cases hseq : s (τ, q x) = 1
    · simp only [hseq, inv_one, one_smul, C.symm_apply_apply]
    · have hradial := hsrad τ (q x) hseq
      have hroot : Real.sqrt (2 * (c - q x)) = ‖x‖ := by
        have heq : 2 * (c - q x) = ‖x‖ ^ 2 := by dsimp [q]; ring
        rw [heq, Real.sqrt_sq (norm_nonneg x)]
      rw [hroot] at hradial
      have hx : 0 < ‖x‖ := by
        have := hradial.2.1.1
        have hratio : 0 < ‖x‖ / r := by linarith
        simpa only [zero_mul] using (lt_div_iff₀ hr).mp hratio
      have heq := radial_inv_smul_of_norm_div_mem C hr (hspos (τ, q x)) hrad hx
        ⟨hradial.2.1.1.le, hradial.2.1.2.le⟩ ⟨hradial.2.2.1.le, hradial.2.2.2.le⟩
      rw [heq, smul_smul, mul_inv_cancel₀ (hspos (τ, q x)).ne', one_smul,
        C.symm_apply_apply]
  have hTlevel (τ : ℝ) : T τ '' {p : E × ℝ | p.2 - q p.1 = 0} =
      {p : E × ℝ | p.2 - q p.1 = 0} := by
    have hfix (p : E × ℝ) (hp : p.2 - q p.1 = 0) : T τ p = p := by
      have hp' : p = (p.1, q p.1) := Prod.ext rfl (sub_eq_zero.mp hp)
      rw [hp']
      exact hTgraph τ p.1
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [hfix p hp]
      exact hp
    · intro p hp
      exact ⟨p, hp, hfix p hp⟩
  have hTsub : T 1 '' {p : E × ℝ | p.2 ≤ q p.1} = {p : E × ℝ | p.2 ≤ q p.1} := by
    have h := Homeomorph.image_sublevel_eq_of_image_level_eq (fun τ => (T τ).toHomeomorph)
      (f := fun p : E × ℝ => p.2 - q p.1) (c := 0) (a := 0) (b := 1)
      (by dsimp [q]; fun_prop)
      (fun p => (hTcont.comp (continuous_id.prodMk continuous_const)).continuousOn)
      (by rw [hTzero]; rfl) (fun τ _ => hTlevel τ) 1 ⟨zero_le_one, le_rfl⟩
    change T 1 '' {p : E × ℝ | p.2 - q p.1 ≤ 0} =
      {p : E × ℝ | p.2 - q p.1 ≤ 0} at h
    simpa only [sub_nonpos] using h
  let A : Set (E × ℝ) := {p | p.1 ∈ closedBall 0 r ∧ b ≤ p.2 ∧ p.2 ≤ q p.1}
  have hTupper (p : E × ℝ) : (T 1 p).2 ≤ q (T 1 p).1 ↔ p.2 ≤ q p.1 := by
    change T 1 p ∈ {p : E × ℝ | p.2 ≤ q p.1} ↔ p ∈ {p : E × ℝ | p.2 ≤ q p.1}
    conv_lhs => rw [← hTsub]
    exact (T 1).injective.mem_set_image
  have hnorm_of_bounds (p : E × ℝ) (hb : b ≤ p.2) (hq : p.2 ≤ q p.1) :
      p.1 ∈ closedBall 0 r := by
    rw [mem_closedBall_zero_iff]
    dsimp [b, q] at hb hq
    nlinarith [norm_nonneg p.1]
  have hTA : T 1 '' A = A := by
    have hmem (p : E × ℝ) : T 1 p ∈ A ↔ p ∈ A := by
      change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      rw [hTupper]
      constructor
      · rintro ⟨_, hb, hq⟩
        exact ⟨hnorm_of_bounds p hb hq, hb, hq⟩
      · rintro ⟨_, hb, hq⟩
        exact ⟨hnorm_of_bounds (T 1 p) hb ((hTupper p).mpr hq), hb, hq⟩
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hmem z).mpr hz
    · intro hp
      exact ⟨(T 1).symm p, (hmem _).mp (by simpa only [(T 1).apply_symm_apply] using hp),
        (T 1).apply_symm_apply p⟩
  refine ⟨min ζ (ε / 2), lt_min hζ (half_pos hε), (T 1).trans G, ?_,
    fun p => hGle (T 1 p), fun p => hGlt (T 1 p), ?_, ?_⟩
  · intro p hp
    change G (T 1 p) = _
    rw [hGslab (T 1 p) (by
      change p.2 ≤ c - r ^ 2 / 2 + ε
      have hle := (abs_le.mp (hp.trans (min_le_right _ _))).2
      linarith), hT, C.apply_symm_apply, hseam p.2 (hp.trans (min_le_left _ _))]
  · intro x hx
    change G (T 1 (x, q x)) = _
    rw [hTgraph]
    exact hGgraph x hx
  · change (G ∘ T 1) '' A = A
    rw [image_comp, hTA]
    exact hGsolid

end Diffeomorph
