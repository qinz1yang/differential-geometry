import DifferentialGeometry.Topology.Diffeomorph.QuadraticCapProjection
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleGraphNeighborhood
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleCapDerivative
import DifferentialGeometry.Analysis.Calculus.Inverse.RadialProjection
import DifferentialGeometry.Analysis.Calculus.Cutoff.SmoothTransition
import Mathlib.Topology.MetricSpace.Thickening

open Set Metric Filter Topology
open scoped ContDiff Manifold
open DifferentialGeometry.Analysis.ODE (saddleBandCurve saddleBandCurve_zero)

namespace DifferentialGeometry.Topology.Morse

private theorem fderiv_saddle_band_height_comp_neg
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {s τ σ k r v₀ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {X : Set (ℝ × ℝ)}
    (hwidth : ∀ z ∈ X, z.1 ∈ Ioo (-k) k)
    (hbottom : ∀ z ∈ X, -v₀ ≤ σ * z.2) :
    ∀ x ∈ (B.trans G.symm) '' X,
      (1 - (B.symm (G x)).1 ^ 2) * ((B.symm (G x)).2 ^ 2 + 2 * s) / 2 - s - τ = 0 →
      fderiv ℝ (fun y =>
        (1 - (B.symm (G y)).1 ^ 2) * ((B.symm (G y)).2 ^ 2 + 2 * s) / 2 - s - τ) x x < 0 := by
  let Q : F → ℝ := fun x =>
    (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2
  have hQ : ContDiff ℝ ∞ Q :=
    ((contDiff_const.sub (B.symm.contDiff.fst.pow 2)).mul
      ((B.symm.contDiff.snd.pow 2).add contDiff_const)).div_const 2
  intro x hx hzero
  obtain ⟨z, hz, rfl⟩ := hx
  have hzlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + τ := by
    change Q (G (G.symm (B z))) - s - τ = 0 at hzero
    rw [G.apply_symm_apply] at hzero
    dsimp only [Q] at hzero
    rw [B.symm_apply_apply] at hzero
    linarith
  have hu := hwidth z hz
  have hzcurve := eq_saddleBandLevelCurve_of_height_eq_of_lower_bound hs hσ hv₀ hv₀τ
    (hbottom z hz) hzlevel
  have hrad := fderiv_saddle_height_radial_neg B G hs hτ hσ hk hr hu hcurve hV
    (hκV ⟨z.1, hu, rfl⟩) hside
  change fderiv ℝ Q (B (saddleBandLevelCurve s τ σ z.1))
    (fderiv ℝ G (G.symm (B (saddleBandLevelCurve s τ σ z.1)))
      (G.symm (B (saddleBandLevelCurve s τ σ z.1)))) < 0 at hrad
  rw [← hzcurve] at hrad
  change fderiv ℝ (fun x => Q (G x) - s - τ) (G.symm (B z)) (G.symm (B z)) < 0
  rw [fderiv_sub_const, fderiv_sub_const]
  have hchain := fderiv_comp (G.symm (B z)) (hQ.differentiable (by simp) _)
    (G.contDiff.differentiable (by simp) _)
  change fderiv ℝ (Q ∘ G) (G.symm (B z)) (G.symm (B z)) < 0
  rw [hchain, G.apply_symm_apply]
  exact hrad

theorem exists_injOn_exp_smul_saddle_band_cutoff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ a b : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {X Y : Set (ℝ × ℝ)} (hX : IsCompact X) (hY : IsCompact Y)
    (hYX : Y ⊆ interior X)
    (hwidth : ∀ z ∈ X, z.1 ∈ Ioo (-k) k)
    (hbottom : ∀ z ∈ X, -v₀ ≤ σ * z.2) :
    let A : ℝ → ℝ := fun t =>
      (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) • G.symm (B p.1))
        {p | p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧
          (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ + κ p.1.1 * A p.2 = 0} := by
  intro A
  let C := B.trans G.symm
  let Q : F → ℝ := fun x =>
    (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2
  let f : F → ℝ := fun x => Q (G x) - s - τ
  have hQ : ContDiff ℝ ∞ Q :=
    ((contDiff_const.sub (B.symm.contDiff.fst.pow 2)).mul
      ((B.symm.contDiff.snd.pow 2).add contDiff_const)).div_const 2
  have hf : ContDiff ℝ 1 f := ((hQ.comp G.contDiff).sub contDiff_const |>.sub contDiff_const).of_le (by simp)
  have hA : ContDiff ℝ 1 A := by
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using (Real.smoothTransition.contDiff_one_sub_mul_sub
      (τ / 4) (τ / 2) τ).of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  have hAn (t : ℝ) : deriv A t ≤ 0 := by
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using Real.smoothTransition.deriv_one_sub_mul_sub_nonpos
      (show τ / 4 < τ / 2 by linarith) (show τ / 2 ≤ τ by linarith) t
  have hAz (t : ℝ) (ht : deriv A t = 0) : A t = 0 := by
    have htlarge : τ / 2 ≤ t := by
      by_contra hn
      have heq : τ / 2 - τ / 4 = τ / 4 := by ring
      have hneg : deriv A t < 0 := by
        simpa only [heq] using Real.smoothTransition.deriv_one_sub_mul_sub_neg
          (show τ / 4 < τ / 2 by linarith) (show τ / 2 ≤ τ by linarith) (lt_of_not_ge hn)
      exact (ne_of_lt hneg) ht
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using Real.smoothTransition.one_sub_mul_sub_eq_zero
      (c := τ) (show τ / 4 < τ / 2 by linarith) htlarge
  let κG : F → ℝ := fun x => κ (B.symm (G x)).1
  have hκG : ContDiff ℝ 1 κG := hκ.comp ((B.symm.contDiff.comp G.contDiff).fst.of_le (by simp))
  have hinner : C '' Y ⊆ interior (C '' X) := by
    change C.toHomeomorph '' Y ⊆ interior (C.toHomeomorph '' X)
    rw [← C.toHomeomorph.image_interior]
    exact image_mono hYX
  obtain ⟨δ, hδ, hinj⟩ := DifferentialGeometry.Analysis.exists_injOn_exp_smul_add_mul_zero_set
    hf hκG hA (fun x => hκnonneg _) (hX.image C.continuous) (hY.image C.continuous) hinner
    (fun t _ => hAn t) (fun t _ => hAz t) (a := a) (b := b) (fderiv_saddle_band_height_comp_neg B G hs hτ hσ hk hr hv₀ hv₀τ
      hcurve hV hκV hside hwidth hbottom)
  refine ⟨δ, hδ, fun μ hμ p hp q hq heq => ?_⟩
  have hmap (p : (ℝ × ℝ) × ℝ) (hp : p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ + κ p.1.1 * A p.2 = 0) :
      (C p.1, p.2) ∈ {p : F × ℝ | p.1 ∈ C '' Y ∧ p.2 ∈ Icc a b ∧ f p.1 + κG p.1 * A p.2 = 0} := by
    refine ⟨mem_image_of_mem _ hp.1, hp.2.1, ?_⟩
    change Q (G (G.symm (B p.1))) - s - τ + κ (B.symm (G (G.symm (B p.1)))).1 * A p.2 = 0
    simpa only [Q, G.apply_symm_apply, B.symm_apply_apply] using hp.2.2
  have he := hinj μ hμ (hmap p hp) (hmap q hq) heq
  exact Prod.ext (C.injective (congrArg Prod.fst he)) (congrArg (fun z : F × ℝ => z.2) he)

theorem exists_injOn_exp_smul_saddle_band_cutoff_of_isCompact
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, p.1.1 ∈ Ioo (-k) k)
    (hbottom : ∀ p ∈ K, -v₀ < σ * p.1.2)
    (hmodel : ∀ p ∈ K,
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) • G.symm (B p.1)) K := by
  let Y : Set (ℝ × ℝ) := Prod.fst '' K
  have hY : IsCompact Y := hK.image continuous_fst
  let O : Set (ℝ × ℝ) := {z | z.1 ∈ Ioo (-k) k ∧ -v₀ < σ * z.2}
  have hO : IsOpen O := (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd))
  have hYO : Y ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hwidth p hp, hbottom p hp⟩
  obtain ⟨ρ, hρ, hρO⟩ := hY.exists_cthickening_subset_open hO hYO
  have hinner : Y ⊆ interior (cthickening ρ Y) :=
    (self_subset_thickening hρ Y).trans (thickening_subset_interior_cthickening ρ Y)
  obtain ⟨R, _, hR⟩ := (hK.image continuous_snd).isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hinj⟩ := exists_injOn_exp_smul_saddle_band_cutoff
    B G hκ hκnonneg hs hτ hσ hk hr hv₀ hv₀τ hcurve hV hκV hside hY.cthickening hY hinner
    (fun z hz => (hρO hz).1) (fun z hz => (hρO hz).2.le) (a := -R) (b := R)
  refine ⟨δ, hδ, fun μ hμ => (hinj μ hμ).mono ?_⟩
  intro p hp
  refine ⟨mem_image_of_mem _ hp, ?_, hmodel p hp⟩
  simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hR p.2 (mem_image_of_mem _ hp)


private theorem isCompact_saddle_half_band
    {s h a j v₀ σ : ℝ} (hh1 : h < 1) :
    IsCompact {z : ℝ × ℝ | |z.1| ≤ h ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j} := by
  let K : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ∈ Icc a j ∧ |p.2.1| ≤ h ∧
    (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1}
  have hK : IsCompact K := isCompact_saddle_band_graph_strip hh1
  have hclosed : IsClosed {p : ℝ × (ℝ × ℝ) | -v₀ ≤ σ * p.2.2} :=
    isClosed_le continuous_const (continuous_const.mul continuous_snd.snd)
  have heq : {z : ℝ × ℝ | |z.1| ≤ h ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j} =
      Prod.snd '' (K ∩ {p : ℝ × (ℝ × ℝ) | -v₀ ≤ σ * p.2.2}) := by
    ext z
    constructor
    · rintro ⟨hu, hv, ha, hj⟩
      exact ⟨((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z),
        ⟨⟨⟨ha, hj⟩, hu, by ring⟩, hv⟩, rfl⟩
    · rintro ⟨p, ⟨⟨ht, hu, heq⟩, hv⟩, rfl⟩
      exact ⟨hu, hv, by linarith [ht.1], by linarith [ht.2]⟩
  rw [heq]
  exact (hK.inter_right hclosed).image continuous_snd

private theorem zero_mem_interior_saddle_half_band
    {s h a j v₀ σ : ℝ} (hh : 0 < h) (ha : a < 0) (hj : 0 < j) (hv₀ : 0 < v₀) :
    (0, 0) ∈ interior {z : ℝ × ℝ | |z.1| ≤ h ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j} := by
  let O : Set (ℝ × ℝ) := {z | |z.1| < h ∧ -v₀ < σ * z.2 ∧
    a < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
    (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s < j}
  have hq : Continuous (fun z : ℝ × ℝ => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) := by fun_prop
  have hO : IsOpen O :=
    (isOpen_lt continuous_fst.abs continuous_const).inter
      ((isOpen_lt continuous_const (continuous_const.mul continuous_snd)).inter
        ((isOpen_lt continuous_const hq).inter (isOpen_lt hq continuous_const)))
  apply mem_interior.mpr
  refine ⟨O, fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩, hO, ?_⟩
  dsimp only [O, mem_ofPred]
  norm_num
  exact ⟨hh, hv₀, ha, hj⟩

private theorem saddle_half_band_side_positive
    {s h a v₀ σ : ℝ} (hh : 0 ≤ h) (hh1 : h < 1) (hσ : σ ^ 2 = 1)
    (hlow : (1 - h ^ 2) * (v₀ ^ 2 + 2 * s) / 2 - s < a)
    {z : ℝ × ℝ} (hu : |z.1| = h) (hv : -v₀ ≤ σ * z.2)
    (ha : a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s) :
    0 < σ * z.2 := by
  by_contra hn
  have hvhi : σ * z.2 ≤ 0 := le_of_not_gt hn
  have hvsq : z.2 ^ 2 ≤ v₀ ^ 2 := by
    have hsquare : (σ * z.2) ^ 2 = z.2 ^ 2 := by rw [mul_pow, hσ, one_mul]
    nlinarith
  have husq : z.1 ^ 2 = h ^ 2 := by nlinarith [sq_abs z.1, congrArg (fun x : ℝ => x ^ 2) hu]
  have hden : 0 ≤ 1 - h ^ 2 := by nlinarith
  rw [husq] at ha
  have hm := mul_le_mul_of_nonneg_left hvsq hden
  nlinarith

private theorem saddleBandCurve_cutoff_eq_self_of_nonpos
    {s h t₀ a v₀ σ t : ℝ} (hs : 0 < s) (hh : 0 < h) (hσ : σ ^ 2 = 1)
    (hv₀t : v₀ ^ 2 / 2 < t₀ / 4) (hsmall : v₀ ^ 2 / 2 - a < s * h ^ 2 / 16)
    {θ : ℝ × ℝ → ℝ}
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    {z : ℝ × ℝ} (hvlo : -v₀ ≤ σ * z.2) (hvhi : σ * z.2 ≤ 0)
    (hta : a ≤ t) (hlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t) :
    saddleBandCurve z (θ (t, z.1) * (t₀ - t)) = z := by
  have hvsq : z.2 ^ 2 ≤ v₀ ^ 2 := by
    have hsquare : (σ * z.2) ^ 2 = z.2 ^ 2 := by rw [mul_pow, hσ, one_mul]
    nlinarith
  have hnonneg := mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)
  have ht : t ≤ v₀ ^ 2 / 2 := by nlinarith [mul_nonneg hs.le (sq_nonneg z.1)]
  have husmall : z.1 ^ 2 < h ^ 2 / 16 := by
    have hu : s * z.1 ^ 2 ≤ v₀ ^ 2 / 2 - a := by nlinarith
    nlinarith
  have hu : |z.1| ≤ h / 4 := by
    have hsqabs := sq_abs z.1
    nlinarith [abs_nonneg z.1]
  rw [hθ0 t z.1 (ht.trans hv₀t.le) hu, zero_mul, saddleBandCurve_zero]

private theorem saddleBandCurve_cutoff_lower_bound
    {s h t₀ a v₀ σ t : ℝ} (hs : 0 < s) (hh : 0 < h) (hσ : σ ^ 2 = 1)
    (hv₀ : 0 ≤ v₀) (hv₀t : v₀ ^ 2 / 2 < t₀ / 4)
    (hsmall : v₀ ^ 2 / 2 - a < s * h ^ 2 / 16)
    {θ : ℝ × ℝ → ℝ}
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    {z : ℝ × ℝ} (hvlo : -v₀ ≤ σ * z.2) (hta : a ≤ t)
    (hlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t) :
    -v₀ ≤ σ * (saddleBandCurve z (θ (t, z.1) * (t₀ - t))).2 := by
  by_cases hvhi : σ * z.2 ≤ 0
  · rw [saddleBandCurve_cutoff_eq_self_of_nonpos hs hh hσ hv₀t hsmall hθ0 hvlo hvhi hta hlevel]
    exact hvlo
  · have hpos : 0 ≤ σ * (saddleBandCurve z (θ (t, z.1) * (t₀ - t))).2 := by
      change 0 ≤ σ * (Real.sqrt _ * z.2)
      rw [mul_left_comm σ]
      exact mul_nonneg (Real.sqrt_nonneg _) (le_of_not_ge hvhi)
    linarith

private theorem isCompact_image_saddle_half_band_and_cutoff_model
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (T : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {c s h k a j ε d t₀ v₀ σ : ℝ} (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1)
    (hkh : k < h) (haε : -ε ≤ a) (hjd : j ≤ d)
    (hσ : σ ^ 2 = 1) (hv₀ : 0 < v₀)
    (hv₀t : v₀ ^ 2 / 2 < t₀ / 4) (hsmall : v₀ ^ 2 / 2 - a < s * h ^ 2 / 16)
    {θ : ℝ × ℝ → ℝ} {κ : ℝ → ℝ}
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (hθformula : ∀ t u, θ (t, u) =
      1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u)
    {V : Set (ℝ × (ℝ × ℝ))}
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hVreg : ∀ q ∈ V, θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
      (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ *
          (θ (q.1, q.2.1) * (t₀ - q.1)) / q.2.2 ^ 2))
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1)) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
      (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    IsCompact (J '' R) ∧
      (∀ p ∈ J '' R, p.1.1 ∈ Ioo (-h) h ∧ -v₀ ≤ σ * p.1.2 ∧
        p.2 ∈ Icc a j ∧
        (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
          κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) *
            (t₀ - p.2)) = 0) := by
  intro R J
  let E : (ℝ × ℝ) → ℝ := fun z => (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2
  have hJ : Continuous J := by
    exact (B.symm.continuous.comp
      ((T.continuous.comp (B.continuous.prodMk (by fun_prop))).fst)).prodMk (by fun_prop)
  have hcompact : IsCompact (J '' R) :=
    (isCompact_saddle_half_band (hkh.trans hh1)).image hJ
  have hpoints : ∀ p ∈ J '' R, p.1.1 ∈ Ioo (-h) h ∧ -v₀ ≤ σ * p.1.2 ∧
      p.2 ∈ Icc a j ∧
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) *
          (t₀ - p.2)) = 0 := by
    rintro _ ⟨z, hz, rfl⟩
    have hzV : (E z - s, z) ∈ V := hKV
      ⟨⟨haε.trans hz.2.2.1, hz.2.2.2.trans hjd⟩, hz.1.trans hkh.le, by dsimp only [E]; ring⟩
    have hJz : J z = (saddleBandCurve z (θ (E z - s, z.1) * (t₀ - (E z - s))), E z - s) := by
      have heq := hTmodel (E z - s, z) hzV
      have hheight : c + s + (E z - s) = c + E z := by ring
      rw [hheight] at heq
      change (B.symm (T (B z, c + E z)).1, E z - s) = _
      rw [heq, B.symm_apply_apply]
    rw [hJz]
    have henergy : E (saddleBandCurve z (θ (E z - s, z.1) * (t₀ - (E z - s)))) =
        E z + θ (E z - s, z.1) * (t₀ - (E z - s)) := by
      rcases hVreg (E z - s, z) hzV with hzero | ⟨hu, hv, hrad⟩
      · rw [hzero, saddleBandCurve_zero, add_zero]
      · simpa only [zero_add, E] using
          DifferentialGeometry.Analysis.ODE.saddleBandCurve_height hu hv hrad.le (0 : ℝ) s
    refine ⟨?_, saddleBandCurve_cutoff_lower_bound hs hh hσ hv₀.le hv₀t hsmall hθ0
      hz.2.1 hz.2.2.1 (by dsimp only [E]; ring), ⟨hz.2.2.1, hz.2.2.2⟩, ?_⟩
    · change z.1 ∈ Ioo (-h) h
      obtain ⟨hl, hr⟩ := abs_le.mp hz.1
      exact ⟨by linarith, hr.trans_lt hkh⟩
    · change E (saddleBandCurve z (θ (E z - s, z.1) * (t₀ - (E z - s)))) - s - t₀ +
        κ z.1 * ((1 - Real.smoothTransition (((E z - s) - t₀ / 4) / (t₀ / 4))) *
          (t₀ - (E z - s))) = 0
      rw [henergy, hθformula]
      ring
  exact ⟨hcompact, hpoints⟩

private theorem exists_injOn_exp_smul_saddle_cutoff_union_wall
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s t₀ σ h r v₀ a b k : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀)
    (hσ : σ ^ 2 = 1) (hh1 : h < 1) (hkh : k < h) (hr : 0 < r)
    (hv₀ : 0 < v₀) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hκzero : ∀ u, h / 2 ≤ |u| → κ u = 0)
    (hcurve : ∀ u ∈ Ioo (-h) h,
      B (saddleBandLevelCurve s t₀ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcurveV : saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ V)
    (hside : ∀ z ∈ V, s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, p.1.1 ∈ Ioo (-h) h)
    (hbottom : ∀ p ∈ K, -v₀ < σ * p.1.2)
    (hmodel : ∀ p ∈ K,
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) * (t₀ - p.2)) = 0) :
    let C : Set ((ℝ × ℝ) × ℝ) :=
      (fun q : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ q.1, q.2)) ''
        {q | |q.1| ≤ k ∧ h / 2 ≤ |q.1| ∧ q.2 ∈ Icc a b}
    IsCompact C ∧ ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) • G.symm (B p.1)) (K ∪ C) := by
  intro C
  let P : Set (ℝ × ℝ) := {q | |q.1| ≤ k ∧ h / 2 ≤ |q.1| ∧ q.2 ∈ Icc a b}
  have hPcompact : IsCompact P := by
    have heq : P = (Icc (-k) k ×ˢ Icc a b) ∩ {q : ℝ × ℝ | h / 2 ≤ |q.1|} := by
      ext q
      simp only [P, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_Icc, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const continuous_fst.abs)
  have hPwidth (q : ℝ × ℝ) (hq : q ∈ P) : q.1 ∈ Ioo (-h) h := by
    have hu := abs_le.mp hq.1
    exact ⟨by linarith [hu.1], hu.2.trans_lt hkh⟩
  have hPunit (q : ℝ × ℝ) (hq : q ∈ P) : q.1 ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [(hPwidth q hq).1], (hPwidth q hq).2.trans hh1⟩
  have hcont : ContinuousOn (fun q : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ q.1, q.2)) P :=
    (((contDiffOn_saddleBandLevelCurve hs ht₀ σ).continuousOn.comp
      continuousOn_fst hPunit).prodMk continuousOn_snd)
  have hC : IsCompact C := hPcompact.image_of_continuousOn hcont
  refine ⟨hC, ?_⟩
  apply exists_injOn_exp_smul_saddle_band_cutoff_of_isCompact B G hκ hκnonneg hs ht₀
    hσ hh1 hr hv₀.le hv₀t hcurve hV hcurveV hside (hK.union hC)
  · intro p hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact hwidth p hp
    · exact hPwidth q hq
  · intro p hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact hbottom p hp
    · have hnonneg : 0 ≤ σ * (saddleBandLevelCurve s t₀ σ q.1).2 := by
        change 0 ≤ σ * (σ * Real.sqrt _)
        rw [← mul_assoc, ← pow_two, hσ, one_mul]
        exact Real.sqrt_nonneg _
      linarith
  · intro p hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact hmodel p hp
    · have hlevel := saddleBandLevelCurve_height hs ht₀ hσ (hPunit q hq) (0 : ℝ)
      have hzero : κ (saddleBandLevelCurve s t₀ σ q.1).1 = 0 := hκzero q.1 hq.2.1
      dsimp only [Prod.fst, Prod.snd]
      rw [hzero, zero_mul, add_zero]
      linarith


theorem exists_injOn_exp_smul_saddle_band_cutoff_on_half_band
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (G : F ≃ₘ[ℝ] F)
    (T : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {c s h ε t₀ d σ r : ℝ} (hs : 0 < s) (hh : 0 < h) (hh1 : h < 1)
    (hε : 0 < ε) (hεh : ε < s * h ^ 2 / 16) (ht₀ : 0 < t₀) (ht₀d : t₀ < d)
    (hσ : σ ^ 2 = 1) (hr : 0 < r)
    {θ : ℝ × ℝ → ℝ} (κ : ContDiffBump (0 : ℝ)) (hκout : κ.rOut = h / 2)
    (hθ0 : ∀ t u, t ≤ t₀ / 4 → |u| ≤ h / 4 → θ (t, u) = 0)
    (hθformula : ∀ t u, θ (t, u) =
      1 - (1 - Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))) * κ u)
    {V : Set (ℝ × (ℝ × ℝ))} {U : Set (ℝ × ℝ)}
    (hKV : {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc (-ε) d ∧ |q.2.1| ≤ h ∧
      (1 - q.2.1 ^ 2) * (q.2.2 ^ 2 + 2 * s) / 2 = s + q.1} ⊆ V)
    (hVreg : ∀ q ∈ V, θ (q.1, q.2.1) * (t₀ - q.1) = 0 ∨
      (1 - q.2.1 ^ 2 ≠ 0 ∧ q.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - q.2.1 ^ 2)⁻¹ *
          (θ (q.1, q.2.1) * (t₀ - q.1)) / q.2.2 ^ 2))
    (hTmodel : ∀ q ∈ V, T (B q.2, c + s + q.1) =
      (B (saddleBandCurve q.2 (θ (q.1, q.2.1) * (t₀ - q.1))), c + s + q.1))
    (hrawU : ∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → z ∈ U)
    (hTheight : ∀ q, (T q).2 = q.2)
    (hcurve : ∀ u ∈ Ioo (-h) h,
      B (saddleBandLevelCurve s t₀ σ u) ∈ G '' sphere 0 r)
    {Vside : Set (ℝ × ℝ)} (hVside : IsOpen Vside)
    (hcurveVside : saddleBandLevelCurve s t₀ σ '' Ioo (-h) h ⊆ Vside)
    (hside : ∀ z ∈ Vside, s + t₀ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    (f : (ℝ × ℝ) → F × ℝ)
    (hgraph : ∀ z ∈ U, f z = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) :
    ∃ v₀ > 0, v₀ ^ 2 / 2 < t₀ / 4 ∧
      ∀ j ∈ Ioo (t₀ / 2) t₀,
      let R : Set (ℝ × ℝ) := {z | |z.1| ≤ 5 * h / 8 ∧ -v₀ ≤ σ * z.2 ∧
        -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
      let J : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun z =>
        (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1,
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
      let C : Set ((ℝ × ℝ) × ℝ) :=
        (fun q : ℝ × ℝ => (saddleBandLevelCurve s t₀ σ q.1, q.2)) ''
          {q | |q.1| ≤ 7 * h / 8 ∧ h / 2 ≤ |q.1| ∧ q.2 ∈ Icc (-ε / 2) j}
      IsCompact R ∧ (0, 0) ∈ interior R ∧ R ⊆ U ∧
        IsCompact (J '' R) ∧ IsCompact C ∧
        (∀ z ∈ R, (B (J z).1, c + s + (J z).2) =
          T (f z)) ∧
        (∀ p ∈ J '' R, p.1.1 ∈ Ioo (-h) h ∧ -v₀ ≤ σ * p.1.2 ∧ p.2 ∈ Icc (-ε / 2) j ∧
          (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - t₀ +
            κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - t₀ / 4) / (t₀ / 4))) *
              (t₀ - p.2)) = 0) ∧
        (∀ z ∈ R, |z.1| = 5 * h / 8 → 0 < σ * z.2) ∧
        ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
          InjOn (fun z => Real.exp (-μ * (J z).2) •
            G.symm ((T (f z)).1)) R ∧
          InjOn (fun p : (ℝ × ℝ) × ℝ => Real.exp (-μ * p.2) •
            G.symm (B p.1)) ((J '' R) ∪ C) := by
  let v₀ := min 1 (min (ε / 8) (t₀ / 8))
  have hv₀ : 0 < v₀ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hv₀1 : v₀ ≤ 1 := min_le_left _ _
  have hv₀ε : v₀ ≤ ε / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hv₀τ : v₀ ≤ t₀ / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hvsq : v₀ ^ 2 ≤ v₀ := by nlinarith
  have hv₀t : v₀ ^ 2 / 2 < t₀ / 4 := by nlinarith
  have hsmall : v₀ ^ 2 / 2 - (-ε / 2) < s * h ^ 2 / 16 := by nlinarith
  have hkh : 5 * h / 8 < h := by linarith
  have hlow : (1 - (5 * h / 8) ^ 2) * (v₀ ^ 2 + 2 * s) / 2 - s < -ε / 2 := by
    have hn := mul_nonneg (sq_nonneg (5 * h / 8)) (sq_nonneg v₀)
    nlinarith
  refine ⟨v₀, hv₀, hv₀t, ?_⟩
  intro j hj R J C
  have hjpos : 0 < j := (half_pos ht₀).trans hj.1
  have hRU : R ⊆ U := by
    intro z hz
    apply hrawU ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
      ⟨by linarith [hz.2.2.1], hz.2.2.2.trans (hj.2.trans ht₀d).le⟩ z
      (hz.1.trans hkh.le)
    ring
  obtain ⟨hK, hpoints⟩ :=
    isCompact_image_saddle_half_band_and_cutoff_model B T
      hs hh hh1 hkh (show -ε ≤ -ε / 2 by linarith) (hj.2.trans ht₀d).le hσ hv₀
      hv₀t hsmall hθ0 hθformula hKV hVreg hTmodel
  have hκzero (u : ℝ) (hu : h / 2 ≤ |u|) : κ u = 0 := by
    apply κ.zero_of_le_dist
    simpa only [hκout, dist_zero_right, Real.norm_eq_abs] using hu
  obtain ⟨hCcompact, ρproj, hρproj, hinj⟩ :=
    exists_injOn_exp_smul_saddle_cutoff_union_wall B G
      (κ.contDiff.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) (fun u => κ.nonneg)
      hs.le ht₀ hσ hh1 (show 7 * h / 8 < h by linarith) hr (v₀ := 2 * v₀)
      (by positivity) (by nlinarith) hκzero hcurve hVside hcurveVside
      hside hK (fun p hp => (hpoints p hp).1)
      (fun p hp => by have hv := (hpoints p hp).2.1; linarith)
      (fun p hp => (hpoints p hp).2.2.2) (a := -ε / 2) (b := j)
  have hJactual (z : ℝ × ℝ) (hz : z ∈ R) :
      (B (J z).1, c + s + (J z).2) = T (f z) := by
    rw [hgraph z (hRU hz)]
    change (B (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1),
      c + s + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) = _
    apply Prod.ext
    · exact B.apply_symm_apply _
    · rw [hTheight]
      dsimp only
      ring
  have hJinj : Function.Injective J := by
    intro z w heq
    have hfst := congrArg (fun p : (ℝ × ℝ) × ℝ => B p.1) heq
    have hsnd := congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) heq
    change B (B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1) =
      B (B.symm (T (B w, c + (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2)).1) at hfst
    simp only [B.apply_symm_apply] at hfst
    have he : T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) =
        T (B w, c + (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2) := by
      apply Prod.ext hfst
      rw [hTheight, hTheight]
      change c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 =
        c + (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2
      change (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s =
        (1 - w.1 ^ 2) * (w.2 ^ 2 + 2 * s) / 2 - s at hsnd
      linarith
    exact B.injective (congrArg Prod.fst (T.injective he))
  refine ⟨isCompact_saddle_half_band (hkh.trans hh1),
    zero_mem_interior_saddle_half_band (by positivity) (by linarith) hjpos hv₀,
    hRU, hK, hCcompact, hJactual, ?_, ?_, ρproj, hρproj, ?_⟩
  · intro p hp
    exact hpoints p hp
  · intro z hz hzu
    exact saddle_half_band_side_positive (by positivity) (hkh.trans hh1) hσ hlow hzu hz.2.1 hz.2.2.1
  · intro μ hμ
    refine ⟨?_, hinj μ hμ⟩
    intro z hz w hw hproj
    apply hJinj
    apply hinj μ hμ (Or.inl (mem_image_of_mem J hz)) (Or.inl (mem_image_of_mem J hw))
    change Real.exp (-μ * (J z).2) • G.symm
      (T (f z)).1 =
        Real.exp (-μ * (J w).2) • G.symm
          (T (f w)).1 at hproj
    rw [← congrArg Prod.fst (hJactual z hz), ← congrArg Prod.fst (hJactual w hw)] at hproj
    exact hproj



theorem exists_contDiffOn_exp_smul_saddle_band_cutoff_graph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ a b : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {X Y : Set (ℝ × ℝ)} (hX : IsCompact X) (hY : IsCompact Y)
    (hYX : Y ⊆ interior X)
    (hwidth : ∀ z ∈ X, z.1 ∈ Ioo (-k) k)
    (hbottom : ∀ z ∈ X, -v₀ ≤ σ * z.2) :
    let A : ℝ → ℝ := fun t =>
      (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)
    let C := B.trans G.symm
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      ∃ O : Set F, IsOpen O ∧ ∃ g : F → ℝ, ContDiffOn ℝ ∞ g O ∧
        {p : F × ℝ | C.symm (Real.exp (μ * p.2) • p.1) ∈ interior Y ∧ p.2 ∈ Ioo a b ∧
          (1 - (C.symm (Real.exp (μ * p.2) • p.1)).1 ^ 2) *
              ((C.symm (Real.exp (μ * p.2) • p.1)).2 ^ 2 + 2 * s) / 2 - s - τ +
            κ (C.symm (Real.exp (μ * p.2) • p.1)).1 * A p.2 = 0} =
              {p : F × ℝ | p.1 ∈ O ∧ p.2 = g p.1} := by
  intro A C
  let L : (ℝ × ℝ) ≃L[ℝ] F := B.mfderivToContinuousLinearEquiv (by simp) (0, 0)
  let : FiniteDimensional ℝ F := FiniteDimensional.of_injective L.symm.toLinearMap L.symm.injective
  let Q : F → ℝ := fun x =>
    (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2
  let f : F → ℝ := fun x => Q (G x) - s - τ
  have hQ : ContDiff ℝ ∞ Q :=
    ((contDiff_const.sub (B.symm.contDiff.fst.pow 2)).mul
      ((B.symm.contDiff.snd.pow 2).add contDiff_const)).div_const 2
  have hf : ContDiff ℝ ∞ f := (hQ.comp G.contDiff).sub contDiff_const |>.sub contDiff_const
  have hA : ContDiff ℝ ∞ A := by
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using (Real.smoothTransition.contDiff_one_sub_mul_sub
      (τ / 4) (τ / 2) τ)
  have hAn (t : ℝ) : deriv A t ≤ 0 := by
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using Real.smoothTransition.deriv_one_sub_mul_sub_nonpos
      (show τ / 4 < τ / 2 by linarith) (show τ / 2 ≤ τ by linarith) t
  have hAz (t : ℝ) (ht : deriv A t = 0) : A t = 0 := by
    have htlarge : τ / 2 ≤ t := by
      by_contra hn
      have heq : τ / 2 - τ / 4 = τ / 4 := by ring
      have hneg : deriv A t < 0 := by
        simpa only [heq] using Real.smoothTransition.deriv_one_sub_mul_sub_neg
          (show τ / 4 < τ / 2 by linarith) (show τ / 2 ≤ τ by linarith) (lt_of_not_ge hn)
      exact (ne_of_lt hneg) ht
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using Real.smoothTransition.one_sub_mul_sub_eq_zero
      (c := τ) (show τ / 4 < τ / 2 by linarith) htlarge
  let κG : F → ℝ := fun x => κ (B.symm (G x)).1
  have hκG : ContDiff ℝ ∞ κG := hκ.comp (B.symm.contDiff.comp G.contDiff).fst
  have hinner : C '' Y ⊆ interior (C '' X) := by
    change C.toHomeomorph '' Y ⊆ interior (C.toHomeomorph '' X)
    rw [← C.toHomeomorph.image_interior]
    exact image_mono hYX
  obtain ⟨δ, hδ, hgraph⟩ := DifferentialGeometry.Analysis.exists_contDiffOn_exp_smul_add_mul_zero_set_graph
    hf hκG hA (fun x => hκnonneg _) (hX.image C.continuous) (hY.image C.continuous) hinner
    (fun t _ => hAn t) (fun t _ => hAz t) (a := a) (b := b) (fderiv_saddle_band_height_comp_neg B G hs hτ hσ hk hr hv₀ hv₀τ
      hcurve hV hκV hside hwidth hbottom)
  refine ⟨δ, hδ, fun μ hμ => ?_⟩
  obtain ⟨O, hO, g, hg, heq⟩ := hgraph μ hμ
  refine ⟨O, hO, g, hg, ?_⟩
  rw [← heq]
  have hmem (x : F) : x ∈ interior (C '' Y) ↔ C.symm x ∈ interior Y := by
    change x ∈ interior (C.toHomeomorph '' Y) ↔ C.symm x ∈ interior Y
    rw [← C.toHomeomorph.image_interior]
    constructor
    · rintro ⟨z, hz, rfl⟩
      change C.symm (C z) ∈ interior Y
      simpa only [C.symm_apply_apply] using hz
    · intro hx
      exact ⟨C.symm x, hx, C.apply_symm_apply x⟩
  ext p
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  rw [hmem]
  rfl


theorem exists_isOpen_graph_exp_smul_saddle_band_cutoff_of_isCompact
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, p.1.1 ∈ Ioo (-k) k)
    (hbottom : ∀ p ∈ K, -v₀ < σ * p.1.2)
    (hmodel : ∀ p ∈ K,
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0) :
    let C := B.trans G.symm
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      ∃ O : Set F, IsOpen O ∧ ∃ g : F → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∃ W : Set (F × ℝ), IsOpen W ∧
          (fun p : (ℝ × ℝ) × ℝ => (Real.exp (-μ * p.2) • C p.1, p.2)) '' K ⊆ W ∧
          W ⊆ {p | p.1 ∈ O} ∧
          W ∩ {p : F × ℝ |
            (1 - (C.symm (Real.exp (μ * p.2) • p.1)).1 ^ 2) *
                ((C.symm (Real.exp (μ * p.2) • p.1)).2 ^ 2 + 2 * s) / 2 - s - τ +
              κ (C.symm (Real.exp (μ * p.2) • p.1)).1 *
                ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0} =
            W ∩ {p : F × ℝ | p.2 = g p.1} := by
  intro C
  let S : Set (ℝ × ℝ) := Prod.fst '' K
  have hS : IsCompact S := hK.image continuous_fst
  let U : Set (ℝ × ℝ) := {z | z.1 ∈ Ioo (-k) k ∧ -v₀ < σ * z.2}
  have hU : IsOpen U := (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd))
  have hSU : S ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hwidth p hp, hbottom p hp⟩
  obtain ⟨ρ, hρ, hρU⟩ := hS.exists_cthickening_subset_open hU hSU
  let X := cthickening ρ S
  let Y := cthickening (ρ / 2) S
  have hYX : Y ⊆ interior X :=
    (cthickening_subset_thickening' hρ (half_lt_self hρ) S).trans
      (thickening_subset_interior_cthickening ρ S)
  have hSY : S ⊆ interior Y := (self_subset_thickening (half_pos hρ) S).trans
    (thickening_subset_interior_cthickening (ρ / 2) S)
  obtain ⟨M, _, hM⟩ := (hK.image continuous_snd).isBounded.exists_pos_norm_le
  have htime (p : (ℝ × ℝ) × ℝ) (hp : p ∈ K) : p.2 ∈ Ioo (-M - 1) (M + 1) := by
    have ht := hM p.2 (mem_image_of_mem Prod.snd hp)
    rw [Real.norm_eq_abs, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨δ, hδ, hgraphs⟩ := exists_contDiffOn_exp_smul_saddle_band_cutoff_graph
    B G hκ hκnonneg hs hτ hσ hk hr hv₀ hv₀τ hcurve hV hκV hside
    (hS.cthickening (r := ρ)) (hS.cthickening (r := ρ / 2)) hYX
    (fun z hz => (hρU hz).1) (fun z hz => (hρU hz).2.le) (a := -M - 1) (b := M + 1)
  refine ⟨δ, hδ, fun μ hμ => ?_⟩
  obtain ⟨O, hO, g, hg, hgraph⟩ := hgraphs μ hμ
  let A : ℝ → ℝ := fun t =>
    (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)
  let f : F × ℝ → ℝ := fun p =>
    (1 - (C.symm (Real.exp (μ * p.2) • p.1)).1 ^ 2) *
        ((C.symm (Real.exp (μ * p.2) • p.1)).2 ^ 2 + 2 * s) / 2 - s - τ +
      κ (C.symm (Real.exp (μ * p.2) • p.1)).1 * A p.2
  let V : Set (F × ℝ) := {p | C.symm (Real.exp (μ * p.2) • p.1) ∈ interior Y ∧
    p.2 ∈ Ioo (-M - 1) (M + 1)}
  have hVe : IsOpen V := (isOpen_interior.preimage
    (C.symm.continuous.comp (by fun_prop))).inter (isOpen_Ioo.preimage continuous_snd)
  let W := V ∩ {p : F × ℝ | p.1 ∈ O}
  have hWe : IsOpen W := hVe.inter (hO.preimage continuous_fst)
  have hgraph' : V ∩ {p | f p = 0} = {p : F × ℝ | p.1 ∈ O ∧ p.2 = g p.1} := by
    convert hgraph using 1
    ext p
    change ((_ ∧ _) ∧ _) ↔ (_ ∧ _ ∧ _)
    exact and_assoc
  have hKgraph (p : (ℝ × ℝ) × ℝ) (hp : p ∈ K) :
      (Real.exp (-μ * p.2) • C p.1, p.2) ∈ V ∩ {q | f q = 0} := by
    have heq : C.symm (Real.exp (μ * p.2) • (Real.exp (-μ * p.2) • C p.1)) = p.1 := by
      rw [smul_smul, ← Real.exp_add, show μ * p.2 + -μ * p.2 = 0 by ring,
        Real.exp_zero, one_smul, C.symm_apply_apply]
    refine ⟨⟨?_, htime p hp⟩, ?_⟩
    · change C.symm (Real.exp (μ * p.2) • (Real.exp (-μ * p.2) • C p.1)) ∈ interior Y
      rw [heq]
      exact hSY (mem_image_of_mem Prod.fst hp)
    · change f (Real.exp (-μ * p.2) • C p.1, p.2) = 0
      dsimp only [f]
      rw [heq]
      exact hmodel p hp
  refine ⟨O, hO, g, hg, W, hWe, ?_, inter_subset_right, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hKgraph p hp).1, (hgraph'.subset (hKgraph p hp)).1⟩
  · ext p
    change (p ∈ W ∧ f p = 0) ↔ (p ∈ W ∧ p.2 = g p.1)
    constructor
    · rintro ⟨hp, hz⟩
      exact ⟨hp, (hgraph'.subset ⟨hp.1, hz⟩).2⟩
    · rintro ⟨hp, heq⟩
      exact ⟨hp, (hgraph'.symm.subset ⟨hp.2, heq⟩).2⟩

theorem saddle_cutoff_half_band_coordinates_and_height
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F)
    (T : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {c s h ε d t₀ j v₀ σ : ℝ} (hh : 0 ≤ h) (hε : 0 ≤ ε) (hjd : j ≤ d) (hjt : j ≤ t₀)
    {θ : ℝ × ℝ → ℝ} (hθle : ∀ q, θ q ≤ 1)
    {V : Set (ℝ × (ℝ × ℝ))}
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
    ∀ z ∈ R, (J z).1.1 = z.1 ∧
      (1 - (J z).1.1 ^ 2) * ((J z).1.2 ^ 2 + 2 * s) / 2 ≤ s + t₀ := by
  intro R J z hz
  let t := (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
  have ht : t ∈ Icc (-ε) d := ⟨by dsimp only [t]; linarith [hz.2.2.1], hz.2.2.2.trans hjd⟩
  have htt₀ : t ≤ t₀ := hz.2.2.2.trans hjt
  have hzV : (t, z) ∈ V := hKV ⟨ht, hz.1.trans (by linarith), by dsimp only [t]; ring⟩
  have hJmodel : (J z).1 = saddleBandCurve z (θ (t, z.1) * (t₀ - t)) := by
    have heq := hTmodel (t, z) hzV
    have hc : c + s + t = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by dsimp only [t]; ring
    rw [hc] at heq
    change B.symm (T (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)).1 = _
    rw [heq, B.symm_apply_apply]
  refine ⟨by rw [hJmodel]; rfl, ?_⟩
  rw [hJmodel]
  rcases hVreg (t, z) hzV with hzero | ⟨hu, hv, hrad⟩
  · rw [hzero, saddleBandCurve_zero]
    dsimp only [t] at htt₀
    linarith
  · have heq := DifferentialGeometry.Analysis.ODE.saddleBandCurve_height hu hv hrad.le (0 : ℝ) s
    simp only [zero_add] at heq
    rw [heq]
    have hshift := mul_le_mul_of_nonneg_right (hθle (t, z.1)) (sub_nonneg.mpr htt₀)
    rw [one_mul] at hshift
    dsimp only [t] at hshift ⊢
    linarith

theorem reference_cylinder_subset_image_of_saddle_cutoff
    {F ι : Type*} (B : (ℝ × ℝ) → F) (T : F × ℝ → F × ℝ)
    {S : Set (F × ℝ)} {C : Set F} {s h t₀ ε d ℓ σ : ℝ}
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hh1 : h < 1) (ht₀ : 0 ≤ t₀)
    (hε : ε < s * h ^ 2 / 16) (hσ : σ ^ 2 = 1)
    {θ : ℝ × ℝ → ℝ} (hθ : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    (hgraph : ∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → (B z, ℓ + t) ∈ S)
    (hmodel : ∀ t ∈ Icc (-ε) d, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t →
      T (B z, ℓ + t) = (B (saddleBandCurve z (θ (t, z.1) * (t₀ - t))), ℓ + t))
    {γ : ℝ × ι → F}
    (hclosing : ∀ t ∈ Icc (-ε) d, ∀ u, (γ (t, u), ℓ + t) ∈ S)
    (hTclosing : ∀ t ∈ Icc (-ε) d, ∀ u,
      T (γ (t, u), ℓ + t) = (γ (t₀, u), ℓ + t))
    (hC : C = B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪
      range (fun u => γ (t₀, u))) :
    (C \ B '' (saddleBandLevelCurve s t₀ σ '' Ioo (-(h / 2)) (h / 2))) ×ˢ
      Icc (ℓ - ε) (ℓ + d) ⊆ T '' S := by
  rintro ⟨y, v⟩ ⟨⟨hy, hyA⟩, hv⟩
  have ht : v - ℓ ∈ Icc (-ε) d := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [hC] at hy
  rcases hy with hyselected | hyclosing
  · obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hyselected
    have hout : h / 2 ≤ |u| := by
      by_contra hn
      exact hyA ⟨_, ⟨u, abs_lt.mp (lt_of_not_ge hn), rfl⟩, rfl⟩
    have hsq : h ^ 2 / 4 ≤ u ^ 2 := by
      have hm := mul_self_le_mul_self (show 0 ≤ h / 2 by positivity) hout
      nlinarith only [hm, sq_abs u]
    have hrad : 0 < v - ℓ + s * u ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hsq hs
      have hnonneg := mul_nonneg hs (sq_nonneg h)
      nlinarith only [ht.1, hε, hm, hnonneg]
    have hunit : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    let z := saddleBandLevelCurve s (v - ℓ) σ u
    have hzwidth : |z.1| ≤ h := abs_le.mpr hu
    have hzlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + (v - ℓ) := by
      simpa only [zero_add] using saddleBandLevelCurve_height_of_nonneg hrad.le hσ hunit (0 : ℝ)
    have hTV := hmodel (v - ℓ) ht z hzwidth hzlevel
    change T (B z, ℓ + (v - ℓ)) =
      (B (saddleBandCurve z (θ (v - ℓ, u) * (t₀ - (v - ℓ)))), ℓ + (v - ℓ)) at hTV
    rw [hθ (v - ℓ) u hout, one_mul,
      saddleBandCurve_saddleBandLevelCurve hrad
        (add_nonneg ht₀ (mul_nonneg hs (sq_nonneg u))) hσ hunit] at hTV
    exact ⟨(B z, ℓ + (v - ℓ)), hgraph (v - ℓ) ht z hzwidth hzlevel,
      hTV.trans (Prod.ext rfl (by ring))⟩
  · obtain ⟨u, hu⟩ := hyclosing
    exact ⟨(γ (v - ℓ, u), ℓ + (v - ℓ)), hclosing (v - ℓ) ht u,
      (hTclosing (v - ℓ) ht u).trans (Prod.ext hu (by ring))⟩


theorem exists_isOpen_graph_image_saddle_cutoff_of_isCompact
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ ℓ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, p.1.1 ∈ Ioo (-k) k)
    (hbottom : ∀ p ∈ K, -v₀ < σ * p.1.2)
    (hmodel : ∀ p ∈ K,
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0)
    {θ : ℝ × ℝ → ℝ}
    (hθformula : ∀ t u, θ (t, u) =
      1 - (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * κ u)
    {Z S : Set (F × ℝ)} (hZ : IsOpen Z)
    (hZeq : Z ∩ S = Z ∩ {q | (1 - (B.symm q.1).1 ^ 2) * ((B.symm q.1).2 ^ 2 + 2 * s) / 2 =
      s + (q.2 - ℓ) + θ (q.2 - ℓ, (B.symm q.1).1) * (τ - (q.2 - ℓ))})
    (hKZ : (fun p : (ℝ × ℝ) × ℝ => (B p.1, ℓ + p.2)) '' K ⊆ Z)
    (hKτ : ∀ p ∈ K, p.2 < τ) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      ∀ (Q : (F × ℝ) ≃ₘ[ℝ] (F × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ) (α : ℝ), 0 < α →
        (∀ t ≤ ℓ + τ, ∀ y, Q (y, t) = ((α * Real.exp (-μ * t)) • G.symm y, ψ t)) →
        ∃ O : Set F, IsOpen O ∧ ∃ g : F → ℝ, ContDiffOn ℝ ∞ g O ∧
          ∃ W : Set (F × ℝ), IsOpen W ∧
            Q '' ((fun p : (ℝ × ℝ) × ℝ => (B p.1, ℓ + p.2)) '' K) ⊆ W ∧
            W ⊆ Q '' Z ∧ W ⊆ {p | p.1 ∈ O} ∧
            W ∩ Q '' S = W ∩ {p | p.2 = g p.1} := by
  obtain ⟨δ, hδ, hgraphs⟩ := exists_isOpen_graph_exp_smul_saddle_band_cutoff_of_isCompact
    B G hκ hκnonneg hs hτ hσ hk hr hv₀ hv₀τ hcurve hV hκV hside hK hwidth hbottom hmodel
  refine ⟨δ, hδ, fun μ hμ Q ψ α hα hQlow => ?_⟩
  obtain ⟨Og, hOg, gg, hgg, Wg, hWg, hKg, hWOg, hgeq⟩ := hgraphs μ hμ
  let P : F × ℝ → F × ℝ := fun q =>
    (Real.exp (-μ * (q.2 - ℓ)) • G.symm q.1, q.2 - ℓ)
  let Kphys : Set (F × ℝ) :=
    (fun q : (ℝ × ℝ) × ℝ => (B q.1, ℓ + q.2)) '' (K)
  have hKP (q : F × ℝ) (hq : q ∈ Kphys) : P q ∈ Wg := by
    obtain ⟨w, hw, rfl⟩ := hq
    have hm := hKg (mem_image_of_mem _ hw)
    change (Real.exp (-μ * w.2) • G.symm (B w.1), w.2) ∈ Wg at hm
    simpa only [P, add_sub_cancel_left] using hm
  have hKtime (q : F × ℝ) (hq : q ∈ Kphys) : q.2 < ℓ + τ := by
    obtain ⟨w, hw, rfl⟩ := hq
    have ht := hKτ w hw
    dsimp only
    linarith only [ht]
  have hactualGraph (q : F × ℝ) (hqZ : q ∈ Z) (hqW : P q ∈ Wg) :
      q ∈ S ↔ (P q).2 = gg (P q).1 := by
    have hcancel : (B.trans G.symm).symm
        (Real.exp (μ * (P q).2) • (P q).1) = B.symm q.1 := by
      dsimp only [P]
      rw [smul_smul, ← Real.exp_add,
        show μ * (q.2 - ℓ) + -μ * (q.2 - ℓ) = 0 by ring,
        Real.exp_zero, one_smul]
      change B.symm (G (G.symm q.1)) = B.symm q.1
      rw [G.apply_symm_apply]
    have hgiff := Set.ext_iff.mp hgeq (P q)
    simp only [mem_inter_iff, mem_ofPred_eq, hqW, true_and] at hgiff
    rw [hcancel] at hgiff
    have hsiff := Set.ext_iff.mp hZeq q
    simp only [mem_inter_iff, mem_ofPred_eq, hqZ, true_and] at hsiff
    rw [← hgiff]
    rw [hsiff, hθformula]
    dsimp only [P]
    constructor <;> intro heq <;> nlinarith only [heq]
  apply Diffeomorph.exists_isOpen_graph_image_of_exponential_formula
    G Q ψ (k := α * Real.exp (-μ * ℓ))
    (μ := μ) (ℓ := ℓ) (a := ℓ + τ)
    (mul_pos hα (Real.exp_pos _)).ne' ?_ hOg hgg hWg hWOg hZ
    hactualGraph hKZ hKtime hKP
  intro q hq
  rw [show q = (q.1, q.2) from rfl, hQlow q.2 hq.le]
  refine Prod.ext ?_ rfl
  dsimp only
  rw [smul_smul, mul_assoc, ← Real.exp_add,
    show -μ * ℓ + -μ * (q.2 - ℓ) = -μ * q.2 by ring]

theorem reference_cylinder_subset_image_of_saddle_band
    {F ι : Type*} (B : (ℝ × ℝ) → F) (T : F × ℝ → F × ℝ)
    {S : Set (F × ℝ)} {C : Set F} {s h t₀ a ℓ σ : ℝ}
    (hs : 0 ≤ s) (hh1 : h < 1) (ha : 0 < a) (hσ : σ ^ 2 = 1)
    (hgraph : ∀ t ∈ Icc a t₀, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t → (B z, ℓ + t) ∈ S)
    (hmodel : ∀ t ∈ Icc a t₀, ∀ z : ℝ × ℝ, |z.1| ≤ h →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t →
      T (B z, ℓ + t) = (B (saddleBandCurve z (t₀ - t)), ℓ + t))
    {γ : ℝ × ι → F}
    (hclosing : ∀ t ∈ Icc a t₀, ∀ u, (γ (t, u), ℓ + t) ∈ S)
    (hTclosing : ∀ t ∈ Icc a t₀, ∀ u,
      T (γ (t, u), ℓ + t) = (γ (t₀, u), ℓ + t))
    (hC : C = B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ∪
      range (fun u => γ (t₀, u))) :
    C ×ˢ Icc (ℓ + a) (ℓ + t₀) ⊆ T '' S := by
  rintro ⟨y, v⟩ ⟨hy, hv⟩
  have ht : v - ℓ ∈ Icc a t₀ := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have htpos : 0 < v - ℓ := ha.trans_le ht.1
  rw [hC] at hy
  rcases hy with hyselected | hyclosing
  · obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hyselected
    have hunit : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    let z := saddleBandLevelCurve s (v - ℓ) σ u
    have hzwidth : |z.1| ≤ h := abs_le.mpr hu
    have hzlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + (v - ℓ) := by
      simpa only [zero_add] using saddleBandLevelCurve_height hs htpos hσ hunit (0 : ℝ)
    have hTV := hmodel (v - ℓ) ht z hzwidth hzlevel
    rw [show z = saddleBandLevelCurve s (v - ℓ) σ u from rfl,
      saddleBandCurve_saddleBandLevelCurve
        (add_pos_of_pos_of_nonneg htpos (mul_nonneg hs (sq_nonneg u)))
        (add_nonneg (htpos.le.trans ht.2) (mul_nonneg hs (sq_nonneg u))) hσ hunit] at hTV
    exact ⟨(B z, ℓ + (v - ℓ)), hgraph (v - ℓ) ht z hzwidth hzlevel,
      hTV.trans (Prod.ext rfl (by ring))⟩
  · obtain ⟨u, hu⟩ := hyclosing
    exact ⟨(γ (v - ℓ, u), ℓ + (v - ℓ)), hclosing (v - ℓ) ht u,
      (hTclosing (v - ℓ) ht u).trans (Prod.ext hu (by ring))⟩

theorem saddle_lower_band_inter_cap_circle_subset
    {F : Type*} [SeminormedAddCommGroup F]
    (B : (ℝ × ℝ) → F) (G : F → F)
    {s t₀ δ σ h k R r v₀ : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀)
    (ht₀δ : t₀ < δ) (hσ : σ ^ 2 = 1) (hh1 : h < 1) (hkh : k < h)
    (hv₀ : 0 ≤ v₀) (hv₀t : v₀ ^ 2 < 2 * t₀)
    (hupper : ∀ u ∈ Icc (-h) h,
      saddleBandLevelCurve s δ σ u ∈ Icc (-h) h ×ˢ Icc (-R) R)
    (hclear : ∀ a < t₀, ∃ ρ > 0, cthickening ρ
      (B '' {z : ℝ × ℝ | z ∈ Icc (-h) h ×ˢ Icc (-R) R ∧
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + a}) ⊆
          (G '' closedBall 0 r)ᶜ)
    {K : Set (ℝ × ℝ)}
    (hwidth : ∀ z ∈ K, |z.1| ≤ k)
    (hbottom : ∀ z ∈ K, -v₀ ≤ σ * z.2)
    (henergy : ∀ z ∈ K, (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + t₀) :
    (B '' K) ∩ (G '' sphere 0 r) ⊆ B '' (saddleBandLevelCurve s t₀ σ '' Icc (-k) k) := by
  rintro y ⟨⟨z, hz, rfl⟩, hyC⟩
  have hu : z.1 ∈ Icc (-h) h := abs_le.mp ((hwidth z hz).trans hkh.le)
  have hui : z.1 ∈ Ioo (-1 : ℝ) 1 := by
    have hu' := abs_le.mp (hwidth z hz)
    exact ⟨by linarith [hu'.1], hu'.2.trans_lt (hkh.trans hh1)⟩
  have hden : 0 < 1 - z.1 ^ 2 := by nlinarith [hui.1, hui.2]
  have hhigh := saddleBandLevelCurve_height hs (ht₀.trans ht₀δ) hσ hui (0 : ℝ)
  have hhighbound := (hupper z.1 hu).2
  have hR : 0 ≤ R := by linarith [hhighbound.1, hhighbound.2]
  have hvsq : z.2 ^ 2 < (saddleBandLevelCurve s δ σ z.1).2 ^ 2 := by
    have hq := henergy z hz
    simp only [zero_add, saddleBandLevelCurve] at hhigh
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hden.le
    dsimp only [saddleBandLevelCurve] at hm
    nlinarith
  have hzrect : z ∈ Icc (-h) h ×ˢ Icc (-R) R := by
    refine ⟨hu, ?_⟩
    have hsquare : (saddleBandLevelCurve s δ σ z.1).2 ^ 2 ≤ R ^ 2 := by
      nlinarith [hhighbound.1, hhighbound.2]
    constructor <;> nlinarith
  have hyD : B z ∈ G '' closedBall 0 r := image_mono sphere_subset_closedBall hyC
  have hlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t₀ := by
    apply le_antisymm (henergy z hz)
    by_contra hn
    have hlt : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s < t₀ := by linarith
    obtain ⟨ρ, _, hρ⟩ := hclear _ hlt
    exact hρ (self_subset_cthickening _ ⟨z, ⟨hzrect, by linarith⟩, rfl⟩) hyD
  have hzcurve := eq_saddleBandLevelCurve_of_height_eq_of_lower_bound hs hσ hv₀ hv₀t
    (hbottom z hz) hlevel
  exact ⟨z, ⟨z.1, abs_le.mp (hwidth z hz), hzcurve.symm⟩, rfl⟩

private theorem reference_level_mem_image_saddle_cutoff_half_band
    {F : Type*} (B : (ℝ × ℝ) → F) (T : F × ℝ → F × ℝ)
    {s k a j v₀ σ ℓ τ t u : ℝ}
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hk : k < 1) (hv₀ : 0 ≤ v₀)
    (hσ : σ ^ 2 = 1) (ht : t ∈ Icc a j) (hu : |u| ≤ k)
    (hrad : 0 < t + s * u ^ 2)
    {θ : ℝ × ℝ → ℝ} (hθ : θ (t, u) = 1)
    (hmodel : ∀ z : ℝ × ℝ, |z.1| ≤ k → -v₀ ≤ σ * z.2 →
      a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j →
      T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) =
        (B (saddleBandCurve z (θ (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z.1) *
          (τ - ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))),
          ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))) :
    (B (saddleBandLevelCurve s τ σ u), t) ∈
      (fun z : ℝ × ℝ =>
        ((T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1,
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) ''
        {z : ℝ × ℝ | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
          a ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
          (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j} := by
  have hunit : u ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (hu.trans_lt hk)
  let z := saddleBandLevelCurve s t σ u
  have hlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s = t := by
    have heq := saddleBandLevelCurve_height_of_nonneg hrad.le hσ hunit (0 : ℝ)
    dsimp only [z]
    linarith only [heq]
  have hbottom : -v₀ ≤ σ * z.2 := by
    change -v₀ ≤ σ * (σ * Real.sqrt (2 * (t + s * u ^ 2) / (1 - u ^ 2)))
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
    exact (neg_nonpos.mpr hv₀).trans (Real.sqrt_nonneg _)
  refine ⟨z, ⟨hu, hbottom, by simpa only [hlevel] using ht.1,
    by simpa only [hlevel] using ht.2⟩, ?_⟩
  have hm := hmodel z hu hbottom (hlevel ▸ ht.1) (hlevel ▸ ht.2)
  dsimp only
  rw [hlevel] at hm ⊢
  change T (B z, ℓ + t) =
    (B (saddleBandCurve z (θ (t, u) * (τ - t))), ℓ + t) at hm
  rw [hθ, one_mul, show z = saddleBandLevelCurve s t σ u from rfl,
    saddleBandCurve_saddleBandLevelCurve hrad
      (add_nonneg hτ (mul_nonneg hs (sq_nonneg u))) hσ hunit] at hm
  exact congrArg (fun x : F × ℝ => (x.1, t)) hm

theorem reference_cylinder_subset_image_saddle_cutoff_half_band
    {F : Type*} (B : (ℝ × ℝ) → F) (T : F × ℝ → F × ℝ)
    {s h k ε j v₀ σ ℓ τ : ℝ} {C : Set F}
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hτ : 0 < τ) (hk : k < 1) (hv₀ : 0 ≤ v₀)
    (hσ : σ ^ 2 = 1) (hε : ε < s * h ^ 2 / 16)
    {θ : ℝ × ℝ → ℝ}
    (hθ : ∀ t u, τ / 2 ≤ t ∨ h / 2 ≤ |u| → θ (t, u) = 1)
    (hmodel : ∀ z : ℝ × ℝ, |z.1| ≤ k → -v₀ ≤ σ * z.2 →
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j →
      T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) =
        (B (saddleBandCurve z (θ (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s), z.1) *
          (τ - ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)))),
          ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))) :
    let R : Set (ℝ × ℝ) := {z | |z.1| ≤ k ∧ -v₀ ≤ σ * z.2 ∧
      -ε / 2 ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ∧
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s ≤ j}
    let J : (ℝ × ℝ) → F × ℝ := fun z =>
      ((T (B z, ℓ + ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s))).1,
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)
    let S := J '' R ∪
      (C \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-k) k)) ×ˢ Icc (-ε / 2) j
    {p : F × ℝ | p.1 ∈ C ∧ p.2 ∈ Icc (-ε / 2) j ∧
      (τ / 2 ≤ p.2 ∨ p.1 ∉ B '' (saddleBandLevelCurve s τ σ '' Icc (-(h / 2)) (h / 2)))} ⊆ S := by
  intro R J S p hp
  by_cases hout : p.1 ∈ B '' (saddleBandLevelCurve s τ σ '' Ioo (-k) k)
  · obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := hout
    have huabs : |u| ≤ k := (abs_lt.mpr hu).le
    have hbranch : τ / 2 ≤ p.2 ∨ h / 2 ≤ |u| := by
      rcases hp.2.2 with ht | hc
      · exact Or.inl ht
      · apply Or.inr
        by_contra hn
        exact hc ⟨_, ⟨u, ⟨(abs_lt.mp (lt_of_not_ge hn)).1.le, (abs_lt.mp (lt_of_not_ge hn)).2.le⟩, rfl⟩, heq⟩
    have hrad : 0 < p.2 + s * u ^ 2 := by
      rcases hbranch with ht | hu'
      · exact add_pos_of_pos_of_nonneg (by linarith only [ht, hτ])
          (mul_nonneg hs (sq_nonneg u))
      · have hsq := mul_self_le_mul_self (show 0 ≤ h / 2 by positivity) hu'
        have hsq' : h ^ 2 / 4 ≤ u ^ 2 := by nlinarith only [hsq, sq_abs u]
        have hmul := mul_le_mul_of_nonneg_left hsq' hs
        have hspos := mul_nonneg hs (sq_nonneg h)
        nlinarith only [hp.2.1.1, hε, hmul, hspos, sq_abs u]
    apply Or.inl
    change (p.1, p.2) ∈ J '' R
    rw [← heq]
    exact reference_level_mem_image_saddle_cutoff_half_band B T hs hτ.le hk hv₀ hσ
      hp.2.1 huabs hrad (hθ p.2 u hbranch) hmodel
  · exact Or.inr ⟨⟨hp.1, hout⟩, hp.2.1⟩

theorem exists_pos_on_exp_smul_saddle_cutoff_trace_of_isCompact
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ a b : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k,
      B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, p.1.1 ∈ Ioo (-k) k)
    (hbottom : ∀ p ∈ K, -v₀ < σ * p.1.2)
    (hmodel : ∀ p ∈ K,
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0)
    (htime : ∀ p ∈ K, p.2 ∈ Icc a b) :
    let C := B.trans G.symm
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ, ∀ p ∈ K, ∀ t ∈ Ico a p.2,
      let z := C.symm (Real.exp (μ * (t - p.2)) • C p.1)
      z.1 ∈ Ioo (-k) k ∧ -v₀ < σ * z.2 ∧
        0 < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s - τ +
          κ z.1 * ((1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)) := by
  intro C
  let S : Set (ℝ × ℝ) := Prod.fst '' K
  have hS : IsCompact S := hK.image continuous_fst
  let U : Set (ℝ × ℝ) := {z | z.1 ∈ Ioo (-k) k ∧ -v₀ < σ * z.2}
  have hU : IsOpen U := (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd))
  have hSU : S ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hwidth p hp, hbottom p hp⟩
  obtain ⟨ρ, hρ, hρU⟩ := hS.exists_cthickening_subset_open hU hSU
  let X := cthickening ρ S
  let Y := cthickening (ρ / 2) S
  have hYX : Y ⊆ interior X :=
    (cthickening_subset_thickening' hρ (half_lt_self hρ) S).trans
      (thickening_subset_interior_cthickening ρ S)
  have hSY : S ⊆ interior Y := (self_subset_thickening (half_pos hρ) S).trans
    (thickening_subset_interior_cthickening (ρ / 2) S)
  let A : ℝ → ℝ := fun t =>
    (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)
  let Q : F → ℝ := fun x =>
    (1 - (B.symm x).1 ^ 2) * ((B.symm x).2 ^ 2 + 2 * s) / 2
  let f : F → ℝ := fun x => Q (G x) - s - τ
  have hQ : ContDiff ℝ ∞ Q :=
    ((contDiff_const.sub (B.symm.contDiff.fst.pow 2)).mul
      ((B.symm.contDiff.snd.pow 2).add contDiff_const)).div_const 2
  have hf : ContDiff ℝ ∞ f := (hQ.comp G.contDiff).sub contDiff_const |>.sub contDiff_const
  have hA : ContDiff ℝ ∞ A := by
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using (Real.smoothTransition.contDiff_one_sub_mul_sub
      (τ / 4) (τ / 2) τ)
  have hAn (t : ℝ) : deriv A t ≤ 0 := by
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using Real.smoothTransition.deriv_one_sub_mul_sub_nonpos
      (show τ / 4 < τ / 2 by linarith) (show τ / 2 ≤ τ by linarith) t
  have hAz (t : ℝ) (ht : deriv A t = 0) : A t = 0 := by
    have htlarge : τ / 2 ≤ t := by
      by_contra hn
      have heq : τ / 2 - τ / 4 = τ / 4 := by ring
      have hneg : deriv A t < 0 := by
        simpa only [heq] using Real.smoothTransition.deriv_one_sub_mul_sub_neg
          (show τ / 4 < τ / 2 by linarith) (show τ / 2 ≤ τ by linarith) (lt_of_not_ge hn)
      exact (ne_of_lt hneg) ht
    have heq : τ / 2 - τ / 4 = τ / 4 := by ring
    simpa only [heq] using Real.smoothTransition.one_sub_mul_sub_eq_zero
      (c := τ) (show τ / 4 < τ / 2 by linarith) htlarge
  let κG : F → ℝ := fun x => κ (B.symm (G x)).1
  have hκG : ContDiff ℝ ∞ κG := hκ.comp (B.symm.contDiff.comp G.contDiff).fst
  have hinner : C '' Y ⊆ interior (C '' X) := by
    change C.toHomeomorph '' Y ⊆ interior (C.toHomeomorph '' X)
    rw [← C.toHomeomorph.image_interior]
    exact image_mono hYX
  obtain ⟨δ, hδ, htrace⟩ := DifferentialGeometry.Analysis.exists_pos_on_exp_smul_add_mul_zero_set_trace
    (hf.of_le (by simp)) (hκG.of_le (by simp)) (hA.of_le (by simp))
    (fun x => hκnonneg _) ((hS.cthickening (r := ρ)).image C.continuous)
    ((hS.cthickening (r := ρ / 2)).image C.continuous) hinner
    (fun t _ => hAn t) (fun t _ => hAz t) (a := a) (b := b)
    (fderiv_saddle_band_height_comp_neg B G hs hτ hσ hk hr hv₀ hv₀τ hcurve hV hκV hside
      (fun z hz => (hρU hz).1) (fun z hz => (hρU hz).2.le))
  refine ⟨δ, hδ, fun μ hμ p hp t ht => ?_⟩
  have hpmodel : f (C p.1) + κG (C p.1) * A p.2 = 0 := by
    dsimp only [f, Q, κG]
    change (1 - (B.symm (G (G.symm (B p.1)))).1 ^ 2) *
      ((B.symm (G (G.symm (B p.1)))).2 ^ 2 + 2 * s) / 2 - s - τ +
      κ (B.symm (G (G.symm (B p.1)))).1 * A p.2 = 0
    rw [G.apply_symm_apply, B.symm_apply_apply]
    exact hmodel p hp
  obtain ⟨hx, hpos⟩ := htrace μ hμ (C p.1, p.2)
    ⟨mem_image_of_mem C (interior_subset (hSY (mem_image_of_mem Prod.fst hp))), htime p hp⟩
    hpmodel t ht
  have hzX : C.symm (Real.exp (μ * (t - p.2)) • C p.1) ∈ X := by
    obtain ⟨z, hz, heq⟩ := interior_subset hx
    rw [← heq, C.symm_apply_apply]
    exact hz
  refine ⟨(hρU hzX).1, (hρU hzX).2, ?_⟩
  exact hpos

private theorem saddle_height_le_on_exp_smul_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {s τ σ k r v₀ μ t b : ℝ} (hs : 0 ≤ s)
    (hσ : σ ^ 2 = 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ) (hμ : 0 < μ) (ht : t < b)
    (hcurve : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    (x : F)
    (hdomain : ∀ v ∈ Icc t b,
      (B.symm (G (Real.exp (μ * (v - b)) • x))).1 ∈ Ioo (-k) k ∧
        -v₀ ≤ σ * (B.symm (G (Real.exp (μ * (v - b)) • x))).2)
    (hstart : (1 - (B.symm (G x)).1 ^ 2) * ((B.symm (G x)).2 ^ 2 + 2 * s) / 2 ≤ s + τ)
    (hout : r ≤ ‖Real.exp (μ * (t - b)) • x‖) :
    (1 - (B.symm (G (Real.exp (μ * (t - b)) • x))).1 ^ 2) *
      ((B.symm (G (Real.exp (μ * (t - b)) • x))).2 ^ 2 + 2 * s) / 2 ≤ s + τ := by
  let z : ℝ → ℝ × ℝ := fun v => B.symm (G (Real.exp (μ * (v - b)) • x))
  let f : ℝ → ℝ := fun v => (1 - (z v).1 ^ 2) * ((z v).2 ^ 2 + 2 * s) / 2 - s - τ
  have hf : Continuous f := by dsimp [f, z]; fun_prop
  have hfb : f b ≤ 0 := by simpa [f, z, add_comm] using sub_nonpos.mpr hstart
  by_contra hn
  have hft : 0 < f t := by dsimp only [f, z]; linarith only [lt_of_not_ge hn]
  obtain ⟨v, hv, hvzero⟩ := intermediate_value_Icc' ht.le hf.continuousOn
    (show (0 : ℝ) ∈ Icc (f b) (f t) from ⟨hfb, hft.le⟩)
  have htv : t < v := lt_of_le_of_ne hv.1 (fun heq => by
    rw [← heq] at hvzero
    exact hft.ne' hvzero)
  have hvlevel : (1 - (z v).1 ^ 2) * ((z v).2 ^ 2 + 2 * s) / 2 = s + τ := by
    change (1 - (z v).1 ^ 2) * ((z v).2 ^ 2 + 2 * s) / 2 - s - τ = 0 at hvzero
    linarith only [hvzero]
  have hvdom := hdomain v hv
  have hzcurve := eq_saddleBandLevelCurve_of_height_eq_of_lower_bound hs hσ hv₀ hv₀τ
    hvdom.2 hvlevel
  change z v = saddleBandLevelCurve s τ σ (z v).1 at hzcurve
  have hC : B (z v) ∈ G '' sphere 0 r := by
    rw [hzcurve]
    exact hcurve (z v).1 hvdom.1
  obtain ⟨y, hy, heq⟩ := hC
  have hynorm : ‖y‖ = r := mem_sphere_zero_iff_norm.mp hy
  have hyx : y = Real.exp (μ * (v - b)) • x := by
    apply G.injective
    exact heq.trans (B.apply_symm_apply _)
  rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hynorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hout
  have hxn : 0 < ‖x‖ := by
    have hmul : 0 < Real.exp (μ * (t - b)) * ‖x‖ := hr.trans_le hout
    exact (mul_pos_iff.mp hmul).resolve_right (fun h => (Real.exp_pos _).not_gt h.1) |>.2
  have hexp : Real.exp (μ * (t - b)) < Real.exp (μ * (v - b)) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (sub_lt_sub_right htv b) hμ)
  have hnormlt := mul_lt_mul_of_pos_right hexp hxn
  linarith only [hnormlt, hynorm, hout]

theorem exists_disjoint_exp_smul_saddle_cutoff_trace
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] F) (G : F ≃ₘ[ℝ] F)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hκnonneg : ∀ u, 0 ≤ κ u)
    {s τ σ k r v₀ a b ℓ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (hσ : σ ^ 2 = 1) (hk : k < 1) (hr : 0 < r)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    (hcurve : ∀ u ∈ Ioo (-k) k, B (saddleBandLevelCurve s τ σ u) ∈ G '' sphere 0 r)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hκV : saddleBandLevelCurve s τ σ '' Ioo (-k) k ⊆ V)
    (hside : ∀ z ∈ V, s + τ ≤ (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      B z ∈ G '' closedBall 0 r)
    {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K)
    (hwidth : ∀ p ∈ K, p.1.1 ∈ Ioo (-k) k)
    (hbottom : ∀ p ∈ K, -v₀ < σ * p.1.2)
    (hmodel : ∀ p ∈ K,
      (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 - s - τ +
        κ p.1.1 * ((1 - Real.smoothTransition ((p.2 - τ / 4) / (τ / 4))) * (τ - p.2)) = 0)
    (htime : ∀ p ∈ K, p.2 ∈ Icc a b)
    (henergy : ∀ p ∈ K, (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 ≤ s + τ)
    {θ : ℝ × ℝ → ℝ}
    (hθ : ∀ t u, θ (t, u) =
      1 - (1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * κ u)
    {S : Set (F × ℝ)}
    (hclear : Disjoint S (interior (G '' closedBall 0 r) ×ˢ Icc (ℓ + a) (ℓ + b)))
    (hwedge : ∀ t ∈ Icc a b, ∀ z : ℝ × ℝ, |z.1| ≤ k →
      s + t + θ (t, z.1) * (τ - t) < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 →
      (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + τ → (B z, ℓ + t) ∉ S) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ, ∀ p ∈ K, ∀ t ∈ Ico a p.2,
      (G (Real.exp (μ * (t - p.2)) • G.symm (B p.1)), ℓ + t) ∉ S := by
  obtain ⟨δ, hδ, htrace⟩ := exists_pos_on_exp_smul_saddle_cutoff_trace_of_isCompact
    B G hκ hκnonneg hs hτ hσ hk hr hv₀ hv₀τ hcurve hV hκV hside hK hwidth hbottom hmodel htime
  refine ⟨δ, hδ, fun μ hμ p hp t ht => ?_⟩
  let x := Real.exp (μ * (t - p.2)) • G.symm (B p.1)
  have htab : t ∈ Icc a b := ⟨ht.1, ht.2.le.trans (htime p hp).2⟩
  by_cases hinside : ‖x‖ < r
  · apply fun hm => disjoint_left.mp hclear hm
      (show (G x, ℓ + t) ∈ interior (G '' closedBall 0 r) ×ˢ Icc (ℓ + a) (ℓ + b) from ?_)
    refine ⟨?_, by dsimp only; linarith only [htab.1], by dsimp only; linarith only [htab.2]⟩
    change G x ∈ interior (G.toHomeomorph '' closedBall 0 r)
    rw [← G.toHomeomorph.image_interior, interior_closedBall (0 : F) hr.ne']
    exact mem_image_of_mem G (mem_ball_zero_iff.mpr hinside)
  · let z := B.symm (G x)
    have hzt := htrace μ hμ p hp t ht
    have hzenergy : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + τ := by
      apply saddle_height_le_on_exp_smul_trace B G hs hσ hr hv₀ hv₀τ hμ.1 ht.2 hcurve
        (G.symm (B p.1)) ?_ ?_ (le_of_not_gt hinside)
      · intro v hv
        rcases hv.2.eq_or_lt with rfl | hvlt
        · simpa only [sub_self, mul_zero, Real.exp_zero, one_smul, G.apply_symm_apply,
            B.symm_apply_apply] using And.intro (hwidth p hp) (hbottom p hp).le
        · have hvtrace := htrace μ hμ p hp v ⟨ht.1.trans hv.1, hvlt⟩
          exact ⟨hvtrace.1, hvtrace.2.1.le⟩
      · simpa only [G.apply_symm_apply, B.symm_apply_apply] using henergy p hp
    have hprofile : s + t + θ (t, z.1) * (τ - t) <
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by
      have hpos : 0 < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s - τ +
          κ z.1 * ((1 - Real.smoothTransition ((t - τ / 4) / (τ / 4))) * (τ - t)) := hzt.2.2
      rw [hθ]
      nlinarith only [hpos]
    have hnot := hwedge t htab z (abs_lt.mpr hzt.1).le hprofile hzenergy
    simpa only [z, B.apply_symm_apply] using hnot

end DifferentialGeometry.Topology.Morse
