import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Topology.Diffeomorph.Perturbation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped ContDiff Manifold NNReal

namespace Diffeomorph

private theorem lipschitzWith_scaled_bump_mul (b : ContDiffBump (0 : ℝ))
    {B : ℝ≥0} (hB : LipschitzWith B b) {R D : ℝ} (hR : 0 < R)
    (hcoeff : D * (B : ℝ) * R⁻¹ ≤ 1 / 2) (t a v : ℝ) (hv : ‖v‖ ≤ D) :
    LipschitzWith (1 / 2) (fun y => Real.smoothTransition t * b (R⁻¹ * (y - a)) * v) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  change dist (Real.smoothTransition t * b (R⁻¹ * (y - a)) * v)
    (Real.smoothTransition t * b (R⁻¹ * (z - a)) * v) ≤
      ((1 / 2 : ℝ≥0) : ℝ) * dist y z
  rw [dist_eq_norm, ← sub_mul, ← mul_sub, norm_mul, norm_mul,
    Real.norm_of_nonneg (Real.smoothTransition.nonneg t)]
  have hb := hB.norm_sub_le (R⁻¹ * (y - a)) (R⁻¹ * (z - a))
  have heq : R⁻¹ * (y - a) - R⁻¹ * (z - a) = R⁻¹ * (y - z) := by ring
  rw [heq, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)] at hb
  calc
    Real.smoothTransition t * ‖b (R⁻¹ * (y - a)) - b (R⁻¹ * (z - a))‖ * ‖v‖ ≤
        ‖b (R⁻¹ * (y - a)) - b (R⁻¹ * (z - a))‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)) (norm_nonneg _)
    _ ≤ ((B : ℝ) * (R⁻¹ * ‖y - z‖)) * D :=
      mul_le_mul hb hv (norm_nonneg _) (by positivity)
    _ = (D * (B : ℝ) * R⁻¹) * ‖y - z‖ := by ring
    _ ≤ (1 / 2) * ‖y - z‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ = ((1 / 2 : ℝ≥0) : ℝ) * dist y z := by norm_num [dist_eq_norm]

private theorem strictMono_add_of_lipschitzWith_half {u : ℝ → ℝ}
    (hu : LipschitzWith (1 / 2) u) : StrictMono (fun x => x + u x) := by
  intro y z hyz
  have hb := hu.norm_sub_le y z
  have hab := le_abs_self (u y - u z)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hyz)] at hb
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one] at hb
  change y + u y < z + u z
  linarith

private theorem exists_addLipschitz_family {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {G : P × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hLip : ∀ p, LipschitzWith (1 / 2) (fun y => G (p, y))) :
    ∃ e : P → ℝ ≃ₘ[ℝ] ℝ, (∀ p y, e p y = y + G (p, y)) ∧
      ContDiff ℝ ∞ (fun z : P × ℝ => e z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : P × ℝ => (e z.1).symm z.2) := by
  have hC : (1 / 2 : ℝ≥0) < 1 := by norm_num
  let e : P → ℝ ≃ₘ[ℝ] ℝ := fun p =>
    addLipschitz (hG.comp (contDiff_const.prodMk contDiff_id)) (hLip p) hC
  refine ⟨e, fun _ _ => rfl, contDiff_snd.add hG, ?_⟩
  exact contDiff_addLipschitz_symm hG (by simp) hLip (fun _ => hC)

theorem exists_isotopy_graphOn_of_hasCompactSupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport (fun x => g x - f x)) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ (t : ℝ) (p : E × ℝ), (H t p).1 = p.1) ∧
      (∀ (t : ℝ) (x : E), H t (x, f x) = (x, f x + Real.smoothTransition t * (g x - f x))) ∧
      (∀ (t : ℝ) (p : E × ℝ), f p.1 = g p.1 → H t p = p ∧ (H t).symm p = p) ∧
      (∀ (t : ℝ) (s : Set E), H t '' Set.graphOn f s =
        Set.graphOn (fun x => f x + Real.smoothTransition t * (g x - f x)) s) ∧
      (∀ (t : ℝ) (s : Set E), H t '' {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ f p.1 + Real.smoothTransition t * (g p.1 - f p.1) ≤ p.2}) ∧
      (∀ (t : ℝ) (s : Set E), H t '' {p : E × ℝ | p.1 ∈ s ∧ f p.1 < p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ f p.1 + Real.smoothTransition t * (g p.1 - f p.1) < p.2}) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Jᶜ ∧ Set.EqOn (H t).symm id Jᶜ := by
  let d : E → ℝ := fun x => g x - f x
  have hd : ContDiff ℝ ∞ d := hg.sub hf
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb₀ : b 0 = 1 := b.one_of_mem_closedBall (by norm_num [b])
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    b.contDiff (show (∞ : ℕ∞ω) ≠ 0 by simp)
  obtain ⟨D₀, hD₀⟩ := hs.exists_bound_of_continuous hd.continuous
  let D : ℝ := max D₀ 0 + 1
  have hD : 0 < D := by dsimp only [D]; linarith [le_max_right D₀ 0]
  have hbound : ∀ x, ‖d x‖ ≤ D := fun x =>
    (hD₀ x).trans (by dsimp only [D]; linarith [le_max_left D₀ 0])
  let R : ℝ := 2 * D * B + 1
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hcoeff : D * (B : ℝ) * R⁻¹ ≤ 1 / 2 := by
    apply (mul_inv_le_iff₀ hR).2
    dsimp only [R]
    linarith
  let G : (ℝ × E) × ℝ → ℝ := fun z =>
    Real.smoothTransition z.1.1 * b (R⁻¹ * (z.2 - f z.1.2)) * d z.1.2
  have hG : ContDiff ℝ ∞ G :=
    ((Real.smoothTransition.contDiff.comp contDiff_fst.fst).mul
      (b.contDiff.comp (contDiff_const.mul
        (contDiff_snd.sub (hf.comp contDiff_fst.snd))))).mul
      (hd.comp contDiff_fst.snd)
  have hLip : ∀ p : ℝ × E, LipschitzWith (1 / 2) (fun y => G (p, y)) :=
    fun p => lipschitzWith_scaled_bump_mul b hB hR hcoeff p.1 (f p.2) (d p.2) (hbound p.2)
  obtain ⟨e, he, hEf, hi⟩ := exists_addLipschitz_family hG hLip
  have hF : ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (z.2.1, e (z.1, z.2.1) z.2.2)) :=
    contDiff_snd.fst.prodMk
      (hEf.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))
  have hI : ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) =>
      (z.2.1, (e (z.1, z.2.1)).symm z.2.2)) :=
    contDiff_snd.fst.prodMk
      (hi.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))
  have heM : ∀ t, ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : E × ℝ => e (t, z.1) z.2) := by
    intro t
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (hEf.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)).contMDiff
  have hiM : ∀ t, ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : E × ℝ => (e (t, z.1)).symm z.2) := by
    intro t
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (hi.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)).contMDiff
  let H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)) := fun t =>
    { toEquiv := (prodCongrRight (fun x => e (t, x)) (heM t) (hiM t)).toEquiv
      contMDiff_toFun := (hF.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hI.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  have hH : ∀ t p, H t p = (p.1, e (t, p.1) p.2) := fun _ _ => rfl
  have hHfst : ∀ t p, (H t p).1 = p.1 := fun _ _ => rfl
  have hHIfst : ∀ t p, ((H t).symm p).1 = p.1 := fun _ _ => rfl
  have hgraph : ∀ t x, H t (x, f x) = (x, f x + Real.smoothTransition t * d x) := by
    intro t x
    rw [hH, he]
    simp only [G, sub_self, mul_zero, hb₀, mul_one]
  have hfiber : ∀ t p, f p.1 = g p.1 → H t p = p ∧ (H t).symm p = p := by
    intro t p hp
    have hd₀ : d p.1 = 0 := by simp only [d, hp, sub_self]
    have heq : H t p = p := by
      rw [hH, he]
      simp only [G, hd₀, mul_zero, add_zero, Prod.eta]
    refine ⟨heq, ?_⟩
    have h := congrArg (H t).symm heq
    simpa only [Diffeomorph.symm_apply_apply] using h.symm
  have hmono : ∀ p, StrictMono (e p) := by
    intro p y z hyz
    rw [he, he]
    exact strictMono_add_of_lipschitzWith_half (hLip p) hyz
  have hle : ∀ t p, f p.1 ≤ p.2 ↔
      f p.1 + Real.smoothTransition t * d p.1 ≤ (H t p).2 := by
    intro t p
    have hzero : e (t, p.1) (f p.1) = f p.1 + Real.smoothTransition t * d p.1 :=
      congrArg Prod.snd (hgraph t p.1)
    rw [hH, ← hzero]
    exact (hmono (t, p.1)).le_iff_le.symm
  have hlt : ∀ t p, f p.1 < p.2 ↔
      f p.1 + Real.smoothTransition t * d p.1 < (H t p).2 := by
    intro t p
    have hzero : e (t, p.1) (f p.1) = f p.1 + Real.smoothTransition t * d p.1 :=
      congrArg Prod.snd (hgraph t p.1)
    rw [hH, ← hzero]
    exact (hmono (t, p.1)).lt_iff_lt.symm
  let J : Set (E × ℝ) := (fun p : E × ℝ => (p.1, p.2 + f p.1)) ''
    ((tsupport d) ×ˢ Metric.closedBall (0 : ℝ) (2 * R))
  have hJ : IsCompact J :=
    (hs.prod (isCompact_closedBall (0 : ℝ) (2 * R))).image
      (continuous_fst.prodMk (continuous_snd.add (hf.continuous.comp continuous_fst)))
  have hfix : ∀ t p, p ∉ J → H t p = p := by
    intro t p hp
    have hz : G ((t, p.1), p.2) = 0 := by
      by_cases hx : p.1 ∈ tsupport d
      · have hu : 2 * R < ‖p.2 - f p.1‖ := by
          by_contra hu
          apply hp
          refine ⟨(p.1, p.2 - f p.1), ⟨hx, ?_⟩, ?_⟩
          · simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hu
          · apply Prod.ext
            · rfl
            · exact sub_add_cancel _ _
        have hb : b (R⁻¹ * (p.2 - f p.1)) = 0 := by
          apply b.zero_of_le_dist
          change 2 ≤ dist (R⁻¹ * (p.2 - f p.1)) 0
          rw [dist_zero_right, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
          rw [← div_eq_inv_mul]
          exact (le_div_iff₀ hR).2 hu.le
        simp only [G, hb, mul_zero, zero_mul]
      · simp only [G, image_eq_zero_of_notMem_tsupport hx, mul_zero]
    rw [hH, he, hz, add_zero]
  refine ⟨H, hF, hI, ?_, hHfst, hgraph, hfiber, ?_, ?_, ?_, J, hJ, ?_⟩
  · apply Diffeomorph.ext
    intro p
    rw [hH, he]
    change (p.1, p.2 + Real.smoothTransition 0 * b (R⁻¹ * (p.2 - f p.1)) * d p.1) = p
    simp only [Real.smoothTransition.zero, zero_mul, add_zero, Prod.eta]
  · intro t s
    simp only [Set.graphOn, Set.image_image]
    congr 1
    funext x
    exact hgraph t x
  · intro t s
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, (hle t q).1 hq.2⟩
    · intro hp
      refine ⟨(H t).symm p, ⟨?_, ?_⟩, (H t).apply_symm_apply p⟩
      · exact hp.1
      · apply (hle t ((H t).symm p)).2
        simpa only [Diffeomorph.apply_symm_apply, hHIfst, d] using hp.2
  · intro t s
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, (hlt t q).1 hq.2⟩
    · intro hp
      refine ⟨(H t).symm p, ⟨?_, ?_⟩, (H t).apply_symm_apply p⟩
      · exact hp.1
      · apply (hlt t ((H t).symm p)).2
        simpa only [Diffeomorph.apply_symm_apply, hHIfst, d] using hp.2
  · intro t
    constructor
    · intro p hp
      exact hfix t p hp
    · intro p hp
      have h := congrArg (H t).symm (hfix t p hp)
      simpa only [Diffeomorph.symm_apply_apply, id_eq] using h.symm

end Diffeomorph
