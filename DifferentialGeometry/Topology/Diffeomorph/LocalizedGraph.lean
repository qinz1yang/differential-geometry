import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Connected.Clopen
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
    (hcoeff : D * (B : ℝ) * R⁻¹ ≤ 1 / 2) (a v : ℝ) (hv : ‖v‖ ≤ D) :
    LipschitzWith (1 / 2) (fun y => b (R⁻¹ * (y - a)) * v) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm, ← sub_mul, norm_mul]
  have hb := hB.norm_sub_le (R⁻¹ * (y - a)) (R⁻¹ * (z - a))
  have heq : R⁻¹ * (y - a) - R⁻¹ * (z - a) = R⁻¹ * (y - z) := by ring
  rw [heq, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)] at hb
  calc
    ‖b (R⁻¹ * (y - a)) - b (R⁻¹ * (z - a))‖ * ‖v‖ ≤
        ((B : ℝ) * (R⁻¹ * ‖y - z‖)) * D :=
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

theorem exists_isotopy_graphOn_family_with_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) {K : Set E} (hK : IsCompact K)
    (hfixed : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∉ K, g (s, x) = g (0, x))
    (b : ContDiffBump (0 : ℝ)) {B D : ℝ≥0} (hB : LipschitzWith B b)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ‖g (s, x) - g (0, x)‖ ≤ D)
    {R : ℝ} (hR : 0 < R) (hcoeff : (D : ℝ) * B * R⁻¹ ≤ 1 / 2) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ (t : ℝ) (p : E × ℝ), (H t p).1 = p.1) ∧
      (∀ (t : ℝ) (x : E), H t (x, g (0, x)) = (x, g (Real.smoothTransition t, x))) ∧
      (∀ (t : ℝ) (p : E × ℝ), g (0, p.1) = g (Real.smoothTransition t, p.1) →
        H t p = p ∧ (H t).symm p = p) ∧
      (∀ (t : ℝ) (s : Set E), H t '' Set.graphOn (fun x => g (0, x)) s =
        Set.graphOn (fun x => g (Real.smoothTransition t, x)) s) ∧
      (∀ (t : ℝ) (s : Set E), H t '' {p : E × ℝ | p.1 ∈ s ∧ g (0, p.1) ≤ p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (Real.smoothTransition t, p.1) ≤ p.2}) ∧
      (∀ (t : ℝ) (s : Set E), H t '' {p : E × ℝ | p.1 ∈ s ∧ g (0, p.1) < p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (Real.smoothTransition t, p.1) < p.2}) ∧
      let C : Set (E × ℝ) := {p | p.1 ∈ K ∧ ‖p.2 - g (0, p.1)‖ ≤ b.rOut * R}
      IsCompact C ∧ ∀ t : ℝ, Set.EqOn (H t) id Cᶜ ∧ Set.EqOn (H t).symm id Cᶜ := by
  let f : E → ℝ := fun x => g (0, x)
  have hf : ContDiff ℝ ∞ f := hg.comp (contDiff_const.prodMk contDiff_id)
  let d : ℝ × E → ℝ := fun p => g p - f p.2
  have hd : ContDiff ℝ ∞ d := hg.sub (hf.comp contDiff_snd)
  have htime : ∀ t : ℝ, Real.smoothTransition t ∈ Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hb₀ : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hbound' : ∀ t x, ‖d (Real.smoothTransition t, x)‖ ≤ D := by
    intro t x
    by_cases hx : x ∈ K
    · exact hbound _ (htime t) x hx
    · simpa only [d, f, hfixed _ (htime t) x hx, sub_self, norm_zero] using D.coe_nonneg
  let G : (ℝ × E) × ℝ → ℝ := fun z =>
    b (R⁻¹ * (z.2 - f z.1.2)) * d (Real.smoothTransition z.1.1, z.1.2)
  have hG : ContDiff ℝ ∞ G :=
    (b.contDiff.comp (contDiff_const.mul
      (contDiff_snd.sub (hf.comp contDiff_fst.snd)))).mul
      (hd.comp ((Real.smoothTransition.contDiff.comp contDiff_fst.fst).prodMk
        contDiff_fst.snd))
  have hLip : ∀ p : ℝ × E, LipschitzWith (1 / 2) (fun y => G (p, y)) :=
    fun p => lipschitzWith_scaled_bump_mul b hB hR hcoeff (f p.2)
      (d (Real.smoothTransition p.1, p.2)) (hbound' p.1 p.2)
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
  have hgraph : ∀ t x, H t (x, f x) = (x, g (Real.smoothTransition t, x)) := by
    intro t x
    rw [hH, he]
    simp only [G, sub_self, mul_zero, hb₀, one_mul, d, add_sub_cancel]
  have hfiber : ∀ t p, f p.1 = g (Real.smoothTransition t, p.1) →
      H t p = p ∧ (H t).symm p = p := by
    intro t p hp
    have hd₀ : d (Real.smoothTransition t, p.1) = 0 := by simp only [d, hp, sub_self]
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
      g (Real.smoothTransition t, p.1) ≤ (H t p).2 := by
    intro t p
    have hzero : e (t, p.1) (f p.1) = g (Real.smoothTransition t, p.1) :=
      congrArg Prod.snd (hgraph t p.1)
    rw [hH, ← hzero]
    exact (hmono (t, p.1)).le_iff_le.symm
  have hlt : ∀ t p, f p.1 < p.2 ↔
      g (Real.smoothTransition t, p.1) < (H t p).2 := by
    intro t p
    have hzero : e (t, p.1) (f p.1) = g (Real.smoothTransition t, p.1) :=
      congrArg Prod.snd (hgraph t p.1)
    rw [hH, ← hzero]
    exact (hmono (t, p.1)).lt_iff_lt.symm
  let J : Set (E × ℝ) := (fun p : E × ℝ => (p.1, p.2 + f p.1)) ''
    (K ×ˢ Metric.closedBall (0 : ℝ) (b.rOut * R))
  have hJ : IsCompact J :=
    (hK.prod (isCompact_closedBall (0 : ℝ) (b.rOut * R))).image
      (continuous_fst.prodMk (continuous_snd.add (hf.continuous.comp continuous_fst)))
  have hfix : ∀ t p, p ∉ J → H t p = p := by
    intro t p hp
    have hz : G ((t, p.1), p.2) = 0 := by
      by_cases hx : p.1 ∈ K
      · have hu : b.rOut * R < ‖p.2 - f p.1‖ := by
          by_contra hu
          apply hp
          refine ⟨(p.1, p.2 - f p.1), ⟨hx, ?_⟩, ?_⟩
          · simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hu
          · apply Prod.ext
            · rfl
            · exact sub_add_cancel _ _
        have hb : b (R⁻¹ * (p.2 - f p.1)) = 0 := by
          apply b.zero_of_le_dist
          change b.rOut ≤ dist (R⁻¹ * (p.2 - f p.1)) 0
          rw [dist_zero_right, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
          rw [← div_eq_inv_mul]
          exact (le_div_iff₀ hR).2 hu.le
        simp only [G, hb, zero_mul]
      · simp only [G, d, f, hfixed _ (htime t) p.1 hx, sub_self, mul_zero]
    rw [hH, he, hz, add_zero]
  have hJ_eq : J = {p : E × ℝ | p.1 ∈ K ∧ ‖p.2 - g (0, p.1)‖ ≤ b.rOut * R} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨hq.1, ?_⟩
      change ‖q.2 + f q.1 - f q.1‖ ≤ b.rOut * R
      rw [add_sub_cancel_right]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hq.2
    · rintro ⟨hx, hy⟩
      refine ⟨(p.1, p.2 - f p.1), ⟨hx, ?_⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right, f] using hy
      · exact Prod.ext rfl (sub_add_cancel _ _)
  refine ⟨H, hF, hI, ?_, hHfst, hgraph, hfiber, ?_, ?_, ?_, hJ_eq ▸ hJ, ?_⟩
  · apply Diffeomorph.ext
    intro p
    rw [hH, he]
    change (p.1, p.2 + b (R⁻¹ * (p.2 - f p.1)) *
      d (Real.smoothTransition 0, p.1)) = p
    simp only [Real.smoothTransition.zero, d, f, sub_self, mul_zero, add_zero, Prod.eta]
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
      exact hfix t p (hJ_eq.symm ▸ hp)
    · intro p hp
      have h := congrArg (H t).symm (hfix t p (hJ_eq.symm ▸ hp))
      simpa only [Diffeomorph.symm_apply_apply, id_eq] using h.symm

theorem exists_isotopy_graphOn_family {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) {K : Set E} (hK : IsCompact K)
    (hfixed : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∉ K, g (s, x) = g (0, x)) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ (t : ℝ) (p : E × ℝ), (H t p).1 = p.1) ∧
      (∀ (t : ℝ) (x : E), H t (x, g (0, x)) = (x, g (Real.smoothTransition t, x))) ∧
      (∀ (t : ℝ) (p : E × ℝ), g (0, p.1) = g (Real.smoothTransition t, p.1) →
        H t p = p ∧ (H t).symm p = p) ∧
      (∀ (t : ℝ) (s : Set E), H t '' Set.graphOn (fun x => g (0, x)) s =
        Set.graphOn (fun x => g (Real.smoothTransition t, x)) s) ∧
      (∀ (t : ℝ) (s : Set E), H t '' {p : E × ℝ | p.1 ∈ s ∧ g (0, p.1) ≤ p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (Real.smoothTransition t, p.1) ≤ p.2}) ∧
      (∀ (t : ℝ) (s : Set E), H t '' {p : E × ℝ | p.1 ∈ s ∧ g (0, p.1) < p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (Real.smoothTransition t, p.1) < p.2}) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Jᶜ ∧ Set.EqOn (H t).symm id Jᶜ := by
  let f : E → ℝ := fun x => g (0, x)
  let d : ℝ × E → ℝ := fun p => g p - f p.2
  have hd : ContinuousOn d (Set.Icc (0 : ℝ) 1 ×ˢ K) :=
    (hg.continuous.sub
      ((hg.continuous.comp (continuous_const.prodMk continuous_id)).comp continuous_snd)).continuousOn
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    b.contDiff (show (∞ : ℕ∞ω) ≠ 0 by simp)
  obtain ⟨D₀, hD₀⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hd
  let D : ℝ≥0 := ⟨max D₀ 0, le_max_right _ _⟩
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ‖g (s, x) - g (0, x)‖ ≤ D := by
    intro s hs x hx
    exact (hD₀ _ ⟨hs, hx⟩).trans (le_max_left _ _)
  let R : ℝ := 2 * D * B + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hcoeff : (D : ℝ) * B * R⁻¹ ≤ 1 / 2 := by
    apply (mul_inv_le_iff₀ hR).2
    dsimp only [R]
    linarith
  obtain ⟨H, hforward, hinverse, hzero, hfst, hgraph, hfiber, himage, hepi, hstrict,
      hcompact, hfix⟩ :=
    exists_isotopy_graphOn_family_with_support hg hK hfixed b hB hbound hR hcoeff
  exact ⟨H, hforward, hinverse, hzero, hfst, hgraph, hfiber, himage, hepi, hstrict,
    {p | p.1 ∈ K ∧ ‖p.2 - g (0, p.1)‖ ≤ b.rOut * R}, hcompact, hfix⟩

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
  let F : ℝ × E → ℝ := fun p => f p.2 + p.1 * (g p.2 - f p.2)
  have hF : ContDiff ℝ ∞ F :=
    (hf.comp contDiff_snd).add
      (contDiff_fst.mul ((hg.comp contDiff_snd).sub (hf.comp contDiff_snd)))
  have hfixed : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∉ tsupport (fun x => g x - f x),
      F (s, x) = F (0, x) := by
    intro s hs x hx
    simp only [F, image_eq_zero_of_notMem_tsupport hx, mul_zero, add_zero]
  obtain ⟨H, hforward, hinverse, hzero, hfst, hgraph, hfiber, himage, hepi, hstrict, hcompact⟩ :=
    exists_isotopy_graphOn_family hF hs hfixed
  refine ⟨H, hforward, hinverse, hzero, hfst, ?_, ?_, ?_, ?_, ?_, hcompact⟩
  · simpa only [F, zero_mul, add_zero] using hgraph
  · intro t p hp
    apply hfiber t p
    simp only [F, hp, sub_self, mul_zero, add_zero]
  · simpa only [F, zero_mul, add_zero] using himage
  · simpa only [F, zero_mul, add_zero] using hepi
  · simpa only [F, zero_mul, add_zero] using hstrict

end Diffeomorph

namespace Diffeomorph

open scoped Topology

private theorem exists_uniform_graph_tube {E : Type*} [PseudoMetricSpace E]
    {g : ℝ × E → ℝ} (hg : Continuous g) {K : Set E} (hK : IsCompact K)
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, (x, g (t, x)) ∈ O) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ y : ℝ,
      ‖y - g (t, x)‖ ≤ δ → (x, y) ∈ O := by
  let S := (fun p : ℝ × E => (p.2, g p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hS : IsCompact S := (isCompact_Icc.prod hK).image (continuous_snd.prodMk hg)
  have hSO : S ⊆ O := by
    rintro z ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact htrace t ht x hx
  obtain ⟨δ, hδ, hsub⟩ := hS.exists_cthickening_subset_open hO hSO
  refine ⟨δ, hδ, ?_⟩
  intro t ht x hx y hy
  apply hsub
  apply Metric.mem_cthickening_of_dist_le (x, y) (x, g (t, x)) δ S
    ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  rw [Prod.dist_eq, dist_self, dist_eq_norm]
  exact (max_eq_right (norm_nonneg (y - g (t, x)))).trans_le hy

private theorem exists_uniform_graph_time_step {E : Type*} [PseudoMetricSpace E]
    {g : ℝ × E → ℝ} (hg : Continuous g) {K : Set E} (hK : IsCompact K)
    {D : ℝ} (hD : 0 < D) :
    ∃ η > 0, ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      dist a b ≤ η → ∀ x ∈ K, ‖g (b, x) - g (a, x)‖ ≤ D := by
  obtain ⟨η, hη, hstep⟩ := Metric.uniformContinuousOn_iff_le.mp
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hg.continuousOn) D hD
  refine ⟨η, hη, ?_⟩
  intro a ha b hb hab x hx
  apply hstep (b, x) ⟨hb, hx⟩ (a, x) ⟨ha, hx⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), dist_comm] using hab

private theorem exists_local_graph_isotopy_in_open {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) {K : Set E} (hK : IsCompact K)
    (hfixed : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∉ K, g (t, x) = g (0, x))
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, (x, g (t, x)) ∈ O) :
    ∃ η > 0, ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      dist a b ≤ η →
      ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
        H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
        (∀ (t : ℝ) (p : E × ℝ), (H t p).1 = p.1) ∧
        (∀ x : E, H 1 (x, g (a, x)) = (x, g (b, x))) ∧
        (∀ s : Set E, H 1 '' {p : E × ℝ | p.1 ∈ s ∧ g (a, p.1) ≤ p.2} =
          {p : E × ℝ | p.1 ∈ s ∧ g (b, p.1) ≤ p.2}) ∧
        (∀ s : Set E, H 1 '' {p : E × ℝ | p.1 ∈ s ∧ g (a, p.1) < p.2} =
          {p : E × ℝ | p.1 ∈ s ∧ g (b, p.1) < p.2}) ∧
        ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ O ∧ ∀ t : ℝ,
          Set.EqOn (H t) id Cᶜ ∧ Set.EqOn (H t).symm id Cᶜ := by
  obtain ⟨δ, hδ, htube⟩ := exists_uniform_graph_tube hg.continuous hK hO htrace
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport bump.hasCompactSupport
    bump.contDiff (show (∞ : ℕ∞ω) ≠ 0 by simp)
  let R : ℝ := δ / 2
  have hR : 0 < R := half_pos hδ
  let D : ℝ≥0 := ⟨R / (2 * ((B : ℝ) + 1)), by positivity⟩
  have hD : 0 < (D : ℝ) := div_pos hR (by positivity)
  have hDmul : (D : ℝ) * (2 * ((B : ℝ) + 1)) = R :=
    div_mul_cancel₀ R (by positivity)
  have hcoeff : (D : ℝ) * B * R⁻¹ ≤ 1 / 2 := by
    apply (mul_inv_le_iff₀ hR).mpr
    nlinarith [D.coe_nonneg, B.coe_nonneg]
  obtain ⟨η, hη, hstep⟩ := exists_uniform_graph_time_step hg.continuous hK hD
  refine ⟨η, hη, ?_⟩
  intro a ha b hb hab
  let f : ℝ × E → ℝ := fun p => g (a, p.2) + p.1 * (g (b, p.2) - g (a, p.2))
  have hfa : ContDiff ℝ ∞ (fun p : ℝ × E => g (a, p.2)) :=
    hg.comp (contDiff_const.prodMk contDiff_snd)
  have hfb : ContDiff ℝ ∞ (fun p : ℝ × E => g (b, p.2)) :=
    hg.comp (contDiff_const.prodMk contDiff_snd)
  have hf : ContDiff ℝ ∞ f := hfa.add (contDiff_fst.mul (hfb.sub hfa))
  have hfzero (x : E) : f (0, x) = g (a, x) := by simp only [f, zero_mul, add_zero]
  have hfone (x : E) : f (1, x) = g (b, x) := by
    dsimp only [f]
    ring
  have hffixed : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∉ K, f (s, x) = f (0, x) := by
    intro s hs x hx
    simp only [f, hfixed a ha x hx, hfixed b hb x hx, sub_self, mul_zero, add_zero]
  have hfbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ‖f (s, x) - f (0, x)‖ ≤ D := by
    intro s hs x hx
    rw [hfzero]
    change ‖g (a, x) + s * (g (b, x) - g (a, x)) - g (a, x)‖ ≤ D
    rw [add_sub_cancel_left, norm_mul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans
      (by simpa only [one_mul] using hstep a ha b hb hab x hx)
  obtain ⟨H, hH, hiH, hzero, hfst, hgraph, _, _, hepi, hstrict, hcompact, hfix⟩ :=
    exists_isotopy_graphOn_family_with_support hf hK hffixed bump hB hfbound hR hcoeff
  refine ⟨H, hH, hiH, hzero, hfst, ?_, ?_, ?_,
    {p | p.1 ∈ K ∧ ‖p.2 - f (0, p.1)‖ ≤ bump.rOut * R}, hcompact, ?_, hfix⟩
  · intro x
    simpa only [Real.smoothTransition.one, hfzero, hfone] using hgraph 1 x
  · intro s
    simpa only [Real.smoothTransition.one, hfzero, hfone] using hepi 1 s
  · intro s
    simpa only [Real.smoothTransition.one, hfzero, hfone] using hstrict 1 s
  · intro p hp
    apply htube a ha p.1 hp.1 p.2
    have h := hp.2
    rw [hfzero] at h
    change ‖p.2 - g (a, p.1)‖ ≤ 2 * (δ / 2) at h
    linarith

theorem exists_isotopy_graphOn_endpoints_in_open {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) {K : Set E} (hK : IsCompact K)
    (hfixed : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∉ K, g (t, x) = g (0, x))
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, (x, g (t, x)) ∈ O) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ (t : ℝ) (p : E × ℝ), (H t p).1 = p.1) ∧
      (∀ x : E, H 1 (x, g (0, x)) = (x, g (1, x))) ∧
      (∀ s : Set E, H 1 '' {p : E × ℝ | p.1 ∈ s ∧ g (0, p.1) ≤ p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (1, p.1) ≤ p.2}) ∧
      (∀ s : Set E, H 1 '' {p : E × ℝ | p.1 ∈ s ∧ g (0, p.1) < p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (1, p.1) < p.2}) ∧
      ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ O ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Cᶜ ∧ Set.EqOn (H t).symm id Cᶜ := by
  let P : ℝ → ℝ → Prop := fun a b =>
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ (t : ℝ) (p : E × ℝ), (H t p).1 = p.1) ∧
      (∀ x : E, H 1 (x, g (a, x)) = (x, g (b, x))) ∧
      (∀ s : Set E, H 1 '' {p : E × ℝ | p.1 ∈ s ∧ g (a, p.1) ≤ p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (b, p.1) ≤ p.2}) ∧
      (∀ s : Set E, H 1 '' {p : E × ℝ | p.1 ∈ s ∧ g (a, p.1) < p.2} =
        {p : E × ℝ | p.1 ∈ s ∧ g (b, p.1) < p.2}) ∧
      ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ O ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Cᶜ ∧ Set.EqOn (H t).symm id Cᶜ
  change P 0 1
  obtain ⟨η, hη, hlocal⟩ := exists_local_graph_isotopy_in_open hg hK hfixed hO htrace
  apply (isPreconnected_Icc : IsPreconnected (Set.Icc (0 : ℝ) 1)).induction₂
    P ?_ ?_ ?_ (by simp) (by simp)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds a hη)] with b hb hab
    exact hlocal a ha b hb (by
      have h : dist a b < η := by simpa only [Metric.mem_ball, dist_comm] using hab
      exact h.le)
  · intro a b c ha hb hc hab hbc
    obtain ⟨H, hH, hiH, hH0, hHfst, hHgraph, hHepi, hHstrict, C, hC, hCO, hHfix⟩ := hab
    obtain ⟨J, hJ, hiJ, hJ0, hJfst, hJgraph, hJepi, hJstrict, D, hD, hDO, hJfix⟩ := hbc
    let L : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)) := fun t => (H t).trans (J t)
    have hLf : ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => L z.1 z.2) :=
      hJ.comp (contDiff_fst.prodMk hH)
    have hLi : ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (L z.1).symm z.2) :=
      hiH.comp (contDiff_fst.prodMk hiJ)
    refine ⟨L, hLf, hLi, ?_, ?_, ?_, ?_, ?_, C ∪ D, hC.union hD,
      Set.union_subset hCO hDO, ?_⟩
    · apply Diffeomorph.ext
      intro p
      change J 0 (H 0 p) = p
      rw [hH0, hJ0]
      rfl
    · intro t p
      change (J t (H t p)).1 = p.1
      rw [hJfst, hHfst]
    · intro x
      change J 1 (H 1 (x, g (a, x))) = (x, g (c, x))
      rw [hHgraph, hJgraph]
    · intro s
      change (J 1 ∘ H 1) '' _ = _
      rw [Set.image_comp, hHepi, hJepi]
    · intro s
      change (J 1 ∘ H 1) '' _ = _
      rw [Set.image_comp, hHstrict, hJstrict]
    · intro t
      constructor
      · intro p hp
        have hpC : p ∉ C := fun h => hp (Or.inl h)
        have hpD : p ∉ D := fun h => hp (Or.inr h)
        change J t (H t p) = p
        rw [(hHfix t).1 hpC, id_eq]
        exact (hJfix t).1 hpD
      · intro p hp
        have hpC : p ∉ C := fun h => hp (Or.inl h)
        have hpD : p ∉ D := fun h => hp (Or.inr h)
        change (H t).symm ((J t).symm p) = p
        rw [(hJfix t).2 hpD, id_eq]
        exact (hHfix t).2 hpC
  · intro a b ha hb hab
    obtain ⟨H, hH, hiH, hH0, hfst, hgraph, hepi, hstrict, C, hC, hCO, hfix⟩ := hab
    refine ⟨fun t => (H t).symm, hiH, ?_, ?_, ?_, ?_, ?_, ?_, C, hC, hCO, ?_⟩
    · exact hH
    · change (H 0).symm = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞
      rw [hH0]
      rfl
    · intro t p
      have h := hfst t ((H t).symm p)
      rw [(H t).apply_symm_apply] at h
      exact h.symm
    · intro x
      change (H 1).symm (x, g (b, x)) = (x, g (a, x))
      exact (congrArg (H 1).symm (hgraph x)).symm.trans
        ((H 1).symm_apply_apply (x, g (a, x)))
    · intro s
      rw [← hepi s]
      exact (H 1).symm_image_image _
    · intro s
      rw [← hstrict s]
      exact (H 1).symm_image_image _
    · intro t
      exact (hfix t).symm

open Set Filter in
theorem exists_diffeomorph_graph_replacement_below
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S W : Set (E × ℝ)} (hS : IsClosed S) (hW : IsOpen W)
    {Y O : Set E} (hY : IsCompact Y) (hO : IsOpen O) (hYO : Y ⊆ O)
    {g k : E → ℝ} (hg : ContDiffOn ℝ ∞ g O) (hk : ContDiff ℝ ∞ k)
    (hgraph : ∀ x ∈ Y, (x, g x) ∈ W ∩ S)
    {a : ℝ} (hbelow : ∀ x ∈ Y, a ≤ k x ∧ k x ≤ g x)
    (hclear : ∀ x ∈ Y, ∀ t ∈ Ico a (g x), (x, t) ∉ S)
    {C : Set E} (hC : IsCompact C) (hCY : C ⊆ interior Y) (hmatch : EqOn k g (Y \ C)) :
    ∃ A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
      (∀ p, (A p).1 = p.1) ∧
      (∀ x ∈ Y, A (x, g x) = (x, k x)) ∧
      (∀ p ∈ S, p ∉ W ∩ {q | q.1 ∈ interior Y} →
        (A : (E × ℝ) → E × ℝ) =ᶠ[𝓝 p] id) := by
  classical
  obtain ⟨g₀, hg₀, _, hg₀eq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact hY hO hYO hg
  have hg₀Y : EqOn g₀ g Y := subset_of_mem_nhdsSet hg₀eq
  obtain ⟨χ, hχ, hχcompact, hχone, hχsupport, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hC isOpen_interior hCY
  have hχC : ∀ x ∈ C, χ x = 1 := fun x hx => subset_of_mem_nhdsSet hχone hx
  let g₁ := fun x => g₀ x + χ x * (k x - g₀ x)
  have hg₁ : ContDiff ℝ ∞ g₁ := hg₀.add (hχ.mul (hk.sub hg₀))
  have hg₁Y : EqOn g₁ k Y := by
    intro x hx
    by_cases hxC : x ∈ C
    · simp only [g₁, hχC x hxC, one_mul, add_sub_cancel]
    · rw [show g₁ x = g₀ x + χ x * (k x - g₀ x) from rfl, hg₀Y hx, hmatch ⟨hx, hxC⟩,
        sub_self, mul_zero, add_zero]
  let G : ℝ × E → ℝ := fun p => (1 - p.1) * g₀ p.2 + p.1 * g₁ p.2
  have hG : ContDiff ℝ ∞ G :=
    ((contDiff_const.sub contDiff_fst).mul (hg₀.comp contDiff_snd)).add
      (contDiff_fst.mul (hg₁.comp contDiff_snd))
  have hGzero (x : E) : G (0, x) = g₀ x := by simp [G]
  have hGone (x : E) : G (1, x) = g₁ x := by simp [G]
  have hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∉ tsupport χ, G (t, x) = G (0, x) := by
    intro t _ x hx
    have hc : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [G, g₁, hc, zero_mul, add_zero, zero_mul, one_mul, sub_zero]
    ring
  let P : Set (E × ℝ) := S \ (W ∩ {q | q.1 ∈ interior Y})
  have hP : IsClosed P := hS.sdiff (hW.inter (isOpen_interior.preimage continuous_fst))
  have htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ tsupport χ, (x, G (t, x)) ∈ Pᶜ := by
    intro t ht x hx
    have hxint := hχsupport hx
    have hxY := interior_subset hxint
    have he : G (t, x) = (1 - t) * g x + t * k x := by
      dsimp [G]; rw [hg₀Y hxY, hg₁Y hxY]
    have hb := hbelow x hxY
    have hlow : a ≤ G (t, x) := by
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hb.1.trans hb.2)),
        mul_nonneg ht.1 (sub_nonneg.mpr hb.1)]
    have hupp : G (t, x) ≤ g x := by
      rw [he]
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hb.2)]
    intro hp
    by_cases heq : G (t, x) = g x
    · exact hp.2 ⟨by simpa only [heq] using (hgraph x hxY).1, hxint⟩
    · exact hclear x hxY _ ⟨hlow, lt_of_le_of_ne hupp heq⟩ hp.1
  obtain ⟨H, _, _, _, hHfst, hHgraph, _, _, D, hD, hDP, hHfix⟩ :=
    exists_isotopy_graphOn_endpoints_in_open hG hχcompact hfixed hP.isOpen_compl htrace
  refine ⟨H 1, hHfst 1, ?_, ?_⟩
  · intro x hx
    have hh := hHgraph x
    simpa only [hGzero, hGone, hg₀Y hx, hg₁Y hx] using hh
  · intro p hp hpP
    have hpD : p ∉ D := fun hpD => hDP hpD ⟨hp, hpP⟩
    exact eventuallyEq_of_mem (hD.isClosed.isOpen_compl.mem_nhds hpD) (fun q hq => (hHfix 1).1 hq)

end Diffeomorph
