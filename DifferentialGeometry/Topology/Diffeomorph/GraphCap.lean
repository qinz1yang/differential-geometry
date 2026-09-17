import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real

open Set Metric
open scoped ContDiff Manifold

namespace Diffeomorph

private theorem exists_pos_halfspace_disjoint_of_isCompact
    {E : Type*} [TopologicalSpace E] {K : Set (E × ℝ)} (hK : IsCompact K)
    {b : ℝ} (hKb : ∀ p ∈ K, b < p.2) :
    ∃ ε > 0, ∀ p : E × ℝ, p.2 ≤ b + ε → p ∉ K := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨1, zero_lt_one, fun _ _ => by simp only [hK0, mem_empty_iff_false, not_false_eq_true]⟩
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne continuous_snd.continuousOn
    refine ⟨(p.2 - b) / 2, by linarith [hKb p hp], ?_⟩
    intro q hq hqK
    have hle : p.2 ≤ q.2 := hmin hqK
    linarith [hKb p hp]

theorem exists_diffeomorph_graph_cap_eqOn_halfspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : E ≃ₘ[ℝ] E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {r δ b : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hC : C '' closedBall 0 r = closedBall 0 r)
    (habove : ∀ x ∈ ball (0 : E) r, b < f x)
    (hnear : ∀ x ∈ closedBall (0 : E) r, r - δ ≤ ‖x‖ → f (C.symm x) = f x) :
    ∃ ε > 0, ∃ G : (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
      (∀ p : E × ℝ, (G p).1 = C p.1) ∧
      (∀ p : E × ℝ, p.2 ≤ b + ε → G p = (C p.1, p.2)) ∧
      (∀ p : E × ℝ, b ≤ (G p).2 ↔ b ≤ p.2) ∧
      (∀ p : E × ℝ, b < (G p).2 ↔ b < p.2) ∧
      (∀ x ∈ closedBall (0 : E) r, G (x, f x) = (C x, f (C x))) ∧
      G '' {p : E × ℝ | p.1 ∈ closedBall 0 r ∧ b ≤ p.2 ∧ p.2 ≤ f p.1} =
        {p : E × ℝ | p.1 ∈ closedBall 0 r ∧ b ≤ p.2 ∧ p.2 ≤ f p.1} := by
  let a := max (r / 2) (r - δ / 2)
  let d := (a + r) / 2
  have ha : 0 < a := (half_pos hr).trans_le (le_max_left _ _)
  have har : a < r := max_lt (by linarith) (by linarith)
  have had : a < d := by dsimp [d]; linarith
  have hdr : d < r := by dsimp [d]; linarith
  have hda : r - δ ≤ a := by dsimp [a]; linarith [le_max_right (r / 2) (r - δ / 2)]
  let χ : ContDiffBump (0 : E) := ⟨a, d, ha, had⟩
  let u : E → ℝ := fun y => f (C.symm y)
  let v : E → ℝ := fun y => u y + χ y * (f y - u y)
  have hu : ContDiff ℝ ∞ u := hf.comp C.symm.contDiff
  have hv : ContDiff ℝ ∞ v := hu.add (χ.contDiff.mul (hf.sub hu))
  have hCi : C.symm '' closedBall 0 r = closedBall 0 r := by
    calc
      C.symm '' closedBall 0 r = C.symm '' (C '' closedBall 0 r) :=
        congrArg (fun s => C.symm '' s) hC.symm
      _ = closedBall 0 r := C.symm_image_image _
  have hCball : C.symm '' ball 0 r = ball 0 r := by
    have h := C.symm.toHomeomorph.image_interior (closedBall 0 r)
    change C.symm '' interior (closedBall 0 r) = interior (C.symm '' closedBall 0 r) at h
    simpa only [interior_closedBall (0 : E) hr.ne', hCi] using h
  have hCmem (x : E) (hx : x ∈ closedBall 0 r) : C x ∈ closedBall 0 r := by
    rw [← hC]
    exact mem_image_of_mem C hx
  have hCimem (x : E) (hx : x ∈ closedBall 0 r) : C.symm x ∈ closedBall 0 r := by
    rw [← hCi]
    exact mem_image_of_mem C.symm hx
  have hvf (y : E) (hy : y ∈ closedBall 0 r) : v y = f y := by
    by_cases hya : ‖y‖ ≤ a
    · rw [show v y = u y + χ y * (f y - u y) from rfl,
        χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hya)]
      ring
    · have heq := hnear y hy (hda.trans (le_of_not_ge hya))
      simp only [v, u, heq, sub_self, mul_zero, add_zero]
  have hχzero (y : E) (hy : y ∉ closedBall 0 d) : χ y = 0 := by
    apply χ.zero_of_le_dist
    change d ≤ dist y 0
    rw [dist_zero_right]
    exact le_of_not_ge (fun h => hy (mem_closedBall_zero_iff.mpr h))
  let g : ℝ × E → ℝ := fun z => u z.2 + z.1 * (v z.2 - u z.2)
  have hg : ContDiff ℝ ∞ g := (hu.comp contDiff_snd).add
    (contDiff_fst.mul ((hv.sub hu).comp contDiff_snd))
  have hg0 (y : E) : g (0, y) = u y := by simp only [g, zero_mul, add_zero]
  have hg1 (y : E) : g (1, y) = v y := by dsimp [g]; ring
  have hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∉ closedBall 0 d, g (t, y) = g (0, y) := by
    intro t _ y hy
    simp only [g, v, hχzero y hy, zero_mul, add_zero, sub_self, mul_zero]
  have htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall (0 : E) d,
      (y, g (t, y)) ∈ {p : E × ℝ | b < p.2} := by
    intro t ht y hy
    have hyr : y ∈ ball (0 : E) r := mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hy).trans_lt hdr)
    have hiyr : C.symm y ∈ ball (0 : E) r := by
      rw [← hCball]
      exact mem_image_of_mem C.symm hyr
    have hbu : b < u y := habove _ hiyr
    have hbv : b < v y := by rw [hvf y (ball_subset_closedBall hyr)]; exact habove y hyr
    change b < u y + t * (v y - u y)
    by_cases ht0 : t = 0
    · simpa only [ht0, zero_mul, add_zero] using hbu
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      nlinarith [mul_pos htpos (sub_pos.mpr hbv),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hbu.le)]
  obtain ⟨H, _, _, _, hHfst, hHgraph, _, hHstrict, K, hK, hKb, hHfix⟩ :=
    exists_isotopy_graphOn_endpoints_in_open hg (isCompact_closedBall (0 : E) d)
      hfixed (isOpen_lt continuous_const continuous_snd) htrace
  obtain ⟨ε, hε, hεK⟩ := exists_pos_halfspace_disjoint_of_isCompact hK hKb
  let P : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := C.toEquiv.prodCongr (Equiv.refl ℝ)
      contMDiff_toFun := ((C.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
      contMDiff_invFun := ((C.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
  let G := P.trans (H 1)
  have hGfst (p : E × ℝ) : (G p).1 = C p.1 := hHfst 1 (P p)
  have hGfix (p : E × ℝ) (hp : p.2 ≤ b + ε) : G p = (C p.1, p.2) :=
    (hHfix 1).1 (hεK (P p) hp)
  have hGgraph (x : E) (hx : x ∈ closedBall 0 r) :
      G (x, f x) = (C x, f (C x)) := by
    have h := hHgraph (C x)
    rw [hg0, hg1, hvf _ (hCmem x hx)] at h
    change H 1 (C x, f x) = (C x, f (C x))
    simpa only [u, C.symm_apply_apply] using h
  have hHupper (p : E × ℝ) : p.2 ≤ u p.1 ↔ (H 1 p).2 ≤ v p.1 := by
    have hmem : H 1 p ∈ (H 1) '' {q : E × ℝ | q.1 ∈ univ ∧ u q.1 < q.2} ↔
        p ∈ {q : E × ℝ | q.1 ∈ univ ∧ u q.1 < q.2} :=
      (H 1).injective.mem_set_image
    rw [show {q : E × ℝ | q.1 ∈ univ ∧ u q.1 < q.2} =
      {q : E × ℝ | q.1 ∈ univ ∧ g (0, q.1) < q.2} by simp only [hg0],
      hHstrict univ] at hmem
    simp only [mem_ofPred_eq, mem_univ, true_and, hg0, hg1, hHfst] at hmem
    exact not_lt.symm.trans (hmem.not.symm.trans not_lt)
  have hGupper (p : E × ℝ) (hp : p.1 ∈ closedBall 0 r) :
      p.2 ≤ f p.1 ↔ (G p).2 ≤ f (C p.1) := by
    have h := hHupper (P p)
    change p.2 ≤ u (C p.1) ↔ (G p).2 ≤ v (C p.1) at h
    simpa only [u, C.symm_apply_apply, hvf _ (hCmem _ hp)] using h
  have hGlower (p : E × ℝ) : b ≤ p.2 ↔ b ≤ (G p).2 := by
    constructor
    · intro hp
      by_contra hn
      have hlt : (G p).2 < b := lt_of_not_ge hn
      have hfix : H 1 (G p) = G p := (hHfix 1).1 (hεK (G p) (by linarith))
      have heq : P p = G p := (H 1).injective hfix.symm
      have ht := congrArg Prod.snd heq
      change p.2 = (G p).2 at ht
      linarith
    · intro hp
      by_contra hn
      have hlt : p.2 < b := lt_of_not_ge hn
      rw [hGfix p (by linarith)] at hp
      exact (not_le_of_gt hlt) hp
  have hGlt (p : E × ℝ) : b < (G p).2 ↔ b < p.2 := by
    constructor
    · intro hp
      by_contra hn
      have hle : p.2 ≤ b := le_of_not_gt hn
      rw [hGfix p (by linarith)] at hp
      exact (not_lt_of_ge hle) hp
    · intro hp
      by_contra hn
      have hle : (G p).2 ≤ b := le_of_not_gt hn
      have hfix : H 1 (G p) = G p := (hHfix 1).1 (hεK (G p) (by linarith))
      have heq : P p = G p := (H 1).injective hfix.symm
      have ht := congrArg Prod.snd heq
      change p.2 = (G p).2 at ht
      linarith
  refine ⟨ε, hε, G, hGfst, hGfix, fun p => (hGlower p).symm, hGlt, hGgraph, ?_⟩
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, (hGlower q).mp hq.2.1, ?_⟩
    · rw [hGfst]
      exact hCmem q.1 hq.1
    · rw [hGfst]
      exact (hGupper q hq.1).mp hq.2.2
  · intro hp
    have hpre : (G.symm p).1 = C.symm p.1 := by
      apply C.injective
      change C (G.symm p).1 = C (C.symm p.1)
      rw [C.apply_symm_apply, ← hGfst, G.apply_symm_apply]
    have hmem : (G.symm p).1 ∈ closedBall 0 r := by
      rw [hpre]
      exact hCimem p.1 hp.1
    refine ⟨G.symm p, ⟨hmem, ?_, ?_⟩, G.apply_symm_apply p⟩
    · apply (hGlower (G.symm p)).mpr
      simpa only [G.apply_symm_apply] using hp.2.1
    · apply (hGupper (G.symm p) hmem).mpr
      simpa only [G.apply_symm_apply, hpre, C.apply_symm_apply] using hp.2.2

theorem exists_diffeomorph_quadratic_cap_eqOn_halfspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : E ≃ₘ[ℝ] E) {r δ c : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hC : C '' closedBall 0 r = closedBall 0 r)
    (hnear : ∀ x ∈ closedBall (0 : E) r, r - δ ≤ ‖x‖ → ‖C.symm x‖ = ‖x‖) :
    ∃ ε > 0, ∃ G : (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
      (∀ p : E × ℝ, (G p).1 = C p.1) ∧
      (∀ p : E × ℝ, p.2 ≤ c - r ^ 2 / 2 + ε → G p = (C p.1, p.2)) ∧
      (∀ p : E × ℝ, c - r ^ 2 / 2 ≤ (G p).2 ↔ c - r ^ 2 / 2 ≤ p.2) ∧
      (∀ p : E × ℝ, c - r ^ 2 / 2 < (G p).2 ↔ c - r ^ 2 / 2 < p.2) ∧
      (∀ x ∈ closedBall (0 : E) r,
        G (x, c - ‖x‖ ^ 2 / 2) = (C x, c - ‖C x‖ ^ 2 / 2)) ∧
      G '' {p : E × ℝ | p.1 ∈ closedBall 0 r ∧
        c - r ^ 2 / 2 ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
        {p : E × ℝ | p.1 ∈ closedBall 0 r ∧
          c - r ^ 2 / 2 ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} := by
  apply exists_diffeomorph_graph_cap_eqOn_halfspace C
    (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2)) hr hδ hC
  · intro x hx
    have hx' := mem_ball_zero_iff.mp hx
    have hsq : ‖x‖ ^ 2 < r ^ 2 := sq_lt_sq₀ (norm_nonneg x) hr.le |>.mpr hx'
    linarith
  · intro x hx hxr
    rw [hnear x hx hxr]

end Diffeomorph
