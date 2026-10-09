/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningJunction
import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSquareWitness
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossQuarter (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  {p | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ p = (a • fourSpokeModelLeaf i, b)}

def crossQuarterTriangle (r : ℝ) (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  {p | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ r ∧ p = (a • fourSpokeModelLeaf i, b)}

theorem fourSpokeModelLeaf_dot_self (i : Fin 4) :
    (fourSpokeModelLeaf i).1 * (fourSpokeModelLeaf i).1 +
      (fourSpokeModelLeaf i).2 * (fourSpokeModelLeaf i).2 = 1 := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;> norm_num [fourSpokeModelLeaf]

theorem norm_fourSpokeModelLeaf (i : Fin 4) : ‖fourSpokeModelLeaf i‖ = 1 := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    simp [fourSpokeModelLeaf, Prod.norm_def]

theorem crossQuarterTriangle_subset_crossQuarter (r : ℝ) (i : Fin 4) :
    crossQuarterTriangle r i ⊆ crossQuarter i := by
  rintro p ⟨a, b, ha, hb, -, rfl⟩
  exact ⟨a, b, ha, hb, rfl⟩

theorem smul_mem_crossQuarter {i : Fin 4} {p : (ℝ × ℝ) × ℝ} (hp : p ∈ crossQuarter i) {s : ℝ}
    (hs : 0 ≤ s) : s • p ∈ crossQuarter i := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hp
  exact ⟨s * a, s * b, mul_nonneg hs ha, mul_nonneg hs hb, by
    rw [Prod.smul_mk, smul_smul, smul_eq_mul]⟩

theorem crossQuarter_inter_ball_subset (i : Fin 4) {r : ℝ} :
    crossQuarter i ∩ ball 0 (r / 2) ⊆ crossQuarterTriangle r i := by
  rintro p ⟨⟨a, b, ha, hb, rfl⟩, hp⟩
  rw [mem_ball, dist_zero_right] at hp
  have h1 : ‖a • fourSpokeModelLeaf i‖ < r / 2 := (norm_fst_le _).trans_lt hp
  have h2 : ‖b‖ < r / 2 := (norm_snd_le _).trans_lt hp
  rw [norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg ha] at h1
  rw [Real.norm_of_nonneg hb] at h2
  exact ⟨a, b, ha, hb, by linarith, rfl⟩

theorem crossQuarterTriangle_subset_closedBall (i : Fin 4) {r : ℝ} :
    crossQuarterTriangle r i ⊆ closedBall 0 r := by
  rintro p ⟨a, b, ha, hb, hab, rfl⟩
  rw [mem_closedBall, dist_zero_right, norm_prod_le_iff]
  refine ⟨?_, ?_⟩
  · change ‖a • fourSpokeModelLeaf i‖ ≤ r
    rw [norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg ha]
    linarith
  · change ‖b‖ ≤ r
    rw [Real.norm_of_nonneg hb]
    linarith

theorem isPLHomeomorphOn_crossQuarterTriangle (i : Fin 4) {r : ℝ} (hr : 0 < r) :
    IsPLHomeomorphOn (fun w : Fin 3 → ℝ => ((r * w 1) • fourSpokeModelLeaf i, r * w 2))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (crossQuarterTriangle r i) := by
  let L : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ) × ℝ :=
    (LinearMap.smulRight (r • LinearMap.proj 1) (fourSpokeModelLeaf i)).prod
      (r • LinearMap.proj 2)
  have hne : fourSpokeModelLeaf i ≠ 0 := fourSpokeModelLeaf_ne_zero i
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isHPolytope_stdSimplex (Fin 3)).isPolyhedron
    ((isPiecewiseAffineOn_of_affine_of_isHPolytope L.toAffineMap
      (isHPolytope_stdSimplex (Fin 3))).congr fun w _ => ?_) ⟨?_, ?_, ?_⟩
  · simp [L, smul_eq_mul]
  · intro w hw
    have hsum := hw.2
    rw [Fin.sum_univ_three] at hsum
    have h0 := hw.1 0
    have h1 := hw.1 1
    have h2 := hw.1 2
    exact ⟨r * w 1, r * w 2, by positivity, by positivity, by nlinarith, rfl⟩
  · intro w hw v hv hwv
    have hwv' := hwv
    simp only [Prod.mk.injEq] at hwv'
    obtain ⟨h1, h2⟩ := hwv'
    have e1 : w 1 = v 1 := by
      have := smul_left_injective ℝ hne h1
      exact mul_left_cancel₀ hr.ne' this
    have e2 : w 2 = v 2 := mul_left_cancel₀ hr.ne' h2
    have hsw := hw.2
    have hsv := hv.2
    rw [Fin.sum_univ_three] at hsw hsv
    have e0 : w 0 = v 0 := by linarith
    funext j
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
  · rintro p ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨![1 - a / r - b / r, a / r, b / r], ⟨fun j => ?_, ?_⟩, ?_⟩
    · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
      · change 0 ≤ 1 - a / r - b / r
        rw [sub_sub, ← add_div, sub_nonneg, div_le_one hr]
        exact hab
      · change 0 ≤ a / r
        positivity
      · change 0 ≤ b / r
        positivity
    · rw [Fin.sum_univ_three]
      change 1 - a / r - b / r + a / r + b / r = 1
      ring
    · change ((r * (a / r)) • fourSpokeModelLeaf i, r * (b / r)) = (a • fourSpokeModelLeaf i, b)
      rw [mul_div_cancel₀ a hr.ne', mul_div_cancel₀ b hr.ne']

theorem exists_isPLHomeomorphOn_Icc_geometricLink_crossQuarterTriangle
    {G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ} (hG : IsPLHomeomorphOn G univ univ)
    (hhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → G (s • v) = s • G v) {i : Fin 4} {r : ℝ}
    (hr : 0 < r) (M : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) [Finite M.faces]
    (hM : M.space = G '' crossQuarterTriangle r i)
    (h0 : ({0} : Finset ((ℝ × ℝ) × ℝ)) ∈ M.faces) :
    ∃ β : ℝ → (ℝ × ℝ) × ℝ,
      IsPLHomeomorphOn β (Icc 0 1) (SimplicialComplex.geometricLink M {0}).space ∧
        β 0 ∈ G '' {p | p.1 = 0 ∧ 0 < p.2} ∧
          β 1 ∈ G '' {p | ∃ a : ℝ, 0 < a ∧ p = (a • fourSpokeModelLeaf i, 0)} := by
  classical
  set l := fourSpokeModelLeaf i with hldef
  have hl : l.1 * l.1 + l.2 * l.2 = 1 := fourSpokeModelLeaf_dot_self i
  have hG0 : G 0 = 0 := by simpa using hhom 0 0 le_rfl
  set Ginv := Function.invFunOn G univ with hGinvdef
  have hGinvG : ∀ q, Ginv (G q) = q := fun q => hG.bijOn.invOn_invFunOn.1 (mem_univ q)
  have hGGinv : ∀ v, G (Ginv v) = v := fun v => hG.bijOn.invOn_invFunOn.2 (mem_univ v)
  have hGinvc : Continuous Ginv :=
    continuousOn_univ.mp hG.isPiecewiseAffineOn_invFunOn.continuousOn
  set L := (SimplicialComplex.geometricLink M {0}).space with hLdef
  have hLsub : L ⊆ M.space :=
    space_mono_of_faces_subset (SimplicialComplex.geometricLink_le M {0})
  have hL0 : (0 : (ℝ × ℝ) × ℝ) ∉ L := notMem_geometricLink_space M
  have hLpt : ∀ v ∈ L, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ Ginv v = (a • l, b) := by
    intro v hv
    have hvM := hLsub hv
    rw [hM] at hvM
    obtain ⟨q, ⟨a, b, ha, hb, -, rfl⟩, rfl⟩ := hvM
    refine ⟨a, b, ha, hb, ?_, hGinvG _⟩
    by_contra hab
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    apply hL0
    have hz : G (a • l, b) = 0 := by rw [ha0, hb0, zero_smul, Prod.mk_zero_zero, hG0]
    exact hz ▸ hv
  let θ : (ℝ × ℝ) × ℝ → ℝ := fun v =>
    (Ginv v).2 / (l.1 * (Ginv v).1.1 + l.2 * (Ginv v).1.2 + (Ginv v).2)
  have hθG : ∀ a b : ℝ, θ (G (a • l, b)) = b / (a + b) := by
    intro a b
    simp only [θ, hGinvG, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    congr 1
    linear_combination a * hl
  have hθv : ∀ v ∈ L, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ Ginv v = (a • l, b) ∧
      θ v = b / (a + b) := by
    intro v hv
    obtain ⟨a, b, ha, hb, hab, hq⟩ := hLpt v hv
    refine ⟨a, b, ha, hb, hab, hq, ?_⟩
    rw [← hθG, ← hq, hGGinv]
  have hden : ∀ v ∈ L, l.1 * (Ginv v).1.1 + l.2 * (Ginv v).1.2 + (Ginv v).2 ≠ 0 := by
    intro v hv
    obtain ⟨a, b, ha, hb, hab, hq⟩ := hLpt v hv
    rw [hq]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    nlinarith [hl]
  have hθc : ContinuousOn θ L := by
    refine ContinuousOn.div (continuous_snd.comp hGinvc).continuousOn ?_ hden
    exact (((continuous_const.mul (continuous_fst.comp (continuous_fst.comp hGinvc))).add
      (continuous_const.mul (continuous_snd.comp (continuous_fst.comp hGinvc)))).add
      (continuous_snd.comp hGinvc)).continuousOn
  have hrad : IsRadiallyInjective (0 : (ℝ × ℝ) × ℝ) L := isRadiallyInjective_geometricLink M
  have hθinj : InjOn θ L := by
    intro v hv v' hv' hvv
    obtain ⟨a, b, ha, hb, hab, hq, e⟩ := hθv v hv
    obtain ⟨a', b', ha', hb', hab', hq', e'⟩ := hθv v' hv'
    rw [e, e', div_eq_div_iff hab.ne' hab'.ne'] at hvv
    have hs : 0 < (a' + b') / (a + b) := div_pos hab' hab
    have h1 : a' = (a' + b') / (a + b) * a := by
      rw [div_mul_eq_mul_div, eq_div_iff hab.ne']
      linear_combination hvv
    have h2 : b' = (a' + b') / (a + b) * b := by
      rw [div_mul_eq_mul_div, eq_div_iff hab.ne']
      linear_combination -hvv
    have hq's : Ginv v' = ((a' + b') / (a + b)) • Ginv v := by
      rw [hq, hq']
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_smul]
        rw [← h1]
      · simp only [Prod.smul_snd, smul_eq_mul]
        exact h2
    have hv's : v' = 0 + ((a' + b') / (a + b)) • (v - 0) := by
      rw [zero_add, sub_zero, ← hGGinv v', hq's, hhom _ _ hs.le, hGGinv]
    exact (hrad v hv v' hv' _ hs hv's).symm
  have hθmem : ∀ v ∈ L, θ v ∈ Icc (0 : ℝ) 1 := by
    intro v hv
    obtain ⟨a, b, ha, hb, hab, -, e⟩ := hθv v hv
    rw [e]
    exact ⟨div_nonneg hb hab.le, (div_le_one hab).mpr (by linarith)⟩
  have hsurj : ∀ θ₀ ∈ Icc (0 : ℝ) 1, ∃ v ∈ L, θ v = θ₀ := by
    intro θ₀ hθ₀
    have hqΔ : ∀ t : ℝ, 0 < t → t ≤ 1 →
        t • (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ) ∈ crossQuarterTriangle r i := by
      intro t ht ht1
      refine ⟨t * (r * (1 - θ₀)), t * (r * θ₀), ?_, ?_, ?_, ?_⟩
      · exact mul_nonneg ht.le (mul_nonneg hr.le (by linarith [hθ₀.2]))
      · exact mul_nonneg ht.le (mul_nonneg hr.le hθ₀.1)
      · nlinarith
      · refine Prod.ext ?_ ?_
        · simp only [Prod.smul_fst, smul_smul, hldef]
        · simp only [Prod.smul_snd, smul_eq_mul]
    have hq0 : G (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ) ≠ 0 := by
      intro h
      have hq : (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ) = 0 := by
        calc (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ)
            = Ginv (G (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ)) := (hGinvG _).symm
          _ = Ginv (G 0) := by rw [h, hG0]
          _ = 0 := hGinvG 0
      have h2 : r * θ₀ = 0 := congrArg Prod.snd hq
      have h1 : (r * (1 - θ₀)) • l = 0 := congrArg Prod.fst hq
      rcases smul_eq_zero.mp h1 with h | h
      · have : r * 1 = 0 := by linear_combination h + h2
        linarith
      · exact fourSpokeModelLeaf_ne_zero i h
    obtain ⟨s, hs, hmem⟩ := exists_ray_mem_geometricLink_space M h0
      (x := G (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ)) (fun t ht ht1 => by
        rw [zero_add, sub_zero, ← hhom _ t ht.le, hM]
        exact ⟨_, hqΔ t ht ht1, rfl⟩) hq0
    rw [zero_add, sub_zero, ← hhom _ s hs.le] at hmem
    have hsq : s • (((r * (1 - θ₀)) • l, r * θ₀) : (ℝ × ℝ) × ℝ) =
        ((s * (r * (1 - θ₀))) • l, s * (r * θ₀)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_smul]
      · simp only [Prod.smul_snd, smul_eq_mul]
    rw [hsq] at hmem
    refine ⟨_, hmem, ?_⟩
    rw [hθG]
    have hr' : s * r ≠ 0 := (mul_pos hs hr).ne'
    field_simp
    ring
  have hθimg : θ '' L = Icc 0 1 := by
    refine Subset.antisymm ?_ fun θ₀ hθ₀ => ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hθmem v hv
    · obtain ⟨v, hv, hvθ⟩ := hsurj θ₀ hθ₀
      exact ⟨v, hv, hvθ⟩
  have hball : IsPLBall (1 + 1) M.space := by
    rw [hM]
    have hΔ := isPLHomeomorphOn_crossQuarterTriangle i hr
    exact ⟨_, hΔ.trans (hG.restrict
      (show IsPLBall 2 (crossQuarterTriangle r i) from ⟨_, hΔ⟩).isPolyhedron (subset_univ _))⟩
  rcases isPLSphere_or_isPLBall_geometricLink_of_isPLBall (n := 1) M hball h0 with hS | hB
  · exfalso
    obtain ⟨v, hv, hvθ⟩ := hsurj (1 / 2) ⟨by norm_num, by norm_num⟩
    have hconn := (hS.isConnected_sdiff_singleton_one v).image θ (hθc.mono sdiff_subset)
    rw [hθinj.image_sdiff_subset (singleton_subset_iff.mpr hv), image_singleton, hθimg,
      hvθ] at hconn
    have hsub := hconn.isPreconnected.Icc_subset
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 \ {1 / 2} from ⟨⟨le_rfl, zero_le_one⟩, by norm_num⟩)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 \ {1 / 2} from ⟨⟨zero_le_one, le_rfl⟩, by norm_num⟩)
    exact (hsub (show (1 / 2 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, by norm_num⟩)).2 rfl
  · obtain ⟨β₀, hβ₀⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hB
    have hmaps : MapsTo β₀ (Icc 0 1) L := hβ₀.bijOn.mapsTo
    have hfc : ContinuousOn (θ ∘ β₀) (Icc 0 1) :=
      hθc.comp hβ₀.isPiecewiseAffineOn.continuousOn hmaps
    have hfi : InjOn (θ ∘ β₀) (Icc 0 1) := hθinj.comp hβ₀.bijOn.injOn hmaps
    have hfimg : (θ ∘ β₀) '' Icc 0 1 = Icc 0 1 := by rw [image_comp, hβ₀.image_eq, hθimg]
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hin : ∀ x ∈ Icc (0 : ℝ) 1, (θ ∘ β₀) x ∈ Icc (0 : ℝ) 1 := by
      intro x hx
      rw [← hfimg]
      exact mem_image_of_mem _ hx
    obtain ⟨x₀, hx₀, hfx₀⟩ : (0 : ℝ) ∈ (θ ∘ β₀) '' Icc 0 1 := by
      rw [hfimg]
      exact h0I
    obtain ⟨x₁, hx₁, hfx₁⟩ : (1 : ℝ) ∈ (θ ∘ β₀) '' Icc 0 1 := by
      rw [hfimg]
      exact h1I
    have hends : ((θ ∘ β₀) 0 = 1 ∧ (θ ∘ β₀) 1 = 0) ∨ ((θ ∘ β₀) 0 = 0 ∧ (θ ∘ β₀) 1 = 1) := by
      rcases hfc.strictMonoOn_of_injOn_Icc' zero_le_one hfi with hm | ha
      · right
        exact ⟨le_antisymm ((hm.monotoneOn h0I hx₀ hx₀.1).trans_eq hfx₀) (hin 0 h0I).1,
          le_antisymm (hin 1 h1I).2 (hfx₁.symm.trans_le (hm.monotoneOn hx₁ h1I hx₁.2))⟩
      · left
        exact ⟨le_antisymm (hin 0 h0I).2 (hfx₁.symm.trans_le (ha.antitoneOn h0I hx₁ hx₁.1)),
          le_antisymm ((ha.antitoneOn hx₀ h1I hx₀.2).trans_eq hfx₀) (hin 1 h1I).1⟩
    have hend1 : ∀ v ∈ L, θ v = 1 → v ∈ G '' {p | p.1 = 0 ∧ 0 < p.2} := by
      intro v hv hθ1
      obtain ⟨a, b, ha, hb, hab, hq, e⟩ := hθv v hv
      rw [e, div_eq_one_iff_eq hab.ne'] at hθ1
      have ha0 : a = 0 := by linarith
      refine ⟨Ginv v, ?_, hGGinv v⟩
      rw [hq, ha0, zero_smul]
      exact ⟨rfl, by linarith⟩
    have hend0 : ∀ v ∈ L, θ v = 0 →
        v ∈ G '' {p | ∃ a : ℝ, 0 < a ∧ p = (a • fourSpokeModelLeaf i, 0)} := by
      intro v hv hθ0
      obtain ⟨a, b, ha, hb, hab, hq, e⟩ := hθv v hv
      rw [e, div_eq_zero_iff] at hθ0
      have hb0 : b = 0 := hθ0.resolve_right hab.ne'
      refine ⟨Ginv v, ⟨a, by linarith, by rw [hq, hb0]⟩, hGGinv v⟩
    rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · exact ⟨β₀, hβ₀, hend1 _ (hmaps h0I) e0, hend0 _ (hmaps h1I) e1⟩
    · refine ⟨fun x => β₀ (1 - x), isPLHomeomorphOn_comp_one_sub hβ₀, ?_, ?_⟩
      · simp only [sub_zero]
        exact hend1 _ (hmaps h1I) e1
      · simp only [sub_self]
        exact hend0 _ (hmaps h0I) e0

theorem exists_quarterLink_complex {G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hG : IsPLHomeomorphOn G univ univ)
    (hhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → G (s • v) = s • G v) :
    ∃ (K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ))
      (M : Fin 4 → Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (ρ : ℝ),
      K.faces.Finite ∧ ({0} : Finset ((ℝ × ℝ) × ℝ)) ∈ K.faces ∧ K.space ∈ 𝓝 0 ∧
        (∀ s ∈ K.faces, convexHull ℝ (s : Set ((ℝ × ℝ) × ℝ)) ⊆ {x | x.2 ≤ 0} ∨
          convexHull ℝ (s : Set ((ℝ × ℝ) × ℝ)) ⊆ {x | 0 ≤ x.2}) ∧
        (∀ i, (M i).faces ⊆ K.faces) ∧ (∀ i, ({0} : Finset ((ℝ × ℝ) × ℝ)) ∈ (M i).faces) ∧
        (∀ i, (M i).space ⊆ G '' crossQuarter i) ∧ 0 < ρ ∧
        (∀ i, ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ, z ∈ G '' crossQuarter i → z ∈ (M i).space) ∧
        ∀ i, ∃ β : ℝ → (ℝ × ℝ) × ℝ,
          IsPLHomeomorphOn β (Icc 0 1) (SimplicialComplex.geometricLink (M i) {0}).space ∧
            β 0 ∈ G '' {p | p.1 = 0 ∧ 0 < p.2} ∧
              β 1 ∈ G '' {p | ∃ a : ℝ, 0 < a ∧ p = (a • fourSpokeModelLeaf i, 0)} := by
  classical
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 2 + 1 := by simp
  obtain ⟨T, hT, hcard, h0T, -, hTn⟩ :=
    exists_affineIndependent_openSimplex_subset hdim (0 : (ℝ × ℝ) × ℝ) Filter.univ_mem
  let K₀ := simplexComplex T hT
  have : Finite K₀.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hK₀space : K₀.space = convexHull ℝ (T : Set ((ℝ × ℝ) × ℝ)) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hG0 : G 0 = 0 := by simpa using hhom 0 0 le_rfl
  have hGc : Continuous G := continuousOn_univ.mp hG.isPiecewiseAffineOn.continuousOn
  obtain ⟨r, hr, hrball⟩ : ∃ r > 0,
      closedBall (0 : (ℝ × ℝ) × ℝ) r ⊆ G ⁻¹' convexHull ℝ (T : Set ((ℝ × ℝ) × ℝ)) := by
    have h : G ⁻¹' convexHull ℝ (T : Set ((ℝ × ℝ) × ℝ)) ∈ 𝓝 (0 : (ℝ × ℝ) × ℝ) :=
      hGc.continuousAt.preimage_mem_nhds (by rw [hG0]; exact hTn)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  have hΔ := fun i => isPLHomeomorphOn_crossQuarterTriangle i hr
  have hΔpoly : ∀ i, IsPolyhedron (crossQuarterTriangle r i) :=
    fun i => (show IsPLBall 2 (crossQuarterTriangle r i) from ⟨_, hΔ i⟩).isPolyhedron
  have hGΔpoly : ∀ i, IsPolyhedron (G '' crossQuarterTriangle r i) := fun i =>
    (show IsPLBall 2 (G '' crossQuarterTriangle r i) from
      ⟨_, (hΔ i).trans (hG.restrict (hΔpoly i) (subset_univ _))⟩).isPolyhedron
  have hGΔK : ∀ i, G '' crossQuarterTriangle r i ⊆ K₀.space := by
    rintro i _ ⟨q, hq, rfl⟩
    rw [hK₀space]
    exact hrball (crossQuarterTriangle_subset_closedBall i hq)
  have h0K₀ : (0 : (ℝ × ℝ) × ℝ) ∈ K₀.space := hK₀space ▸ openSimplex_subset_convexHull T h0T
  obtain ⟨K₁, hK₁, hK₁fin, h0K₁⟩ := exists_isSubdivision_singleton_mem K₀ h0K₀
  have : Finite K₁.faces := hK₁fin.to_subtype
  obtain ⟨K₂, hK₂, hK₂fin, hK₂Q⟩ := exists_isSubdivision_subcomplexes K₁
    (fun i => G '' crossQuarterTriangle r i) hGΔpoly (fun i => hK₁.space_eq ▸ hGΔK i)
  have : Finite K₂.faces := hK₂fin.to_subtype
  obtain ⟨R, hRfin, -, hRK₂, -, hRside⟩ := exists_triangulation_union_with_halfSpace_faces K₂
    (isPolyhedron_space K₂) (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toLinearMap.toAffineMap 0
  have : Finite R.faces := hRfin.to_subtype
  set K := restrict R K₂.space with hKdef
  have : Finite K.faces := (restrict_faces_finite R K₂.space).to_subtype
  have h0K : ({0} : Finset ((ℝ × ℝ) × ℝ)) ∈ K.faces :=
    hRK₂.singleton_mem (hK₂.singleton_mem h0K₁)
  have hKspace : K.space = convexHull ℝ (T : Set ((ℝ × ℝ) × ℝ)) := by
    rw [hRK₂.space_eq, hK₂.space_eq, hK₁.space_eq, hK₀space]
  have hMspace : ∀ i, (restrict K (G '' crossQuarterTriangle r i)).space =
      G '' crossQuarterTriangle r i := by
    intro i
    have hsp : (restrict K₂ (G '' crossQuarterTriangle r i)).space =
        G '' crossQuarterTriangle r i := restrict_space_of_eq_biUnion K₂ _ (hK₂Q i)
    have hsub := hRK₂.restrict (restrict K₂ (G '' crossQuarterTriangle r i))
      (restrict_faces_subset _ _)
    rw [hsp] at hsub
    exact hsub.space_eq.trans hsp
  set Ginv := Function.invFunOn G univ with hGinvdef
  have hGinvG : ∀ q, Ginv (G q) = q := fun q => hG.bijOn.invOn_invFunOn.1 (mem_univ q)
  have hGinvc : Continuous Ginv :=
    continuousOn_univ.mp hG.isPiecewiseAffineOn_invFunOn.continuousOn
  have hGinv0 : Ginv 0 = 0 := by
    have h := hGinvG 0
    rwa [hG0] at h
  obtain ⟨ρ, hρ, hρball⟩ : ∃ ρ > 0,
      ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ, Ginv z ∈ ball (0 : (ℝ × ℝ) × ℝ) (r / 2) := by
    have h : Ginv ⁻¹' ball (0 : (ℝ × ℝ) × ℝ) (r / 2) ∈ 𝓝 (0 : (ℝ × ℝ) × ℝ) :=
      hGinvc.continuousAt.preimage_mem_nhds (by rw [hGinv0]; exact ball_mem_nhds 0 (half_pos hr))
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp h
    exact ⟨ρ, hρ, fun z hz => hball hz⟩
  refine ⟨K, fun i => restrict K (G '' crossQuarterTriangle r i), ρ,
    restrict_faces_finite R K₂.space, h0K, hKspace ▸ hTn, fun s hs => hRside s hs.1,
    fun i => restrict_faces_subset _ _, fun i => ⟨h0K, ?_⟩, fun i => ?_, hρ, ?_, fun i => ?_⟩
  · rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff]
    exact ⟨0, ⟨0, 0, le_rfl, le_rfl, by linarith, by rw [zero_smul, Prod.mk_zero_zero]⟩, hG0⟩
  · rw [hMspace i]
    exact image_mono (crossQuarterTriangle_subset_crossQuarter r i)
  · intro i z hz hzQ
    rw [hMspace i]
    obtain ⟨q, hq, rfl⟩ := hzQ
    have hqb := hρball _ hz
    rw [hGinvG] at hqb
    exact ⟨q, crossQuarter_inter_ball_subset i ⟨hq, hqb⟩, rfl⟩
  · have : Finite (restrict K (G '' crossQuarterTriangle r i)).faces :=
      (restrict_faces_finite K _).to_subtype
    exact exists_isPLHomeomorphOn_Icc_geometricLink_crossQuarterTriangle hG hhom hr _
      (hMspace i) ⟨h0K, by
        rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff]
        exact ⟨0, ⟨0, 0, le_rfl, le_rfl, by linarith, by rw [zero_smul, Prod.mk_zero_zero]⟩, hG0⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
