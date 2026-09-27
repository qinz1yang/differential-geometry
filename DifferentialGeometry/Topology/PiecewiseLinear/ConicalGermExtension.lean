/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_radial_eq_of_isPiecewiseAffineOn {f : E → F} {U : Set E}
    (hf : IsPiecewiseAffineOn f U) (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ U ∧ ∀ v : E, ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ →
      ‖s₁ • v‖ < ρ → ‖s₂ • v‖ < ρ →
        s₂ • (f (x + s₁ • v) - f x) = s₁ • (f (x + s₂ • v) - f x) := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf x hx
  rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] at hCx
  have hfar : (⋂ i, {z | z ∈ C i → x ∈ C i}) ∈ 𝓝 x := by
    refine Filter.iInter_mem.mpr fun i => ?_
    by_cases hxi : x ∈ C i
    · exact Filter.mem_of_superset Filter.univ_mem fun z _ _ => hxi
    · exact Filter.mem_of_superset ((hC i).1.isClosed.isOpen_compl.mem_nhds hxi)
        fun z hz hzi => (hz hzi).elim
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Filter.inter_mem hCx hfar) (hU.mem_nhds hx))
  refine ⟨ρ, hρ, fun z hz => (hball hz).2, ?_⟩
  have key : ∀ v : E, ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ → ‖s₂ • v‖ < ρ →
      s₂ • (f (x + s₁ • v) - f x) = s₁ • (f (x + s₂ • v) - f x) := by
    intro v s₁ s₂ hs₁ hs₁₂ hs₂
    have hmem : x + s₂ • v ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hs₂
    obtain ⟨⟨hU', hfar'⟩, -⟩ := hball hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hU'
    have hxi : x ∈ C i := (mem_iInter.mp hfar' i) hi
    have hpos : 0 < s₂ := hs₁.trans_le hs₁₂
    have hmem₁ : x + s₁ • v ∈ C i := by
      have h := (hC i).1.convex.add_smul_sub_mem hxi hi
        ⟨div_nonneg hs₁.le hpos.le, (div_le_one hpos).mpr hs₁₂⟩
      rwa [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hpos.ne'] at h
    have hlin : ∀ s : ℝ, x + s • v ∈ C i → f (x + s • v) - f x = s • (A i).linear v := by
      intro s hs
      rw [(hC i).2.2 hs, (hC i).2.2 hxi, ← vsub_eq_sub, ← AffineMap.linearMap_vsub,
        vsub_eq_sub, add_sub_cancel_left, map_smul]
    rw [hlin s₁ hmem₁, hlin s₂ hi, smul_smul, smul_smul, mul_comm]
  intro v s₁ s₂ hs₁ hs₂ h₁ h₂
  rcases le_total s₁ s₂ with h | h
  · exact key v s₁ s₂ hs₁ h h₂
  · exact (key v s₂ s₁ hs₂ h h₁).symm

theorem exists_pos_forall_mem_ball_norm_smul_sub_lt (x z : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ ∀ w ∈ ball z 1, ‖s • (w - x)‖ < ρ := by
  have hden : 0 < 2 * (‖z - x‖ + 1 + ρ) := by positivity
  refine ⟨ρ / (2 * (‖z - x‖ + 1 + ρ)), div_pos hρ hden, fun w hw => ?_⟩
  have hw' : ‖w - x‖ < ‖z - x‖ + 1 := by
    have hwz := mem_ball.mp hw
    rw [dist_eq_norm] at hwz
    calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
      _ < ‖z - x‖ + 1 := by linarith
  rw [norm_smul, Real.norm_of_nonneg (div_pos hρ hden).le, div_mul_eq_mul_div,
    div_lt_iff₀ hden]
  nlinarith [norm_nonneg (w - x), norm_nonneg (z - x)]

noncomputable def conicalGermExtension (f : E → F) (x : E) (ρ : ℝ) (z : E) : F :=
  f x + (ρ / (2 * (‖z - x‖ + ρ)))⁻¹ • (f (x + (ρ / (2 * (‖z - x‖ + ρ))) • (z - x)) - f x)

section Radial

variable {f : E → F} {x : E} {ρ : ℝ}

theorem conicalGermExtension_eq (hρ : 0 < ρ)
    (hrad : ∀ v : E, ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ → ‖s₁ • v‖ < ρ → ‖s₂ • v‖ < ρ →
      s₂ • (f (x + s₁ • v) - f x) = s₁ • (f (x + s₂ • v) - f x))
    {z : E} {s : ℝ} (hs : 0 < s) (hsz : ‖s • (z - x)‖ < ρ) :
    conicalGermExtension f x ρ z = f x + s⁻¹ • (f (x + s • (z - x)) - f x) := by
  have hden : 0 < 2 * (‖z - x‖ + ρ) := by positivity
  have hs₀pos : 0 < ρ / (2 * (‖z - x‖ + ρ)) := div_pos hρ hden
  have hs₀z : ‖(ρ / (2 * (‖z - x‖ + ρ))) • (z - x)‖ < ρ := by
    rw [norm_smul, Real.norm_of_nonneg hs₀pos.le, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [norm_nonneg (z - x)]
  have h := hrad (z - x) _ s hs₀pos hs hs₀z hsz
  rw [conicalGermExtension]
  congr 1
  set s₀ := ρ / (2 * (‖z - x‖ + ρ))
  calc s₀⁻¹ • (f (x + s₀ • (z - x)) - f x)
      = (s₀⁻¹ * s⁻¹) • (s • (f (x + s₀ • (z - x)) - f x)) := by
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
    _ = (s₀⁻¹ * s⁻¹) • (s₀ • (f (x + s • (z - x)) - f x)) := by rw [h]
    _ = s⁻¹ • (f (x + s • (z - x)) - f x) := by
        rw [smul_smul, mul_comm s₀⁻¹ s⁻¹, mul_assoc, inv_mul_cancel₀ hs₀pos.ne', mul_one]

theorem conicalGermExtension_eq_of_mem_ball (hρ : 0 < ρ)
    (hrad : ∀ v : E, ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ → ‖s₁ • v‖ < ρ → ‖s₂ • v‖ < ρ →
      s₂ • (f (x + s₁ • v) - f x) = s₁ • (f (x + s₂ • v) - f x))
    {z : E} (hz : z ∈ ball x ρ) : conicalGermExtension f x ρ z = f z := by
  have hz' : ‖(1 : ℝ) • (z - x)‖ < ρ := by
    rw [one_smul, ← dist_eq_norm]
    exact mem_ball.mp hz
  rw [conicalGermExtension_eq hρ hrad one_pos hz', inv_one, one_smul, one_smul,
    add_sub_cancel, add_sub_cancel]

theorem conicalGermExtension_add_smul (hρ : 0 < ρ)
    (hrad : ∀ v : E, ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ → ‖s₁ • v‖ < ρ → ‖s₂ • v‖ < ρ →
      s₂ • (f (x + s₁ • v) - f x) = s₁ • (f (x + s₂ • v) - f x))
    (v : E) {t : ℝ} (ht : 0 ≤ t) :
    conicalGermExtension f x ρ (x + t • v) =
      conicalGermExtension f x ρ x +
        t • (conicalGermExtension f x ρ (x + v) - conicalGermExtension f x ρ x) := by
  have hx : conicalGermExtension f x ρ x = f x :=
    conicalGermExtension_eq_of_mem_ball hρ hrad (mem_ball_self hρ)
  rw [hx]
  rcases ht.eq_or_lt with rfl | htpos
  · rw [zero_smul, add_zero, zero_smul, add_zero, hx]
  obtain ⟨σ, hσ, hσv⟩ := exists_pos_forall_mem_ball_norm_smul_sub_lt x (x + v) hρ
  have hσv' : ‖σ • v‖ < ρ := by
    have h := hσv (x + v) (mem_ball_self one_pos)
    rwa [add_sub_cancel_left] at h
  have h1 : conicalGermExtension f x ρ (x + v) = f x + σ⁻¹ • (f (x + σ • v) - f x) := by
    have h := conicalGermExtension_eq hρ hrad (z := x + v) hσ
      (by rw [add_sub_cancel_left]; exact hσv')
    rwa [add_sub_cancel_left] at h
  have h2 : conicalGermExtension f x ρ (x + t • v) =
      f x + (t * σ⁻¹) • (f (x + σ • v) - f x) := by
    have hmul : (σ / t) • (t • v) = σ • v := by
      rw [smul_smul, div_mul_cancel₀ σ htpos.ne']
    have h := conicalGermExtension_eq hρ hrad (z := x + t • v) (div_pos hσ htpos)
      (by rw [add_sub_cancel_left, hmul]; exact hσv')
    rwa [add_sub_cancel_left, hmul, inv_div, div_eq_mul_inv] at h
  rw [h1, h2, add_sub_cancel_left, smul_smul]

end Radial

theorem isPiecewiseAffineOn_add_smul_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] (c : G) (s : ℝ) {u : Set G} (hu : IsOpen u) :
    IsPiecewiseAffineOn (fun w => c + s • (w - c)) u :=
  (isPiecewiseAffineOn_of_affine (AffineMap.homothety c s) hu).congr fun w _ => by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]

theorem isPLHomeomorphOn_conicalGermExtension [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {U : Set E} {V : Set F}
    (hf : IsPLHomeomorphOn f U V) (hV : IsOpen V) {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball x ρ ⊆ U)
    (hrad : ∀ v : E, ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ → ‖s₁ • v‖ < ρ → ‖s₂ • v‖ < ρ →
      s₂ • (f (x + s₁ • v) - f x) = s₁ • (f (x + s₂ • v) - f x)) :
    IsPLHomeomorphOn (conicalGermExtension f x ρ) univ univ := by
  classical
  set G := conicalGermExtension f x ρ with hGdef
  have hinj : InjOn G univ := by
    intro z _ z' _ hzz
    obtain ⟨σ₁, hσ₁, hσ₁z⟩ := exists_pos_forall_mem_ball_norm_smul_sub_lt x z hρ
    obtain ⟨σ₂, hσ₂, hσ₂z⟩ := exists_pos_forall_mem_ball_norm_smul_sub_lt x z' hρ
    set σ := min σ₁ σ₂
    have hσ : 0 < σ := lt_min hσ₁ hσ₂
    have hmono : ∀ {τ : ℝ} (w : E), 0 < τ → σ ≤ τ → ‖τ • (w - x)‖ < ρ →
        ‖σ • (w - x)‖ < ρ := by
      intro τ w hτ hστ hw
      rw [norm_smul, Real.norm_of_nonneg hσ.le]
      rw [norm_smul, Real.norm_of_nonneg hτ.le] at hw
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hστ (norm_nonneg _)) hw
    have hz : ‖σ • (z - x)‖ < ρ :=
      hmono z hσ₁ (min_le_left _ _) (hσ₁z z (mem_ball_self one_pos))
    have hz' : ‖σ • (z' - x)‖ < ρ :=
      hmono z' hσ₂ (min_le_right _ _) (hσ₂z z' (mem_ball_self one_pos))
    have hmemz : x + σ • (z - x) ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hz
    have hmemz' : x + σ • (z' - x) ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hz'
    rw [hGdef, conicalGermExtension_eq hρ hrad hσ hz,
      conicalGermExtension_eq hρ hrad hσ hz'] at hzz
    have hf' : f (x + σ • (z - x)) = f (x + σ • (z' - x)) := by
      have h := add_left_cancel hzz
      exact sub_left_injective (smul_right_injective F (inv_ne_zero hσ.ne') h)
    have hpt := hf.bijOn.injOn (hball hmemz) (hball hmemz') hf'
    have hsm := add_left_cancel hpt
    have := smul_right_injective E hσ.ne' hsm
    exact sub_left_injective this
  have hV₀ : IsOpen (f '' ball x ρ) := hf.isOpen_image_of_isOpen hV isOpen_ball hball
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hV₀ (f x) ⟨x, mem_ball_self hρ, rfl⟩
  have hlocinv : ∀ y : F, ∃ s : ℝ, 0 < s ∧ ∀ y' ∈ ball y 1,
      f x + s • (y' - f x) ∈ f '' ball x ρ ∧
        G (x + s⁻¹ • (Function.invFunOn f U (f x + s • (y' - f x)) - x)) = y' := by
    intro y
    obtain ⟨s, hs, hsy⟩ := exists_pos_forall_mem_ball_norm_smul_sub_lt (f x) y hr
    refine ⟨s, hs, fun y' hy' => ?_⟩
    have hp : f x + s • (y' - f x) ∈ f '' ball x ρ := by
      apply hrball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hsy y' hy'
    refine ⟨hp, ?_⟩
    obtain ⟨u, hu, hfu⟩ := hp
    have hinv : Function.invFunOn f U (f x + s • (y' - f x)) = u := by
      rw [← hfu]
      exact hf.bijOn.injOn.leftInvOn_invFunOn (hball hu)
    rw [hinv]
    have hsu : s • (x + s⁻¹ • (u - x) - x) = u - x := by
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    have hnorm : ‖s • (x + s⁻¹ • (u - x) - x)‖ < ρ := by
      rw [hsu, ← dist_eq_norm]
      exact mem_ball.mp hu
    rw [hGdef, conicalGermExtension_eq hρ hrad hs hnorm, hsu, add_sub_cancel, hfu,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, add_sub_cancel]
  have hsurj : SurjOn G univ univ := by
    intro y _
    obtain ⟨s, -, hs⟩ := hlocinv y
    exact ⟨_, mem_univ _, (hs y (mem_ball_self one_pos)).2⟩
  have hbij : BijOn G univ univ := ⟨mapsTo_univ _ _, hinj, hsurj⟩
  refine ⟨hbij, ?_, ?_⟩
  · refine isPiecewiseAffineOn_of_locally fun z _ => ⟨ball z 1, isOpen_ball,
      mem_ball_self one_pos, ?_⟩
    obtain ⟨s, hs, hsz⟩ := exists_pos_forall_mem_ball_norm_smul_sub_lt x z hρ
    have hcomp := (isPiecewiseAffineOn_add_smul_sub (f x) s⁻¹ isOpen_univ).comp
      (hf.isPiecewiseAffineOn.comp (isPiecewiseAffineOn_add_smul_sub x s isOpen_univ))
    rw [univ_inter]
    refine (hcomp.mono isOpen_ball fun w hw => ?_).congr fun w hw => ?_
    · refine ⟨⟨mem_univ _, hball ?_⟩, mem_univ _⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hsz w hw
    · exact conicalGermExtension_eq hρ hrad hs (hsz w hw)
  · refine isPiecewiseAffineOn_of_locally fun y _ => ⟨ball y 1, isOpen_ball,
      mem_ball_self one_pos, ?_⟩
    obtain ⟨s, hs, hsy⟩ := hlocinv y
    have hcomp := (isPiecewiseAffineOn_add_smul_sub x s⁻¹ isOpen_univ).comp
      (hf.isPiecewiseAffineOn_invFunOn.comp
        (isPiecewiseAffineOn_add_smul_sub (f x) s isOpen_univ))
    rw [univ_inter]
    refine (hcomp.mono isOpen_ball fun y' hy' => ?_).congr fun y' hy' => ?_
    · refine ⟨⟨mem_univ _, ?_⟩, mem_univ _⟩
      obtain ⟨u, hu, hfu⟩ := (hsy y' hy').1
      change f x + s • (y' - f x) ∈ V
      rw [← hfu]
      exact hf.bijOn.mapsTo (hball hu)
    · have hG := (hsy y' hy').2
      have hmem : ∃ a ∈ univ, G a = y' := ⟨_, mem_univ _, hG⟩
      apply hinj (mem_univ _) (mem_univ _)
      rw [Function.invFunOn_eq hmem]
      exact hG.symm

theorem forall_mem_iff_of_homogeneous {G : E → F} {x : E} {S : Set E} {S' : Set F} {ρ : ℝ}
    (hG : ∀ v : E, ∀ t : ℝ, 0 ≤ t → G (x + t • v) = G x + t • (G (x + v) - G x))
    (hS : ∀ v : E, ∀ t : ℝ, 0 < t → (x + t • v ∈ S ↔ x + v ∈ S))
    (hS' : ∀ w : F, ∀ t : ℝ, 0 < t → (G x + t • w ∈ S' ↔ G x + w ∈ S'))
    (hρ : 0 < ρ) (hloc : ∀ z ∈ ball x ρ, z ∈ S ↔ G z ∈ S') (z : E) : z ∈ S ↔ G z ∈ S' := by
  obtain ⟨t, ht, htz⟩ := exists_pos_forall_mem_ball_norm_smul_sub_lt x z hρ
  have hmem : x + t • (z - x) ∈ ball x ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact htz z (mem_ball_self one_pos)
  have h1 := hS (z - x) t ht
  have h2 := hS' (G z - G x) t ht
  rw [add_sub_cancel] at h1 h2
  rw [← h1, hloc _ hmem, hG (z - x) t ht.le, add_sub_cancel, h2]

theorem IsPLHomeomorphOn.exists_isPLHomeomorphOn_univ_homogeneous [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : E → F} {U : Set E} {V : Set F} (hf : IsPLHomeomorphOn f U V)
    (hU : IsOpen U) (hV : IsOpen V) {x : E} (hx : x ∈ U) :
    ∃ (G : E → F) (ρ : ℝ), 0 < ρ ∧ ball x ρ ⊆ U ∧ IsPLHomeomorphOn G univ univ ∧
      EqOn G f (ball x ρ) ∧
        ∀ v : E, ∀ t : ℝ, 0 ≤ t → G (x + t • v) = G x + t • (G (x + v) - G x) := by
  obtain ⟨ρ, hρ, hball, hrad⟩ := exists_pos_radial_eq_of_isPiecewiseAffineOn
    hf.isPiecewiseAffineOn hU hx
  exact ⟨conicalGermExtension f x ρ, ρ, hρ, hball,
    isPLHomeomorphOn_conicalGermExtension hf hV hρ hball hrad,
    fun z hz => conicalGermExtension_eq_of_mem_ball hρ hrad hz,
    fun v t ht => conicalGermExtension_add_smul hρ hrad v ht⟩

end DifferentialGeometry.Topology.PiecewiseLinear
