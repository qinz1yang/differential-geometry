/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningJunction

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcPatternEndJunction {ι : Type*} (P : ι → Set (ℝ × ℝ))
    (hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i))
    {Φ ψ : (ℝ × ℝ) × ℝ → A} {N V : Set ((ℝ × ℝ) × ℝ)}
    {S Ω Ω' D : Set A} {Z : ι → Set A}
    (hN : IsOpen N) (hV : IsOpen V) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω)) (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω'))
    (hZ : ∀ i p, p ∈ N → 0 < p.2 → (Φ p ∈ Z i ↔ p.1 ∈ P i))
    (hD : ∀ p ∈ N, 0 < p.2 → (Φ p ∈ D ↔ p.1 = 0))
    {c : ℝ} (hψZ : ∀ i p, p ∈ V → p.2 < c → (ψ p ∈ Z i ↔ p.1 ∈ P i))
    (hψD : ∀ p ∈ V, p.2 < c → (ψ p ∈ D ↔ p.1 = 0))
    {τ : ℝ} (hτ : 0 < τ) (hq : ((0, 0), τ) ∈ N) (hqΩ' : Φ ((0, 0), τ) ∈ Ω')
    (hc : (Function.invFunOn ψ V (Φ ((0, 0), τ))).2 < c)
    {v₀ u₀ : ℝ} (hv₀ : 0 < v₀) (hu₀ : 0 < u₀)
    (horient : ∀ v : ℝ, 0 < v → v ≤ v₀ → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      Φ ((0, 0), τ - u) ≠ ψ (Function.invFunOn ψ V (Φ ((0, 0), τ)) + ((0, 0), v))) :
    ∃ (G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) (ρ μ : ℝ), 0 < ρ ∧ 0 < μ ∧
      IsPLHomeomorphOn G univ univ ∧ ball ((0, 0), τ) ρ ⊆ N ∩ Φ ⁻¹' Ω' ∧
      (∀ p ∈ ball ((0, 0), τ) ρ, G p ∈ V ∧ ψ (G p) = Φ p) ∧
      (∀ i p, p.1 ∈ P i ↔ (G p).1 ∈ P i) ∧ (∀ p, p.1 = 0 ↔ (G p).1 = 0) ∧
      G ((0, 0), τ) = Function.invFunOn ψ V (Φ ((0, 0), τ)) ∧
      (∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 ≤ t →
        G (((0, 0), τ) + t • v) = G ((0, 0), τ) + t • (G (((0, 0), τ) + v) - G ((0, 0), τ))) ∧
      ∀ u : ℝ, 0 ≤ u → G ((0, 0), τ + u) = G ((0, 0), τ) + ((0, 0), u / μ) := by
  obtain ⟨hU, hV₀, hg⟩ := IsPLHomeomorphOn.invFunOn_comp_of_inter hN hV hΩ hΩ' hΦ hψ
  set q₀ : (ℝ × ℝ) × ℝ := ((0, 0), τ) with hq₀def
  set w₀ := Function.invFunOn ψ V (Φ q₀) with hw₀def
  obtain ⟨G, ρ₁, hρ₁, hball₁, hG, hGeq, hGhom⟩ :=
    hg.exists_isPLHomeomorphOn_univ_homogeneous hU hV₀ ⟨hq, hqΩ'⟩
  have hmemψ : ∀ p ∈ N ∩ Φ ⁻¹' Ω', Φ p ∈ S ∩ Ω' := fun p hp =>
    ⟨(hΦ.bijOn.mapsTo hp.1).1, hp.2⟩
  have hGloc : ∀ p ∈ ball q₀ ρ₁, G p ∈ V ∧ ψ (G p) = Φ p := by
    intro p hp
    rw [hGeq hp]
    have hy := hmemψ p (hball₁ hp)
    exact ⟨hψ.bijOn.surjOn.mapsTo_invFunOn hy, hψ.bijOn.invOn_invFunOn.2 hy⟩
  have hGq₀ : G q₀ = w₀ := hGeq (mem_ball_self hρ₁)
  have hGcont : Continuous G := continuousOn_univ.mp hG.isPiecewiseAffineOn.continuousOn
  have hw₀V : w₀ ∈ V := hψ.bijOn.surjOn.mapsTo_invFunOn (hmemψ q₀ ⟨hq, hqΩ'⟩)
  have hψw₀ : ψ w₀ = Φ q₀ := hψ.bijOn.invOn_invFunOn.2 (hmemψ q₀ ⟨hq, hqΩ'⟩)
  have hw₀axis : w₀.1 = 0 := by
    have h1 : Φ q₀ ∈ D := (hD q₀ hq hτ).mpr rfl
    rw [← hψw₀] at h1
    exact (hψD w₀ hw₀V hc).mp h1
  have hopen : IsOpen {p : (ℝ × ℝ) × ℝ | (G p).2 < c} :=
    isOpen_lt (continuous_snd.comp hGcont) continuous_const
  obtain ⟨ρ₂, hρ₂, hball₂⟩ := Metric.isOpen_iff.mp hopen q₀ (by
    change (G q₀).2 < c
    rw [hGq₀]
    exact hc)
  set ρ := min (min ρ₁ τ) ρ₂ with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ hτ) hρ₂
  have hballsub : ball q₀ ρ ⊆ ball q₀ ρ₁ :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hpos : ∀ p ∈ ball q₀ ρ, 0 < p.2 := by
    intro p hp
    have h1 : dist p.2 q₀.2 < τ := lt_of_le_of_lt (le_max_right _ _)
      (lt_of_lt_of_le (mem_ball.mp hp) ((min_le_left _ _).trans (min_le_right _ _)))
    have hq2 : q₀.2 = τ := rfl
    rw [hq2, Real.dist_eq] at h1
    have h2 := neg_abs_le (p.2 - τ)
    linarith
  have hsmall : ∀ p ∈ ball q₀ ρ, (G p).2 < c := fun p hp =>
    hball₂ (ball_subset_ball (min_le_right _ _) hp)
  have hcone (q : (ℝ × ℝ) × ℝ) (hq : q.1 = 0) (i : ι)
      (v : (ℝ × ℝ) × ℝ) (t : ℝ) (ht : 0 < t) :
      (q + t • v).1 ∈ P i ↔ (q + v).1 ∈ P i := by
    simpa only [Prod.fst_add, Prod.smul_fst, hq, zero_add] using hP i v.1 t ht
  have hconeAxis : ∀ q : (ℝ × ℝ) × ℝ, q.1 = 0 → ∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 < t →
      (q + t • v ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0} ↔ q + v ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0}) :=
    fun q hq v t ht => add_smul_fst_eq_zero_iff hq v ht
  have hGq₀axis : (G q₀).1 = 0 := by rw [hGq₀]; exact hw₀axis
  have hX : ∀ i p, p.1 ∈ P i ↔ (G p).1 ∈ P i := by
    intro i
    refine forall_mem_iff_of_homogeneous hGhom
      (S := {p : (ℝ × ℝ) × ℝ | p.1 ∈ P i})
      (S' := {p : (ℝ × ℝ) × ℝ | p.1 ∈ P i})
      (hcone q₀ rfl i) (hcone (G q₀) hGq₀axis i) hρ ?_
    intro p hp
    obtain ⟨hGV, hψG⟩ := hGloc p (hballsub hp)
    change p.1 ∈ P i ↔ (G p).1 ∈ P i
    rw [← hZ i p (hball₁ (hballsub hp)).1 (hpos p hp), ← hψG]
    exact hψZ i (G p) hGV (hsmall p hp)
  have hL : ∀ p, p ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0} ↔ G p ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0} := by
    refine forall_mem_iff_of_homogeneous hGhom (hconeAxis q₀ rfl) (hconeAxis (G q₀) hGq₀axis)
      hρ ?_
    intro p hp
    obtain ⟨hGV, hψG⟩ := hGloc p (hballsub hp)
    change p.1 = 0 ↔ (G p).1 = 0
    rw [← hD p (hball₁ (hballsub hp)).1 (hpos p hp), ← hψG]
    exact hψD (G p) hGV (hsmall p hp)
  obtain ⟨m, -, hm⟩ := hG.bijOn.surjOn (mem_univ (w₀ + ((0, 0), 1)))
  have hmaxis : m.1 = 0 := by
    refine (hL m).mpr ?_
    change (G m).1 = 0
    rw [hm]
    simp only [Prod.fst_add, hw₀axis, zero_add, Prod.mk_zero_zero]
  set μ := m.2 - τ with hμdef
  have hmq : m - q₀ = ((0, 0), μ) := by
    rw [hq₀def]
    ext <;> simp [hmaxis, hμdef]
  have hGsmul : ∀ t : ℝ, 0 ≤ t → G (q₀ + t • (m - q₀)) = w₀ + ((0, 0), t) := by
    intro t ht
    rw [hGhom (m - q₀) t ht, add_sub_cancel, hm, hGq₀, add_sub_cancel_left]
    congr 1
    ext <;> simp
  have hμpos : 0 < μ := by
    rcases lt_trichotomy μ 0 with hneg | hzero | hposμ
    · exfalso
      have hnμ : 0 < -μ := neg_pos.mpr hneg
      set t := min (min v₀ (u₀ / (-μ))) (ρ / (2 * (-μ))) with htdef
      have ht : 0 < t := lt_min (lt_min hv₀ (div_pos hu₀ hnμ)) (div_pos hρ (by positivity))
      have htv : t ≤ v₀ := (min_le_left _ _).trans (min_le_left _ _)
      have htu : t * (-μ) ≤ u₀ := by
        have h1 : t ≤ u₀ / (-μ) := (min_le_left _ _).trans (min_le_right _ _)
        rwa [le_div_iff₀ hnμ] at h1
      have htρ : t * (-μ) < ρ := by
        have h1 : t ≤ ρ / (2 * (-μ)) := min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at h1
        nlinarith
      have hpeq : q₀ + t • (m - q₀) = ((0, 0), τ - t * (-μ)) := by
        rw [hmq, hq₀def]
        ext <;> simp
      have hpball : q₀ + t • (m - q₀) ∈ ball q₀ ρ := by
        rw [hpeq, mem_ball, hq₀def, dist_corePoint]
        rw [show τ - t * -μ - τ = -(t * -μ) by ring, abs_neg, abs_of_pos (mul_pos ht hnμ)]
        exact htρ
      have hΦp := (hGloc _ (hballsub hpball)).2
      rw [hGsmul t ht.le, hpeq] at hΦp
      exact horient t ht htv (t * (-μ)) (mul_pos ht hnμ) htu hΦp.symm
    · exfalso
      have hmeq : m = q₀ := by
        rw [← sub_eq_zero, hmq, hzero]
        rfl
      rw [hmeq, hGq₀] at hm
      have h2 := congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) hm
      simp only [Prod.snd_add, left_eq_add] at h2
      exact one_ne_zero h2
    · exact hposμ
  refine ⟨G, ρ, μ, hρ, hμpos, hG, fun p hp => hball₁ (hballsub hp),
    fun p hp => hGloc p (hballsub hp), hX, fun p => hL p, hGq₀, hGhom, fun u hu => ?_⟩
  have hpt : ((0, 0), τ + u) = q₀ + (u / μ) • (m - q₀) := by
    rw [hmq, hq₀def]
    ext <;> simp [div_mul_cancel₀ u hμpos.ne']
  rw [hpt, hGsmul (u / μ) (div_nonneg hu hμpos.le), hGq₀]

end DifferentialGeometry.Topology.PiecewiseLinear
