/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConicalGermPattern
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningJunction

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcPatternJunction {ι : Type*} (P : ι → Set (ℝ × ℝ))
    (hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i))
    {Φ ψ : (ℝ × ℝ) × ℝ → A} {N V : Set ((ℝ × ℝ) × ℝ)}
    {S Ω Ω' D : Set A} {Z : ι → Set A}
    (hN : IsOpen N) (hV : IsOpen V) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω)) (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω'))
    (hZ : ∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i))
    (hD : ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0)
    (hψZ : ∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i))
    (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0)
    {τ : ℝ} (hq : ((0, 0), τ) ∈ N) (hqΩ' : Φ ((0, 0), τ) ∈ Ω')
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
  have hmemψ : ∀ p ∈ N ∩ Φ ⁻¹' Ω', Φ p ∈ S ∩ Ω' := fun p hp =>
    ⟨(hΦ.bijOn.mapsTo hp.1).1, hp.2⟩
  have hw₀V : w₀ ∈ V := hψ.bijOn.surjOn.mapsTo_invFunOn (hmemψ q₀ ⟨hq, hqΩ'⟩)
  have hψw₀ : ψ w₀ = Φ q₀ := hψ.bijOn.invOn_invFunOn.2 (hmemψ q₀ ⟨hq, hqΩ'⟩)
  have hw₀axis : w₀.1 = 0 := by
    apply (hψD w₀ hw₀V).mp
    rw [hψw₀]
    exact (hD q₀ hq).mpr rfl
  have hcone (q : (ℝ × ℝ) × ℝ) (hq : q.1 = 0) (i : ι)
      (v : (ℝ × ℝ) × ℝ) (t : ℝ) (ht : 0 < t) :
      (q + t • v).1 ∈ P i ↔ (q + v).1 ∈ P i := by
    simpa only [Prod.fst_add, Prod.smul_fst, hq, zero_add] using hP i v.1 t ht
  obtain ⟨G, ρ, hρ, hball, hG, hGeq, hGhom, hX, -⟩ :=
    hg.exists_homogeneous_preserving_radial_patterns hU hV₀ ⟨hq, hqΩ'⟩
      (fun i => {p | p.1 ∈ P i}) (fun i => {p | p.1 ∈ P i})
      (hcone q₀ rfl) (hcone w₀ hw₀axis) (fun i p hp => by
        have hy := hmemψ p hp
        have hinv := hψ.bijOn.invOn_invFunOn.2 hy
        have hVinv := hψ.bijOn.surjOn.mapsTo_invFunOn hy
        change p.1 ∈ P i ↔ (Function.invFunOn ψ V (Φ p)).1 ∈ P i
        rw [← hZ i p hp.1, ← hψZ i _ hVinv, hinv])
  have hGloc : ∀ p ∈ ball q₀ ρ, G p ∈ V ∧ ψ (G p) = Φ p := by
    intro p hp
    rw [hGeq hp]
    have hy := hmemψ p (hball hp)
    exact ⟨hψ.bijOn.surjOn.mapsTo_invFunOn hy, hψ.bijOn.invOn_invFunOn.2 hy⟩
  have hGq₀ : G q₀ = w₀ := hGeq (mem_ball_self hρ)
  have hconeAxis (q : (ℝ × ℝ) × ℝ) (hq : q.1 = 0)
      (v : (ℝ × ℝ) × ℝ) (t : ℝ) (ht : 0 < t) :
      (q + t • v).1 = 0 ↔ (q + v).1 = 0 :=
    add_smul_fst_eq_zero_iff hq v ht
  have hGq₀axis : (G q₀).1 = 0 := by rw [hGq₀]; exact hw₀axis
  have hL : ∀ p, p ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0} ↔
      G p ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0} := by
    refine forall_mem_iff_of_homogeneous hGhom (hconeAxis q₀ rfl)
      (hconeAxis (G q₀) hGq₀axis) hρ ?_
    intro p hp
    obtain ⟨hGV, hψG⟩ := hGloc p hp
    change p.1 = 0 ↔ (G p).1 = 0
    rw [← hD p (hball hp).1, ← hψG]
    exact hψD (G p) hGV
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
      have hΦp := (hGloc _ hpball).2
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
  refine ⟨G, ρ, μ, hρ, hμpos, hG, hball, hGloc, hX, fun p => hL p, hGq₀, hGhom, fun u hu => ?_⟩
  have hpt : ((0, 0), τ + u) = q₀ + (u / μ) • (m - q₀) := by
    rw [hmq, hq₀def]
    ext <;> simp [div_mul_cancel₀ u hμpos.ne']
  rw [hpt, hGsmul (u / μ) (div_nonneg hu hμpos.le), hGq₀]

end DifferentialGeometry.Topology.PiecewiseLinear
