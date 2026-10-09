/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConicalGermExtension
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossPlanes : Set ((ℝ × ℝ) × ℝ) := {p | p.1.1 = 0 ∨ p.1.2 = 0}

def coreSegment (τ : ℝ) : Set ((ℝ × ℝ) × ℝ) := {p | p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ}

theorem add_smul_mem_crossPlanes_iff {q : (ℝ × ℝ) × ℝ} (hq : q.1 = 0) (v : (ℝ × ℝ) × ℝ)
    {t : ℝ} (ht : 0 < t) : q + t • v ∈ crossPlanes ↔ q + v ∈ crossPlanes := by
  have h1 : q.1.1 = 0 := by rw [hq]; rfl
  have h2 : q.1.2 = 0 := by rw [hq]; rfl
  simp only [crossPlanes, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, h1, h2, zero_add, mul_eq_zero, ht.ne', false_or]

theorem add_smul_fst_eq_zero_iff {q : (ℝ × ℝ) × ℝ} (hq : q.1 = 0) (v : (ℝ × ℝ) × ℝ)
    {t : ℝ} (ht : 0 < t) : (q + t • v).1 = 0 ↔ (q + v).1 = 0 := by
  rw [Prod.fst_add, Prod.fst_add, hq, zero_add, zero_add, Prod.smul_fst, smul_eq_zero,
    or_iff_right ht.ne']

section Restrict

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem IsPLHomeomorphOn.restrict_of_image_eq_inter {f : E → A} {P : Set E} {Q : Set A}
    (h : IsPLHomeomorphOn f P Q) {P₀ : Set E} (hP₀ : IsOpen P₀) (hsub : P₀ ⊆ P) {O : Set A}
    (hO : IsOpen O) (himg : f '' P₀ = Q ∩ O) : IsPLHomeomorphOn f P₀ (Q ∩ O) := by
  have hinj : InjOn f P₀ := h.bijOn.injOn.mono hsub
  refine ⟨himg ▸ hinj.bijOn_image, fun x hx => ?_, ?_⟩
  · have hw := (h.isPiecewiseAffineOn x (hsub hx)).inter_of_mem_nhds (hP₀.mem_nhds hx)
    rwa [inter_eq_right.mpr hsub] at hw
  · have hpa : IsPiecewiseAffineOn (Function.invFunOn f P) (Q ∩ O) := fun y hy =>
      (h.isPiecewiseAffineOn_invFunOn y hy.1).inter_of_mem_nhds (hO.mem_nhds hy.2)
    refine hpa.congr fun y hy => ?_
    rw [← himg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hinj.leftInvOn_invFunOn hx, h.bijOn.injOn.leftInvOn_invFunOn (hsub hx)]

omit [FiniteDimensional ℝ E] in
theorem IsPLHomeomorphOn.exists_image_eq_inter {f : E → A} {P : Set E} {S Ω : Set A}
    (h : IsPLHomeomorphOn f P (S ∩ Ω)) {O : Set E} (hO : IsOpen O) :
    ∃ Ω' : Set A, IsOpen Ω' ∧ f '' (P ∩ O) = S ∩ (Ω ∩ Ω') := by
  obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.mp
    h.isPiecewiseAffineOn_invFunOn.continuousOn O hO
  refine ⟨u, hu, ?_⟩
  have himg : f '' (P ∩ O) = Function.invFunOn f P ⁻¹' O ∩ (S ∩ Ω) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxP, hxO⟩, rfl⟩
      refine ⟨?_, h.bijOn.mapsTo hxP⟩
      change Function.invFunOn f P (f x) ∈ O
      rw [h.bijOn.injOn.leftInvOn_invFunOn hxP]
      exact hxO
    · rintro ⟨hyO, hy⟩
      exact ⟨Function.invFunOn f P y, ⟨h.bijOn.surjOn.mapsTo_invFunOn hy, hyO⟩,
        h.bijOn.invOn_invFunOn.2 hy⟩
  rw [himg, hueq]
  ext y
  simp only [mem_inter_iff]
  tauto

theorem IsPLHomeomorphOn.invFunOn_comp_of_inter {Φ ψ : E → A} {N V : Set E}
    {S Ω Ω' : Set A} (hN : IsOpen N) (hV : IsOpen V) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω)) (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω')) :
    IsOpen (N ∩ Φ ⁻¹' Ω') ∧ IsOpen (V ∩ ψ ⁻¹' Ω) ∧
      IsPLHomeomorphOn (Function.invFunOn ψ V ∘ Φ) (N ∩ Φ ⁻¹' Ω') (V ∩ ψ ⁻¹' Ω) := by
  have hU : IsOpen (N ∩ Φ ⁻¹' Ω') :=
    hΦ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hN hΩ'
  have hV' : IsOpen (V ∩ ψ ⁻¹' Ω) :=
    hψ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hV hΩ
  refine ⟨hU, hV', ?_⟩
  have h1 : IsPLHomeomorphOn Φ (N ∩ Φ ⁻¹' Ω') ((S ∩ Ω) ∩ Ω') :=
    hΦ.restrict_of_image_eq_inter hU inter_subset_left hΩ'
      (by rw [image_inter_preimage, hΦ.image_eq])
  have h2 : IsPLHomeomorphOn ψ (V ∩ ψ ⁻¹' Ω) ((S ∩ Ω') ∩ Ω) :=
    hψ.restrict_of_image_eq_inter hV' inter_subset_left hΩ
      (by rw [image_inter_preimage, hψ.image_eq])
  have heq : (S ∩ Ω') ∩ Ω = (S ∩ Ω) ∩ Ω' := inter_right_comm S Ω' Ω
  rw [heq] at h2
  refine (h1.trans h2.symm).congr fun x hx => ?_
  have hy : Φ x ∈ (S ∩ Ω) ∩ Ω' := h1.bijOn.mapsTo hx
  have hz := h2.bijOn.surjOn.mapsTo_invFunOn hy
  have hψz := h2.bijOn.invOn_invFunOn.2 hy
  change Function.invFunOn ψ V (Φ x) = Function.invFunOn ψ (V ∩ ψ ⁻¹' Ω) (Φ x)
  conv_lhs => rw [← hψz]
  exact hψ.bijOn.injOn.leftInvOn_invFunOn hz.1

end Restrict

theorem exists_isOpen_injOn_of_isCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {N K : Set X} (hN : IsOpen N) (hf : ContinuousOn f N)
    (hK : IsCompact K) (hKN : K ⊆ N) (hinj : InjOn f K)
    (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 x, InjOn f U) :
    ∃ N' : Set X, IsOpen N' ∧ K ⊆ N' ∧ N' ⊆ N ∧ InjOn f N' := by
  let O : Set (X × X) := {z | ∀ᶠ w in 𝓝 z, f w.1 = f w.2 → w.1 = w.2}
  have hO : IsOpen O := isOpen_setOfPred_eventually_nhds
  have hKO : K ×ˢ K ⊆ O := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨U, hU, hinjU⟩ := hloc x hx
      change ∀ᶠ w in 𝓝 (x, x), f w.1 = f w.2 → w.1 = w.2
      filter_upwards [prod_mem_nhds hU hU] with w hw heq using hinjU hw.1 hw.2 heq
    · have hne : f x ≠ f y := fun h => hxy (hinj hx hy h)
      have hcx : ContinuousAt f x := hf.continuousAt (hN.mem_nhds (hKN hx))
      have hcy : ContinuousAt f y := hf.continuousAt (hN.mem_nhds (hKN hy))
      have h1 : Tendsto (fun w : X × X => f w.1) (𝓝 (x, y)) (𝓝 (f x)) :=
        (hcx.comp continuousAt_fst).tendsto
      have h2 : Tendsto (fun w : X × X => f w.2) (𝓝 (x, y)) (𝓝 (f y)) :=
        (hcy.comp continuousAt_snd).tendsto
      have hopen : IsOpen {p : Y × Y | p.1 ≠ p.2} :=
        (isClosed_eq continuous_fst continuous_snd).isOpen_compl
      change ∀ᶠ w in 𝓝 (x, y), f w.1 = f w.2 → w.1 = w.2
      filter_upwards [(h1.prodMk_nhds h2) (hopen.mem_nhds hne)] with w hw heq
      exact absurd heq hw
  obtain ⟨u, v, hu, hv, hKu, hKv, huv⟩ := generalized_tube_lemma hK hK hO hKO
  refine ⟨u ∩ v ∩ N, (hu.inter hv).inter hN, fun x hx => ⟨⟨hKu hx, hKv hx⟩, hKN hx⟩,
    inter_subset_right, fun x hx y hy hxy => ?_⟩
  have hmem : (x, y) ∈ O := huv ⟨hx.1.1, hy.1.2⟩
  exact hmem.self_of_nhds hxy

theorem dist_corePoint (s t : ℝ) :
    dist (((0 : ℝ), (0 : ℝ)), s) (((0 : ℝ), (0 : ℝ)), t) = |s - t| := by
  rw [Prod.dist_eq, dist_self, Real.dist_eq]
  exact max_eq_right (abs_nonneg _)

section Junction

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_junction {Φ ψ : (ℝ × ℝ) × ℝ → A} {N V : Set ((ℝ × ℝ) × ℝ)}
    {S Ω Ω' Z D : Set A} (hN : IsOpen N) (hV : IsOpen V) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω)) (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω'))
    (hZ : ∀ p ∈ N, 0 < p.2 → (Φ p ∈ Z ↔ p ∈ crossPlanes))
    (hD : ∀ p ∈ N, 0 < p.2 → (Φ p ∈ D ↔ p.1 = 0))
    {c : ℝ} (hψZ : ∀ p ∈ V, p.2 < c → (ψ p ∈ Z ↔ p ∈ crossPlanes))
    (hψD : ∀ p ∈ V, p.2 < c → (ψ p ∈ D ↔ p.1 = 0))
    {τ : ℝ} (hτ : 0 < τ) (hq : ((0, 0), τ) ∈ N) (hqΩ' : Φ ((0, 0), τ) ∈ Ω')
    (hc : (Function.invFunOn ψ V (Φ ((0, 0), τ))).2 < c)
    {v₀ u₀ : ℝ} (hv₀ : 0 < v₀) (hu₀ : 0 < u₀)
    (horient : ∀ v : ℝ, 0 < v → v ≤ v₀ → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      Φ ((0, 0), τ - u) ≠ ψ (Function.invFunOn ψ V (Φ ((0, 0), τ)) + ((0, 0), v))) :
    ∃ (G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) (ρ μ : ℝ), 0 < ρ ∧ 0 < μ ∧
      IsPLHomeomorphOn G univ univ ∧ ball ((0, 0), τ) ρ ⊆ N ∩ Φ ⁻¹' Ω' ∧
      (∀ p ∈ ball ((0, 0), τ) ρ, G p ∈ V ∧ ψ (G p) = Φ p) ∧
      (∀ p, p ∈ crossPlanes ↔ G p ∈ crossPlanes) ∧ (∀ p, p.1 = 0 ↔ (G p).1 = 0) ∧
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
  have hcone : ∀ q : (ℝ × ℝ) × ℝ, q.1 = 0 →
      ∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 < t → (q + t • v ∈ crossPlanes ↔ q + v ∈ crossPlanes) :=
    fun q hq v t ht => add_smul_mem_crossPlanes_iff hq v ht
  have hconeAxis : ∀ q : (ℝ × ℝ) × ℝ, q.1 = 0 → ∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 < t →
      (q + t • v ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0} ↔ q + v ∈ {p : (ℝ × ℝ) × ℝ | p.1 = 0}) :=
    fun q hq v t ht => add_smul_fst_eq_zero_iff hq v ht
  have hGq₀axis : (G q₀).1 = 0 := by rw [hGq₀]; exact hw₀axis
  have hX : ∀ p, p ∈ crossPlanes ↔ G p ∈ crossPlanes := by
    refine forall_mem_iff_of_homogeneous hGhom (hcone q₀ rfl) (hcone (G q₀) hGq₀axis) hρ ?_
    intro p hp
    obtain ⟨hGV, hψG⟩ := hGloc p (hballsub hp)
    rw [← hZ p (hball₁ (hballsub hp)).1 (hpos p hp), ← hψG]
    exact hψZ (G p) hGV (hsmall p hp)
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

end Junction

end DifferentialGeometry.Topology.PiecewiseLinear
