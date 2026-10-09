/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlockTransfer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def kinkOffset (c₀ c₁ t₀ t : ℝ) : ℝ :=
  c₀ + c₁ * max (t - t₀) 0

def kinkHeight (t₀ κ t : ℝ) : ℝ :=
  (t - t₀) + κ * max (t - t₀) 0

noncomputable def kinkHeightInv (t₀ κ s : ℝ) : ℝ :=
  t₀ + s - κ / (1 + κ) * max s 0

noncomputable def kinkBound (α₁ β₁ κ : ℝ) : ℝ :=
  1 + (1 + |α₁| + |β₁|) * (1 + 1 / (1 + κ))

section Kink

variable {t₀ κ : ℝ}

theorem max_kinkHeight (hκ : -1 < κ) (t : ℝ) :
    max (kinkHeight t₀ κ t) 0 = (1 + κ) * max (t - t₀) 0 := by
  unfold kinkHeight
  rcases le_total 0 (t - t₀) with h | h
  · rw [max_eq_left h, max_eq_left (by nlinarith)]
    ring
  · rw [max_eq_right h, max_eq_right (by linarith)]
    ring

theorem max_kinkHeightInv_sub (hκ : -1 < κ) (s : ℝ) :
    max (kinkHeightInv t₀ κ s - t₀) 0 = max s 0 / (1 + κ) := by
  have h1 : 0 < 1 + κ := by linarith
  have h1' : 1 + κ ≠ 0 := h1.ne'
  unfold kinkHeightInv
  rcases le_total 0 s with h | h
  · have heq : t₀ + s - κ / (1 + κ) * max s 0 - t₀ = s / (1 + κ) := by
      rw [max_eq_left h]
      field_simp
      ring
    rw [heq, max_eq_left h, max_eq_left (div_nonneg h h1.le)]
  · have heq : t₀ + s - κ / (1 + κ) * max s 0 - t₀ = s := by
      rw [max_eq_right h]
      ring
    rw [heq, max_eq_right h, zero_div]

theorem kinkHeight_kinkHeightInv (hκ : -1 < κ) (s : ℝ) :
    kinkHeight t₀ κ (kinkHeightInv t₀ κ s) = s := by
  have hm := max_kinkHeightInv_sub (t₀ := t₀) hκ s
  unfold kinkHeight
  rw [hm]
  unfold kinkHeightInv
  ring

theorem kinkHeightInv_kinkHeight (hκ : -1 < κ) (t : ℝ) :
    kinkHeightInv t₀ κ (kinkHeight t₀ κ t) = t := by
  have h1 : 0 < 1 + κ := by linarith
  have h1' : 1 + κ ≠ 0 := h1.ne'
  unfold kinkHeightInv
  rw [max_kinkHeight hκ t]
  unfold kinkHeight
  field_simp
  ring

theorem kinkHeight_surjective (hκ : -1 < κ) : Function.Surjective (kinkHeight t₀ κ) :=
  fun s => ⟨kinkHeightInv t₀ κ s, kinkHeight_kinkHeightInv hκ s⟩

theorem kinkHeight_nonneg_iff (hκ : -1 < κ) (t : ℝ) : 0 ≤ kinkHeight 0 κ t ↔ 0 ≤ t := by
  unfold kinkHeight
  rw [sub_zero]
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
    exact ⟨fun _ => h, fun _ => by nlinarith⟩
  · rw [max_eq_right h, mul_zero, add_zero]

theorem kinkHeight_eq_zero_iff (hκ : -1 < κ) (t : ℝ) : kinkHeight 0 κ t = 0 ↔ t = 0 := by
  unfold kinkHeight
  rw [sub_zero]
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
    constructor
    · intro h0
      have : (1 + κ) * t = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · linarith
      · exact h2
    · intro h0
      rw [h0]
      ring
  · rw [max_eq_right h, mul_zero, add_zero]

theorem kinkHeight_self (t₀ κ : ℝ) : kinkHeight t₀ κ t₀ = 0 := by
  simp [kinkHeight]

theorem kinkOffset_self (c₀ c₁ t₀ : ℝ) : kinkOffset c₀ c₁ t₀ t₀ = c₀ := by
  simp [kinkOffset]

end Kink

theorem isPiecewiseAffineOn_add_mul_max {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L₁ L₂ : E →ᵃ[ℝ] ℝ) (c : ℝ) :
    IsPiecewiseAffineOn (fun x => L₁ x + c * max (L₂ x) 0) univ := by
  have h2 : IsPiecewiseAffineOn (fun x => max (L₂ x) ((AffineMap.const ℝ E (0 : ℝ)) x)) univ :=
    (isPiecewiseAffineOn_of_affine L₂ isOpen_univ).max
      (isPiecewiseAffineOn_of_affine _ isOpen_univ)
  have h3 := (isPiecewiseAffineOn_of_affine L₁ isOpen_univ).add
    (h2.affine_comp (LinearMap.lsmul ℝ ℝ c).toAffineMap)
  refine h3.congr fun x _ => ?_
  simp [smul_eq_mul]

theorem isPLHomeomorphOn_kinkShear (c₀ c₁ t₀ : ℝ) {κ : ℝ} (hκ : -1 < κ) :
    IsPLHomeomorphOn (fun q : ℝ × ℝ => (q.1 + kinkOffset c₀ c₁ t₀ q.2, kinkHeight t₀ κ q.2))
      univ univ := by
  have h1 : 0 < 1 + κ := by linarith
  have h1' : 1 + κ ≠ 0 := h1.ne'
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 + kinkOffset c₀ c₁ t₀ q.2, kinkHeight t₀ κ q.2)
  let ψ : ℝ × ℝ → ℝ × ℝ := fun q =>
    (q.1 - c₀ - c₁ / (1 + κ) * max q.2 0, kinkHeightInv t₀ κ q.2)
  have hΦψ : ∀ q, Φ (ψ q) = q := by
    intro q
    refine Prod.ext ?_ (kinkHeight_kinkHeightInv hκ q.2)
    change q.1 - c₀ - c₁ / (1 + κ) * max q.2 0 +
      (c₀ + c₁ * max (kinkHeightInv t₀ κ q.2 - t₀) 0) = q.1
    rw [max_kinkHeightInv_sub hκ]
    ring
  have hψΦ : ∀ q, ψ (Φ q) = q := by
    intro q
    refine Prod.ext ?_ (kinkHeightInv_kinkHeight hκ q.2)
    change q.1 + (c₀ + c₁ * max (q.2 - t₀) 0) - c₀ -
      c₁ / (1 + κ) * max (kinkHeight t₀ κ q.2) 0 = q.1
    rw [max_kinkHeight hκ]
    field_simp
    ring
  have hbij : BijOn Φ univ univ :=
    ⟨mapsTo_univ _ _, (Function.LeftInverse.injective hψΦ).injOn,
      fun q _ => ⟨ψ q, mem_univ _, hΦψ q⟩⟩
  have hΦpl : IsPiecewiseAffineOn Φ univ := by
    have ha := isPiecewiseAffineOn_add_mul_max
      ((LinearMap.fst ℝ ℝ ℝ).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) c₀)
      ((LinearMap.snd ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) t₀) c₁
    have hb := isPiecewiseAffineOn_add_mul_max
      ((LinearMap.snd ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) t₀)
      ((LinearMap.snd ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) t₀) κ
    refine (ha.prod_mk hb).congr fun q _ => Prod.ext ?_ ?_ <;> simp [Φ, kinkOffset, kinkHeight]
    ring
  have hψpl : IsPiecewiseAffineOn ψ univ := by
    have ha := isPiecewiseAffineOn_add_mul_max
      ((LinearMap.fst ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) c₀)
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap (-(c₁ / (1 + κ)))
    have hb := isPiecewiseAffineOn_add_mul_max
      ((LinearMap.snd ℝ ℝ ℝ).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) t₀)
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap (-(κ / (1 + κ)))
    refine (ha.prod_mk hb).congr fun q _ => Prod.ext ?_ ?_ <;>
      simp [ψ, kinkHeightInv] <;> ring
  refine ⟨hbij, hΦpl, hψpl.congr fun q _ => ?_⟩
  have h := hbij.invOn_invFunOn.2 (mem_univ q)
  refine (Function.LeftInverse.injective hψΦ) ?_
  rw [h, hΦψ]

theorem isPiecewiseAffineOn_add_kinkOffset {a : ℝ × ℝ → ℝ} (ha : IsPiecewiseAffineOn a univ)
    (c₀ c₁ t₀ : ℝ) :
    IsPiecewiseAffineOn (fun q : ℝ × ℝ => a q + kinkOffset c₀ c₁ t₀ q.2) univ := by
  have hk := isPiecewiseAffineOn_add_mul_max (AffineMap.const ℝ (ℝ × ℝ) c₀)
    ((LinearMap.snd ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) t₀) c₁
  refine (ha.add hk).congr fun q _ => ?_
  simp [kinkOffset]

theorem exists_kinkGraph {a : ℝ × ℝ → ℝ} (ha : IsPiecewiseAffineOn a univ)
    (α₀ α₁ β₀ β₁ t₀ : ℝ) {κ : ℝ} (hκ : -1 < κ) :
    ∃ a' : ℝ × ℝ → ℝ, IsPiecewiseAffineOn a' univ ∧
      ∀ v t, a' (v + kinkOffset β₀ β₁ t₀ t, kinkHeight t₀ κ t) =
        a (v, t) + kinkOffset α₀ α₁ t₀ t := by
  have hΦ := isPLHomeomorphOn_kinkShear β₀ β₁ t₀ hκ
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 + kinkOffset β₀ β₁ t₀ q.2, kinkHeight t₀ κ q.2)
  set ψ := Function.invFunOn Φ univ
  have hg := isPiecewiseAffineOn_add_kinkOffset ha α₀ α₁ t₀
  have hc := hg.comp hΦ.isPiecewiseAffineOn_invFunOn
  rw [preimage_univ, inter_univ] at hc
  refine ⟨_, hc, fun v t => ?_⟩
  have hψ : ψ (Φ (v, t)) = (v, t) := hΦ.bijOn.invOn_invFunOn.1 (mem_univ _)
  change a (ψ (Φ (v, t))) + kinkOffset α₀ α₁ t₀ (ψ (Φ (v, t))).2 = _
  rw [hψ]

theorem dist_le_kinkBound_mul {α₁ β₁ κ r' tlo' : ℝ} (hκ : -1 < κ) (htlo' : -r' ≤ tlo')
    {w w₀ : ℝ × ℝ × ℝ}
    (hw : (w.1 + kinkOffset (-w₀.1) α₁ w₀.2.2 w.2.2, w.2.1 + kinkOffset (-w₀.2.1) β₁ w₀.2.2 w.2.2,
      kinkHeight w₀.2.2 κ w.2.2) ∈ blockBox r' tlo') :
    dist w w₀ ≤ kinkBound α₁ β₁ κ * r' := by
  have h1 : 0 < 1 + κ := by linarith
  have hu : |w.1 + kinkOffset (-w₀.1) α₁ w₀.2.2 w.2.2| ≤ r' := hw.1
  have hv : |w.2.1 + kinkOffset (-w₀.2.1) β₁ w₀.2.2 w.2.2| ≤ r' := hw.2.1
  have htlo : tlo' ≤ kinkHeight w₀.2.2 κ w.2.2 := hw.2.2.1
  have htr : kinkHeight w₀.2.2 κ w.2.2 ≤ r' := hw.2.2.2
  rw [abs_le] at hu hv
  set s := w.2.2 - w₀.2.2 with hs
  set m := max s 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  have hr' : 0 ≤ r' := by
    have := hu.1.trans hu.2
    linarith
  have hK1 : 0 ≤ 1 + 1 / (1 + κ) := by positivity
  have hsabs : |s| ≤ r' * (1 + 1 / (1 + κ)) := by
    have hk : kinkHeight w₀.2.2 κ w.2.2 = s + κ * m := rfl
    rw [hk] at htlo htr
    rcases le_total 0 s with h | h
    · have hme : m = s := max_eq_left h
      rw [hme] at htr
      have hs1 : s ≤ r' / (1 + κ) := by
        rw [le_div_iff₀ h1]
        linarith
      rw [abs_of_nonneg h]
      have : r' / (1 + κ) = r' * (1 / (1 + κ)) := by ring
      nlinarith
    · have hme : m = 0 := max_eq_right h
      rw [hme, mul_zero, add_zero] at htlo
      rw [abs_of_nonpos h]
      have : 0 ≤ r' * (1 / (1 + κ)) := by positivity
      nlinarith
  have hmle : m ≤ |s| := max_le (le_abs_self s) (abs_nonneg s)
  have hu' : |w.1 - w₀.1| ≤ r' + |α₁| * m := by
    have e : w.1 + kinkOffset (-w₀.1) α₁ w₀.2.2 w.2.2 = (w.1 - w₀.1) + α₁ * m := by
      simp only [kinkOffset, hm, hs]
      ring
    rw [e] at hu
    rw [abs_le]
    have := neg_abs_le α₁
    have := le_abs_self α₁
    constructor <;> nlinarith [abs_nonneg α₁]
  have hv' : |w.2.1 - w₀.2.1| ≤ r' + |β₁| * m := by
    have e : w.2.1 + kinkOffset (-w₀.2.1) β₁ w₀.2.2 w.2.2 = (w.2.1 - w₀.2.1) + β₁ * m := by
      simp only [kinkOffset, hm, hs]
      ring
    rw [e] at hv
    rw [abs_le]
    have := neg_abs_le β₁
    have := le_abs_self β₁
    constructor <;> nlinarith [abs_nonneg β₁]
  have hK : kinkBound α₁ β₁ κ * r' =
      r' + (1 + |α₁| + |β₁|) * (r' * (1 + 1 / (1 + κ))) := by
    unfold kinkBound
    ring
  have hsabs' : |w.2.2 - w₀.2.2| ≤ r' * (1 + 1 / (1 + κ)) := hsabs
  have hmle' : m ≤ r' * (1 + 1 / (1 + κ)) := hmle.trans hsabs
  rw [hK, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  have hA := abs_nonneg α₁
  have hB := abs_nonneg β₁
  have hX : 0 ≤ r' * (1 + 1 / (1 + κ)) := mul_nonneg hr' hK1
  have hαm : |α₁| * m ≤ |α₁| * (r' * (1 + 1 / (1 + κ))) := mul_le_mul_of_nonneg_left hmle' hA
  have hβm : |β₁| * m ≤ |β₁| * (r' * (1 + 1 / (1 + κ))) := mul_le_mul_of_nonneg_left hmle' hB
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith
  · nlinarith
  · nlinarith

end DifferentialGeometry.Topology.PiecewiseLinear
