/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def planeBoxClamp (s tl : ℝ) (w : ℝ × ℝ) : ℝ × ℝ :=
  (max (-s) (min s w.1), max tl (min s w.2))

theorem planeBoxClamp_mem {s tl : ℝ} (hs : 0 ≤ s) (htl : tl ≤ s) (w : ℝ × ℝ) :
    planeBoxClamp s tl w ∈ Icc (-s) s ×ˢ Icc tl s :=
  ⟨⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩,
    ⟨le_max_left _ _, max_le htl (min_le_left _ _)⟩⟩

theorem planeBoxClamp_eq_self {s tl : ℝ} {w : ℝ × ℝ} (hw : w ∈ Icc (-s) s ×ˢ Icc tl s) :
    planeBoxClamp s tl w = w := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
  simp only [planeBoxClamp, min_eq_right h2, max_eq_right h1, min_eq_right h4, max_eq_right h3]

theorem abs_max_min_sub_le (c d x y : ℝ) :
    |max c (min d x) - max c (min d y)| ≤ |x - y| := by
  have h := ((LipschitzWith.id.const_min d).const_max c).dist_le_mul x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id] using h

theorem lipschitzWith_planeBoxClamp (s tl : ℝ) : LipschitzWith 1 (planeBoxClamp s tl) := by
  have h1 := ((LipschitzWith.id.const_min s).const_max (-s)).comp
    (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have h2 := ((LipschitzWith.id.const_min s).const_max tl).comp
    (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))
  have h := h1.prodMk h2
  simp only [mul_one, max_self] at h
  exact h

theorem isPiecewiseAffineOn_planeBoxClamp (s tl : ℝ) :
    IsPiecewiseAffineOn (planeBoxClamp s tl) univ := by
  have hfst : IsPiecewiseAffineOn (fun w : ℝ × ℝ => w.1) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hsnd : IsPiecewiseAffineOn (fun w : ℝ × ℝ => w.2) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hc : ∀ c : ℝ, IsPiecewiseAffineOn (fun _ : ℝ × ℝ => c) univ := fun c =>
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) c) isOpen_univ
  exact ((hc (-s)).max ((hc s).min hfst)).prod_mk ((hc tl).max ((hc s).min hsnd))

theorem exists_graph_of_planeBoxClamp_perturbation {s tl La : ℝ} {Lt μ : NNReal}
    (hs : 0 ≤ s) (htl : tl ≤ s) (hLa : 0 ≤ La) {a eU : ℝ × ℝ → ℝ} {eP : ℝ × ℝ → ℝ × ℝ}
    (ha : IsPiecewiseAffineOn a univ)
    (haLip : ∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|)
    (haT : LipschitzOnWith Lt a (Icc (-s) s ×ˢ Icc tl s))
    (heU : IsPiecewiseAffineOn eU (Icc (-s) s ×ˢ Icc tl s))
    (heP : IsPiecewiseAffineOn eP (Icc (-s) s ×ˢ Icc tl s))
    (heULip : LipschitzOnWith μ eU (Icc (-s) s ×ˢ Icc tl s))
    (hePLip : LipschitzOnWith μ eP (Icc (-s) s ×ˢ Icc tl s)) (hμ : (μ : ℝ) ≤ 1 / 2) :
    ∃ a' : ℝ × ℝ → ℝ,
      IsPLHomeomorphOn (fun w => w + eP (planeBoxClamp s tl w)) univ univ ∧
        IsPiecewiseAffineOn a' univ ∧
        (∀ w ∈ Icc (-s) s ×ˢ Icc tl s, a' (w + eP w) = a w + eU w) ∧
        ∀ v v' t : ℝ, |a' (v, t) - a' (v', t)| ≤ (La + 2 * (La + Lt + 1) * μ) * |v - v'| := by
  set B : Set (ℝ × ℝ) := Icc (-s) s ×ˢ Icc tl s
  have hclB : ∀ w, planeBoxClamp s tl w ∈ B := planeBoxClamp_mem hs htl
  have hclid : ∀ w ∈ B, planeBoxClamp s tl w = w := fun w hw => planeBoxClamp_eq_self hw
  have hclPL := isPiecewiseAffineOn_planeBoxClamp s tl
  have hclset : univ ∩ planeBoxClamp s tl ⁻¹' B = univ := by
    ext w
    simp only [mem_inter_iff, mem_univ, mem_preimage, true_and, iff_true]
    exact hclB w
  set h : ℝ × ℝ → ℝ × ℝ := fun w => eP (planeBoxClamp s tl w) with hh
  have hhLip : LipschitzWith μ h := by
    refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    have h1 := hePLip.dist_le_mul _ (hclB w) _ (hclB w')
    have h2 := (lipschitzWith_planeBoxClamp s tl).dist_le_mul w w'
    simp only [NNReal.coe_one, one_mul] at h2
    calc dist (h w) (h w') ≤ μ * dist (planeBoxClamp s tl w) (planeBoxClamp s tl w') := h1
      _ ≤ μ * dist w w' := mul_le_mul_of_nonneg_left h2 μ.2
  have hhPL : IsPiecewiseAffineOn h univ := by
    have hc := heP.comp hclPL
    rw [hclset] at hc
    exact hc
  have hμ1 : μ < 1 := by
    have : (μ : ℝ) < 1 := by linarith
    exact_mod_cast this
  have hψ : IsPLHomeomorphOn (fun w => w + h w) univ univ :=
    isPLHomeomorphOn_id_add_of_lipschitz hhPL hhLip hμ1
  set ψi := Function.invFunOn (fun w => w + h w) univ
  have hψψi : ∀ z, ψi z + h (ψi z) = z := fun z => hψ.bijOn.invOn_invFunOn.2 (mem_univ z)
  have hψiψ : ∀ w, ψi (w + h w) = w := fun w => hψ.bijOn.invOn_invFunOn.1 (mem_univ w)
  have haPL : IsPiecewiseAffineOn (fun w => a (planeBoxClamp s tl w)) univ := by
    have hc := ha.comp hclPL
    rw [preimage_univ, inter_univ] at hc
    exact hc
  have heUPL : IsPiecewiseAffineOn (fun w => eU (planeBoxClamp s tl w)) univ := by
    have hc := heU.comp hclPL
    rw [hclset] at hc
    exact hc
  have hsumPL := haPL.add heUPL
  have ha'PL := hsumPL.comp hψ.isPiecewiseAffineOn_invFunOn
  rw [preimage_univ, inter_univ] at ha'PL
  refine ⟨fun z => a (planeBoxClamp s tl (ψi z)) + eU (planeBoxClamp s tl (ψi z)), hψ, ha'PL,
    ?_, ?_⟩
  · intro w hw
    have hhw : h w = eP w := by simp only [hh, hclid w hw]
    have hw' : ψi (w + eP w) = w := by rw [← hhw]; exact hψiψ w
    simp only [hw', hclid w hw]
  · intro v v' t
    set w₁ := ψi (v, t)
    set w₂ := ψi (v', t)
    have h1 : w₁ + h w₁ = (v, t) := hψψi (v, t)
    have h2 : w₂ + h w₂ = (v', t) := hψψi (v', t)
    have hdiff : w₁ - w₂ = ((v - v', 0) : ℝ × ℝ) - (h w₁ - h w₂) := by
      have e : w₁ - w₂ = (w₁ + h w₁) - (w₂ + h w₂) - (h w₁ - h w₂) := by abel
      rw [e, h1, h2]
      congr 1
      ext <;> simp
    have hhd : ‖h w₁ - h w₂‖ ≤ μ * ‖w₁ - w₂‖ := by
      simpa only [dist_eq_norm] using hhLip.dist_le_mul w₁ w₂
    have hnorm0 : ‖((v - v', 0) : ℝ × ℝ)‖ = |v - v'| := by
      simp [Prod.norm_def, Real.norm_eq_abs]
    set D := ‖w₁ - w₂‖
    have hD0 : 0 ≤ D := norm_nonneg _
    have hμ0 : (0 : ℝ) ≤ μ := μ.2
    have hD : D ≤ 2 * |v - v'| := by
      have htri := norm_sub_le ((v - v', 0) : ℝ × ℝ) (h w₁ - h w₂)
      rw [← hdiff, hnorm0] at htri
      nlinarith
    have hh1 : |(h w₁ - h w₂).1| ≤ μ * D := (norm_fst_le _).trans hhd
    have hh2 : |(h w₁ - h w₂).2| ≤ μ * D := (norm_snd_le _).trans hhd
    have hw1 : |w₁.1 - w₂.1| ≤ |v - v'| + μ * D := by
      have e : w₁.1 - w₂.1 = (v - v') - (h w₁ - h w₂).1 := by
        have := congrArg Prod.fst hdiff
        simpa using this
      rw [e]
      exact (abs_sub _ _).trans (add_le_add le_rfl hh1)
    have hw2 : |w₁.2 - w₂.2| ≤ μ * D := by
      have e : w₁.2 - w₂.2 = -(h w₁ - h w₂).2 := by
        have := congrArg Prod.snd hdiff
        simpa using this
      rw [e, abs_neg]
      exact hh2
    set c₁ := planeBoxClamp s tl w₁
    set c₂ := planeBoxClamp s tl w₂
    have hcc1 : |c₁.1 - c₂.1| ≤ |w₁.1 - w₂.1| := abs_max_min_sub_le (-s) s w₁.1 w₂.1
    have hcc2 : |c₁.2 - c₂.2| ≤ |w₁.2 - w₂.2| := abs_max_min_sub_le tl s w₁.2 w₂.2
    have hc₁B : c₁ ∈ B := hclB w₁
    have hc₂B : c₂ ∈ B := hclB w₂
    have hmixB : ((c₂.1, c₁.2) : ℝ × ℝ) ∈ B := ⟨hc₂B.1, hc₁B.2⟩
    have hdcc : dist c₁ c₂ ≤ D := by
      have := (lipschitzWith_planeBoxClamp s tl).dist_le_mul w₁ w₂
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using this
    have hA1 : |a (c₁.1, c₁.2) - a (c₂.1, c₁.2)| ≤ La * |c₁.1 - c₂.1| := haLip _ _ _
    have hA2 : |a (c₂.1, c₁.2) - a c₂| ≤ Lt * |c₁.2 - c₂.2| := by
      have hd : dist ((c₂.1, c₁.2) : ℝ × ℝ) c₂ = |c₁.2 - c₂.2| := by
        simp only [Prod.dist_eq, dist_self, Real.dist_eq]
        exact max_eq_right (abs_nonneg _)
      have := haT.dist_le_mul _ hmixB _ hc₂B
      rwa [Real.dist_eq, hd] at this
    have hE : |eU c₁ - eU c₂| ≤ μ * D := by
      have := heULip.dist_le_mul _ hc₁B _ hc₂B
      rw [Real.dist_eq] at this
      exact this.trans (mul_le_mul_of_nonneg_left hdcc hμ0)
    have hsplit : a c₁ + eU c₁ - (a c₂ + eU c₂) =
        (a (c₁.1, c₁.2) - a (c₂.1, c₁.2)) + (a (c₂.1, c₁.2) - a c₂) + (eU c₁ - eU c₂) := by
      simp only [Prod.mk.eta]
      ring
    have hLt0 : (0 : ℝ) ≤ Lt := Lt.2
    change |a c₁ + eU c₁ - (a c₂ + eU c₂)| ≤ _
    rw [hsplit]
    calc |(a (c₁.1, c₁.2) - a (c₂.1, c₁.2)) + (a (c₂.1, c₁.2) - a c₂) + (eU c₁ - eU c₂)|
        ≤ |a (c₁.1, c₁.2) - a (c₂.1, c₁.2)| + |a (c₂.1, c₁.2) - a c₂| + |eU c₁ - eU c₂| :=
          abs_add_three _ _ _
      _ ≤ La * (|v - v'| + μ * D) + Lt * (μ * D) + μ * D :=
          add_le_add (add_le_add (hA1.trans (mul_le_mul_of_nonneg_left (hcc1.trans hw1) hLa))
            (hA2.trans (mul_le_mul_of_nonneg_left (hcc2.trans hw2) hLt0))) hE
      _ = La * |v - v'| + (La + Lt + 1) * μ * D := by ring
      _ ≤ La * |v - v'| + (La + Lt + 1) * μ * (2 * |v - v'|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hD
            (mul_nonneg (by linarith : (0 : ℝ) ≤ La + Lt + 1) hμ0))
      _ = (La + 2 * (La + Lt + 1) * μ) * |v - v'| := by ring

end DifferentialGeometry.Topology.PiecewiseLinear
