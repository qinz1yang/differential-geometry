/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BranchCollarPrism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

noncomputable def boundaryDrop (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (n : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (LinearMap.id - ℓ.smulRight n).toAffineMap

theorem boundaryDrop_apply (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (n w : EuclideanSpace ℝ (Fin 3)) : boundaryDrop ℓ n w = w - ℓ w • n := rfl

theorem apply_boundaryDrop {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ}
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ℓ n = 1) (w : EuclideanSpace ℝ (Fin 3)) :
    ℓ (boundaryDrop ℓ n w) = 0 := by
  rw [boundaryDrop_apply, map_sub, map_smul, hn, smul_eq_mul, mul_one, sub_self]

theorem boundaryDrop_eq_self {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ}
    {n w : EuclideanSpace ℝ (Fin 3)} (hw : ℓ w = 0) : boundaryDrop ℓ n w = w := by
  rw [boundaryDrop_apply, hw, zero_smul, sub_zero]

noncomputable def arcLevel (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (c : ℝ)
    (b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) × ℝ → ℝ :=
  fun z => min (c * |1 - z.2|) (-(ℓ (b z.1)))

noncomputable def levelPrism (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (n : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    (b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun z => Φ (z.1, planarClamp z.2) +
    (-(ℓ (Φ (z.1, planarClamp z.2)) + arcLevel ℓ c b z)) • n

theorem arcLevel_nonneg {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {c : ℝ} (hc : 0 ≤ c)
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {z : EuclideanSpace ℝ (Fin 2) × ℝ} (hb : ℓ (b z.1) ≤ 0) : 0 ≤ arcLevel ℓ c b z :=
  le_min (mul_nonneg hc (abs_nonneg _)) (neg_nonneg.mpr hb)

theorem arcLevel_le {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {c : ℝ}
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {z : EuclideanSpace ℝ (Fin 2) × ℝ} (hb : -c ≤ ℓ (b z.1)) : arcLevel ℓ c b z ≤ c :=
  (min_le_right _ _).trans (neg_le.mpr hb)

theorem apply_levelPrism {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ}
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ℓ n = 1) (c : ℝ)
    (b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 2) × ℝ) :
    ℓ (levelPrism ℓ n c b Φ z) = -(arcLevel ℓ c b z) := by
  rw [levelPrism, map_add, map_smul, hn, smul_eq_mul, mul_one]
  ring

theorem levelPrism_eq_of_add_eq_zero {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ}
    {n : EuclideanSpace ℝ (Fin 3)} {c : ℝ}
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {z : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : ℓ (Φ (z.1, planarClamp z.2)) + arcLevel ℓ c b z = 0) :
    levelPrism ℓ n c b Φ z = Φ (z.1, planarClamp z.2) := by
  rw [levelPrism, h, neg_zero, zero_smul, add_zero]

theorem levelPrism_eq_boundaryDrop_sub (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (n : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    (b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 2) × ℝ) :
    levelPrism ℓ n c b Φ z =
      boundaryDrop ℓ n (Φ (z.1, planarClamp z.2)) - arcLevel ℓ c b z • n := by
  rw [levelPrism, boundaryDrop_apply]
  module

theorem isPiecewiseAffineOn_fst_prod {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPolyhedron J) :
    IsPiecewiseAffineOn (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => z.1)
      (J ×ˢ Icc (0 : ℝ) 1) :=
  ((isPiecewiseAffineOn_of_affine
    (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).toAffineMap
    isOpen_univ).congr (fun _ _ => rfl)).mono_of_isPolyhedron
      (hJ.prod isHPolytope_Icc.isPolyhedron) (subset_univ _)

theorem isPiecewiseAffineOn_snd_prod {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPolyhedron J) :
    IsPiecewiseAffineOn (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => z.2)
      (J ×ˢ Icc (0 : ℝ) 1) :=
  ((isPiecewiseAffineOn_of_affine
    (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).toAffineMap
    isOpen_univ).congr (fun _ _ => rfl)).mono_of_isPolyhedron
      (hJ.prod isHPolytope_Icc.isPolyhedron) (subset_univ _)

theorem isPiecewiseAffineOn_arcLevel {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPolyhedron J)
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} (hb : IsPiecewiseAffineOn b J)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (c : ℝ) :
    IsPiecewiseAffineOn (arcLevel ℓ c b) (J ×ˢ Icc (0 : ℝ) 1) := by
  have hfst := isPiecewiseAffineOn_fst_prod hJ
  have hsnd := isPiecewiseAffineOn_snd_prod hJ
  have hone : IsPiecewiseAffineOn
      (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => 1 - z.2) (J ×ˢ Icc (0 : ℝ) 1) :=
    (hsnd.affine_comp (AffineMap.const ℝ ℝ (1 : ℝ) + (-AffineMap.id ℝ ℝ))).congr
      (fun _ _ => by simp [sub_eq_add_neg])
  have hscale : IsPiecewiseAffineOn
      (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => c * |1 - z.2|) (J ×ˢ Icc (0 : ℝ) 1) :=
    (hone.abs.affine_comp ((c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap)).congr
      (fun _ _ => by simp [smul_eq_mul])
  have hcomp : IsPiecewiseAffineOn
      (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => b z.1) (J ×ˢ Icc (0 : ℝ) 1) := by
    have h := hb.comp hfst
    have hset : (J ×ˢ Icc (0 : ℝ) 1) ∩ (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => z.1) ⁻¹' J
        = J ×ˢ Icc (0 : ℝ) 1 := inter_eq_left.mpr (fun _ hz => hz.1)
    rw [hset] at h
    exact h
  have hdepth : IsPiecewiseAffineOn
      (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => -(ℓ (b z.1))) (J ×ˢ Icc (0 : ℝ) 1) :=
    ((hcomp.affine_comp ℓ.toAffineMap).affine_comp (-AffineMap.id ℝ ℝ)).congr
      (fun _ _ => rfl)
  exact hscale.min hdepth

theorem isPiecewiseAffineOn_levelPrism {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPolyhedron J)
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} (hb : IsPiecewiseAffineOn b J)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (n : EuclideanSpace ℝ (Fin 3)) (c : ℝ)
    {Φ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hΦ : IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) 1)) :
    IsPiecewiseAffineOn (levelPrism ℓ n c b Φ) (J ×ˢ Icc (0 : ℝ) 1) := by
  have harc := isPiecewiseAffineOn_arcLevel hJ hb ℓ c
  have hcoef : IsPiecewiseAffineOn
      (fun z => (-(ℓ (Φ z) + arcLevel ℓ c b z)) • n) (J ×ˢ Icc (0 : ℝ) 1) :=
    ((((hΦ.affine_comp ℓ.toAffineMap).add harc).affine_comp
      (-AffineMap.id ℝ ℝ)).affine_comp
        (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight n).toAffineMap)).congr (fun _ _ => rfl)
  refine (hΦ.add hcoef).congr ?_
  rintro ⟨y, t⟩ ⟨-, ht0, ht1⟩
  have hclamp : planarClamp t = t := planarClamp_eq_self ht0 ht1
  simp only [levelPrism, hclamp]

theorem exists_levelPrism_over_arc
    {J : Set (EuclideanSpace ℝ (Fin 2))} {θ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J)
    {b : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} (hb : IsPiecewiseAffineOn b J)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (n : EuclideanSpace ℝ (Fin 3)) (hn : ℓ n = 1)
    {c : ℝ} (hc : 0 < c)
    (hle : ∀ z ∈ J, ℓ (b z) ≤ 0) (hge : ∀ z ∈ J, -c ≤ ℓ (b z))
    (hend0 : ℓ (b (θ 0)) = 0) (hend1 : ℓ (b (θ 1)) = 0)
    {S T : Set (EuclideanSpace ℝ (Fin 3))} (hS : Convex ℝ S) (hbS : MapsTo b J S)
    (hdS : MapsTo (fun z => boundaryDrop ℓ n (b z)) J S)
    (hslab : ∀ v ∈ S, ∀ r : ℝ, 0 ≤ r → r ≤ c → boundaryDrop ℓ n v - r • n ∈ T) :
    ∃ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3),
      IsPiecewiseAffineOn Ψ (J ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ J, ∀ s : ℝ, Ψ (z, s) ∈ T) ∧
      (∀ z ∈ J, Ψ (z, 0) = b z) ∧
      (∀ z ∈ J, Ψ (z, 1) = boundaryDrop ℓ n (b z)) ∧
      (∀ s : ℝ, Ψ (θ 0, s) = b (θ 0)) ∧ (∀ s : ℝ, Ψ (θ 1, s) = b (θ 1)) ∧
      (∀ z ∈ J, ∀ s : ℝ, ℓ (Ψ (z, s)) = 0 → ℓ (b z) = 0 ∨ s = 1) := by
  have hJ : IsPolyhedron J :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hθ).isPolyhedron
  obtain ⟨Φ, hPA, hbot, htop, hl, hr, himg⟩ :=
    exists_isPiecewiseAffineOn_prism_arc_landing hθ hb (boundaryDrop ℓ n)
      (boundaryDrop_eq_self hend0) (boundaryDrop_eq_self hend1)
  have hΦS : MapsTo Φ (J ×ˢ Icc (0 : ℝ) 1) S := himg S hS hbS hdS
  have hmem : ∀ z ∈ J, ∀ s : ℝ,
      ((z, planarClamp s) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ J ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz s => ⟨hz, planarClamp_nonneg s, planarClamp_le_one s⟩
  refine ⟨levelPrism ℓ n c b Φ, isPiecewiseAffineOn_levelPrism hJ hb ℓ n c hPA,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz s
    rw [levelPrism_eq_boundaryDrop_sub]
    exact hslab _ (hΦS (hmem z hz s)) _ (arcLevel_nonneg hc.le (hle z hz))
      (arcLevel_le (hge z hz))
  · intro z hz
    have hcl : planarClamp (0 : ℝ) = 0 := planarClamp_eq_self le_rfl zero_le_one
    refine (levelPrism_eq_of_add_eq_zero ?_).trans ?_
    · have hlv : arcLevel ℓ c b ((z, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ)
          = -(ℓ (b z)) := by
        have : |(1 : ℝ) - 0| = 1 := by norm_num
        simp only [arcLevel, this, mul_one]
        exact min_eq_right (neg_le.mpr (hge z hz))
      simp only [hcl, hlv, hbot z hz]
      ring
    · simp only [hcl]
      exact hbot z hz
  · intro z hz
    have hcl : planarClamp (1 : ℝ) = 1 := planarClamp_eq_self zero_le_one le_rfl
    refine (levelPrism_eq_of_add_eq_zero ?_).trans ?_
    · have hlv : arcLevel ℓ c b ((z, (1 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) = 0 := by
        have : |(1 : ℝ) - 1| = 0 := by norm_num
        simp only [arcLevel, this, mul_zero]
        exact min_eq_left (neg_nonneg.mpr (hle z hz))
      simp only [hcl, hlv, htop z hz, apply_boundaryDrop hn]
      ring
    · simp only [hcl]
      exact htop z hz
  · intro s
    have hΦe := hl (planarClamp s) ⟨planarClamp_nonneg s, planarClamp_le_one s⟩
    refine (levelPrism_eq_of_add_eq_zero ?_).trans ?_
    · have hlv : arcLevel ℓ c b ((θ 0, s) : EuclideanSpace ℝ (Fin 2) × ℝ) = 0 := by
        simp only [arcLevel, hend0, neg_zero]
        exact min_eq_right (mul_nonneg hc.le (abs_nonneg _))
      simp only [hlv, hΦe, hend0]
      ring
    · exact hΦe
  · intro s
    have hΦe := hr (planarClamp s) ⟨planarClamp_nonneg s, planarClamp_le_one s⟩
    refine (levelPrism_eq_of_add_eq_zero ?_).trans ?_
    · have hlv : arcLevel ℓ c b ((θ 1, s) : EuclideanSpace ℝ (Fin 2) × ℝ) = 0 := by
        simp only [arcLevel, hend1, neg_zero]
        exact min_eq_right (mul_nonneg hc.le (abs_nonneg _))
      simp only [hlv, hΦe, hend1]
      ring
    · exact hΦe
  · intro z hz s hzero
    rw [apply_levelPrism hn, neg_eq_zero] at hzero
    have hnn : (0 : ℝ) ≤ c * |1 - s| := mul_nonneg hc.le (abs_nonneg _)
    have hnd : (0 : ℝ) ≤ -(ℓ (b z)) := neg_nonneg.mpr (hle z hz)
    rcases le_total (c * |1 - s|) (-(ℓ (b z))) with hcase | hcase
    · right
      have h0 : c * |1 - s| = 0 := by
        rw [arcLevel, min_eq_left hcase] at hzero
        exact hzero
      have habs : |1 - s| = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hc.ne'
        · exact h
      have : (1 : ℝ) - s = 0 := abs_eq_zero.mp habs
      linarith
    · left
      have h0 : -(ℓ (b z)) = 0 := by
        rw [arcLevel, min_eq_right hcase] at hzero
        exact hzero
      linarith [neg_eq_zero.mp h0]

open Classical in
theorem exists_collarExtension_image_inter_boundary_of_levelPrism_over_arc
    {D : SingularTwoCell M} {BdM N : Set M} {hslide : M → M}
    {P A B J Δ' : Set (EuclideanSpace ℝ (Fin 2))} {θ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (n : EuclideanSpace ℝ (Fin 3)) (hn : ℓ n = 1)
    (hBd : ∀ y ∈ ec.target, ec.symm y ∈ BdM ↔ ℓ y = 0)
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, hslide x ∈ BdM → x ∈ BdM)
    (hgpl : IsPLOn 2 3 (P.piecewise (hslide ∘ D) D) D.domain)
    (hΔ'ball : IsPLBall 2 Δ') (hsubint : D.domain ⊆ interior Δ')
    (hρid : ∀ x ∈ D.domain, ρ x = x)
    (hρfr : MapsTo ρ (Δ' \ D.domain) (frontier D.domain))
    (hρsurj : frontier D.domain ⊆ ρ '' frontier Δ')
    (hτ0 : ∀ x ∈ D.domain, τ x = 0) (hτ1 : ∀ x ∈ frontier Δ', τ x = 1)
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J)
    (hJfr : J ⊆ frontier D.domain)
    (hinj : InjOn (P.piecewise (hslide ∘ D) D) J)
    (hqsrc : MapsTo (P.piecewise (hslide ∘ D) D) J ec.source)
    (hfr : ∀ z ∈ frontier D.domain, z ∉ J → P.piecewise (hslide ∘ D) D z ∈ BdM)
    (hApoly : IsPolyhedron A) (hBpoly : IsPolyhedron B)
    (hunion : A ∪ B = Δ' \ interior D.domain)
    (hρA : IsPiecewiseAffineOn ρ A) (hτA : IsPiecewiseAffineOn τ A)
    (hρB : IsPiecewiseAffineOn ρ B)
    (hmapA : MapsTo (fun x => (ρ x, τ x)) A (J ×ˢ Icc (0 : ℝ) 1))
    (hmapB : MapsTo ρ B (frontier D.domain))
    (hBbd : ∀ x ∈ B, P.piecewise (hslide ∘ D) D (ρ x) ∈ BdM)
    {c : ℝ} (hc : 0 < c)
    (hle : ∀ z ∈ J, ℓ (ec (P.piecewise (hslide ∘ D) D z)) ≤ 0)
    (hge : ∀ z ∈ J, -c ≤ ℓ (ec (P.piecewise (hslide ∘ D) D z)))
    (hend0 : ℓ (ec (P.piecewise (hslide ∘ D) D (θ 0))) = 0)
    (hend1 : ℓ (ec (P.piecewise (hslide ∘ D) D (θ 1))) = 0)
    (hends : ∀ z ∈ J, ℓ (ec (P.piecewise (hslide ∘ D) D z)) = 0 → z = θ 0 ∨ z = θ 1)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : Convex ℝ S)
    (hbS : MapsTo (fun z => ec (P.piecewise (hslide ∘ D) D z)) J S)
    (hdS : MapsTo (fun z => boundaryDrop ℓ n (ec (P.piecewise (hslide ∘ D) D z))) J S)
    (hslab : ∀ v ∈ S, ∀ r : ℝ, 0 ≤ r → r ≤ c → boundaryDrop ℓ n v - r • n ∈ ec.target) :
    ∃ G : SingularTwoCell M, G.domain = Δ' ∧
      EqOn G (P.piecewise (hslide ∘ D) D) D.domain ∧
      Set.range G.boundary ⊆ BdM ∧
      G '' G.domain ∩ BdM = Set.range G.boundary := by
  classical
  have hJ : IsPolyhedron J :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hθ).isPolyhedron
  have hqJ : IsPLOn 2 3 (P.piecewise (hslide ∘ D) D) J :=
    hgpl.mono_of_isPolyhedron hJ (hJfr.trans D.frontier_subset_domain)
  have hb : IsPiecewiseAffineOn
      (fun z => ec (P.piecewise (hslide ∘ D) D z)) J :=
    ((isPLOn_iff_isPiecewiseAffineOn_comp_chart ec hec hqsrc).mp hqJ).congr (fun _ _ => rfl)
  obtain ⟨Ψ, hΨ, hΨT, hbot, htop, hl, hr, hzero⟩ :=
    exists_levelPrism_over_arc hθ hb ℓ n hn hc hle hge hend0 hend1 hS hbS hdS hslab
  have hΨmaps : MapsTo Ψ (J ×ˢ Icc (0 : ℝ) 1) ec.target := by
    rintro ⟨y, t⟩ ⟨hy, -⟩
    exact hΨT y hy t
  have hsrcmem : ∀ z ∈ J, ec (P.piecewise (hslide ∘ D) D z) ∈ ec.target :=
    fun z hz => ec.map_source (hqsrc hz)
  have hleft : ∀ z ∈ J, ec.symm (ec (P.piecewise (hslide ∘ D) D z))
      = P.piecewise (hslide ∘ D) D z := fun z hz => ec.left_inv (hqsrc hz)
  have hedge : ∀ z ∈ J, ℓ (ec (P.piecewise (hslide ∘ D) D z)) = 0 → ∀ s : ℝ,
      Ψ (z, s) = ec (P.piecewise (hslide ∘ D) D z) := by
    intro z hz hz0 s
    rcases hends z hz hz0 with rfl | rfl
    · exact hl s
    · exact hr s
  refine exists_collarExtension_image_inter_boundary_of_prism_over_arc ec hec hbdpre hDN hrefl
    hgpl hΔ'ball hsubint hρid hρfr hρsurj hτ0 hτ1 hinj hqsrc ?_ hfr hApoly hBpoly hunion
    hρA hτA hρB hmapA hmapB hBbd hΨ hΨmaps hbot ?_ ?_
  · intro z hz hzbd s
    have hz0 : ℓ (ec (P.piecewise (hslide ∘ D) D z)) = 0 :=
      (hBd _ (hsrcmem z hz)).mp (by rw [hleft z hz]; exact hzbd)
    rw [hedge z hz hz0 s, hleft z hz]
  · intro z hz
    refine (hBd _ (hΨT z hz 1)).mpr ?_
    rw [htop z hz]
    exact apply_boundaryDrop hn _
  · intro z hz s hmem
    have hz0 : ℓ (Ψ (z, s)) = 0 := (hBd _ (hΨT z hz s)).mp hmem
    rcases hzero z hz s hz0 with h | h
    · left
      have := (hBd _ (hsrcmem z hz)).mpr h
      rwa [hleft z hz] at this
    · exact Or.inr h

end DifferentialGeometry.Topology.PiecewiseLinear
