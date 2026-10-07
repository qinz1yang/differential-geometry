/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Deformation

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.HorosphereProjection

open Hyperbolic HyperbolicAction HyperbolicBoundary AsymptoticRays
open Busemann BusemannCocycle LorentzExtremal

variable {n : ℕ}

theorem rayTo_val_exp (p : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    (rayTo p ξ t).val = Real.exp (-t) • p.val +
      (Real.sinh t / (-lorB p.val ξ.val)) • ξ.val := by
  have h := rayTo_neg_val p ξ (-t)
  simpa only [neg_neg, Real.sinh_neg, neg_div, neg_smul, sub_neg_eq_add] using h

theorem neg_lorB_rayTo (p : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    -lorB (rayTo p ξ t).val ξ.val = Real.exp (-t) * (-lorB p.val ξ.val) := by
  rw [rayTo_val_exp, lorB_add_left, lorB_smul_left, lorB_smul_left, ξ.is_null]
  ring

theorem busemann_rayTo (p : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    busemann ξ (rayTo p ξ t) = busemann ξ p - t := by
  rw [busemann, neg_lorB_rayTo,
    Real.log_mul (Real.exp_ne_zero _) (neg_lorB_upper_boundary_pos p ξ).ne', Real.log_exp]
  change -t + Real.log (-lorB p.val ξ.val) = Real.log (-lorB p.val ξ.val) - t
  ring

theorem rayTo_add (p : HUpper n) (ξ : BoundaryH n) (s t : ℝ) :
    rayTo (rayTo p ξ s) ξ t = rayTo p ξ (s + t) := by
  apply HUpper.ext
  rw [rayTo_val_exp (rayTo p ξ s) ξ t, neg_lorB_rayTo,
    rayTo_val_exp p ξ s, rayTo_val_exp p ξ (s + t)]
  let L := -lorB p.val ξ.val
  have hL : L ≠ 0 := (neg_lorB_upper_boundary_pos p ξ).ne'
  have hc : Real.exp (-t) * (Real.sinh s / L) +
      Real.sinh t / (Real.exp (-s) * L) = Real.sinh (s + t) / L := by
    simp only [Real.sinh_eq, Real.exp_add, Real.exp_neg]
    field_simp
    ring
  have he : Real.exp (-t) * Real.exp (-s) = Real.exp (-(s + t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp (-t) • (Real.exp (-s) • p.val + (Real.sinh s / L) • ξ.val) +
    (Real.sinh t / (Real.exp (-s) * L)) • ξ.val =
      Real.exp (-(s + t)) • p.val + (Real.sinh (s + t) / L) • ξ.val
  calc
    _ = (Real.exp (-t) * Real.exp (-s)) • p.val +
        (Real.exp (-t) * (Real.sinh s / L) + Real.sinh t / (Real.exp (-s) * L)) • ξ.val := by
          module
    _ = _ := by rw [he, hc]

theorem continuous_rayTo (ξ : BoundaryH n) :
    Continuous (fun z : HUpper n × ℝ => rayTo z.1 ξ z.2) := by
  apply StratumDeformation.continuous_of_val
  have hL : Continuous (fun z : HUpper n × ℝ => -lorB z.1.val ξ.val) :=
    (HyperbolicGeometry.continuous_neg_lorB_right ξ.val).comp (continuous_val.comp continuous_fst)
  have h := ((Real.continuous_exp.comp continuous_snd.neg).smul
    (continuous_val.comp continuous_fst)).add
      (((Real.continuous_sinh.comp continuous_snd).div hL
        (fun z => (neg_lorB_upper_boundary_pos z.1 ξ).ne')).smul (continuous_const (y := ξ.val)))
  exact h.congr (fun z => (rayTo_val_exp z.1 ξ z.2).symm)

theorem continuous_busemann (ξ : BoundaryH n) : Continuous (busemann ξ) :=
  ((HyperbolicGeometry.continuous_neg_lorB_right ξ.val).comp continuous_val).log
    (fun p => (neg_lorB_upper_boundary_pos p ξ).ne')

def retract (ξ : BoundaryH n) (c : ℝ) (p : HUpper n) : HUpper n :=
  rayTo p ξ (busemann ξ p - c)

theorem continuous_retract (ξ : BoundaryH n) (c : ℝ) : Continuous (retract ξ c) :=
  (continuous_rayTo ξ).comp (continuous_id.prodMk ((continuous_busemann ξ).sub continuous_const))

theorem retract_mem_horosphere (ξ : BoundaryH n) (c : ℝ) (p : HUpper n) :
    retract ξ c p ∈ horosphere ξ c := by
  change busemann ξ (rayTo p ξ (busemann ξ p - c)) = c
  rw [busemann_rayTo]
  ring

theorem retract_eq_self (ξ : BoundaryH n) (c : ℝ) {p : HUpper n}
    (hp : p ∈ horosphere ξ c) : retract ξ c p = p := by
  change busemann ξ p = c at hp
  simp only [retract, hp, sub_self, rayTo_zero]

theorem retract_rayTo (ξ : BoundaryH n) (c : ℝ) (p : HUpper n) (t : ℝ) :
    retract ξ c (rayTo p ξ t) = retract ξ c p := by
  simp only [retract, busemann_rayTo, rayTo_add]
  congr 1
  ring

theorem retract_smul (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n) (c : ℝ)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (p : HUpper n) :
    retract ξ c ((poMulAction hn).smul g p) =
      (poMulAction hn).smul g (retract ξ c p) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  change g • ξ = ξ at hfix
  change retract ξ c (g • p) = g • retract ξ c p
  have hb := po_busemann_smul hn g ξ p
  change busemann (g • ξ) (g • p) = busemann ξ p - Real.log (poConfFactor hn g ξ) at hb
  rw [hfix, hscale, Real.log_one, sub_zero] at hb
  have he := BoundaryExtension.po_smul_rayTo hn g p ξ (busemann ξ p - c)
  rw [hfix] at he
  simpa only [retract, hb] using he.symm

theorem continuous_height {m : ℕ} :
    Continuous (Horospherical.height : HUpper (m + 1) → ℝ) := by
  have hc : Continuous (fun p : HUpper (m + 1) => Horospherical.vHeight p.val) :=
    ((continuous_apply (Sum.inr 0)).comp continuous_val).sub
      ((continuous_apply (Sum.inl (Fin.last m))).comp continuous_val)
  exact hc.inv₀ (fun p => (Horospherical.vHeight_pos p).ne')

theorem continuous_horizontal {m : ℕ} :
    Continuous (Horospherical.horizontal : HUpper (m + 1) → Horospherical.Horizontal m) := by
  apply continuous_height.smul
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi_iff.mpr (fun i =>
    (continuous_apply (Sum.inl i.castSucc)).comp continuous_val)

end DifferentialGeometry.HorosphereProjection
