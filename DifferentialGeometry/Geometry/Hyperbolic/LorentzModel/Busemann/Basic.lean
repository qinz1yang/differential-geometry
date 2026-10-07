/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.SpecialFunctions.Hyperbolic.Asymptotics
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.AsymptoticRays

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter Topology

namespace DifferentialGeometry.Busemann

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicAction DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary DifferentialGeometry.HyperbolicGeometry DifferentialGeometry.AsymptoticRays
open DifferentialGeometry.HyperbolicConvexity
open Matrix

variable {n : ℕ}

theorem lorB_upper_boundary_neg (x : HUpper n) (ξ : BoundaryH n) :
    lorB x.val ξ.val < 0 := by
  have htv : tc ξ.val = 1 := ξ.tc_eq
  have hnull : lorB ξ.val ξ.val = 0 := ξ.is_null
  have hsv : sdot ξ.val ξ.val = 1 := by
    have h := hnull
    simp only [lorB] at h
    rw [htv] at h
    nlinarith
  have htx : 0 < tc x.val := x.future
  have hx2 : tc x.val ^ 2 = 1 + sdot x.val x.val := HUpper.tc_sq x
  have hcs : |sdot x.val ξ.val| ≤ Real.sqrt (sdot x.val x.val) := by
    have h := abs_sdot_le x.val ξ.val
    rw [hsv, Real.sqrt_one, mul_one] at h
    exact h
  have hsqrt : Real.sqrt (sdot x.val x.val) < tc x.val := by
    have h1 : sdot x.val x.val < tc x.val ^ 2 := by linarith [hx2]
    calc Real.sqrt (sdot x.val x.val) < Real.sqrt (tc x.val ^ 2) :=
          Real.sqrt_lt_sqrt (sdot_self_nonneg _) h1
      _ = tc x.val := Real.sqrt_sq (le_of_lt htx)
  have hsd : sdot x.val ξ.val < tc x.val :=
    lt_of_le_of_lt ((le_abs_self _).trans hcs) hsqrt
  have heq : lorB x.val ξ.val = sdot x.val ξ.val - tc x.val := by
    simp only [lorB]; rw [htv]; ring
  rw [heq]; linarith [hsd]

theorem neg_lorB_upper_boundary_pos (x : HUpper n) (ξ : BoundaryH n) :
    0 < - lorB x.val ξ.val :=
  neg_pos.mpr (lorB_upper_boundary_neg x ξ)

noncomputable def busemann (ξ : BoundaryH n) (x : HUpper n) : ℝ :=
  Real.log (- lorB x.val ξ.val)

theorem lorB_basepointH_boundary (ξ : BoundaryH n) :
    lorB (basepointH : HUpper n).val ξ.val = -1 := by
  have h1 : sdot (eTime : LorVec n) ξ.val = 0 := by
    simp [sdot, eTime_apply_inl]
  have hte : tc (eTime : LorVec n) = 1 := eTime_apply_inr
  change lorB eTime ξ.val = -1
  simp only [lorB]
  rw [h1, hte, ξ.tc_eq]
  ring

theorem busemann_basepointH (ξ : BoundaryH n) : busemann ξ basepointH = 0 := by
  change Real.log (- lorB (basepointH : HUpper n).val ξ.val) = 0
  rw [lorB_basepointH_boundary, neg_neg, Real.log_one]

theorem add_dirTo_eq (o : HUpper n) (ξ : BoundaryH n) :
    o.val + dirTo o ξ = (- lorB o.val ξ.val)⁻¹ • ξ.val := by
  have hlam : (- lorB o.val ξ.val) ≠ 0 := ne_of_gt (neg_lorB_upper_boundary_pos o ξ)
  change o.val + (- lorB o.val ξ.val)⁻¹ • (ξ.val + lorB o.val ξ.val • o.val) = _
  rw [smul_add, smul_smul]
  have h2 : (- lorB o.val ξ.val)⁻¹ * lorB o.val ξ.val = -1 := by
    have hc : lorB o.val ξ.val ≠ 0 := ne_of_lt (lorB_upper_boundary_neg o ξ)
    rw [inv_neg, neg_mul, inv_mul_cancel₀ hc]
  rw [h2, neg_one_smul]
  have : o.val + ((- lorB o.val ξ.val)⁻¹ • ξ.val + -o.val)
      = (o.val + -o.val) + (- lorB o.val ξ.val)⁻¹ • ξ.val := by abel
  rw [this, add_neg_cancel, zero_add]

theorem cosh_dist_rayTo (x o : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    Real.cosh (dist x (rayTo o ξ t))
      = Real.cosh t * (- lorB x.val o.val) + Real.sinh t * (- lorB x.val (dirTo o ξ)) := by
  have h1 : (1 : ℝ) ≤ - lorB x.val (rayTo o ξ t).val := HUpper.one_le_neg_lorB x _
  have h2 : Real.cosh (dist x (rayTo o ξ t)) = - lorB x.val (rayTo o ξ t).val := by
    change Real.cosh (Real.arcosh (- lorB x.val (rayTo o ξ t).val)) = _
    rw [Real.cosh_arcosh h1]
  rw [h2]
  change - lorB x.val (Real.cosh t • o.val + Real.sinh t • dirTo o ξ) = _
  rw [lorB_add_right, lorB_smul_right, lorB_smul_right]
  ring

theorem tendsto_dist_rayTo_sub (x o : HUpper n) (ξ : BoundaryH n) :
    Tendsto (fun t => dist x (rayTo o ξ t) - t) atTop
      (𝓝 (Real.log (- lorB x.val ξ.val) - Real.log (- lorB o.val ξ.val))) := by
  have hlam : 0 < - lorB o.val ξ.val := neg_lorB_upper_boundary_pos o ξ
  have hABeq : (- lorB x.val o.val) + (- lorB x.val (dirTo o ξ))
      = (- lorB o.val ξ.val)⁻¹ * (- lorB x.val ξ.val) := by
    have hadd : - lorB x.val o.val + - lorB x.val (dirTo o ξ)
        = - lorB x.val (o.val + dirTo o ξ) := by
      rw [lorB_add_right]; ring
    rw [hadd, add_dirTo_eq o ξ, lorB_smul_right]; ring
  have hAB : 0 < (- lorB x.val o.val) + (- lorB x.val (dirTo o ξ)) := by
    rw [hABeq]
    exact mul_pos (inv_pos.mpr hlam) (neg_lorB_upper_boundary_pos x ξ)
  have hlim := DifferentialGeometry.HyperbolicFunctions.tendsto_sub_log_of_cosh
    (- lorB x.val o.val) (- lorB x.val (dirTo o ξ)) hAB
    (fun t => dist_nonneg) (fun t => cosh_dist_rayTo x o ξ t)
  have hlog : Real.log ((- lorB o.val ξ.val)⁻¹ * (- lorB x.val ξ.val))
      = Real.log (- lorB x.val ξ.val) - Real.log (- lorB o.val ξ.val) := by
    rw [Real.log_mul (ne_of_gt (inv_pos.mpr hlam))
        (ne_of_gt (neg_lorB_upper_boundary_pos x ξ)), Real.log_inv]
    ring
  rw [hABeq, hlog] at hlim
  exact hlim

theorem busemann_lipschitz (ξ : BoundaryH n) (x y : HUpper n) :
    |busemann ξ x - busemann ξ y| ≤ dist x y := by
  have hb : Real.log (- lorB (basepointH : HUpper n).val ξ.val) = 0 := by
    rw [lorB_basepointH_boundary, neg_neg, Real.log_one]
  have hx : Tendsto (fun t => dist x (rayTo basepointH ξ t) - t) atTop (𝓝 (busemann ξ x)) := by
    have h := tendsto_dist_rayTo_sub x basepointH ξ
    rw [hb, sub_zero] at h
    exact h
  have hy : Tendsto (fun t => dist y (rayTo basepointH ξ t) - t) atTop (𝓝 (busemann ξ y)) := by
    have h := tendsto_dist_rayTo_sub y basepointH ξ
    rw [hb, sub_zero] at h
    exact h
  have hdiff : Tendsto (fun t => dist x (rayTo basepointH ξ t) - dist y (rayTo basepointH ξ t))
      atTop (𝓝 (busemann ξ x - busemann ξ y)) := by
    refine (hx.sub hy).congr fun t => ?_
    ring
  have habs : Tendsto
      (fun t => |dist x (rayTo basepointH ξ t) - dist y (rayTo basepointH ξ t)|)
      atTop (𝓝 |busemann ξ x - busemann ξ y|) := hdiff.abs
  have hbound : ∀ t, |dist x (rayTo basepointH ξ t) - dist y (rayTo basepointH ξ t)|
      ≤ dist x y := fun t => abs_dist_sub_le x y _
  exact le_of_tendsto habs (Filter.Eventually.of_forall hbound)

def horoball (ξ : BoundaryH n) (c : ℝ) : Set (HUpper n) :=
  { x | busemann ξ x ≤ c }

def horosphere (ξ : BoundaryH n) (c : ℝ) : Set (HUpper n) :=
  { x | busemann ξ x = c }

theorem mem_horoball (ξ : BoundaryH n) (c : ℝ) (x : HUpper n) :
    x ∈ horoball ξ c ↔ - lorB x.val ξ.val ≤ Real.exp c := by
  change Real.log (- lorB x.val ξ.val) ≤ c ↔ - lorB x.val ξ.val ≤ Real.exp c
  constructor
  · intro h
    have hpos := neg_lorB_upper_boundary_pos x ξ
    calc - lorB x.val ξ.val = Real.exp (Real.log (- lorB x.val ξ.val)) :=
          (Real.exp_log hpos).symm
      _ ≤ Real.exp c := Real.exp_le_exp.mpr h
  · intro h
    have hpos := neg_lorB_upper_boundary_pos x ξ
    have h2 : Real.log (- lorB x.val ξ.val) ≤ Real.log (Real.exp c) :=
      Real.log_le_log hpos h
    rwa [Real.log_exp] at h2

theorem basepointH_mem_horosphere (ξ : BoundaryH n) :
    basepointH ∈ horosphere ξ 0 :=
  busemann_basepointH ξ

theorem tc_pos_of_lorB_boundary_neg {v : LorVec n} (hv : lorB v v = -1) {ξ : BoundaryH n}
    (h : lorB v ξ.val < 0) : 0 < tc v := by
  have htv : tc ξ.val = 1 := ξ.tc_eq
  have hsv : sdot ξ.val ξ.val = 1 := by
    have h0 := ξ.is_null
    simp only [lorB] at h0
    rw [htv] at h0
    nlinarith
  have hvv : sdot v v = tc v ^ 2 - 1 := by
    have h0 := hv
    simp only [lorB] at h0
    nlinarith [h0, pow_two (tc v)]
  have hcs : |sdot v ξ.val| ≤ Real.sqrt (tc v ^ 2 - 1) := by
    have hh := abs_sdot_le v ξ.val
    rw [hsv, Real.sqrt_one, mul_one, hvv] at hh
    exact hh
  by_contra htc0
  have htc : tc v ≤ 0 := not_lt.mp htc0
  have hsqrt : Real.sqrt (tc v ^ 2 - 1) ≤ - tc v := by
    have h2 : Real.sqrt (tc v ^ 2 - 1) ≤ Real.sqrt (tc v ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos htc] at h2
    exact h2
  have hsd : tc v ≤ sdot v ξ.val := by
    have hle := (abs_le.mp hcs).1
    linarith [hle, hsqrt]
  have hlor : lorB v ξ.val = sdot v ξ.val - tc v := by
    simp only [lorB]; rw [htv]; ring
  rw [hlor] at h
  linarith [hsd]

theorem busemann_smul_of_fix (g : LorGrp n) (ξ : BoundaryH n)
    (hfix : matOf g *ᵥ ξ.val = ξ.val) (x : HUpper n) :
    busemann ξ (g • x) = busemann ξ x := by
  have hunit : lorB (matOf g *ᵥ x.val) (matOf g *ᵥ x.val) = -1 := by
    rw [lorB_matOf_mulVec]; exact x.is_unit
  have hpair : lorB (matOf g *ᵥ x.val) ξ.val = lorB x.val ξ.val := by
    conv_lhs => rw [← hfix]
    rw [lorB_matOf_mulVec]
  have htc : 0 < tc (matOf g *ᵥ x.val) :=
    tc_pos_of_lorB_boundary_neg hunit (hpair ▸ lorB_upper_boundary_neg x ξ)
  have hup : upperize (matOf g *ᵥ x.val) = matOf g *ᵥ x.val := by
    unfold upperize; rw [ite_eq_left htc]
  change Real.log (- lorB (g • x).val ξ.val) = Real.log (- lorB x.val ξ.val)
  rw [smul_val, hup, hpair]

theorem smul_mem_horoball_of_fix {g : LorGrp n} {ξ : BoundaryH n}
    (hfix : matOf g *ᵥ ξ.val = ξ.val) {c : ℝ} {x : HUpper n} (hx : x ∈ horoball ξ c) :
    g • x ∈ horoball ξ c := by
  change busemann ξ (g • x) ≤ c
  rw [busemann_smul_of_fix g ξ hfix x]
  exact hx

theorem mem_horoball_geodFromTo (ξ : BoundaryH n) {c : ℝ} {x y : HUpper n}
    (hx : x ∈ horoball ξ c) (hy : y ∈ horoball ξ c) (hd : x ≠ y) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ dist x y) :
    geodFromTo x y hd t ∈ horoball ξ c := by
  have hxm : - lorB x.val ξ.val ≤ Real.exp c := (mem_horoball ξ c x).mp hx
  have hym : - lorB y.val ξ.val ≤ Real.exp c := (mem_horoball ξ c y).mp hy
  rw [mem_horoball]
  set T := dist x y with hTdef
  set a := lorB x.val ξ.val with hadef
  set b := lorB (dirVec x y) ξ.val with hbdef
  have hg : lorB (geodFromTo x y hd t).val ξ.val = Real.cosh t * a + Real.sinh t * b := by
    change lorB (Real.cosh t • x.val + Real.sinh t • dirVec x y) ξ.val = _
    rw [lorB_add_left, lorB_smul_left, lorB_smul_left]
  have hg0 : - a ≤ Real.exp c := hxm
  have hgT : Real.cosh T * a + Real.sinh T * b = lorB y.val ξ.val := by
    have h1 : lorB (geodFromTo x y hd T).val ξ.val = Real.cosh T * a + Real.sinh T * b := by
      change lorB (Real.cosh T • x.val + Real.sinh T • dirVec x y) ξ.val = _
      rw [lorB_add_left, lorB_smul_left, lorB_smul_left]
    rw [geodFromTo_dist hd] at h1
    exact h1.symm
  have hgTm : - Real.exp c ≤ Real.cosh T * a + Real.sinh T * b := by
    rw [hgT]; linarith [hym]
  have hid : Real.sinh T * (Real.cosh t * a + Real.sinh t * b)
      = Real.sinh (T - t) * a + Real.sinh t * (Real.cosh T * a + Real.sinh T * b) := by
    rw [Real.sinh_sub]; ring
  have hTpos : 0 < T := by rw [hTdef]; exact dist_pos.mpr hd
  have hsinhT : 0 < Real.sinh T := Real.sinh_pos_iff.mpr hTpos
  have hst0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht0
  have hsTt : 0 ≤ Real.sinh (T - t) := Real.sinh_nonneg_iff.mpr (by linarith [htT])
  have hsum : Real.sinh (T - t) + Real.sinh t ≤ Real.sinh T :=
    DifferentialGeometry.HyperbolicFunctions.sinh_sub_add_sinh_le (le_of_lt hTpos) ht0 (by rwa [hTdef])
  have h1 : Real.sinh (T - t) * a ≥ Real.sinh (T - t) * (- Real.exp c) :=
    mul_le_mul_of_nonneg_left (by linarith [hg0]) hsTt
  have h2 : Real.sinh t * (Real.cosh T * a + Real.sinh T * b) ≥ Real.sinh t * (- Real.exp c) :=
    mul_le_mul_of_nonneg_left (by linarith [hgTm]) hst0
  have hec : 0 ≤ Real.exp c := (Real.exp_pos c).le
  have hbound : Real.sinh T * (- Real.exp c)
      ≤ Real.sinh (T - t) * (- Real.exp c) + Real.sinh t * (- Real.exp c) := by
    have h3 : (Real.sinh (T - t) + Real.sinh t) * (- Real.exp c)
        ≥ Real.sinh T * (- Real.exp c) :=
      mul_le_mul_of_nonpos_right hsum (by linarith [hec])
    calc Real.sinh T * (- Real.exp c)
        ≤ (Real.sinh (T - t) + Real.sinh t) * (- Real.exp c) := h3
      _ = Real.sinh (T - t) * (- Real.exp c) + Real.sinh t * (- Real.exp c) := by ring
  have hkey : Real.sinh T * (- Real.exp c) ≤ Real.sinh T * (Real.cosh t * a + Real.sinh t * b) := by
    rw [hid]; linarith [h1, h2, hbound]
  have hfinal : - Real.exp c ≤ Real.cosh t * a + Real.sinh t * b :=
    le_of_mul_le_mul_left (by rw [mul_comm] at hkey ⊢; exact hkey) hsinhT
  rw [hg]; linarith [hfinal]

end DifferentialGeometry.Busemann
