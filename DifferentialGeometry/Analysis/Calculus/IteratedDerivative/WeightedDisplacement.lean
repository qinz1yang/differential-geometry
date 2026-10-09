import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology NNReal

namespace DifferentialGeometry.Analysis

theorem norm_iteratedFDeriv_weighted_displacement_sub_le
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : Finset ι) {U : Set H} (hU : IsOpen U)
    {w : ι → H → ℝ} {Q : H → H →L[ℝ] H} {m : ℕ}
    (hw : ∀ i ∈ S, ContDiffOn ℝ m (w i) U)
    (hQ : ContDiffOn ℝ m Q U) (P : H →L[ℝ] H) (c : ι → H)
    {x : H} (hx : x ∈ U) {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (A B D R a : ℝ≥0)
    (hwjet : ∀ j, j ≤ m → (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) ≤ B * (r⁻¹) ^ j)
    (hQjet : ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => Q y - P) x‖ ≤ A * δ * (r⁻¹) ^ j)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ D * r)
    (hPc : ∀ i ∈ S, ‖P (c i)‖ ≤ a * δ * r)
    (hxnorm : ‖x‖ ≤ R * r) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n
        (fun z => Q z (z - ∑ i ∈ S, w i z • c i) - P z) x‖ ≤
          ((2 : ℝ) ^ n * A * (max (R : ℝ) 1 + D * B) + a * B) *
            δ * r * (r⁻¹) ^ n := by
  classical
  let μ : H → H := fun z => ∑ i ∈ S, w i z • c i
  let ν : H → H := fun z => ∑ i ∈ S, w i z • P (c i)
  let d : H → H := fun z => z - μ z
  let q : H → H →L[ℝ] H := fun z => Q z - P
  let σ : ℝ := r⁻¹
  let M : ℝ := max (R : ℝ) 1 + D * B
  have hσ : 0 ≤ σ := inv_nonneg.mpr hr.le
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hμ : ContDiffOn ℝ m μ U := ContDiffOn.sum (fun i hi => (hw i hi).smul_const (c i))
  have hν : ContDiffOn ℝ m ν U := ContDiffOn.sum (fun i hi => (hw i hi).smul_const (P (c i)))
  have hd : ContDiffOn ℝ m d U := contDiffOn_id.sub hμ
  have hq : ContDiffOn ℝ m q U := hQ.sub contDiffOn_const
  have hweighted (v : ι → H) (L : ℝ) (hL : 0 ≤ L)
      (hv : ∀ i ∈ S, ‖v i‖ ≤ L) (j : ℕ) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun z => ∑ i ∈ S, w i z • v i) x‖ ≤ L * B * σ ^ j := by
    have h : ‖iteratedFDeriv ℝ j (fun z => ∑ i ∈ S, w i z • v i) x‖ ≤
        ∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖ * ‖v i‖ := by
      rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
        (((hw i hi).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm)).smul_const (v i))]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have h := (ContinuousLinearMap.toSpanSingleton ℝ (v i)).norm_iteratedFDeriv_comp_left
        (((hw i hi).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm)) le_rfl
      simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.norm_toSpanSingleton, mul_comm] using h
    apply h.trans
    calc
      _ ≤ ∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖ * L := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hv i hi) (norm_nonneg _)
      _ = (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) * L := (Finset.sum_mul _ _ _).symm
      _ ≤ (B * σ ^ j) * L := mul_le_mul_of_nonneg_right (hwjet j hjm) hL
      _ = L * B * σ ^ j := by ring
  have hμjet (j : ℕ) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j μ x‖ ≤ D * B * r * σ ^ j := by
    calc
      _ ≤ (D * r) * B * σ ^ j := hweighted c (D * r) (by positivity) hc j hjm
      _ = D * B * r * σ ^ j := by ring
  have hνjet (j : ℕ) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j ν x‖ ≤ a * B * δ * r * σ ^ j := by
    calc
      _ ≤ (a * δ * r) * B * σ ^ j :=
        hweighted (fun i => P (c i)) (a * δ * r) (by positivity) hPc j hjm
      _ = a * B * δ * r * σ ^ j := by ring
  have hidjet (j : ℕ) :
      ‖iteratedFDeriv ℝ j (fun z : H => z) x‖ ≤ max (R : ℝ) 1 * r * σ ^ j := by
    cases j with
    | zero =>
      simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one]
      exact hxnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le)
    | succ k =>
      cases k with
      | zero =>
        rw [norm_iteratedFDeriv_one]
        change ‖fderiv ℝ id x‖ ≤ _
        rw [fderiv_id]
        have h := (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H)).trans
          (le_max_right (R : ℝ) 1)
        simpa only [σ, Nat.zero_add, pow_one, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] using h
      | succ k =>
        rw [← norm_iteratedFDeriv_fderiv]
        have hid : fderiv ℝ (fun z : H => z) = fun _ => ContinuousLinearMap.id ℝ H :=
          funext (fun _ => fderiv_id)
        rw [hid, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
        positivity
  have hdjet (j : ℕ) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j d x‖ ≤ M * r * σ ^ j := by
    change ‖iteratedFDeriv ℝ j (fun z => z - μ z) x‖ ≤ _
    rw [fun_iteratedFDeriv_sub_apply (f := fun z : H => z) contDiffAt_id
      ((hμ.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm))]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (fun z : H => z) x‖ + ‖iteratedFDeriv ℝ j μ x‖ := norm_sub_le _ _
      _ ≤ max (R : ℝ) 1 * r * σ ^ j + D * B * r * σ ^ j := add_le_add (hidjet j) (hμjet j hjm)
      _ = M * r * σ ^ j := by dsimp only [M]; ring
  have hidentity : (fun z => Q z (z - ∑ i ∈ S, w i z • c i) - P z) =
      (fun z => q z (d z) - ν z) := by
    funext z
    have hPμ : P (μ z) = ν z := by simp only [μ, ν, map_sum, map_smul]
    change Q z (z - μ z) - P z = (Q z - P) (z - μ z) - ν z
    simp only [sub_apply, map_sub, hPμ]
    abel
  intro n hnm
  have hprod : ‖iteratedFDeriv ℝ n (fun z => q z (d z)) x‖ ≤
      (2 : ℝ) ^ n * A * M * δ * r * σ ^ n := by
    have h := norm_iteratedFDerivWithin_clm_apply hq hd hU.uniqueDiffOn hx
      (n := n) (by exact_mod_cast hnm)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
    apply h.trans
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (A * M * δ * r * σ ^ n) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        calc
          _ ≤ (n.choose j : ℝ) * (A * δ * σ ^ j) * (M * r * σ ^ (n - j)) := by
            gcongr
            · exact hQjet j (hjn.trans hnm)
            · exact hdjet (n - j) ((Nat.sub_le n j).trans hnm)
          _ = ((n.choose j : ℝ) * A * M * δ * r) * (σ ^ j * σ ^ (n - j)) := by ring
          _ = (n.choose j : ℝ) * (A * M * δ * r * σ ^ n) := by
            rw [← pow_add, Nat.add_sub_of_le hjn]
            ring
      _ = (2 : ℝ) ^ n * A * M * δ * r * σ ^ n := by
        have hchoose : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [← Finset.sum_mul, hchoose]
        ring
  rw [hidentity, fun_iteratedFDeriv_sub_apply
    (((hq.clm_apply hd).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hnm))
    ((hν.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hnm))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun z => q z (d z)) x‖ + ‖iteratedFDeriv ℝ n ν x‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ n * A * M * δ * r * σ ^ n + a * B * δ * r * σ ^ n :=
      add_le_add hprod (hνjet n hnm)
    _ = ((2 : ℝ) ^ n * A * (max (R : ℝ) 1 + D * B) + a * B) * δ * r * (r⁻¹) ^ n := by
      dsimp only [M, σ]
      ring

end DifferentialGeometry.Analysis
