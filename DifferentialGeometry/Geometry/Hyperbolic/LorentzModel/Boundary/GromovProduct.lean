/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.CoarseGeometry.PseudoIsometry
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Interpolation
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Metric
import Mathlib.Algebra.Order.Ring.Star

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter

namespace DifferentialGeometry.GromovBoundary

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicAction DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary DifferentialGeometry.BoundaryTopology
open DifferentialGeometry.HyperbolicConvexity DifferentialGeometry.HyperbolicGeometry

variable {n : ℕ}

noncomputable def gromovProduct (o x y : HUpper n) : ℝ :=
  (dist o x + dist o y - dist x y) / 2

theorem gromovProduct_comm (o x y : HUpper n) :
    gromovProduct o x y = gromovProduct o y x := by
  unfold gromovProduct
  rw [dist_comm x y]
  ring

theorem gromovProduct_nonneg (o x y : HUpper n) : 0 ≤ gromovProduct o x y := by
  unfold gromovProduct
  have h := dist_triangle x o y
  rw [dist_comm x o] at h
  linarith [h]

theorem gromovProduct_le_dist_left (o x y : HUpper n) :
    gromovProduct o x y ≤ dist o x := by
  unfold gromovProduct
  have h := dist_triangle o x y
  linarith [h]

theorem gromovProduct_le_dist_right (o x y : HUpper n) :
    gromovProduct o x y ≤ dist o y := by
  rw [gromovProduct_comm]
  exact gromovProduct_le_dist_left o y x

theorem gromovProduct_le_dist_geodFromTo (o x y : HUpper n) (hd : x ≠ y) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ dist x y) :
    gromovProduct o x y ≤ dist o (geodFromTo x y hd t) := by
  have hwx : dist (geodFromTo x y hd t) x = t := by
    have h1 : dist (geodFromTo x y hd t) (geodFromTo x y hd 0) = t := by
      rw [dist_geodFromTo hd, sub_zero, abs_of_nonneg ht0]
    rwa [geodFromTo_zero hd] at h1
  have hwy : dist (geodFromTo x y hd t) y = dist x y - t := by
    have h1 : dist (geodFromTo x y hd t) (geodFromTo x y hd (dist x y)) = dist x y - t := by
      rw [dist_geodFromTo hd, abs_of_nonpos (by linarith : t - dist x y ≤ 0)]
      ring
    rwa [geodFromTo_dist hd] at h1
  have h1 := dist_triangle o (geodFromTo x y hd t) x
  have h2 := dist_triangle o (geodFromTo x y hd t) y
  unfold gromovProduct
  linarith [h1, h2, hwx, hwy]

theorem abs_gromovProduct_sub_le (o o' x y : HUpper n) :
    |gromovProduct o x y - gromovProduct o' x y| ≤ dist o o' := by
  have h1 : |dist o x - dist o' x| ≤ dist o o' := abs_dist_sub_le o o' x
  have h2 : |dist o y - dist o' y| ≤ dist o o' := abs_dist_sub_le o o' y
  rw [abs_le] at h1 h2
  unfold gromovProduct
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

noncomputable def radial (x : HUpper n) : LorVec n := (tc x.val)⁻¹ • x.val

theorem tc_radial (x : HUpper n) : tc (radial x) = 1 := by
  change (tc x.val)⁻¹ * tc x.val = 1
  exact inv_mul_cancel₀ (ne_of_gt x.future)

theorem lorB_radial_radial (x y : HUpper n) :
    lorB (radial x) (radial y)
      = -(Real.cosh (dist x y) / (tc x.val * tc y.val)) := by
  have hxy : lorB x.val y.val = - Real.cosh (dist x y) := by
    have h := cosh_dist x y
    linarith [h]
  change lorB ((tc x.val)⁻¹ • x.val) ((tc y.val)⁻¹ • y.val) = _
  rw [lorB_smul_left, lorB_smul_right, hxy, div_eq_mul_inv, mul_inv]
  ring

theorem sdot_radial_radial (x y : HUpper n) :
    sdot (radial x) (radial y)
      = 1 - Real.cosh (dist x y) / (tc x.val * tc y.val) := by
  have h := lorB_radial_radial x y
  have h2 : lorB (radial x) (radial y)
      = sdot (radial x) (radial y) - tc (radial x) * tc (radial y) := rfl
  rw [tc_radial, tc_radial, h] at h2
  linarith [h2]

theorem sdot_radial_self (x : HUpper n) :
    sdot (radial x) (radial x) = 1 - (tc x.val)⁻¹ ^ 2 := by
  rw [sdot_radial_radial x x, dist_self, Real.cosh_zero, div_eq_mul_inv, mul_inv, ← sq]
  ring

theorem sdot_radial_sub_radial (x y : HUpper n) :
    sdot (radial x - radial y) (radial x - radial y)
      = 2 * Real.cosh (dist x y) / (tc x.val * tc y.val)
        - (tc x.val)⁻¹ ^ 2 - (tc y.val)⁻¹ ^ 2 := by
  rw [sdot_sub_left, sdot_sub_right, sdot_sub_right]
  rw [sdot_radial_self x, sdot_radial_self y, sdot_comm (radial y) (radial x),
    sdot_radial_radial x y]
  ring

theorem cosh_dist_basepoint (x : HUpper n) :
    Real.cosh (dist basepointH x) = tc x.val := by
  rw [cosh_dist]
  have hsd : sdot (eTime : LorVec n) x.val = 0 := by
    change (∑ i : Fin n, (eTime : LorVec n) (Sum.inl i) * x.val (Sum.inl i)) = 0
    simp [eTime_apply_inl]
  have htc : tc (eTime : LorVec n) = 1 := eTime_apply_inr
  change - (sdot (eTime : LorVec n) x.val - tc (eTime : LorVec n) * tc x.val) = tc x.val
  rw [hsd, htc]
  ring

theorem sinh_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.sinh t := by
  rw [Real.sinh_eq]
  have h : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith [ht])
  have h2 := Real.exp_pos t
  linarith [h, h2]

theorem sinh_le_cosh (t : ℝ) : Real.sinh t ≤ Real.cosh t := by
  rw [Real.sinh_eq, Real.cosh_eq]
  have h := Real.exp_pos (-t)
  linarith [h]

theorem exp_div_two_le_cosh (t : ℝ) : Real.exp t / 2 ≤ Real.cosh t := by
  rw [Real.cosh_eq]
  have h := Real.exp_pos (-t)
  linarith [h]

theorem cosh_le_exp {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith [ht])
  have h2 := Real.exp_pos t
  linarith [h1, h2]

theorem cosh_sub_le {a R : ℝ} (hR : R ≤ a) :
    Real.cosh (a - R) ≤ 2 * Real.exp (-R) * Real.cosh a := by
  have h1 : Real.cosh (a - R) ≤ Real.exp a * Real.exp (-R) := by
    have h := cosh_le_exp (sub_nonneg.mpr hR)
    rwa [sub_eq_add_neg, Real.exp_add] at h
  have h2 : Real.exp a ≤ 2 * Real.cosh a := by
    have h := exp_div_two_le_cosh a
    rw [div_le_iff₀ (two_pos)] at h
    linarith [h]
  calc Real.cosh (a - R) ≤ Real.exp a * Real.exp (-R) := h1
    _ ≤ (2 * Real.cosh a) * Real.exp (-R) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2 * Real.exp (-R) * Real.cosh a := by ring

theorem sdot_radial_sub_radial_le {x y : HUpper n} {R : ℝ}
    (hx : R ≤ dist basepointH x) (hy : R ≤ dist basepointH y)
    (hp : R ≤ gromovProduct basepointH x y) :
    sdot (radial x - radial y) (radial x - radial y) ≤ 16 * Real.exp (-(2 * R)) := by
  have hc_le : dist x y ≤ dist basepointH x + dist basepointH y - 2 * R := by
    unfold gromovProduct at hp
    linarith [hp]
  have hab : 0 ≤ dist basepointH x + dist basepointH y - 2 * R := by linarith [hx, hy]
  have hcosh_c : Real.cosh (dist x y)
      ≤ Real.cosh (dist basepointH x + dist basepointH y - 2 * R) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg hab]
    exact hc_le
  have hcosh_split : Real.cosh (dist basepointH x + dist basepointH y - 2 * R)
      ≤ 2 * (Real.cosh (dist basepointH x - R) * Real.cosh (dist basepointH y - R)) := by
    rw [show dist basepointH x + dist basepointH y - 2 * R
        = (dist basepointH x - R) + (dist basepointH y - R) from by ring, Real.cosh_add]
    have h1 := sinh_nonneg_of_nonneg (sub_nonneg.mpr hx)
    have h2 := sinh_nonneg_of_nonneg (sub_nonneg.mpr hy)
    have h5 : Real.sinh (dist basepointH x - R) * Real.sinh (dist basepointH y - R)
        ≤ Real.cosh (dist basepointH x - R) * Real.cosh (dist basepointH y - R) :=
      mul_le_mul (sinh_le_cosh _) (sinh_le_cosh _) h2 (Real.cosh_pos _).le
    have h6 : (0:ℝ) ≤ Real.sinh (dist basepointH x - R) * Real.sinh (dist basepointH y - R) :=
      mul_nonneg h1 h2
    linarith [h5, h6]
  have htc_x : tc x.val = Real.cosh (dist basepointH x) := (cosh_dist_basepoint x).symm
  have htc_y : tc y.val = Real.cosh (dist basepointH y) := (cosh_dist_basepoint y).symm
  rw [sdot_radial_sub_radial, htc_x, htc_y]
  have hpos : (0:ℝ) < Real.cosh (dist basepointH x) * Real.cosh (dist basepointH y) :=
    mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hmain : 2 * Real.cosh (dist x y)
        / (Real.cosh (dist basepointH x) * Real.cosh (dist basepointH y))
      ≤ 16 * Real.exp (-(2 * R)) := by
    rw [div_le_iff₀ hpos]
    calc 2 * Real.cosh (dist x y)
        ≤ 2 * (2 * (Real.cosh (dist basepointH x - R)
            * Real.cosh (dist basepointH y - R))) := by
          linarith [hcosh_c, hcosh_split]
      _ ≤ 2 * (2 * ((2 * Real.exp (-R) * Real.cosh (dist basepointH x))
            * (2 * Real.exp (-R) * Real.cosh (dist basepointH y)))) := by
          have hX : Real.cosh (dist basepointH x - R) * Real.cosh (dist basepointH y - R)
              ≤ (2 * Real.exp (-R) * Real.cosh (dist basepointH x))
                * (2 * Real.exp (-R) * Real.cosh (dist basepointH y)) :=
            mul_le_mul (cosh_sub_le hx) (cosh_sub_le hy) (Real.cosh_pos _).le
              (by positivity)
          linarith [hX]
      _ = 16 * Real.exp (-(2 * R))
            * (Real.cosh (dist basepointH x) * Real.cosh (dist basepointH y)) := by
          rw [show (-(2 * R) : ℝ) = -R + -R from by ring, Real.exp_add]
          ring
  have hnn1 : (0:ℝ) ≤ (Real.cosh (dist basepointH x))⁻¹ ^ 2 := by positivity
  have hnn2 : (0:ℝ) ≤ (Real.cosh (dist basepointH y))⁻¹ ^ 2 := by positivity
  linarith [hmain, hnn1, hnn2]

theorem abs_radial_sub_apply_inl_le {x y : HUpper n} {R : ℝ}
    (hx : R ≤ dist basepointH x) (hy : R ≤ dist basepointH y)
    (hp : R ≤ gromovProduct basepointH x y) (i : Fin n) :
    |radial x (Sum.inl i) - radial y (Sum.inl i)| ≤ 4 * Real.exp (-R) := by
  have hsd := sdot_radial_sub_radial_le hx hy hp
  have hsingle : (radial x (Sum.inl i) - radial y (Sum.inl i)) ^ 2
      ≤ sdot (radial x - radial y) (radial x - radial y) := by
    have hsum : sdot (radial x - radial y) (radial x - radial y)
        = ∑ j : Fin n, ((radial x - radial y) (Sum.inl j)) ^ 2 := by
      change (∑ j : Fin n, (radial x - radial y) (Sum.inl j)
          * (radial x - radial y) (Sum.inl j)) = _
      exact Finset.sum_congr rfl (fun j _ => (pow_two _).symm)
    rw [hsum]
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg ((radial x - radial y) (Sum.inl j))) (Finset.mem_univ i)
  have hsq : (radial x (Sum.inl i) - radial y (Sum.inl i)) ^ 2
      ≤ (4 * Real.exp (-R)) ^ 2 :=
    calc _ ≤ sdot (radial x - radial y) (radial x - radial y) := hsingle
      _ ≤ 16 * Real.exp (-(2 * R)) := hsd
      _ = (4 * Real.exp (-R)) ^ 2 := by
          rw [show (-(2 * R) : ℝ) = -R + -R from by ring, Real.exp_add]; ring
  exact abs_le_of_sq_le_sq hsq (by positivity)

def GromovCauchy (o : HUpper n) (x : ℕ → HUpper n) : Prop :=
  Tendsto (fun m => dist o (x m)) atTop atTop ∧
    ∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N, R ≤ gromovProduct o (x m) (x k)

theorem GromovCauchy.of_basepoint {o : HUpper n} {x : ℕ → HUpper n}
    (h : GromovCauchy o x) (o' : HUpper n) : GromovCauchy o' x := by
  obtain ⟨hdiv, hgrom⟩ := h
  refine ⟨?_, ?_⟩
  · rw [tendsto_atTop] at hdiv ⊢
    intro B
    have h1 := hdiv (B + dist o o')
    exact h1.mono fun m hm => by
      have htri := dist_triangle o o' (x m)
      linarith [hm, htri]
  · intro R
    obtain ⟨N, hN⟩ := hgrom (R + dist o o')
    exact ⟨N, fun m hm k hk => by
      have h1 := hN m hm k hk
      have h2 := abs_gromovProduct_sub_le o o' (x m) (x k)
      have h3 : gromovProduct o (x m) (x k) - dist o o'
          ≤ gromovProduct o' (x m) (x k) := by
        have h4 := abs_le.mp h2
        linarith [h4.1]
      linarith [h1, h3]⟩

theorem GromovCauchy.of_bounded_dist {o : HUpper n} {x y : ℕ → HUpper n} {B : ℝ}
    (hx : GromovCauchy o x) (hB : ∀ m, dist (x m) (y m) ≤ B) : GromovCauchy o y := by
  obtain ⟨hdiv, hgrom⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [tendsto_atTop] at hdiv ⊢
    intro C₀
    have h1 := hdiv (C₀ + B)
    exact h1.mono fun m hm => by
      have htri : dist o (x m) ≤ dist o (y m) + B := by
        have h := dist_triangle o (y m) (x m)
        rw [dist_comm (y m) (x m)] at h
        linarith [h, hB m]
      linarith [hm, htri]
  · intro R
    obtain ⟨N, hN⟩ := hgrom (R + 2 * B)
    exact ⟨N, fun m hm k hk => by
      have h1 := hN m hm k hk
      have ham : dist o (x m) - B ≤ dist o (y m) := by
        have h := dist_triangle o (y m) (x m)
        rw [dist_comm (y m) (x m)] at h
        linarith [h, hB m]
      have hak : dist o (x k) - B ≤ dist o (y k) := by
        have h := dist_triangle o (y k) (x k)
        rw [dist_comm (y k) (x k)] at h
        linarith [h, hB k]
      have hmk : dist (y m) (y k) ≤ dist (x m) (x k) + 2 * B := by
        have h := dist_triangle (y m) (x m) (y k)
        have h2 := dist_triangle (x m) (x k) (y k)
        rw [dist_comm (y m) (x m)] at h
        linarith [h, h2, hB m, hB k]
      unfold gromovProduct at h1 ⊢
      linarith [h1, ham, hak, hmk]⟩

theorem exists_convergesToBoundary {x : ℕ → HUpper n}
    (h : GromovCauchy basepointH x) : ∃ ξ : BoundaryH n, ConvergesToBoundary x ξ := by
  obtain ⟨hdiv, hgrom⟩ := h
  have hcau : ∀ a : Fin n ⊕ Fin 1, CauchySeq (fun m => radial (x m) a) := by
    intro a
    rcases a with i | k
    · rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨R, hR⟩ : ∃ R : ℝ, 4 * Real.exp (-R) < ε := by
        refine ⟨Real.log (4 / ε) + 1, ?_⟩
        have hpos : (0:ℝ) < 4 / ε := by positivity
        have h1 : Real.exp (-(Real.log (4 / ε) + 1)) = (4 / ε)⁻¹ * Real.exp (-1) := by
          rw [show -(Real.log (4 / ε) + 1) = -Real.log (4 / ε) + -1 from by ring,
            Real.exp_add, Real.exp_neg, Real.exp_log hpos]
        rw [h1]
        have h3 : (4:ℝ) * ((4 / ε)⁻¹) = ε := by field_simp
        have h4 : Real.exp (-1 : ℝ) < 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_strictMono (by norm_num)
        have h5 : ε * Real.exp (-1) < ε * 1 := mul_lt_mul_of_pos_left h4 hε
        rw [mul_one] at h5
        calc (4:ℝ) * ((4 / ε)⁻¹ * Real.exp (-1))
            = (4 * (4 / ε)⁻¹) * Real.exp (-1) := by ring
          _ = ε * Real.exp (-1) := by rw [h3]
          _ < ε := h5
      obtain ⟨N₁, hN₁⟩ := hgrom R
      obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ m ≥ N₂, R ≤ dist basepointH (x m) := by
        have h2 := (tendsto_atTop.mp hdiv) R
        rw [eventually_atTop] at h2
        exact h2
      refine ⟨max N₁ N₂, fun m hm k hk => ?_⟩
      rw [Real.dist_eq]
      have hm1 : R ≤ dist basepointH (x m) := hN₂ m (le_trans (le_max_right _ _) hm)
      have hk1 : R ≤ dist basepointH (x k) := hN₂ k (le_trans (le_max_right _ _) hk)
      have hmk : R ≤ gromovProduct basepointH (x m) (x k) :=
        hN₁ m (le_trans (le_max_left _ _) hm) k (le_trans (le_max_left _ _) hk)
      exact lt_of_le_of_lt (abs_radial_sub_apply_inl_le hm1 hk1 hmk i) hR
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      have hconst : (fun m => radial (x m) (Sum.inr 0)) = fun _ => (1 : ℝ) :=
        funext fun m => tc_radial (x m)
      rw [hconst]
      exact cauchySeq_const (1 : ℝ)
  choose L hL using fun a => cauchySeq_tendsto_of_complete (hcau a)
  have hpi : Tendsto (fun m => radial (x m)) atTop (nhds (fun a => L a)) :=
    tendsto_pi_nhds.mpr hL
  have htc_eq : (fun a => L a) (Sum.inr 0) = 1 := by
    have h1 : Tendsto (fun m => radial (x m) (Sum.inr 0)) atTop (nhds 1) := by
      have h2 : ∀ m, radial (x m) (Sum.inr 0) = 1 := fun m => tc_radial (x m)
      exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun m => (h2 m).symm)
    exact tendsto_nhds_unique (hL (Sum.inr 0)) h1
  have htc_lim : Tendsto (fun m => tc (x m).val) atTop atTop := by
    have hcosh : Tendsto Real.cosh atTop atTop := by
      have hexp2 : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.exp t) atTop atTop :=
        Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
      have hexp2' : Tendsto (fun t : ℝ => Real.exp t / 2) atTop atTop :=
        hexp2.congr' (Filter.Eventually.of_forall fun t => by
          change (1 / 2 : ℝ) * Real.exp t = Real.exp t / 2
          ring)
      exact tendsto_atTop_mono (fun t => exp_div_two_le_cosh t) hexp2'
    have h1 : ∀ m, tc (x m).val = Real.cosh (dist basepointH (x m)) := fun m =>
      (cosh_dist_basepoint (x m)).symm
    exact (hcosh.comp hdiv).congr' (Filter.Eventually.of_forall fun m => (h1 m).symm)
  have hsdot1 : Tendsto (fun m => sdot (radial (x m)) (radial (x m))) atTop (nhds 1) := by
    have heq : ∀ m, sdot (radial (x m)) (radial (x m)) = 1 - (tc (x m).val)⁻¹ ^ 2 :=
      fun m => sdot_radial_self (x m)
    have hinv : Tendsto (fun m => (tc (x m).val)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp htc_lim
    have hsq0 : Tendsto (fun m => ((tc (x m).val)⁻¹) ^ 2) atTop (nhds 0) := by
      have h2 := hinv.pow 2
      rwa [zero_pow two_ne_zero] at h2
    have hsub : Tendsto (fun m => (1:ℝ) - ((tc (x m).val)⁻¹) ^ 2) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hsq0
    rw [sub_zero] at hsub
    exact hsub.congr' (Filter.Eventually.of_forall fun m => (heq m).symm)
  have hsdot2 : Tendsto (fun m => sdot (radial (x m)) (radial (x m))) atTop
      (nhds (sdot (fun a => L a) (fun a => L a))) := by
    have hterm : ∀ i : Fin n, Tendsto
        (fun m => radial (x m) (Sum.inl i) * radial (x m) (Sum.inl i)) atTop
        (nhds (L (Sum.inl i) * L (Sum.inl i))) :=
      fun i => (hL (Sum.inl i)).mul (hL (Sum.inl i))
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
    exact hsum
  have hsdot_eq : sdot (fun a => L a) (fun a => L a) = 1 :=
    tendsto_nhds_unique hsdot2 hsdot1
  have hlorB : lorB (fun a => L a) (fun a => L a) = 0 := by
    have h2 : lorB (fun a => L a) (fun a => L a)
        = sdot (fun a => L a) (fun a => L a)
          - tc (fun a => L a) * tc (fun a => L a) := rfl
    have htc2 : tc (fun a => L a) = 1 := htc_eq
    rw [hsdot_eq, htc2] at h2
    linarith [h2]
  exact ⟨⟨fun a => L a, hlorB, htc_eq⟩, hpi⟩

theorem convergesToBoundary_unique {x : ℕ → HUpper n} {ξ η : BoundaryH n}
    (hξ : ConvergesToBoundary x ξ) (hη : ConvergesToBoundary x η) : ξ = η :=
  BoundaryH.ext (tendsto_nhds_unique hξ hη)

theorem gromovCauchy_geodesicRay (ξ : BoundaryH n) :
    GromovCauchy basepointH (fun m => geodesicRay ξ (m : ℝ)) := by
  constructor
  · have heq : ∀ m : ℕ, dist basepointH (geodesicRay ξ (m : ℝ)) = (m : ℝ) := by
      intro m
      rw [dist_basepoint_geodesicRay, abs_of_nonneg (Nat.cast_nonneg m)]
    exact tendsto_natCast_atTop_atTop.congr'
      (Filter.Eventually.of_forall fun m => (heq m).symm)
  · intro R
    refine ⟨Nat.ceil R, fun m hm k hk => ?_⟩
    have hmR : R ≤ (m : ℝ) := (Nat.le_ceil R).trans (Nat.cast_le.mpr hm)
    have hkR : R ≤ (k : ℝ) := (Nat.le_ceil R).trans (Nat.cast_le.mpr hk)
    unfold gromovProduct
    rw [dist_basepoint_geodesicRay, dist_basepoint_geodesicRay, dist_geodesicRay,
      abs_of_nonneg (Nat.cast_nonneg m), abs_of_nonneg (Nat.cast_nonneg k)]
    rcases le_total (m : ℝ) (k : ℝ) with hmk | hmk
    · rw [abs_of_nonpos (by linarith : (m : ℝ) - (k : ℝ) ≤ 0)]
      have h : ((m : ℝ) + (k : ℝ) - -((m : ℝ) - (k : ℝ))) / 2 = (m : ℝ) := by ring
      rw [h]
      exact hmR
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ))]
      have h : ((m : ℝ) + (k : ℝ) - ((m : ℝ) - (k : ℝ))) / 2 = (k : ℝ) := by ring
      rw [h]
      exact hkR

theorem convergesToBoundary_geodesicRay (ξ : BoundaryH n) :
    ConvergesToBoundary (fun m => geodesicRay ξ (m : ℝ)) ξ := by
  obtain ⟨η, hη⟩ := exists_convergesToBoundary (gromovCauchy_geodesicRay ξ)
  have hηξ : η = ξ := convergesToBoundary_unique hη (tendsto_geodesicRay ξ)
  subst hηξ
  exact hη

theorem tendsto_atTop_of_isPseudoIsometry {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) {o : HUpper n} {x : ℕ → HUpper n}
    (hdiv : Tendsto (fun m => dist o (x m)) atTop atTop) :
    Tendsto (fun m => dist (Φ o) (Φ (x m))) atTop atTop := by
  have hK : (0:ℝ) < K := one_pos.trans_le hΦ.hK
  rw [tendsto_atTop] at hdiv ⊢
  intro B
  have h := hdiv (K * (B + C))
  exact h.mono fun m hm => by
    have h1 := hΦ.lower o (x m)
    have h2 : B + C ≤ K⁻¹ * dist o (x m) := by
      have h3 := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hK.le)
      rwa [show K⁻¹ * (K * (B + C)) = B + C from by
        rw [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]] at h3
    linarith [h1, h2]

theorem exists_convergesToBoundary_pseudoIsometry_ray {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (ξ : BoundaryH n)
    (hgrom : ∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
      R ≤ gromovProduct basepointH (Φ (geodesicRay ξ (m : ℝ)))
        (Φ (geodesicRay ξ (k : ℝ)))) :
    ∃ η : BoundaryH n, ConvergesToBoundary (fun m => Φ (geodesicRay ξ (m : ℝ))) η := by
  apply exists_convergesToBoundary
  refine ⟨?_, hgrom⟩
  have h1 : Tendsto (fun m : ℕ => dist (Φ basepointH) (Φ (geodesicRay ξ (m : ℝ))))
      atTop atTop :=
    tendsto_atTop_of_isPseudoIsometry hΦ (gromovCauchy_geodesicRay ξ).1
  rw [tendsto_atTop] at h1 ⊢
  intro B
  have h2 := h1 (B + dist basepointH (Φ basepointH))
  exact h2.mono fun m hm => by
    have htri := dist_triangle (Φ basepointH) basepointH (Φ (geodesicRay ξ (m : ℝ)))
    rw [dist_comm (Φ basepointH) basepointH] at htri
    change B ≤ dist basepointH (Φ (geodesicRay ξ (m : ℝ)))
    linarith [hm, htri]

theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop := by
  have hexp2 : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.exp t) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
  have hexp2' : Tendsto (fun t : ℝ => Real.exp t / 2) atTop atTop :=
    hexp2.congr' (Filter.Eventually.of_forall fun t => by
      change (1 / 2 : ℝ) * Real.exp t = Real.exp t / 2
      ring)
  exact tendsto_atTop_mono (fun t => exp_div_two_le_cosh t) hexp2'

theorem tendsto_atTop_tc {x : ℕ → HUpper n}
    (hdiv : Tendsto (fun m => dist basepointH (x m)) atTop atTop) :
    Tendsto (fun m => tc (x m).val) atTop atTop := by
  have h1 : ∀ m, tc (x m).val = Real.cosh (dist basepointH (x m)) := fun m =>
    (cosh_dist_basepoint (x m)).symm
  exact (tendsto_cosh_atTop.comp hdiv).congr' (Filter.Eventually.of_forall fun m => (h1 m).symm)

theorem tendsto_atTop_dist_basepoint {x : ℕ → HUpper n}
    (h : Tendsto (fun m => tc (x m).val) atTop atTop) :
    Tendsto (fun m => dist basepointH (x m)) atTop atTop := by
  have h2 : ∀ m, dist basepointH (x m) = Real.arcosh (tc (x m).val) := by
    intro m
    rw [← cosh_dist_basepoint (x m), Real.arcosh_cosh dist_nonneg]
  have h3 : ∀ m, Real.log (tc (x m).val) ≤ dist basepointH (x m) := by
    intro m
    rw [h2 m]
    change Real.log (tc (x m).val)
      ≤ Real.log (tc (x m).val + Real.sqrt (tc (x m).val ^ 2 - 1))
    exact Real.log_le_log (x m).future
      (by linarith [Real.sqrt_nonneg (tc (x m).val ^ 2 - 1)])
  exact tendsto_atTop_mono h3 (Real.tendsto_log_atTop.comp h)

theorem tendsto_atTop_tc_of_convergesToBoundary {x : ℕ → HUpper n} {ξ : BoundaryH n}
    (hx : ConvergesToBoundary x ξ) :
    Tendsto (fun m => tc (x m).val) atTop atTop := by
  have hterm : ∀ i : Fin n, Tendsto
      (fun m => radial (x m) (Sum.inl i) * radial (x m) (Sum.inl i)) atTop
      (nhds (ξ.val (Sum.inl i) * ξ.val (Sum.inl i))) :=
    fun i => ((tendsto_pi_nhds.mp hx) (Sum.inl i)).mul ((tendsto_pi_nhds.mp hx) (Sum.inl i))
  have h1 : Tendsto (fun m => sdot (radial (x m)) (radial (x m))) atTop
      (nhds (sdot ξ.val ξ.val)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  rw [sdot_self_of_boundary ξ] at h1
  have heq : ∀ m, sdot (radial (x m)) (radial (x m)) = 1 - (tc (x m).val)⁻¹ ^ 2 :=
    fun m => sdot_radial_self (x m)
  have h2 : Tendsto (fun m => 1 - (tc (x m).val)⁻¹ ^ 2) atTop (nhds 1) :=
    h1.congr' (Filter.Eventually.of_forall fun m => heq m)
  have h3 : Tendsto (fun m => (tc (x m).val)⁻¹ ^ 2) atTop (nhds 0) := by
    have h : Tendsto (fun m => (1:ℝ) - (1 - (tc (x m).val)⁻¹ ^ 2)) atTop
        (nhds (1 - 1)) :=
      tendsto_const_nhds.sub h2
    rw [sub_self] at h
    exact h.congr' (Filter.Eventually.of_forall fun m => sub_sub_self 1 _)
  rw [tendsto_atTop]
  intro B
  set B' := max B 1 with hB'
  have hB'1 : (0:ℝ) < B' := lt_of_lt_of_le one_pos (le_max_right B 1)
  have h4 : ∀ᶠ m in atTop, ((tc (x m).val)⁻¹) ^ 2 < (B'⁻¹) ^ 2 :=
    h3.eventually (Iio_mem_nhds (by positivity))
  exact h4.mono fun m hm => by
    have htc : 0 < tc (x m).val := (x m).future
    have h5 : (tc (x m).val)⁻¹ < B'⁻¹ := by
      have h6 : |(tc (x m).val)⁻¹| < |B'⁻¹| := sq_lt_sq.mp hm
      rwa [abs_of_nonneg (inv_nonneg.mpr htc.le),
        abs_of_nonneg (inv_nonneg.mpr hB'1.le)] at h6
    have h7 : B' < tc (x m).val := by
      rw [inv_lt_inv₀ htc hB'1] at h5
      exact h5
    exact (le_max_left B 1).trans h7.le

theorem ConvergesToBoundary.of_bounded_dist {x y : ℕ → HUpper n} {ξ : BoundaryH n} {B : ℝ}
    (hx : ConvergesToBoundary x ξ) (hB : ∀ m, dist (x m) (y m) ≤ B)
    (hy : Tendsto (fun m => dist basepointH (y m)) atTop atTop) :
    ConvergesToBoundary y ξ := by
  have hB0 : (0:ℝ) ≤ B := dist_nonneg.trans (hB 0)
  have htx : Tendsto (fun m => tc (x m).val) atTop atTop :=
    tendsto_atTop_tc_of_convergesToBoundary hx
  have hty : Tendsto (fun m => tc (y m).val) atTop atTop := tendsto_atTop_tc hy
  have hdiff : Tendsto (fun m => radial (y m) - radial (x m)) atTop (nhds 0) := by
    rw [tendsto_pi_nhds]
    intro a
    rcases a with i | k
    · have h1 : ∀ m, ((radial (y m) - radial (x m)) (Sum.inl i)) ^ 2
          ≤ 2 * Real.cosh B * ((tc (x m).val)⁻¹ * (tc (y m).val)⁻¹) := by
        intro m
        have hsingle : ((radial (y m) - radial (x m)) (Sum.inl i)) ^ 2
            ≤ sdot (radial (y m) - radial (x m)) (radial (y m) - radial (x m)) := by
          have hsum2 : sdot (radial (y m) - radial (x m)) (radial (y m) - radial (x m))
              = ∑ j : Fin n, ((radial (y m) - radial (x m)) (Sum.inl j)) ^ 2 := by
            change (∑ j : Fin n, (radial (y m) - radial (x m)) (Sum.inl j)
                * (radial (y m) - radial (x m)) (Sum.inl j)) = _
            exact Finset.sum_congr rfl (fun j _ => (pow_two _).symm)
          rw [hsum2]
          exact Finset.single_le_sum
            (fun j _ => sq_nonneg ((radial (y m) - radial (x m)) (Sum.inl j)))
            (Finset.mem_univ i)
        have hid := sdot_radial_sub_radial (y m) (x m)
        have hcosh : Real.cosh (dist (y m) (x m)) ≤ Real.cosh B := by
          rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg hB0]
          rw [dist_comm]
          exact hB m
        calc ((radial (y m) - radial (x m)) (Sum.inl i)) ^ 2
            ≤ sdot (radial (y m) - radial (x m)) (radial (y m) - radial (x m)) := hsingle
          _ = 2 * Real.cosh (dist (y m) (x m)) / (tc (y m).val * tc (x m).val)
              - (tc (y m).val)⁻¹ ^ 2 - (tc (x m).val)⁻¹ ^ 2 := hid
          _ ≤ 2 * Real.cosh (dist (y m) (x m)) / (tc (y m).val * tc (x m).val) := by
              have h2 : (0:ℝ) ≤ (tc (y m).val)⁻¹ ^ 2 := by positivity
              have h3 : (0:ℝ) ≤ (tc (x m).val)⁻¹ ^ 2 := by positivity
              linarith [h2, h3]
          _ ≤ 2 * Real.cosh B / (tc (y m).val * tc (x m).val) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcosh (by norm_num))
                (inv_nonneg.mpr (mul_nonneg (y m).future.le (x m).future.le))
          _ = 2 * Real.cosh B * ((tc (x m).val)⁻¹ * (tc (y m).val)⁻¹) := by
              rw [div_eq_mul_inv, mul_inv]; ring
      have h0 : Tendsto
          (fun m => 2 * Real.cosh B * ((tc (x m).val)⁻¹ * (tc (y m).val)⁻¹)) atTop
          (nhds (2 * Real.cosh B * (0 * 0))) :=
        tendsto_const_nhds.mul
          ((tendsto_inv_atTop_zero.comp htx).mul (tendsto_inv_atTop_zero.comp hty))
      rw [mul_zero, mul_zero] at h0
      have h2 : Tendsto (fun m => ((radial (y m) - radial (x m)) (Sum.inl i)) ^ 2) atTop
          (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
          (fun m => sq_nonneg _) h1
      have h3 : Tendsto (fun m => Real.sqrt (((radial (y m) - radial (x m)) (Sum.inl i)) ^ 2))
          atTop (nhds (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp h2
      rw [Real.sqrt_zero] at h3
      have h4 : Tendsto (fun m => |((radial (y m) - radial (x m)) (Sum.inl i))|) atTop
          (nhds (0 : ℝ)) :=
        h3.congr' (Filter.Eventually.of_forall fun m => Real.sqrt_sq_eq_abs _)
      have h5 : Tendsto (fun m => -|((radial (y m) - radial (x m)) (Sum.inl i))|) atTop
          (nhds (0 : ℝ)) := by
        have h5 := h4.neg
        rwa [neg_zero] at h5
      have h6 := tendsto_of_tendsto_of_tendsto_of_le_of_le h5 h4
        (fun m => neg_abs_le _) (fun m => le_abs_self _)
      exact h6
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      have hconst : (fun m => (radial (y m) - radial (x m)) (Sum.inr 0)) = fun _ => (0 : ℝ) := by
        funext m
        change tc (radial (y m)) - tc (radial (x m)) = 0
        rw [tc_radial, tc_radial, sub_self]
      rw [hconst]
      exact tendsto_const_nhds
  have hsum : Tendsto (fun m => radial (x m) + (radial (y m) - radial (x m))) atTop
      (nhds (ξ.val + 0)) := hx.add hdiff
  rw [add_zero] at hsum
  exact hsum.congr' (Filter.Eventually.of_forall fun m =>
    add_sub_cancel (radial (x m)) (radial (y m)))

end DifferentialGeometry.GromovBoundary
