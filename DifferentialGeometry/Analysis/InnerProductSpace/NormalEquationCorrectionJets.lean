import DifferentialGeometry.Analysis.InnerProductSpace.NearestNormalEquationJets
import DifferentialGeometry.Analysis.Calculus.Inverse.ScaledContractionGraphJets
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u

theorem exists_uniform_nearest_normal_equation_correction_jets
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [CompleteSpace L]
        (o : H) (g : L → Lᗮ) (R a : ℝ),
        0 < R → 0 ≤ a → a ≤ 1 / 100 →
        ContDiffOn ℝ (m + 1 : ℕ) g (ball (0 : L) (4 * R)) →
        (∀ i ≤ m + 1, ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ a * R * (R⁻¹) ^ i) →
        let q : H × L → L := fun p => L.orthogonalProjectionOnto (p.1 - o) + p.2
        let e : H × L → L := fun p =>
          (ContinuousLinearMap.adjoint (fderiv ℝ g (q p)))
            (g (q p) - Lᗮ.orthogonalProjectionOnto (p.1 - o))
        ∃ h : H → L, ContDiffOn ℝ m h (ball o R) ∧
          (∀ z ∈ ball o R, ‖h z‖ ≤ R / 4 ∧ h z + e (z, h z) = 0) ∧
          (∀ z ∈ ball o R, ∀ n ∈ closedBall (0 : L) R,
            n + e (z, n) = 0 ↔ n = h z) ∧
          ∀ z ∈ ball o R, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j h z‖ ≤ B * a * R * (R⁻¹) ^ j := by
  obtain ⟨B, hB, hconstruct⟩ :=
    exists_uniform_scaled_contraction_graph_jets.{u,u} m (3 * (4 : ℝ) ^ m) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro H _ _ _ L _ o g R a hR ha0 ha hg hjet
  have ha1 : a ≤ 1 := by linarith
  have hvalue (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖g t‖ ≤ a * R := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hjet 0 (by omega) t ht
  have hfirst (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖fderiv ℝ g t‖ ≤ a := by
    have hh := hjet 1 (by omega) t ht
    simpa only [norm_iteratedFDeriv_one, pow_one, mul_assoc,
      mul_inv_cancel₀ hR.ne', mul_one] using hh
  have hsecond (t : L) (ht : t ∈ ball (0 : L) (4 * R)) :
      ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R := by
    have hn : ‖fderiv ℝ (fderiv ℝ g) t‖ = ‖iteratedFDeriv ℝ 2 g t‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    rw [hn]
    calc
      _ ≤ a * R * (R⁻¹) ^ 2 := hjet 2 (by omega) t ht
      _ = a / R := by field_simp [hR.ne']
  let u : H → L := fun z => L.orthogonalProjectionOnto (z - o)
  let v : H → Lᗮ := fun z => Lᗮ.orthogonalProjectionOnto (z - o)
  let V : Set (H × L) := ball o (2 * R) ×ˢ ball 0 (2 * R)
  let q : H × L → L := fun p => u p.1 + p.2
  let e : H × L → L := fun p =>
    (ContinuousLinearMap.adjoint (fderiv ℝ g (q p))) (g (q p) - v p.1)
  let J : (L →L[ℝ] Lᗮ) →L[ℝ] (Lᗮ →L[ℝ] L) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hu : ContDiff ℝ m u :=
    L.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hv : ContDiff ℝ m v :=
    Lᗮ.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hq : ContDiff ℝ m q := (hu.comp contDiff_fst).add contDiff_snd
  have hmaps : MapsTo q V (ball (0 : L) (4 * R)) := by
    intro p hp
    have h1 : ‖u p.1‖ < 2 * R :=
      (L.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans_lt
        (by simpa only [mem_ball, dist_eq_norm] using hp.1)
    have h2 : ‖p.2‖ < 2 * R := by simpa only [mem_ball, dist_zero_right] using hp.2
    rw [mem_ball, dist_zero_right]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hdg : ContDiffOn ℝ m (fderiv ℝ g) (ball (0 : L) (4 * R)) :=
    hg.fderiv_of_isOpen isOpen_ball (by simp)
  have hgm : ContDiffOn ℝ m g (ball (0 : L) (4 * R)) := hg.of_le (by simp)
  have he : ContDiffOn ℝ m e V :=
    (J.contDiff.comp_contDiffOn (hdg.comp hq.contDiffOn hmaps)).clm_apply
      ((hgm.comp hq.contDiffOn hmaps).sub (hv.comp contDiff_fst).contDiffOn)
  have hmn : (m : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiff (t : L) (ht : t ∈ ball (0 : L) (4 * R)) :
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (fderiv ℝ g) t := by
    exact ⟨(hgm.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt hmn,
      (hdg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt hmn⟩
  have hcylinder : ball o R ×ˢ closedBall (0 : L) R ⊆ V := by
    intro p hp
    constructor
    · change dist p.1 o < 2 * R
      have hh : dist p.1 o < R := hp.1
      linarith
    · change dist p.2 0 < 2 * R
      have hh : dist p.2 0 ≤ R := hp.2
      linarith
  have hscaled (z : H) (hz : z ∈ ball o R) (n : L)
      (hn : n ∈ closedBall (0 : L) R) :
      ‖e (z, n)‖ ≤ R / 4 ∧ ‖fderiv ℝ (fun w : L => e (z, w)) n‖ ≤ 1 / 2 := by
    have hp : (z, n) ∈ V := hcylinder ⟨hz, hn⟩
    have ht : q (z, n) ∈ ball (0 : L) (4 * R) := hmaps hp
    have hvnorm : ‖v z‖ ≤ R :=
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans
        (by simpa only [mem_ball, dist_eq_norm] using (show dist z o < R from hz).le)
    have hh := normal_graph_remainder_small_of_scaled_bounds g (u z + n) (v z) R a hR ha
      (hdiff _ ht).1 (hdiff _ ht).2 (hvalue _ ht) (hfirst _ ht) (hsecond _ ht) hvnorm
    refine ⟨hh.1, ?_⟩
    change ‖fderiv ℝ (fun w : L =>
      (ContinuousLinearMap.adjoint (fderiv ℝ g (u z + w))) (g (u z + w) - v z)) n‖ ≤ _
    rw [fderiv_comp_add_left (f := fun t : L =>
      (ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v z)) (u z)]
    exact hh.2
  have herr (p : H × L) (hp : p ∈ V) (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i e p‖ ≤ (3 * (4 : ℝ) ^ m) * a * R * (R⁻¹) ^ i := by
    have hh := norm_iteratedFDeriv_nearest_normal_equation_remainder_le L o g R a
      hR ha0 ha1 i (hg.of_le (by exact_mod_cast (by omega : i + 1 ≤ m + 1)))
      (fun k hk t ht => hjet k (by omega) t ht) p hp
    change ‖iteratedFDeriv ℝ i e p‖ ≤ (3 * (4 : ℝ) ^ i) * a * R * (R⁻¹) ^ i at hh
    apply hh.trans
    have hpow : (4 : ℝ) ^ i ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hi
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) ha0)
        hR.le) (by positivity)
  have hemax : ContDiffOn ℝ (max m 1 : ℕ) e V := by
    simpa only [max_eq_left hm] using he
  obtain ⟨h, hh, hroot, hunique, hjets⟩ := hconstruct L H
    (ball o R) V isOpen_ball (isOpen_ball.prod isOpen_ball) R a hR ha0 ha1
    hcylinder e hemax (fun z hz n hn => (hscaled z hz n hn).1)
    (fun z hz n hn => (hscaled z hz n hn).2) herr
  refine ⟨h, ?_, hroot, hunique, hjets⟩
  simpa only [max_eq_left hm] using hh

end DifferentialGeometry.Analysis
