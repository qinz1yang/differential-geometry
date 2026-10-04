import Mathlib.Analysis.Calculus.FDeriv.Add
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphRemainderAllJets
import DifferentialGeometry.Analysis.InnerProductSpace.NormalEquationCorrectionJets
import DifferentialGeometry.Analysis.Calculus.Inverse.AllOrderContractionGraphJets

/-! All finite normal-equation jets with a single smallness threshold on the first two jets. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u

section Remainder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_iteratedFDeriv_nearest_normal_equation_remainder_le_linear_error
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (R C δ : ℝ) (hR : 0 < R)
    (hC : 0 ≤ C) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (j : ℕ)
    (hg : ContDiffOn ℝ (j + 1 : ℕ) g (ball (0 : L) (4 * R)))
    (hjet : ∀ i ≤ j + 1, ∀ t ∈ ball (0 : L) (4 * R),
      ‖iteratedFDeriv ℝ i g t‖ ≤ C * δ * R * (R⁻¹) ^ i)
    (p : H × L) (hp : p ∈ ball o (2 * R) ×ˢ ball (0 : L) (2 * R)) :
    ‖iteratedFDeriv ℝ j (fun y : H × L =>
      (ContinuousLinearMap.adjoint
        (fderiv ℝ g (L.orthogonalProjectionOnto (y.1 - o) + y.2)))
          (g (L.orthogonalProjectionOnto (y.1 - o) + y.2) -
            Lᗮ.orthogonalProjectionOnto (y.1 - o))) p‖ ≤
      ((C + 2) * C * (4 : ℝ) ^ j) * δ * R * (R⁻¹) ^ j := by
  let A : (H × L) →L[ℝ] L :=
    L.orthogonalProjectionOnto.coprod (ContinuousLinearMap.id ℝ L)
  let B : (H × L) →L[ℝ] Lᗮ :=
    Lᗮ.orthogonalProjectionOnto.comp (ContinuousLinearMap.fst ℝ H L)
  let a₀ : L := -L.orthogonalProjectionOnto o
  let b₀ : Lᗮ := -Lᗮ.orthogonalProjectionOnto o
  have hq (y : H × L) :
      a₀ + A y = L.orthogonalProjectionOnto (y.1 - o) + y.2 := by
    change -L.orthogonalProjectionOnto o +
      (L.orthogonalProjectionOnto y.1 + y.2) = _
    rw [map_sub]
    abel
  have hv (y : H × L) : b₀ + B y = Lᗮ.orthogonalProjectionOnto (y.1 - o) := by
    change -Lᗮ.orthogonalProjectionOnto o + Lᗮ.orthogonalProjectionOnto y.1 = _
    rw [map_sub]
    abel
  have hA : ‖A‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    change ‖L.orthogonalProjectionOnto y.1 + y.2‖ ≤ 2 * ‖y‖
    have h1 := L.norm_orthogonalProjectionOnto_apply_le y.1
    have h2 : ‖y.1‖ ≤ ‖y‖ := le_max_left _ _
    have h3 : ‖y.2‖ ≤ ‖y‖ := le_max_right _ _
    have h4 := norm_add_le (L.orthogonalProjectionOnto y.1) y.2
    linarith
  have hB : ‖B‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖Lᗮ.orthogonalProjectionOnto y.1‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le y.1).trans (norm_fst_le y)
  have hp1 : ‖p.1 - o‖ < 2 * R := by
    simpa only [mem_ball, dist_eq_norm] using hp.1
  have hp2 : ‖p.2‖ < 2 * R := by
    simpa only [mem_ball, dist_zero_right] using hp.2
  have hmem : a₀ + A p ∈ ball (0 : L) (4 * R) := by
    rw [hq, mem_ball, dist_zero_right]
    have h1 := (L.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans_lt hp1
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hvnorm : ‖b₀ + B p‖ ≤ 2 * R := by
    rw [hv]
    exact (Lᗮ.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans hp1.le
  have h := norm_iteratedFDeriv_affine_normal_graph_remainder_le_unrestricted
    g a₀ A b₀ B (ball (0 : L) (4 * R)) isOpen_ball j hg p hmem
    R (C * δ) 2 hR (by positivity) (by norm_num) hA hB hvnorm
    (fun i hi => hjet i hi _ hmem)
  simp only [hq, hv, show (2 : ℝ) * 2 = 4 by norm_num] at h
  apply h.trans
  have hsmall : C * δ + 2 ≤ C + 2 := by nlinarith
  calc
    ((C * δ + 2) * 4 ^ j) * (C * δ) * R * (R⁻¹) ^ j =
        ((C * δ + 2) * C * 4 ^ j) * δ * R * (R⁻¹) ^ j := by ring
    _ ≤ _ := by gcongr


end Remainder

theorem exists_uniform_nearest_normal_equation_all_jets
    (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [CompleteSpace L]
        (o : H) (g : L → Lᗮ) (R δ : ℝ),
        0 < R → 0 ≤ δ → δ ≤ δ₀ →
        ContDiffOn ℝ ∞ g (ball (0 : L) (4 * R)) →
        (∀ m i, i ≤ m → ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ F m * δ * R * (R⁻¹) ^ i) →
        let q : H × L → L := fun p => L.orthogonalProjectionOnto (p.1 - o) + p.2
        let e : H × L → L := fun p =>
          (ContinuousLinearMap.adjoint (fderiv ℝ g (q p)))
            (g (q p) - Lᗮ.orthogonalProjectionOnto (p.1 - o))
        ∃ h : H → L, ContDiffOn ℝ ∞ h (ball o R) ∧
          (∀ z ∈ ball o R, ‖h z‖ ≤ R / 4 ∧ h z + e (z, h z) = 0) ∧
          (∀ z ∈ ball o R, ∀ n ∈ closedBall (0 : L) R,
            n + e (z, n) = 0 ↔ n = h z) ∧
          ∀ m, ∀ z ∈ ball o R, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j h z‖ ≤ B m * δ * R * (R⁻¹) ^ j := by
  have hF2 : 0 ≤ F 2 := hF 2
  obtain ⟨B, hB, hconstruct⟩ := exists_uniform_allOrder_scaled_contraction_graph_jets.{u,u}
    (fun m => (F (m + 1) + 2) * F (m + 1) * (4 : ℝ) ^ m)
    (by intro m; have hFm := hF (m + 1); positivity)
  refine ⟨B, hB, 1 / (100 * (F 2 + 1)), by positivity, ?_⟩
  intro H _ _ _ L _ o g R δ hR hδ0 hδsmall hg hjet
  have hden : 0 < 100 * (F 2 + 1) := by positivity
  have hbudget : δ * (100 * (F 2 + 1)) ≤ 1 := (le_div_iff₀ hden).mp hδsmall
  have hδ1 : δ ≤ 1 := by nlinarith [hF 2]
  let a : ℝ := F 2 * δ
  have ha0 : 0 ≤ a := mul_nonneg (hF 2) hδ0
  have ha : a ≤ 1 / 100 := by dsimp only [a]; nlinarith [hF 2]
  have hvalue (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖g t‖ ≤ a * R := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hjet 2 0 (by omega) t ht
  have hfirst (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖fderiv ℝ g t‖ ≤ a := by
    have hh := hjet 2 1 (by omega) t ht
    simpa only [norm_iteratedFDeriv_one, pow_one, mul_assoc,
      mul_inv_cancel₀ hR.ne', mul_one] using hh
  let : NormedAddCommGroup (L →L[ℝ] Lᗮ) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] Lᗮ) := inferInstance
  have hsecond (t : L) (ht : t ∈ ball (0 : L) (4 * R)) :
      ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R := by
    have hn : ‖fderiv ℝ (fderiv ℝ g) t‖ = ‖iteratedFDeriv ℝ 2 g t‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    rw [hn]
    calc
      _ ≤ a * R * (R⁻¹) ^ 2 := hjet 2 2 (by omega) t ht
      _ = a / R := by field_simp [hR.ne']
  let u : H → L := fun z => L.orthogonalProjectionOnto (z - o)
  let v : H → Lᗮ := fun z => Lᗮ.orthogonalProjectionOnto (z - o)
  let V : Set (H × L) := ball o (2 * R) ×ˢ ball 0 (2 * R)
  let q : H × L → L := fun p => u p.1 + p.2
  let e : H × L → L := fun p =>
    (ContinuousLinearMap.adjoint (fderiv ℝ g (q p))) (g (q p) - v p.1)
  let J : (L →L[ℝ] Lᗮ) →L[ℝ] (Lᗮ →L[ℝ] L) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hu : ContDiff ℝ ∞ u :=
    L.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hv : ContDiff ℝ ∞ v :=
    Lᗮ.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hq : ContDiff ℝ ∞ q := (hu.comp contDiff_fst).add contDiff_snd
  have hmaps : MapsTo q V (ball (0 : L) (4 * R)) := by
    intro p hp
    have h1 : ‖u p.1‖ < 2 * R :=
      (L.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans_lt
        (by simpa only [mem_ball, dist_eq_norm] using hp.1)
    have h2 : ‖p.2‖ < 2 * R := by simpa only [mem_ball, dist_zero_right] using hp.2
    rw [mem_ball, dist_zero_right]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hdg : ContDiffOn ℝ ∞ (fderiv ℝ g) (ball (0 : L) (4 * R)) :=
    hg.fderiv_of_isOpen isOpen_ball (by simp)
  have hgm : ContDiffOn ℝ ∞ g (ball (0 : L) (4 * R)) := hg
  have he : ContDiffOn ℝ ∞ e V := by
    change ContDiffOn ℝ ∞ (fun p => J (fderiv ℝ g (q p)) (g (q p) - v p.1)) V
    exact (J.contDiff.comp_contDiffOn (hdg.comp hq.contDiffOn hmaps)).clm_apply
      ((hgm.comp hq.contDiffOn hmaps).sub (hv.comp contDiff_fst).contDiffOn)
  have hdiff (t : L) (ht : t ∈ ball (0 : L) (4 * R)) :
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (fderiv ℝ g) t := by
    exact ⟨(hgm.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp),
      (hdg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp)⟩
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
  have herr (m : ℕ) (p : H × L) (hp : p ∈ V) (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i e p‖ ≤
        ((F (m + 1) + 2) * F (m + 1) * (4 : ℝ) ^ m) * δ * R * (R⁻¹) ^ i := by
    have hh := norm_iteratedFDeriv_nearest_normal_equation_remainder_le_linear_error
      L o g R (F (m + 1)) δ hR (hF _) hδ0 hδ1 i
      (hg.of_le (by simp)) (fun k hk t ht => hjet (m + 1) k (by omega) t ht) p hp
    change ‖iteratedFDeriv ℝ i e p‖ ≤
      ((F (m + 1) + 2) * F (m + 1) * (4 : ℝ) ^ i) * δ * R * (R⁻¹) ^ i at hh
    apply hh.trans
    have hFm := hF (m + 1)
    have hpow : (4 : ℝ) ^ i ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hi
    gcongr
  obtain ⟨h, hh, hroot, hunique, hjets⟩ := hconstruct L H
    (ball o R) V isOpen_ball (isOpen_ball.prod isOpen_ball) R δ hR hδ0 hδ1
    hcylinder e he (fun z hz n hn => (hscaled z hz n hn).1)
    (fun z hz n hn => (hscaled z hz n hn).2) herr
  exact ⟨h, hh, hroot, hunique, hjets⟩

end DifferentialGeometry.Analysis
