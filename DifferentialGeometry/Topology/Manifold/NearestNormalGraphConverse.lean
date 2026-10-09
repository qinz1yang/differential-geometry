import DifferentialGeometry.Topology.Manifold.NearestNormalGraphStationarity
import DifferentialGeometry.Analysis.InnerProductSpace.NearestNormalEquationAllJets
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraph

/-! A normal candidate and the original nearest point agree in the same graph uniqueness window. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped ContDiff Manifold Topology
namespace GC.MetricGeometry
universe u

theorem exists_uniform_actual_normal_graph_nearest_converse
    (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (k : ℕ) (Z : Set H) [ChartedSpace (Fin k → ℝ) Z],
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
          (Subtype.val : Z → H) →
        ∀ (L : Submodule ℝ H) [CompleteSpace L] (o : H) (g : L → Lᗮ) (R δ : ℝ),
        0 < R → 0 ≤ δ → δ ≤ δ₀ →
        ContDiffOn ℝ ∞ g (ball (0 : L) (4 * R)) →
        (∀ m i, i ≤ m → ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ F m * δ * R * (R⁻¹) ^ i) →
        (∀ t ∈ ball (0 : L) (4 * R),
          o + orthogonalCoordinateSum L (t, g t) ∈ Z) →
        (∀ y ∈ Z ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
          y = o + orthogonalCoordinateSum L (t, g t)) →
        let Ω : TopologicalSpace.Opens H := ⟨ball o R, isOpen_ball⟩
        ∀ (p : Ω → Z), (∀ z : Ω, IsMinOn (fun w => dist (z : H) w) Z (p z : H)) →
        ∀ (y : Z), (y : H) ∈ ball o (R / 4) →
        ∀ (n : H), ‖n‖ ≤ R / 4 → n ∈ (actualZeroSetTangentSpace k Z y)ᗮ →
        ∃ hz : (y : H) + n ∈ Ω, p ⟨(y : H) + n, hz⟩ = y := by
  obtain ⟨B, hB, δc, hδc, hconstruct⟩ :=
    exists_uniform_nearest_normal_equation_all_jets.{u} F hF
  refine ⟨min δc (1 / (100 * (F 2 + 1))), lt_min hδc (by have hh := hF 2; positivity), ?_⟩
  intro H _ _ _ k Z _ hemb L _ o g R δ hR hδ0 hδsmall hg hjet hgraph hsheet
  dsimp only
  intro p hnearest
  obtain ⟨h, hh, hroot, hunique, hjets⟩ := hconstruct H L o g R δ hR hδ0
    (hδsmall.trans (min_le_left _ _)) hg hjet
  have hden : 0 < 100 * (F 2 + 1) := by have hh := hF 2; positivity
  have hbudget : δ * (100 * (F 2 + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (hδsmall.trans (min_le_right _ _))
  let a : ℝ := F 2 * δ
  have ha0 : 0 ≤ a := mul_nonneg (hF 2) hδ0
  have ha : a ≤ 1 / 100 := by dsimp only [a]; nlinarith [hF 2]
  have hvalue (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖g t‖ ≤ a * R := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hjet 2 0 (by omega) t ht
  have hfirst (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖fderiv ℝ g t‖ ≤ a := by
    simpa only [norm_iteratedFDeriv_one, pow_one, mul_assoc,
      mul_inv_cancel₀ hR.ne', mul_one] using hjet 2 1 (by omega) t ht
  intro y hy n hn hnormal
  let z : H := (y : H) + n
  have hz : z ∈ ball o R := by
    have hdist : ‖(y : H) - o‖ < R / 4 := by
      simpa only [mem_ball, dist_eq_norm] using hy
    have heq : z - o = ((y : H) - o) + n := by dsimp only [z]; abel
    rw [mem_ball, dist_eq_norm, heq]
    exact (norm_add_le _ _).trans_lt (by linarith)
  let U : TopologicalSpace.Opens L := ⟨ball 0 (4 * R), isOpen_ball⟩
  let u : L := L.orthogonalProjectionOnto (z - o)
  let v : Lᗮ := Lᗮ.orthogonalProjectionOnto (z - o)
  have hproj (t : L) (w : H) (hw : w = o + orthogonalCoordinateSum L (t, g t)) :
      L.orthogonalProjectionOnto (w - o) = t := by
    have heq : w - o = (t : H) + (g t : H) := by
      rw [hw]
      change o + ((t : H) + (g t : H)) - o = _
      abel
    rw [heq, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property, add_zero]
  have hrootOf (t : U) (w : Z) (hw : (w : H) = o + orthogonalCoordinateSum L (t, g t))
      (hc : z - (w : H) ∈ (actualZeroSetTangentSpace k Z w)ᗮ)
      (hsize : ‖(t : L) - u‖ ≤ R) : (t : L) - u = h z := by
    have heq := normal_equation_of_actual_normal_graph hemb L o g U hg hgraph t w hw z hc
    have hcorrect : u + ((t : L) - u) = t := by abel
    have hzero : ((t : L) - u) +
        (ContinuousLinearMap.adjoint (fderiv ℝ g (u + ((t : L) - u))))
          (g (u + ((t : L) - u)) - v) = 0 := by
      simpa only [hcorrect, u, v] using heq
    exact (hunique z hz ((t : L) - u)
      (by simpa only [mem_closedBall, dist_zero_right] using hsize)).mp hzero
  have hy3 : (y : H) ∈ ball o (3 * R) := ball_subset_ball (by linarith) hy
  obtain ⟨t, ht, hty⟩ := hsheet y ⟨y.property, hy3⟩
  have htc : t - u = -L.orthogonalProjectionOnto n := by
    have hp := hproj t y hty
    dsimp only [u, z]
    have heq : (y : H) + n - o = ((y : H) - o) + n := by abel
    rw [heq, map_add, hp]
    abel
  have htn : ‖t - u‖ ≤ R := by
    rw [htc, norm_neg]
    exact (L.norm_orthogonalProjectionOnto_apply_le n).trans (by linarith)
  have hnt : z - (y : H) ∈ (actualZeroSetTangentSpace k Z y)ᗮ := by
    simpa only [z, add_sub_cancel_left] using hnormal
  have hct := hrootOf ⟨t, ht⟩ y hty hnt htn
  let w : Z := p ⟨z, hz⟩
  obtain ⟨hzw, hwnear, s, hs, hsw⟩ := minimizer_mem_buffered_normal_graph L o g Z R a
    hR ha hvalue hgraph hsheet z w hz w.property (hnearest ⟨z, hz⟩)
  have hs4 : s ∈ ball (0 : L) (4 * R) := ball_subset_ball (by linarith) hs
  have hsn : z - (w : H) ∈ (actualZeroSetTangentSpace k Z w)ᗮ :=
    nearestPoint_residual_mem_actual_normal hemb z w (hnearest ⟨z, hz⟩)
  have heq := normal_equation_of_actual_normal_graph hemb L o g U hg hgraph
    ⟨s, hs4⟩ w hsw z hsn
  have hvnorm : ‖v‖ ≤ R :=
    (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans
      (by simpa only [mem_ball, dist_eq_norm] using (show dist z o < R from hz).le)
  have hres : ‖g s - v‖ ≤ (a + 1) * R := by
    have hle := (norm_sub_le (g s) v).trans (add_le_add (hvalue s hs4) hvnorm)
    nlinarith
  have hsmall : ‖(ContinuousLinearMap.adjoint (fderiv ℝ g s)) (g s - v)‖ ≤ R / 4 := by
    calc
      _ ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ g s)‖ * ‖g s - v‖ :=
        (ContinuousLinearMap.adjoint (fderiv ℝ g s)).le_opNorm _
      _ = ‖fderiv ℝ g s‖ * ‖g s - v‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ a * ((a + 1) * R) := mul_le_mul (hfirst s hs4) hres (norm_nonneg _) ha0
      _ ≤ R / 4 := by nlinarith [mul_le_mul_of_nonneg_left ha ha0]
  have hsc : ‖s - u‖ ≤ R := by
    change s - u + (ContinuousLinearMap.adjoint (fderiv ℝ g s)) (g s - v) = 0 at heq
    rw [eq_neg_of_add_eq_zero_left heq, norm_neg]
    exact hsmall.trans (by linarith)
  have hcs := hrootOf ⟨s, hs4⟩ w hsw hsn hsc
  have hts : t = s := by have he := hct.trans hcs.symm; exact sub_left_injective he
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  change (w : H) = (y : H)
  rw [hsw, hty, hts]

end GC.MetricGeometry
