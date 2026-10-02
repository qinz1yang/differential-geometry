import DifferentialGeometry.Analysis.InnerProductSpace.NormalEquationCorrectionJets
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraph
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphStationarity

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u

theorem exists_bound_nearest_tangent_correction_jets (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [CompleteSpace L]
        (o : H) (g : L → Lᗮ) (W : Set H) (P : H → H) (R a : ℝ),
        0 < R → 0 ≤ a → a ≤ 1 / 100 →
        ContDiffOn ℝ (m + 1 : ℕ) g (ball (0 : L) (4 * R)) →
        (∀ i ≤ m + 1, ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ a * R * (R⁻¹) ^ i) →
        (∀ t ∈ ball (0 : L) (4 * R),
          o + orthogonalCoordinateSum L (t, g t) ∈ W) →
        (∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
          y = o + orthogonalCoordinateSum L (t, g t)) →
        (∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun w => dist z w) W (P z)) →
        let c : H → L := fun z =>
          L.orthogonalProjectionOnto (P z - o) - L.orthogonalProjectionOnto (z - o)
        ContDiffOn ℝ m c (ball o R) ∧
          ∀ z ∈ ball o R, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j c z‖ ≤ B * a * R * (R⁻¹) ^ j := by
  obtain ⟨B, hB, hconstruct⟩ :=
    exists_uniform_nearest_normal_equation_correction_jets.{u} m hm
  refine ⟨B, hB, ?_⟩
  intro H _ _ _ L _ o g W P R a hR ha0 ha hg hjet hgraph hsheet hnearest
  obtain ⟨h, hh, _hroot, hunique, hjets⟩ := hconstruct H L o g R a hR ha0 ha hg hjet
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
  let c : H → L := fun z => L.orthogonalProjectionOnto (P z - o) - u z
  have hg2 : ContDiffOn ℝ 2 g (ball (0 : L) (4 * R)) :=
    hg.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hdg : ContDiffOn ℝ 1 (fderiv ℝ g) (ball (0 : L) (4 * R)) :=
    hg2.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdiff (t : L) (ht : t ∈ ball (0 : L) (4 * R)) :
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (fderiv ℝ g) t :=
    ⟨(hg2.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by norm_num),
      (hdg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by norm_num)⟩
  have heq (z : H) (hz : z ∈ ball o R) : c z = h z := by
    obtain ⟨_, _, t, ht, hrep⟩ := minimizer_mem_buffered_normal_graph L o g W R a
      hR ha hvalue hgraph hsheet z (P z) hz (hnearest z hz).1 (hnearest z hz).2
    have ht4 : t ∈ ball (0 : L) (4 * R) := by
      have ht' : dist t 0 < 5 * R / 2 := ht
      change dist t 0 < 4 * R
      linarith
    have hproj : L.orthogonalProjectionOnto (P z - o) = t := by
      have hsub : P z - o = (t : H) + (g t : H) := by
        rw [hrep]
        change (o + ((t : H) + (g t : H))) - o = _
        abel
      rw [hsub, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property,
        add_zero]
    have huz : o + orthogonalCoordinateSum L (u z, v z) = z := by
      change o + (L.starProjection (z - o) + Lᗮ.starProjection (z - o)) = z
      rw [L.starProjection_add_starProjection_orthogonal]
      abel
    have hmin : IsMinOn (fun w => dist (o + orthogonalCoordinateSum L (u z, v z)) w)
        W (o + orthogonalCoordinateSum L (t, g t)) := by
      rw [huz, ← hrep]
      exact (hnearest z hz).2
    have hstation := normal_equation_of_isMinOn_normal_graph L o g (ball 0 (4 * R))
      W (u z) t (v z) (isOpen_ball.mem_nhds ht4) (hdiff t ht4).1 hgraph hmin
    have hvnorm : ‖v z‖ ≤ R :=
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans
        (by simpa only [dist_eq_norm] using (show dist z o < R from hz).le)
    have hsmall := (normal_graph_remainder_small_of_scaled_bounds g t (v z) R a hR ha
      (hdiff t ht4).1 (hdiff t ht4).2 (hvalue t ht4) (hfirst t ht4)
      (hsecond t ht4) hvnorm).1
    have hnsmall : ‖t - u z‖ ≤ R / 4 := by
      rw [eq_neg_of_add_eq_zero_left hstation, norm_neg]
      exact hsmall
    have hnmem : t - u z ∈ closedBall (0 : L) R := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hcorrect : u z + (t - u z) = t := by abel
    have hzero : (t - u z) +
        (ContinuousLinearMap.adjoint (fderiv ℝ g (u z + (t - u z))))
          (g (u z + (t - u z)) - v z) = 0 := by
      simpa only [hcorrect] using hstation
    have hid := (hunique z hz (t - u z) hnmem).mp hzero
    change L.orthogonalProjectionOnto (P z - o) - u z = h z
    simpa only [hproj] using hid
  change ContDiffOn ℝ m c (ball o R) ∧ _
  refine ⟨hh.congr heq, ?_⟩
  intro z hz j hj
  have hevent : c =ᶠ[𝓝 z] h := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact heq y hy
  rw [(hevent.iteratedFDeriv ℝ j).eq_of_nhds]
  exact hjets z hz j hj

end DifferentialGeometry.Analysis
