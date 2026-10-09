import DifferentialGeometry.Analysis.InnerProductSpace.NearestProjectionErrorJets
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphQuantitativeProjection

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u

theorem exists_uniform_buffered_normal_graph_nearest_all_jets :
    ∃ c : ℕ → ℝ, (∀ q, 0 ≤ c q) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [FiniteDimensional ℝ L]
        (m : ℕ), 1 ≤ m →
        ∀ (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ),
        0 < R → 0 ≤ a → a ≤ 1 / 100 →
        ContDiffOn ℝ (m + 1 : ℕ) g (ball (0 : L) (4 * R)) →
        (∀ i ≤ m + 1, ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ a * R * (R⁻¹) ^ i) →
        (∀ t ∈ ball (0 : L) (4 * R),
          o + orthogonalCoordinateSum L (t, g t) ∈ W) →
        (∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
          y = o + orthogonalCoordinateSum L (t, g t)) →
        ∃ P : H → H, ContDiffOn ℝ m P (ball o R) ∧
          (∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun y => dist z y) W (P z) ∧
            (∀ y ∈ W, IsMinOn (fun w => dist z w) W y → y = P z) ∧
            ‖P z - (o + L.starProjection (z - o))‖ ≤ 3 * a * R ∧
            ‖fderiv ℝ P z - L.starProjection‖ ≤ 7 * a ∧
            Module.finrank ℝ (LinearMap.range (fderiv ℝ P z).toLinearMap) =
              Module.finrank ℝ L ∧
            ∀ q, 2 ≤ q → q ≤ m →
              ‖iteratedFDeriv ℝ q (fun y => P y - (o + L.starProjection (y - o))) z‖ ≤
                c q * a * R * (R⁻¹) ^ q) ∧
          (ContDiffOn ℝ ∞ g (ball (0 : L) (4 * R)) → ContDiffOn ℝ ∞ P (ball o R)) := by
  classical
  choose c hc hbound using
    (fun q : ℕ => exists_bound_nearest_projection_error_jet.{u} (max q 1) (le_max_right _ _))
  refine ⟨c, hc, ?_⟩
  intro H _ _ _ L _ m hm o g W R a hR ha0 ha hg hjet hgraph hsheet
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
  obtain ⟨P, hP, hmin⟩ := exists_contDiffOn_unique_nearest_buffered_normal_graph_with_bounds
    L o g W R a m hm hR ha hg hvalue hfirst hsecond hgraph hsheet
  have hnearest : ∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun w => dist z w) W (P z) :=
    fun z hz => ⟨(hmin z hz).1, (hmin z hz).2.1⟩
  refine ⟨P, hP, ?_, ?_⟩
  · intro z hz
    have hp := hmin z hz
    refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
      hp.2.2.2.2.2, ?_⟩
    intro q hq2 hqm
    have hq1 : 1 ≤ q := by omega
    have hbq := hbound q
    rw [max_eq_left hq1] at hbq
    have hqg : ContDiffOn ℝ (q + 1 : ℕ) g (ball (0 : L) (4 * R)) :=
      hg.of_le (by exact_mod_cast (by omega : q + 1 ≤ m + 1))
    have hqjet : ∀ i ≤ q + 1, ∀ t ∈ ball (0 : L) (4 * R),
        ‖iteratedFDeriv ℝ i g t‖ ≤ a * R * (R⁻¹) ^ i :=
      fun i hi t ht => hjet i (by omega) t ht
    exact (hbq H L o g W P R a hR ha0 ha hqg hqjet hgraph hsheet hnearest).2 z hz
  · intro hgsmooth
    obtain ⟨Q, hQ, hQmin⟩ := exists_smooth_unique_nearest_buffered_normal_graph
      L o g W R a hR ha hgsmooth hvalue hfirst hsecond hgraph hsheet
    apply hQ.congr
    intro z hz
    exact ((hmin z hz).2.2.1 (Q z) (hQmin z hz).1 (hQmin z hz).2.1).symm

end DifferentialGeometry.Analysis
