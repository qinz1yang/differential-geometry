import DifferentialGeometry.Analysis.Calculus.Inverse.ContractionGraphJets
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Rescaling

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u v

theorem exists_uniform_scaled_contraction_graph_jets (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (N : Type u) (E : Type v)
        [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
        [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (U : Set E) (W : Set (E × N)), IsOpen U → IsOpen W →
        ∀ r δ : ℝ, 0 < r → 0 ≤ δ → δ ≤ 1 →
        U ×ˢ closedBall (0 : N) r ⊆ W →
        ∀ e : E × N → N, ContDiffOn ℝ (max m 1 : ℕ) e W →
        (∀ t ∈ U, ∀ z ∈ closedBall (0 : N) r, ‖e (t,z)‖ ≤ r / 4) →
        (∀ t ∈ U, ∀ z ∈ closedBall (0 : N) r,
          ‖fderiv ℝ (fun w : N => e (t,w)) z‖ ≤ 1 / 2) →
        (∀ p ∈ W, ∀ i, i ≤ m →
          ‖iteratedFDeriv ℝ i e p‖ ≤ C * δ * r * (r⁻¹)^i) →
        ∃ g : E → N, ContDiffOn ℝ (max m 1 : ℕ) g U ∧
          (∀ t ∈ U, ‖g t‖ ≤ r / 4 ∧ g t + e (t,g t) = 0) ∧
          (∀ t ∈ U, ∀ z ∈ closedBall (0 : N) r,
            z + e (t,z) = 0 ↔ z = g t) ∧
          ∀ t ∈ U, ∀ j, j ≤ m →
            ‖iteratedFDeriv ℝ j g t‖ ≤ B * δ * r * (r⁻¹)^j := by
  obtain ⟨B, hB, hconstruct⟩ := exists_uniform_contraction_graph_jets.{u,v} m C hC
  refine ⟨B, hB, ?_⟩
  intro N E _ _ _ _ _ _ U W hU hW r δ hr hδ0 hδ1 hcylinder e he hsmall hnormal herr
  let U' : Set E := (fun t : E => r • t) ⁻¹' U
  let W' : Set (E × N) := (fun p : E × N => r • p) ⁻¹' W
  let e' : E × N → N := fun p => r⁻¹ • e (r • p)
  have hU' : IsOpen U' := hU.preimage (continuous_const_smul r)
  have hW' : IsOpen W' := hW.preimage (continuous_const_smul r)
  have hnorm (z : N) : ‖r • z‖ = r * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hnorminv (z : N) : ‖r⁻¹ • z‖ = r⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hball (z : N) (hz : z ∈ closedBall (0 : N) 1) : r • z ∈ closedBall (0 : N) r := by
    rw [mem_closedBall, dist_zero_right] at hz ⊢
    rw [hnorm]
    nlinarith
  have hcyl' : U' ×ˢ closedBall (0 : N) 1 ⊆ W' := by
    intro p hp
    exact hcylinder ⟨hp.1, hball p.2 hp.2⟩
  have he' : ContDiffOn ℝ (max m 1 : ℕ) e' W' :=
    (he.comp (contDiff_const_smul r).contDiffOn (fun _ hp => hp)).const_smul r⁻¹
  have hsmall' : ∀ t ∈ U', ∀ z ∈ closedBall (0 : N) 1, ‖e' (t,z)‖ ≤ 1 / 4 := by
    intro t ht z hz
    change ‖r⁻¹ • e (r • t,r • z)‖ ≤ 1 / 4
    rw [hnorminv]
    calc
      _ ≤ r⁻¹ * (r / 4) := mul_le_mul_of_nonneg_left
        (hsmall (r • t) ht (r • z) (hball z hz)) (inv_nonneg.mpr hr.le)
      _ = 1 / 4 := by field_simp
  have hnormal' : ∀ t ∈ U', ∀ z ∈ closedBall (0 : N) 1,
      ‖fderiv ℝ (fun w : N => e' (t,w)) z‖ ≤ 1 / 2 := by
    intro t ht z hz
    have h := norm_iteratedFDeriv_rescale (fun n : N => e (r • t,n)) r hr 1 (r • z)
    simp only [inv_smul_smul₀ hr.ne', pow_one, inv_mul_cancel₀ hr.ne', one_mul,
      norm_iteratedFDeriv_one] at h
    change ‖fderiv ℝ (fun n : N => r⁻¹ • e (r • t,r • n)) z‖ ≤ 1 / 2
    rw [h]
    exact hnormal (r • t) ht (r • z) (hball z hz)
  have herr' : ∀ p ∈ W', ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i e' p‖ ≤ C * δ := by
    intro p hp i hi
    have h := norm_iteratedFDeriv_rescale e r hr i (r • p)
    simp only [inv_smul_smul₀ hr.ne'] at h
    change ‖iteratedFDeriv ℝ i (fun q => r⁻¹ • e (r • q)) p‖ ≤ C * δ
    rw [h]
    calc
      _ ≤ (r⁻¹ * r^i) * (C * δ * r * (r⁻¹)^i) :=
        mul_le_mul_of_nonneg_left (herr (r • p) hp i hi) (by positivity)
      _ = C * δ := by rw [inv_pow]; field_simp
  obtain ⟨g', hg', hvalue', huniq', hjet'⟩ :=
    hconstruct N E U' W' hU' hW' 1 δ (by norm_num) hδ0 hδ1 hcyl' e' he'
      hsmall' hnormal' herr'
  let g : E → N := fun t => r • g' (r⁻¹ • t)
  have hscaled (t : E) (ht : t ∈ U) : r⁻¹ • t ∈ U' := by
    change r • (r⁻¹ • t) ∈ U
    rwa [smul_inv_smul₀ hr.ne']
  have hg : ContDiffOn ℝ (max m 1 : ℕ) g U :=
    (hg'.comp (contDiff_const_smul r⁻¹).contDiffOn hscaled).const_smul r
  have hvalue (t : E) (ht : t ∈ U) : ‖g t‖ ≤ r / 4 ∧ g t + e (t,g t) = 0 := by
    have hv := hvalue' (r⁻¹ • t) (hscaled t ht)
    constructor
    · change ‖r • g' (r⁻¹ • t)‖ ≤ r / 4
      rw [hnorm]
      nlinarith [hv.1]
    · have h := congrArg (fun z : N => r • z) hv.2
      simpa only [e', smul_add, smul_zero, Prod.smul_mk, smul_inv_smul₀ hr.ne'] using h
  refine ⟨g, hg, hvalue, ?_, ?_⟩
  · intro t ht z hz
    constructor
    · intro hzroot
      have hz' : r⁻¹ • z ∈ closedBall (0 : N) 1 := by
        rw [mem_closedBall, dist_zero_right] at hz ⊢
        rw [hnorminv]
        exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hr.le)).trans_eq
          (inv_mul_cancel₀ hr.ne')
      have heq : r⁻¹ • z + e' (r⁻¹ • t,r⁻¹ • z) = 0 := by
        simpa only [e', Prod.smul_mk, smul_inv_smul₀ hr.ne', smul_add, smul_zero] using
          congrArg (fun n : N => r⁻¹ • n) hzroot
      have h := (huniq' (r⁻¹ • t) (hscaled t ht) (r⁻¹ • z) hz').mp heq
      simpa only [smul_inv_smul₀ hr.ne'] using congrArg (fun n : N => r • n) h
    · rintro rfl
      exact (hvalue t ht).2
  · intro t ht j hj
    change ‖iteratedFDeriv ℝ j (fun y => r • g' (r⁻¹ • y)) t‖ ≤ _
    rw [iteratedFDeriv_smul_comp_smul_of_ne_zero g' r⁻¹ r (inv_ne_zero hr.ne') hr.ne',
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ r * (r⁻¹)^j)]
    calc
      _ ≤ (r * (r⁻¹)^j) * (B * δ) :=
        mul_le_mul_of_nonneg_left (hjet' (r⁻¹ • t) (hscaled t ht) j hj) (by positivity)
      _ = B * δ * r * (r⁻¹)^j := by ring

end DifferentialGeometry.Analysis
