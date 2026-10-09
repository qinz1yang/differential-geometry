import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.EuclideanLocalCk

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace DifferentialGeometry.Geometry

theorem christoffel_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {K' : ℕ} (hb : ContDiffOn ℝ K' b U)
    (hco : ∀ x ∈ U, IsCoercive (b x)) (hK : 1 ≤ K') :
    ContDiffOn ℝ ((K' - 1 : ℕ) : ℕ∞ω)
      (fun x => MetricKoszul.raisedKoszulOp (b x) (fderiv ℝ b x)) U := by
  obtain ⟨m, rfl⟩ : ∃ m, K' = m + 1 := ⟨K' - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [Nat.cast_add_one] at hb
  exact MetricKoszul.raisedOp_contDiffOn_succ hU hb hco

theorem exists_local_geodesic_flow_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ContinuousDualEquiv E] [FiniteDimensional ℝ E] {U : Set E}
    (hU : IsOpen U) {b : E → E →L[ℝ] E →L[ℝ] ℝ} {K' : ℕ} (hb : ContDiffOn ℝ K' b U)
    (hco : ∀ x ∈ U, IsCoercive (b x)) (hK : 2 ≤ K') {z₀ : E × E} (hz₀ : z₀.1 ∈ U) :
    ∃ (r : ℝ≥0) (ε : ℝ), 0 < (r : ℝ) ∧ 0 < ε ∧
      ∃ Φ : (E × E) × ℝ → E × E,
        Analysis.ODE.Flow.IsLocalFlow (fun _ z => MetricKoszul.metricSpray b z) 0 z₀ r (-ε) ε Φ ∧
        ContDiffOn ℝ ((K' - 1 : ℕ) : ℕ∞ω) Φ (closedBall z₀ (r : ℝ) ×ˢ Icc (-ε) ε) ∧
        MapsTo Φ (closedBall z₀ (r : ℝ) ×ˢ Icc (-ε) ε) (U ×ˢ univ) := by
  obtain ⟨m, rfl⟩ : ∃ m, K' = m + 1 + 1 := ⟨K' - 2, by omega⟩
  rw [Nat.cast_add_one] at hb
  have hF : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : ℕ∞ω) (MetricKoszul.metricSpray b)
      (U ×ˢ univ) := by
    exact_mod_cast MetricKoszul.metricSpray_contDiffOn_succ hU hb hco
  have hz : z₀ ∈ U ×ˢ univ := ⟨hz₀, mem_univ _⟩
  obtain ⟨r, ε, hr, hε, Φ, hflow, hΦ, hmaps⟩ :=
    Analysis.ODE.exists_confined_isLocalFlow_contDiffOn_of_contDiffOn
      (k := ((m + 1 : ℕ) : ℕ∞)) (by exact_mod_cast Nat.le_add_left 1 m)
      (hU.prod isOpen_univ) hF hz
  refine ⟨r, ε, hr, hε, Φ, hflow, ?_, hmaps⟩
  rw [Nat.add_sub_cancel]
  exact_mod_cast hΦ

theorem bilinearComp_fderiv_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} {b : E → E →L[ℝ] E →L[ℝ] ℝ} {h : E → E} {K' s : ℕ} (hV : IsOpen V)
    (hb : ContDiffOn ℝ K' b U) (hh : ContDiffOn ℝ s h V) (hhV : MapsTo h V U) (hs : 1 ≤ s) :
    ContDiffOn ℝ ((min K' (s - 1) : ℕ) : ℕ∞ω)
      (fun y => (b (h y)).bilinearComp (fderiv ℝ h y) (fderiv ℝ h y)) V := by
  generalize hn : min K' (s - 1) = n
  have hnK : (n : ℕ∞ω) ≤ K' := Nat.cast_le.mpr (by omega)
  have hns : (n : ℕ∞ω) ≤ s := Nat.cast_le.mpr (by omega)
  have hn1 : n + 1 ≤ s := by omega
  have hns1 : (n : ℕ∞ω) + 1 ≤ s := by exact_mod_cast hn1
  have hbh : ContDiffOn ℝ n (fun y => b (h y)) V := (hb.of_le hnK).comp (hh.of_le hns) hhV
  have hdh : ContDiffOn ℝ n (fderiv ℝ h) V := hh.fderiv_of_isOpen hV hns1
  have hA : ContDiffOn ℝ n (fun y => (b (h y)).comp (fderiv ℝ h y)) V := hbh.clm_comp hdh
  have hB : ContDiffOn ℝ n (fun y => ((b (h y)).comp (fderiv ℝ h y)).flip) V :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff.comp_contDiffOn hA
  have hC : ContDiffOn ℝ n
      (fun y => ((b (h y)).comp (fderiv ℝ h y)).flip.comp (fderiv ℝ h y)) V :=
    hB.clm_comp hdh
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff.comp_contDiffOn hC

end DifferentialGeometry.Geometry
