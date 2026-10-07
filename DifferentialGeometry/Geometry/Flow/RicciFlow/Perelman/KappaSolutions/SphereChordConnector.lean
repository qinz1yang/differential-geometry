import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereShortConnector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The short round-sphere connector retains the chord bound for its own angle. -/
theorem sphere2_exists_chord_controlled_curve (p q : SpatialNeckSphere) :
    ∃ (L : ℝ) (γ : ℝ → SpatialNeckSphere),
      L ∈ Icc 0 Real.pi ∧ L ≤ Real.pi / 2 * ‖(p : EuclideanSpace ℝ (Fin 3)) - q‖ ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ ∧ γ 0 = p ∧ γ 1 = q ∧
      ∀ t : ℝ, (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
        (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = L ^ 2 := by
  classical
  by_cases hpq : p = q
  · refine ⟨0, fun _ => p, ⟨le_rfl, Real.pi_pos.le⟩, by positivity,
      contMDiff_const, rfl, hpq, ?_⟩
    intro t
    simp only [mfderiv_const, zero_apply, map_zero]
    norm_num
  have hdata : ∃ (L : ℝ) (v : EuclideanSpace ℝ (Fin 3))
      (hv : ‖v‖ = 1) (hpv : ⟪(p : EuclideanSpace ℝ (Fin 3)), v⟫ = 0),
      L ∈ Icc 0 Real.pi ∧ greatCircle p v hv hpv L = q := by
    by_cases hanti : q = -p
    · obtain ⟨v, hv, hpv⟩ := sphere2_exists_unit_orthogonal p
      refine ⟨Real.pi, v, hv, hpv, ⟨Real.pi_pos.le, le_rfl⟩, ?_⟩
      apply Subtype.ext
      simp only [greatCircle_val, Real.cos_pi, Real.sin_pi, neg_one_smul,
        zero_smul, add_zero, hanti, coe_neg_sphere]
    · have hqp : (q : EuclideanSpace ℝ (Fin 3)) ≠ (p : EuclideanSpace ℝ (Fin 3)) :=
        fun heq => hpq (Subtype.ext heq).symm
      have hqnp : (q : EuclideanSpace ℝ (Fin 3)) ≠ -(p : EuclideanSpace ℝ (Fin 3)) :=
        fun heq => hanti (Subtype.ext heq)
      obtain ⟨hL, hpv, hv, heq⟩ := polar_decomp
        (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere q) hqp hqnp
      refine ⟨Real.arccos ⟪(p : EuclideanSpace ℝ (Fin 3)),
        (q : EuclideanSpace ℝ (Fin 3))⟫, _, hv, hpv, ⟨hL.1.le, hL.2.le⟩, ?_⟩
      exact Subtype.ext heq
  obtain ⟨L, v, hv, hpv, hL, hend⟩ := hdata
  have hpqInner : ⟪(p : EuclideanSpace ℝ (Fin 3)),
      (q : EuclideanSpace ℝ (Fin 3))⟫ = Real.cos L := by
    rw [← hend, greatCircle_val, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p,
      hpv]
    ring
  have hchord : ‖(p : EuclideanSpace ℝ (Fin 3)) - q‖ ^ 2 = 2 - 2 * Real.cos L := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q, hpqInner,
      real_inner_comm (p : EuclideanSpace ℝ (Fin 3)) (q : EuclideanSpace ℝ (Fin 3)),
      hpqInner]
    ring
  have hcos := Real.cos_le_one_sub_mul_cos_sq
    (show |L| ≤ Real.pi by
      rw [abs_of_nonneg hL.1]
      exact hL.2)
  have hsq : L ^ 2 ≤ (Real.pi / 2 * ‖(p : EuclideanSpace ℝ (Fin 3)) - q‖) ^ 2 := by
    have hmul : 2 * L ^ 2 ≤ (1 - Real.cos L) * Real.pi ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp
      calc
        2 * L ^ 2 / Real.pi ^ 2 = 2 / Real.pi ^ 2 * L ^ 2 := by ring
        _ ≤ 1 - Real.cos L := by linarith
    have hscaled := congrArg (fun r : ℝ => Real.pi ^ 2 * r) hchord
    nlinarith [hscaled]
  have hbound : L ≤ Real.pi / 2 * ‖(p : EuclideanSpace ℝ (Fin 3)) - q‖ := by
    have hnonneg : 0 ≤ Real.pi / 2 * ‖(p : EuclideanSpace ℝ (Fin 3)) - q‖ :=
      mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) (norm_nonneg _)
    nlinarith [hL.1]
  let γ : ℝ → SpatialNeckSphere := fun t => greatCircle p v hv hpv (L * t)
  have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => L * t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  refine ⟨L, γ, hL, hbound, (greatCircle_smooth (n := 2) p v hv hpv).comp hlin,
    ?_, ?_, ?_⟩
  · simp only [γ, mul_zero, greatCircle_zero]
  · simpa only [γ, mul_one] using hend
  · intro t
    exact sphere2_greatCircle_rescaled_speed p v hv hpv L t

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
