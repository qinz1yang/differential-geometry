import DifferentialGeometry.Topology.LocalDegree.SphereMap
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false

open Filter Metric Set
open scoped Topology unitInterval

noncomputable section

namespace DifferentialGeometry.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_uniform_linearization_error {f : E → F} {x : E}
    (A : E ≃L[ℝ] F) (hz : f x = 0) (hd : HasFDerivAt f A.toContinuousLinearMap x) :
    ∃ R > 0, ∀ v : E, ‖v‖ ≤ R → ‖f (x + v) - A v‖ ≤ ‖A v‖ / 2 := by
  let C : ℝ := ‖A.symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound
    (show 0 < (2 * C)⁻¹ by positivity)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε / 2, by positivity, ?_⟩
  intro v hv
  have herr : ‖f (x + v) - A v‖ ≤ (2 * C)⁻¹ * ‖v‖ := by
    have hvball : v ∈ ball (0 : E) ε := by
      rw [mem_ball, dist_zero_right]
      linarith
    simpa [hz] using hball hvball
  have hbound : ‖v‖ ≤ C * ‖A v‖ := by
    have hi := A.symm.toContinuousLinearMap.le_opNorm (A v)
    simp only [ContinuousLinearEquiv.coe_coe, A.symm_apply_apply] at hi
    dsimp [C]
    nlinarith [norm_nonneg (A v)]
  calc
    ‖f (x + v) - A v‖ ≤ (2 * C)⁻¹ * ‖v‖ := herr
    _ ≤ (2 * C)⁻¹ * (C * ‖A v‖) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ‖A v‖ / 2 := by field_simp

private theorem linearization_ne_zero {f : E → F} {x v : E}
    (A : E ≃L[ℝ] F) (hv : v ≠ 0)
    (herr : ‖f (x + v) - A v‖ ≤ ‖A v‖ / 2) (t : I) :
    (1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v ≠ 0 := by
  have hAv : 0 < ‖A v‖ := norm_pos_iff.mpr (by simpa using A.injective.ne hv)
  have hscale : ‖(1 - (t : ℝ)) • (f (x + v) - A v)‖ ≤ ‖A v‖ / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.property.2)]
    calc
      (1 - (t : ℝ)) * ‖f (x + v) - A v‖ ≤ ‖f (x + v) - A v‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (by linarith [t.property.1])
      _ ≤ ‖A v‖ / 2 := herr
  intro heq
  have hid : (1 - (t : ℝ)) • (f (x + v) - A v) = -A v := by
    calc
      (1 - (t : ℝ)) • (f (x + v) - A v) =
          ((1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v) - A v := by module
      _ = -A v := by rw [heq, zero_sub]
  rw [hid, norm_neg] at hscale
  linarith

theorem exists_pos_linearization_nonzero {f : E → F} {x : E}
    (A : E ≃L[ℝ] F) (hz : f x = 0) (hd : HasFDerivAt f A.toContinuousLinearMap x) :
    ∃ R > 0, ∀ v : E, ‖v‖ ≤ R → v ≠ 0 → ∀ t : I,
      (1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v ≠ 0 := by
  obtain ⟨R, hR, herr⟩ := exists_uniform_linearization_error A hz hd
  exact ⟨R, hR, fun v hv hv0 t ↦ linearization_ne_zero A hv0 (herr v hv) t⟩

private theorem nonzero_of_linearization {f : E → F} {x : E} {R : ℝ}
    {A : E ≃L[ℝ] F}
    (hn : ∀ v : E, ‖v‖ ≤ R → v ≠ 0 → ∀ t : I,
      (1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v ≠ 0) :
    ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0 := by
  intro y hy hyx
  have hv : ‖y - x‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hy
  simpa using hn (y - x) hv (sub_ne_zero.mpr hyx) 0

private theorem norm_sphere_smul {R : ℝ} (r : Ioc (0 : ℝ) R)
    (v : sphere (0 : E) 1) : ‖(r : ℝ) • (v : E)‖ = (r : ℝ) := by
  rw [norm_smul, Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]

private theorem sphere_linearization_nonzero {f : E → F} {x : E} {R : ℝ}
    {A : E ≃L[ℝ] F}
    (hn : ∀ v : E, ‖v‖ ≤ R → v ≠ 0 → ∀ t : I,
      (1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v ≠ 0)
    (r : Ioc (0 : ℝ) R) (t : I) (v : sphere (0 : E) 1) :
    (1 - (t : ℝ)) • f (x + (r : ℝ) • (v : E)) +
      (t : ℝ) • A ((r : ℝ) • (v : E)) ≠ 0 := by
  apply hn
  · rw [norm_sphere_smul]
    exact r.property.2
  · apply norm_pos_iff.mp
    rw [norm_sphere_smul]
    exact r.property.1

private def normalizedLinearizationHomotopy {f : E → F} {x : E} {R : ℝ}
    (A : E ≃L[ℝ] F) (hf : ContinuousOn f (closedBall x R))
    (hn : ∀ v : E, ‖v‖ ≤ R → v ≠ 0 → ∀ t : I,
      (1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v ≠ 0)
    (r : Ioc (0 : ℝ) R) :
    (sphereMap f x R hf (nonzero_of_linearization hn) r).Homotopy
      (sphereMap A 0 R A.continuous.continuousOn
        (fun _ _ hy ↦ mt A.map_eq_zero_iff.mp hy) r) where
  toFun p := (homeomorphUnitSphereProd F
    ⟨(1 - (p.1 : ℝ)) • f (x + (r : ℝ) • (p.2 : E)) +
      (p.1 : ℝ) • A ((r : ℝ) • (p.2 : E)), sphere_linearization_nonzero hn r p.1 p.2⟩).1
  continuous_toFun := by
    have hq : Continuous (fun p : I × sphere (0 : E) 1 ↦ (r : ℝ) • (p.2 : E)) :=
      continuous_const.smul (continuous_subtype_val.comp continuous_snd)
    have harg : Continuous (fun p : I × sphere (0 : E) 1 ↦
        x + (r : ℝ) • (p.2 : E)) := continuous_const.add hq
    have hfp := hf.comp_continuous harg (fun p ↦ by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_sphere_smul]
      exact r.property.2)
    have ht : Continuous (fun p : I × sphere (0 : E) 1 ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hcont : Continuous (fun p : I × sphere (0 : E) 1 ↦
        (1 - (p.1 : ℝ)) • f (x + (r : ℝ) • (p.2 : E)) +
          (p.1 : ℝ) • A ((r : ℝ) • (p.2 : E))) :=
      ((continuous_const.sub ht).smul hfp).add (ht.smul (A.continuous.comp hq))
    exact (homeomorphUnitSphereProd F).continuous.fst.comp
      (hcont.subtype_mk (fun p ↦ sphere_linearization_nonzero hn r p.1 p.2))
  map_zero_left v := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe]
  map_one_left v := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe]

theorem exists_sphereMap_linearization_homotopy {f : E → F} {x : E} {s : Set E}
    (A : E ≃L[ℝ] F) (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s)
    (hz : f x = 0) (hd : HasFDerivAt f A.toContinuousLinearMap x) :
    ∃ R > 0, ∃ hc : ContinuousOn f (closedBall x R),
      ∃ hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0,
        ∀ r : Ioc (0 : ℝ) R,
          ∃ H : (sphereMap f x R hc hzero r).Homotopy
            (sphereMap A 0 R A.continuous.continuousOn
              (fun _ _ hy ↦ mt A.map_eq_zero_iff.mp hy) r),
            ∀ t : I, ∀ v : sphere (0 : E) 1,
              (H (t, v) : F) =
                ‖(1 - (t : ℝ)) • f (x + (r : ℝ) • (v : E)) +
                  (t : ℝ) • A ((r : ℝ) • (v : E))‖⁻¹ •
                ((1 - (t : ℝ)) • f (x + (r : ℝ) • (v : E)) +
                  (t : ℝ) • A ((r : ℝ) • (v : E))) := by
  obtain ⟨R₀, hR₀, hn₀⟩ := exists_pos_linearization_nonzero A hz hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let R := min R₀ (ε / 2)
  have hR : 0 < R := lt_min hR₀ (by positivity)
  have hc : ContinuousOn f (closedBall x R) := hf.mono (fun y hy ↦
    hball (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hy))
  have hn : ∀ v : E, ‖v‖ ≤ R → v ≠ 0 → ∀ t : I,
      (1 - (t : ℝ)) • f (x + v) + (t : ℝ) • A v ≠ 0 :=
    fun v hv ↦ hn₀ v (hv.trans (min_le_left _ _))
  refine ⟨R, hR, hc, nonzero_of_linearization hn, fun r ↦
    ⟨normalizedLinearizationHomotopy A hc hn r, fun t v ↦ ?_⟩⟩
  exact homeomorphUnitSphereProd_apply_fst_coe F _

end DifferentialGeometry.LocalDegree
