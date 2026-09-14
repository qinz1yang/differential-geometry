import DifferentialGeometry.Geometry.Curvature.RoundSphere
import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem metricScalarAt_roundMetric_eq (hn : 0 < n) (x : Metric.sphere (0 : E) 1) :
    metricScalarAt (roundMetric (E := E) (n := n)) x = (n : ℝ) * ((n : ℝ) - 1) := by
  have hne : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact Nat.pos_iff_ne_zero.mp hn⟩
  have hsec : ∀ u v : TangentSpace (𝓡 n) x,
      metricRm04StandardAt (roundMetric (E := E) (n := n)) x u v v u =
        1 * ((roundMetric (E := E) (n := n)).inner x u u *
            (roundMetric (E := E) (n := n)).inner x v v -
          ((roundMetric (E := E) (n := n)).inner x u v) ^ 2) := by
    intro u v
    simpa only [one_mul, pow_two] using roundMetric_sec_value (E := E) (n := n) x u v
  have h := DifferentialGeometry.Geometry.Riemannian.metricScalarAt_of_constant_sectional
    (I := 𝓡 n) (M := Metric.sphere (0 : E) 1) (roundMetric (E := E) (n := n)) x 1 hsec
  rw [finrank_euclideanSpace_fin, mul_one] at h
  exact h

theorem metricScalarAt_scaledRoundSphere_eq (c : ℝ) (hc : 0 < c) (hn : 0 < n)
    (x : Metric.sphere (0 : E) 1) :
    metricScalarAt (scaleMetric c hc (roundMetric (E := E) (n := n))) x =
      c⁻¹ * ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [metricScalarAt_scaleMetric, metricScalarAt_roundMetric_eq hn x]

theorem metricScalarAt_normalizedRoundSphere_eq (hn : 2 ≤ n) (x : Metric.sphere (0 : E) 1) :
    metricScalarAt
        (scaleMetric ((n : ℝ) * ((n : ℝ) - 1))
          (by
            have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
            nlinarith)
          (roundMetric (E := E) (n := n))) x = 1 := by
  have hn0 : 0 < n := by omega
  have hc : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    nlinarith
  rw [metricScalarAt_scaledRoundSphere_eq _ hc hn0 x]
  exact inv_mul_cancel₀ (ne_of_gt hc)

theorem ricciTensor_normalizedRoundSphere_eq (hn : 2 ≤ n) (x : Metric.sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    ricciTensor
        (scaleMetric ((n : ℝ) * ((n : ℝ) - 1))
          (by
            have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
            nlinarith)
          (roundMetric (E := E) (n := n))) x v w =
      (1 / (n : ℝ)) *
        (scaleMetric ((n : ℝ) * ((n : ℝ) - 1))
          (by
            have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
            nlinarith)
          (roundMetric (E := E) (n := n))).inner x v w := by
  have hc : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    nlinarith
  rw [ricciTensor_scaledRoundSphere _ hc x v w]
  have hne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact ne_of_gt this
  have hne1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hcoef : ((n : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / (n : ℝ) := by
    field_simp
  rw [hcoef]

section RoundCylinder

private local instance roundCylinderThreeSpace :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem roundCylinderModel_axis_inner
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (cylinderAxis x) z = z.2 := by
  let gS := scaleMetric 2 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  change (cylinderMetric gS).inner x (cylinderAxis x) z = z.2
  rw [cylinderMetric_inner]
  change gS.inner x.1 (0 : TangentSpace (𝓡 2) x.1) z.1 + (1 : ℝ) * z.2 = z.2
  rw [map_zero]
  change (0 : ℝ) + 1 * z.2 = z.2
  ring

theorem ricciSharp_roundCylinderModel_eq
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z =
      (1 / 2 : ℝ) • (z -
        (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
          (cylinderAxis x) z • cylinderAxis x) := by
  have haxis := roundCylinderModel_axis_inner x z
  rw [haxis]
  refine (ricciSharp_roundCylinder (E := EuclideanSpace ℝ (Fin 3)) (n := 2) x z).trans ?_
  apply Prod.ext
  · change (((2 : ℝ) - 1) / 2) • z.1 = (1 / 2 : ℝ) •
      (z.1 - z.2 • (0 : EuclideanSpace ℝ (Fin 2)))
    norm_num
  · change (0 : ℝ) = (1 / 2 : ℝ) * (z.2 - z.2 * 1)
    ring

theorem ricciSharp_roundCylinderModel_axis_eq_zero
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x
      (cylinderAxis x) = 0 := by
  let gS := scaleMetric 2 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  have hunit : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (cylinderAxis x) (cylinderAxis x) = 1 :=
    cylinderMetric_axis_unit gS x
  rw [ricciSharp_roundCylinderModel_eq x (cylinderAxis x), hunit, one_smul, sub_self, smul_zero]

theorem ricciSharp_roundCylinderModel_eq_zero_iff
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z = 0 ↔
      z = (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (cylinderAxis x) z • cylinderAxis x := by
  rw [ricciSharp_roundCylinderModel_eq x z, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by norm_num)
    · exact sub_eq_zero.mp h
  · intro hz'
    right
    let gS := scaleMetric 2 (by norm_num)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    have hunit : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (cylinderAxis x) (cylinderAxis x) = 1 :=
      cylinderMetric_axis_unit gS x
    have hsmul : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (cylinderAxis x)
          ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
            (cylinderAxis x) z • cylinderAxis x) =
        (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
          (cylinderAxis x) z := by
      rw [map_smul, hunit, smul_eq_mul, mul_one]
    rw [hz', hsmul, sub_self]

theorem ricciSharp_roundCylinderModel_eq_half_smul_of_axis_inner_eq_zero
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x)
    (hz : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (cylinderAxis x) z = 0) :
    ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z =
      (1 / 2 : ℝ) • z := by
  rw [ricciSharp_roundCylinderModel_eq x z, hz, zero_smul, sub_zero]

theorem roundCylinderModel_axis_ne_zero
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    (cylinderAxis x : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) ≠ 0 := by
  let gS := scaleMetric 2 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  have hunit : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (cylinderAxis x) (cylinderAxis x) = 1 :=
    cylinderMetric_axis_unit gS x
  intro hzero
  rw [hzero] at hunit
  simp at hunit

theorem inner_ricciSharp_roundCylinderModel_eq
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z)
        (ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z) =
      (1 / 4 : ℝ) * (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (z - (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
          (cylinderAxis x) z • cylinderAxis x)
        (z - (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
          (cylinderAxis x) z • cylinderAxis x) := by
  rw [ricciSharp_roundCylinderModel_eq]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem inner_ricciSharp_roundCylinderModel_le
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z)
        (ricciSharp (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x z) ≤
      (1 / 4 : ℝ) *
        (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x z z := by
  let gS := scaleMetric 2 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  have hunit : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (cylinderAxis x) (cylinderAxis x) = 1 :=
    cylinderMetric_axis_unit gS x
  have hsymm : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x z
      (cylinderAxis x) =
      (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (cylinderAxis x) z :=
    (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).symm x z (cylinderAxis x)
  have hexp : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (z - (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (cylinderAxis x) z • cylinderAxis x)
      (z - (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
        (cylinderAxis x) z • cylinderAxis x) =
      (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x z z -
        ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
          (cylinderAxis x) z) ^ 2 := by
    simp only [map_sub, sub_apply, map_smul, smul_apply, hunit, hsymm, smul_eq_mul]
    ring
  rw [inner_ricciSharp_roundCylinderModel_eq, hexp]
  have hsq : 0 ≤ ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (cylinderAxis x) z) ^ 2 := sq_nonneg _
  linarith

theorem metricScalarAt_roundCylinderModel_eq_one
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    metricScalarAt (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x = 1 := by
  rw [metricScalarAt_roundCylinder (E := EuclideanSpace ℝ (Fin 3)) (n := 2) x]
  norm_num

end RoundCylinder

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
