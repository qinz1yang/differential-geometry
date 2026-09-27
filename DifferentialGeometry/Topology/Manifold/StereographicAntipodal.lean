import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Topology.Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def sphereAntipodalDiffeomorph :
    Metric.sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : E) 1 where
  toFun := fun p => -p
  invFun := fun p => -p
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_neg_sphere
  contMDiff_invFun := contMDiff_neg_sphere

theorem stereographicInverse_antipodal (north : Metric.sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    (stereographic' n north).symm ((-4 / ‖x‖ ^ 2) • x) =
      -(stereographic' n north).symm x := by
  let U : (ℝ ∙ (north : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere north)).repr
  have hn (y : EuclideanSpace ℝ (Fin n)) : ‖(U.symm y : E)‖ = ‖y‖ := U.symm.norm_map y
  have hr : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hlarge : 16 / ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hnorm : ‖(-4 / ‖x‖ ^ 2) • x‖ ^ 2 = 16 / ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    ring
  have hlin : (U.symm ((-4 / ‖x‖ ^ 2) • x) : E) =
      (-4 / ‖x‖ ^ 2) • (U.symm x : E) := by simp only [map_smul, Submodule.coe_smul]
  have hfirst : ((16 / ‖x‖ ^ 2 + 4)⁻¹ * 4) * (-4 / ‖x‖ ^ 2) =
      -((‖x‖ ^ 2 + 4)⁻¹ * 4) := by
    field_simp
    ring
  have hsecond : (16 / ‖x‖ ^ 2 + 4)⁻¹ * (16 / ‖x‖ ^ 2 - 4) =
      -((‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4)) := by
    field_simp
    ring
  apply Subtype.ext
  change ((stereographic' n north).symm ((-4 / ‖x‖ ^ 2) • x) : E) =
    -((stereographic' n north).symm x : E)
  simp only [stereographic'_symm_apply]
  change (‖(U.symm ((-4 / ‖x‖ ^ 2) • x) : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) •
      (U.symm ((-4 / ‖x‖ ^ 2) • x) : E) +
      (‖(U.symm ((-4 / ‖x‖ ^ 2) • x) : E)‖ ^ 2 + 4)⁻¹ •
        (‖(U.symm ((-4 / ‖x‖ ^ 2) • x) : E)‖ ^ 2 - 4) • (north : E) =
    -((‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E) +
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • (north : E))
  simp only [hn]
  rw [hnorm]
  simp only [hlin, smul_smul, ← mul_assoc]
  rw [hfirst, hsecond]
  module

theorem stereographic_antipodal_coordinates (north : Metric.sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    stereographic' n north (sphereAntipodalDiffeomorph (n := n) ((stereographic' n north).symm x)) =
      (-4 / ‖x‖ ^ 2) • x := by
  change stereographic' n north (-(stereographic' n north).symm x) = _
  rw [← stereographicInverse_antipodal north x hx]
  exact (stereographic' n north).right_inv (by simp)
end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry

open Bundle Manifold Set Metric Module
open scoped Manifold ContDiff

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "S" => Metric.sphere (0 : V) 1

private local instance antipodalOrientationFact : Fact (Module.finrank ℝ V = 2 + 1) := ⟨by simp⟩

private noncomputable abbrev antipodalDiffeomorph : S ≃ₘ⟮𝓡 2, 𝓡 2⟯ S :=
  Topology.Manifold.sphereAntipodalDiffeomorph (E := V) (n := 2)

private theorem dIncl_antipodalDiffeomorph (x : S) (v : TangentSpace (𝓡 2) x) :
    Geometry.dIncl (n := 2) (-x) (mfderiv (𝓡 2) (𝓡 2) antipodalDiffeomorph x v) =
      -Geometry.dIncl (n := 2) x v := by
  have hc := mfderiv_comp_apply (x := x)
    ((contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp))
    (antipodalDiffeomorph.contMDiff.mdifferentiableAt (by simp)) v
  have hfun : (Subtype.val : S → V) ∘ antipodalDiffeomorph = -(Subtype.val : S → V) := rfl
  rw [hfun, mfderiv_neg] at hc
  exact hc.symm

private theorem det_entry_antipodal_eq (x : S)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x))
    (c : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (antipodalDiffeomorph x)))
    (hc : ∀ k : Fin 2, c k = mfderiv (𝓡 2) (𝓡 2) antipodalDiffeomorph x (b k)) :
    (fun i j : Fin 3 => ((Fin.cases (motive := fun _ => V) (((-x : S) : V))
        (fun k : Fin 2 => Geometry.dIncl (n := 2) (-x) (c k)) j : V) i)) =
      -(fun i j : Fin 3 => ((Fin.cases (motive := fun _ => V) (((x : S) : V))
        (fun k : Fin 2 => Geometry.dIncl (n := 2) x (b k)) j : V) i)) := by
  have key : ∀ j : Fin 3,
      (fun i : Fin 3 => ((Fin.cases (motive := fun _ => V) (((-x : S) : V))
        (fun k : Fin 2 => Geometry.dIncl (n := 2) (-x) (c k)) j : V) i)) =
      -(fun i : Fin 3 => ((Fin.cases (motive := fun _ => V) (((x : S) : V))
        (fun k : Fin 2 => Geometry.dIncl (n := 2) x (b k)) j : V) i)) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · funext i
      simp
    · funext i
      rw [Fin.cases_succ, Fin.cases_succ]
      simp [hc k, dIncl_antipodalDiffeomorph]
  funext i j
  exact congrFun (key j) i

private theorem sphereOutwardDeterminant_antipodal_eq_neg (x : S)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x))
    (c : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (antipodalDiffeomorph x)))
    (hc : ∀ k : Fin 2, c k = mfderiv (𝓡 2) (𝓡 2) antipodalDiffeomorph x (b k)) :
    sphereOutwardDeterminant 2 (antipodalDiffeomorph x) c =
      -sphereOutwardDeterminant 2 x b := by
  have hmat := det_entry_antipodal_eq x b c hc
  rw [sphereOutwardDeterminant]
  rw [sphereOutwardDeterminant]
  change Matrix.det (fun i j : Fin 3 => ((Fin.cases (motive := fun _ => V)
      (((-x : S) : V))
      (fun k : Fin 2 => Geometry.dIncl (n := 2) (-x) (c k)) j : V) i)) =
    -Matrix.det (fun i j : Fin 3 => ((Fin.cases (motive := fun _ => V) (((x : S) : V))
      (fun k : Fin 2 => Geometry.dIncl (n := 2) x (b k)) j : V) i))
  rw [hmat]
  have hneg := Matrix.det_neg (A := fun i j : Fin 3 =>
    ((Fin.cases (motive := fun _ => V) (((x : S) : V))
      (fun k : Fin 2 => Geometry.dIncl (n := 2) x (b k)) j : V) i))
  exact hneg.trans (by rw [Fintype.card_fin]; ring)

theorem sphereAntipodalDiffeomorph_preservesOrientation_opposite :
    (Topology.Manifold.sphereAntipodalDiffeomorph (E := V) (n := 2)).preservesOrientation
      (sphereOrientation 2 (by decide)) (sphereOrientation 2 (by decide)).opposite := by
  intro x
  set o := sphereOrientation 2 (by decide)
  have hfin : Module.Finite ℝ (TangentSpace (𝓡 2) x) := by
    change Module.Finite ℝ (EuclideanSpace ℝ (Fin 2))
    infer_instance
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace (𝓡 2) x) := by
    change Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
    simp
  let b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    Orientation.someBasis (o.orientation x) hcard
  have hb : b.orientation = o.orientation x := Orientation.someBasis_orientation _ _
  let DA : TangentSpace (𝓡 2) x ≃ₗ[ℝ] TangentSpace (𝓡 2) (antipodalDiffeomorph x) :=
    (antipodalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let c : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (antipodalDiffeomorph x)) := b.map DA
  have hc : ∀ k : Fin 2, c k = mfderiv (𝓡 2) (𝓡 2) antipodalDiffeomorph x (b k) := by
    intro k
    rw [show c k = DA (b k) from Basis.map_apply b DA k]
    exact congrArg (fun (L : TangentSpace (𝓡 2) x →L[ℝ]
      TangentSpace (𝓡 2) (antipodalDiffeomorph x)) =>
      L (b k)) (Diffeomorph.mfderivToContinuousLinearEquiv_coe antipodalDiffeomorph (by simp))
  have hpos : 0 < sphereOutwardDeterminant 2 x b :=
    (sphereOrientation_characterization 2 (by decide) x b).mp hb
  have hneg : sphereOutwardDeterminant 2 (antipodalDiffeomorph x) c < 0 := by
    have h := sphereOutwardDeterminant_antipodal_eq_neg x b c hc
    rw [h]
    linarith
  have hne : c.orientation ≠ o.orientation (antipodalDiffeomorph x) := by
    intro h
    have hlt :=
      (sphereOrientation_characterization 2 (by decide) (antipodalDiffeomorph x) c).mp h
    exact absurd hlt (not_lt.mpr (le_of_lt hneg))
  have hmap : Orientation.map (Fin 2) DA (o.orientation x) = c.orientation := by
    rw [← hb]
    exact (Basis.orientation_map b DA).symm
  rcases Basis.orientation_eq_or_eq_neg c (o.orientation (antipodalDiffeomorph x)) with h | h
  · exact absurd h.symm hne
  · rw [hmap, ManifoldOrientation.opposite_orientation, h]
    exact (neg_neg c.orientation).symm

end DifferentialGeometry
