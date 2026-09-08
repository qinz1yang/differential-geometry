import DifferentialGeometry.Bundle.Hom.Regularity
import DifferentialGeometry.Tensor.Alternating.BundleCompSmooth
import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConn
import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  {n : Nat} [Fact (Module.finrank Real A = n + 1)]

private theorem sphere_inner_self (y : Metric.sphere (0 : A) 1) :
    inner Real (y : A) (y : A) = 1 := by
  rw [real_inner_self_eq_norm_sq, (mem_sphere_zero_iff_norm.mp y.2)]
  norm_num

private theorem sphere_inner_dIncl (y : Metric.sphere (0 : A) 1)
    (v : TangentSpace (𝓡 n) y) : inner Real (y : A) (dIncl (n := n) y v) = 0 := by
  rw [← dInclEquiv_coe (n := n) y]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (dInclEquiv (n := n) y v).property

private def cylinderTangentFramingMap (x : Metric.sphere (0 : A) 1 × Real) :
    TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x →L[Real] A :=
  (dIncl (n := n) x.1).coprod ((ContinuousLinearMap.id Real Real).smulRight (x.1 : A))

private theorem cylinderTangentFramingMap_apply (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    cylinderTangentFramingMap x v = dIncl (n := n) x.1 v.1 + v.2 • (x.1 : A) := rfl

private theorem cylinderTangentFramingMap_inner (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    inner Real (x.1 : A) (cylinderTangentFramingMap x v) = v.2 := by
  rw [cylinderTangentFramingMap_apply, inner_add_right, inner_smul_right]
  erw [sphere_inner_dIncl, sphere_inner_self]
  simp only [mul_one, zero_add]

private theorem cylinderTangentFramingMap_bijective (x : Metric.sphere (0 : A) 1 × Real) :
    Function.Bijective (cylinderTangentFramingMap (n := n) x) := by
  constructor
  · intro u v huv
    have hs : u.2 = v.2 := by
      rw [← cylinderTangentFramingMap_inner x u, ← cylinderTangentFramingMap_inner x v, huv]
    apply Prod.ext
    · apply injective_mvfderiv_subtypeVal_sphere x.1
      have h := huv
      rw [cylinderTangentFramingMap_apply, cylinderTangentFramingMap_apply, hs] at h
      exact add_right_cancel h
    · exact hs
  · intro w
    let a := inner Real (x.1 : A) w
    have hz : w - a • (x.1 : A) ∈ (Real ∙ (x.1 : A))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        inner_smul_right, sphere_inner_self, mul_one]
      exact sub_self a
    let v := (dInclEquiv (n := n) x.1).symm ⟨w - a • (x.1 : A), hz⟩
    refine ⟨(v, a), ?_⟩
    change dIncl (n := n) x.1 v + a • (x.1 : A) = w
    rw [← dInclEquiv_coe (n := n) x.1]
    have hv : (dInclEquiv (n := n) x.1) v = ⟨w - a • (x.1 : A), hz⟩ :=
      (dInclEquiv (n := n) x.1).apply_symm_apply _
    rw [hv]
    exact sub_add_cancel w (a • (x.1 : A))

def cylinderTangentFraming (x : Metric.sphere (0 : A) 1 × Real) :
    TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x ≃L[Real] A := by
  let _ : FiniteDimensional Real A :=
    FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
  let _ : FiniteDimensional Real (TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :=
    inferInstanceAs (FiniteDimensional Real (EuclideanSpace Real (Fin n) × Real))
  let _ : T2Space (TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :=
    inferInstanceAs (T2Space (EuclideanSpace Real (Fin n) × Real))
  exact LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective (cylinderTangentFramingMap x).toLinearMap
      (cylinderTangentFramingMap_bijective x))

@[simp] theorem cylinderTangentFraming_apply (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    cylinderTangentFraming x v = dIncl (n := n) x.1 v.1 + v.2 • (x.1 : A) := rfl


theorem cylinderTangentFraming_contMDiff :
    ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, A) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
          (Metric.sphere (0 : A) 1 × Real) => cylinderTangentFraming v.proj v.2) := by
  have hsplit := contMDiff_equivTangentBundleProd (n := ∞)
    (I := 𝓡 n) (M := Metric.sphere (0 : A) 1) (I' := 𝓘(Real, Real)) (M' := Real)
  have hsphere : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent (𝓡 n).tangent ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) =>
        (⟨v.proj.1, v.2.1⟩ : TangentBundle (𝓡 n) (Metric.sphere (0 : A) 1))) :=
    contMDiff_fst.comp hsplit
  have hreal : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, Real).tangent ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) =>
        (⟨v.proj.2, v.2.2⟩ : TangentBundle 𝓘(Real, Real) Real)) :=
    contMDiff_snd.comp hsplit
  have hinc := (show ContMDiff (𝓡 n) 𝓘(Real, A) ∞
      (Subtype.val : Metric.sphere (0 : A) 1 → A) from contMDiff_coe_sphere).contMDiff_tangentMap
    (m := ∞) (by simp)
  have hhor : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, A) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) => dIncl (n := n) v.proj.1 v.2.1) := by
    exact (contMDiff_snd_tangentBundle_modelSpace A 𝓘(Real, A)).comp
      (hinc.comp hsphere)
  have hver : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, Real) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) => v.2.2) :=
    (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp hreal
  have hbase : ContMDiff ((𝓡 n).prod 𝓘(Real, Real)).tangent 𝓘(Real, A) ∞
      (fun v : TangentBundle ((𝓡 n).prod 𝓘(Real, Real))
        (Metric.sphere (0 : A) 1 × Real) => (v.proj.1 : A)) :=
    contMDiff_coe_sphere.comp ((contMDiff_proj (TangentSpace (𝓡 n))).comp hsphere)
  exact hhor.add (hver.smul hbase)


theorem cylinderTangentFraming_prodCongr (e : A ≃ₗᵢ[Real] A)
    (psi : Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real)
    (x : Metric.sphere (0 : A) 1 × Real)
    (v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    let _ : FiniteDimensional Real A :=
      FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
    cylinderTangentFraming ((sphereDiffeo (n := n) e).prodCongr psi x)
      (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real))
        ((sphereDiffeo (n := n) e).prodCongr psi) x v) =
      e (dIncl (n := n) x.1 v.1 +
        (show Real from mfderiv 𝓘(Real, Real) 𝓘(Real, Real) psi x.2 v.2) • (x.1 : A)) := by
  let _ : FiniteDimensional Real A :=
    FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
  dsimp only
  rw [cylinderTangentFraming_apply]
  change dIncl (n := n) (sphereDiffeo (n := n) e x.1)
    (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real))
      (Prod.map (sphereDiffeo (n := n) e) psi) x v).1 +
    (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real))
      (Prod.map (sphereDiffeo (n := n) e) psi) x v).2 •
      (sphereDiffeo (n := n) e x.1 : A) = _
  rw [mfderiv_prodMap ((sphereDiffeo (n := n) e).contMDiff.mdifferentiableAt (by simp))
    (psi.contMDiff.mdifferentiableAt (by simp))]
  erw [mfderiv_incl_sphereDiffeo]
  rw [sphereDiffeo_coe, map_add]
  erw [map_smul]
  rfl

theorem cylinderTangentFraming_hom_contMDiff :
    ContMDiff ((𝓡 n).prod 𝓘(Real, Real))
      (((𝓡 n).prod 𝓘(Real, Real)).prod
        𝓘(Real, (EuclideanSpace Real (Fin n) × Real) →L[Real] A)) ∞
      (fun x : Metric.sphere (0 : A) 1 × Real =>
        (⟨x, (cylinderTangentFraming x).toContinuousLinearMap⟩ :
          TotalSpace ((EuclideanSpace Real (Fin n) × Real) →L[Real] A)
            (fun x => TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x →L[Real]
              Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) A x))) := by
  apply ContMDiff.clm_bundle_of_map
  intro v
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiff_proj (TangentSpace ((𝓡 n).prod 𝓘(Real, Real))) v, ?_⟩
  exact cylinderTangentFraming_contMDiff v


def cylinderDifferentialForm {k : Nat} (α : A [⋀^Fin k]→L[Real] Real) :
    DifferentialForm ((𝓡 n).prod 𝓘(Real, Real)) (Metric.sphere (0 : A) 1 × Real) k := by
  refine ⟨fun x => α.compContinuousLinearMap (cylinderTangentFraming x).toContinuousLinearMap, ?_⟩
  have hα : ContMDiff ((𝓡 n).prod 𝓘(Real, Real))
      (((𝓡 n).prod 𝓘(Real, Real)).prod 𝓘(Real, A [⋀^Fin k]→L[Real] Real)) ∞
      (fun x : Metric.sphere (0 : A) 1 × Real =>
        (⟨x, α⟩ : TotalSpace (A [⋀^Fin k]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin k) A
            (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) A) Real
              (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) Real)))) := by
    intro x
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    have heq : (fun y : Metric.sphere (0 : A) 1 × Real =>
        (trivializationAt (A [⋀^Fin k]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin k) A
            (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) A) Real
              (Bundle.Trivial (Metric.sphere (0 : A) 1 × Real) Real)) x ⟨y, α⟩).2) =
        fun _ => α := by
      funext y
      rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
      ext v
      simp [ContinuousAlternatingMap.inCoordinates]
    rw [heq]
    exact contMDiffAt_const
  exact hα.alternating_bundle_comp cylinderTangentFraming_hom_contMDiff

@[simp] theorem cylinderDifferentialForm_apply {k : Nat}
    (α : A [⋀^Fin k]→L[Real] Real) (x : Metric.sphere (0 : A) 1 × Real)
    (v : Fin k → TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    cylinderDifferentialForm α x v = α (fun i => cylinderTangentFraming x (v i)) := rfl

theorem cylinderDifferentialForm_ne_zero {k : Nat}
    (α : A [⋀^Fin k]→L[Real] Real) (hα : α ≠ 0)
    (x : Metric.sphere (0 : A) 1 × Real) : cylinderDifferentialForm (n := n) α x ≠ 0 := by
  intro h
  apply hα
  ext v
  have hv := congrArg (fun β : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x [⋀^Fin k]→L[Real] Real =>
    β (fun i => (cylinderTangentFraming x).symm (v i))) h
  simpa [cylinderDifferentialForm_apply] using hv

end DifferentialGeometry.Geometry
