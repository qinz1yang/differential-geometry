import DifferentialGeometry.Tensor.Exterior.Cotangent
import DifferentialGeometry.Tensor.Exterior.Exact
import DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter FiberBundle
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem extend_eq_symmL
    (x : M) (v : TangentSpace I x) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    FiberBundle.extend E v y =
      (trivializationAt E (TangentSpace I) x).symmL Real y
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  unfold FiberBundle.extend
  rw [e.symmL_apply hy, e.apply_eq_prod_continuousLinearEquivAt Real x hx v]
  apply congrArg (e.symm y)
  exact congrFun (e.coe_continuousLinearEquivAt_eq (R := Real) hx) v

set_option backward.isDefEq.respectTransparency false in
private theorem mlieBracket_extend_extend_eq_zero
    (x : M) (v w : TangentSpace I x) :
    VectorField.mlieBracket I (FiberBundle.extend E v) (FiberBundle.extend E w) x = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  let e := trivializationAt E (TangentSpace I) x
  let vE := e.continuousLinearMapAt Real x v
  let wE := e.continuousLinearMapAt Real x w
  have hleft :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x).symm
          (FiberBundle.extend E v) (Set.range I) =ᶠ[nhdsWithin (extChartAt I x x) (Set.range I)]
        fun _ : E => vE := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    simp only [VectorField.mpullbackWithin_apply]
    have hysrc : (extChartAt I x).symm y ∈ (chartAt H x).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x).map_target hy
    have hybase : (extChartAt I x).symm y ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hysrc
    rw [extend_eq_symmL (I := I) x v hybase]
    rw [TangentBundle.symmL_trivializationAt hysrc]
    rw [(extChartAt I x).right_inv hy]
    exact ContinuousLinearMap.IsInvertible.inverse_apply_self
      (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy) vE
  have hright :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x).symm
          (FiberBundle.extend E w) (Set.range I) =ᶠ[nhdsWithin (extChartAt I x x) (Set.range I)]
        fun _ : E => wE := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    simp only [VectorField.mpullbackWithin_apply]
    have hysrc : (extChartAt I x).symm y ∈ (chartAt H x).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x).map_target hy
    have hybase : (extChartAt I x).symm y ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hysrc
    rw [extend_eq_symmL (I := I) x w hybase]
    rw [TangentBundle.symmL_trivializationAt hysrc]
    rw [(extChartAt I x).right_inv hy]
    exact ContinuousLinearMap.IsInvertible.inverse_apply_self
      (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy) wE
  have hleft' :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x).symm
          (FiberBundle.extend E v) (Set.range I) =ᶠ[
            nhdsWithin (extChartAt I x x)
              ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I)]
        fun _ : E => vE := by
    simpa using hleft
  have hright' :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x).symm
          (FiberBundle.extend E w) (Set.range I) =ᶠ[
            nhdsWithin (extChartAt I x x)
              ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I)]
        fun _ : E => wE := by
    simpa using hright
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft' hright' (by simp)]
  change (mfderiv I 𝓘(Real, E) (extChartAt I x) x).inverse
    (VectorField.lieBracketWithin Real (fun _ : E => vE) (fun _ : E => wE)
      ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x)) = 0
  rw [show VectorField.lieBracketWithin Real (fun _ : E => vE) (fun _ : E => wE)
      ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x) = 0 by
    simp [VectorField.lieBracketWithin]]
  exact ContinuousLinearMap.map_zero _

omit [IsManifold I ∞ M] in
private theorem mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    [BoundarylessManifold I M]
    {f : M → Real} {φ : E → Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hφ : writtenInExtChartAt I 𝓘(Real, Real) x f =ᶠ[nhds (extChartAt I x x)] φ)
    (v : TangentSpace I x) :
    mvfderiv (I := I) f x v = fderiv Real φ (extChartAt I x x) v := by
  rw [mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt (I := I) hf]
  have hzint : extChartAt I x x ∈ interior (Set.range I) := by
    exact interior_mono (extChartAt_target_subset_range x)
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp
        (BoundarylessManifold.isInteriorPoint (I := I) (M := M) (x := x)))
  rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hzint)]
  rw [hφ.fderiv_eq]
  rfl

private def cotangentLocalRep
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x)))
    (x : M) : E → E [⋀^Fin 1]→L[Real] Real := fun z =>
  (trivializationAt (E [⋀^Fin 1]→L[Real] Real)
    (Bundle.continuousAlternatingMap Real (Fin 1) E (TangentSpace I) Real
      (Bundle.Trivial M Real)) x
    ⟨(extChartAt I x).symm z, ofCotangent theta htheta ((extChartAt I x).symm z)⟩).2

private theorem cotangentLocalRep_apply_const_eventuallyEq
    [BoundarylessManifold I M]
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x)))
    (x : M) (w : TangentSpace I x) :
    writtenInExtChartAt I 𝓘(Real, Real) x
        (fun y : M => theta y (FiberBundle.extend E w y)) =ᶠ[
          nhds (extChartAt I x x)]
      fun z => cotangentLocalRep theta htheta x z
        (fun _ : Fin 1 =>
          (trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x w) := by
  have hzint : extChartAt I x x ∈ interior ((extChartAt I x).target) :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (M := M) (x := x))
  filter_upwards [mem_interior_iff_mem_nhds.mp hzint] with z hz
  have hysrc : (extChartAt I x).symm z ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz
  have hybase : (extChartAt I x).symm z ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa [extChartAt_source] using hysrc
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [show FiberBundle.extend E w ((extChartAt I x).symm z) =
      (trivializationAt E (TangentSpace I) x).symmL Real ((extChartAt I x).symm z)
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x w) by
    exact extend_eq_symmL (I := I) x w hybase]
  unfold cotangentLocalRep
  rw [continuousAlternatingMap_trivializationAt_apply]
  change theta ((extChartAt I x).symm z)
      ((trivializationAt E (TangentSpace I) x).symmL Real ((extChartAt I x).symm z)
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x w)) =
    theta ((extChartAt I x).symm z)
      ((trivializationAt E (TangentSpace I) x).symmL Real ((extChartAt I x).symm z)
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x w))
  rfl

private theorem exteriorDerivative_ofCotangent_apply_eq_mvfderiv_sub
    [BoundarylessManifold I M]
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x)))
    (x : M) (v w : TangentSpace I x) :
    exteriorDerivative (ofCotangent theta htheta) x ![v, w] =
      mvfderiv (I := I) (fun y : M => theta y (FiberBundle.extend E w y)) x v -
        mvfderiv (I := I) (fun y : M => theta y (FiberBundle.extend E v y)) x w := by
  let alpha := ofCotangent theta htheta
  let e := trivializationAt E (TangentSpace I) x
  let ed := trivializationAt (E [⋀^Fin 2]→L[Real] Real)
    (Bundle.continuousAlternatingMap Real (Fin 2) E (TangentSpace I) Real
      (Bundle.Trivial M Real)) x
  have he : e.continuousLinearMapAt Real x = ContinuousLinearMap.id Real E := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp)]
    apply ContinuousLinearMap.ext
    intro u
    exact tangentCoordChange_self (I := I) (x := x) (z := x) (by simp)
  let vE : E := e.continuousLinearMapAt Real x v
  let wE : E := e.continuousLinearMapAt Real x w
  have hvE : vE = v := by
    change e.continuousLinearMapAt Real x v = v
    rw [he]
    rfl
  have hwE : wE = w := by
    change e.continuousLinearMapAt Real x w = w
    rw [he]
    rfl
  have hstep : exteriorDerivativeAt alpha x ![v, w] =
      (ed ⟨x, exteriorDerivativeAt alpha x⟩).2 ![vE, wE] := by
    rw [continuousAlternatingMap_trivializationAt_apply]
    change exteriorDerivativeAt alpha x ![v, w] =
      exteriorDerivativeAt alpha x (e.symmL Real x ∘ ![vE, wE])
    apply congrArg (exteriorDerivativeAt alpha x)
    funext i
    fin_cases i
    · simpa [vE] using (Trivialization.symmL_continuousLinearMapAt
        (R := Real) e (mem_baseSet_trivializationAt E (TangentSpace I) x) v).symm
    · simpa [wE] using (Trivialization.symmL_continuousLinearMapAt
        (R := Real) e (mem_baseSet_trivializationAt E (TangentSpace I) x) w).symm
  have hloc := exteriorDerivative_localRepresentation (IM := I) (M := M)
    (α := alpha) (x₀ := x) (x := x) (mem_extChartAt_source x)
    (BoundarylessManifold.isInteriorPoint (I := I) (M := M) (x := x))
  have hloc' : (ed ⟨x, exteriorDerivativeAt alpha x⟩).2 =
      extDeriv (cotangentLocalRep theta htheta x) (extChartAt I x x) := by
    change (ed ⟨x, exteriorDerivativeAt alpha x⟩).2 =
      extDeriv (cotangentLocalRep theta htheta x) (extChartAt I x x) at hloc
    exact hloc
  have hzint : extChartAt I x x ∈ interior (extChartAt I x).target :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (M := M) (x := x))
  have hrep : DifferentiableAt Real (cotangentLocalRep theta htheta x)
      (extChartAt I x x) := by
    exact ((localRep_contDiffOn alpha x).contDiffAt
      (mem_interior_iff_mem_nhds.mp hzint)).differentiableAt (by simp)
  have hremove₀ : (Fin.removeNth (n := 1) 0 ![vE, wE]) = fun _ : Fin 1 => wE := by
    funext i
    fin_cases i
    rfl
  have hremove₁ : (Fin.removeNth (n := 1) 1 ![vE, wE]) = fun _ : Fin 1 => vE := by
    funext i
    fin_cases i
    rfl
  have heventw := cotangentLocalRep_apply_const_eventuallyEq theta htheta x w
  have heventv := cotangentLocalRep_apply_const_eventuallyEq theta htheta x v
  change writtenInExtChartAt I 𝓘(Real, Real) x
      (fun y : M => theta y (FiberBundle.extend E w y)) =ᶠ[nhds (extChartAt I x x)]
        fun z => cotangentLocalRep theta htheta x z (fun _ : Fin 1 => wE) at heventw
  change writtenInExtChartAt I 𝓘(Real, Real) x
      (fun y : M => theta y (FiberBundle.extend E v y)) =ᶠ[nhds (extChartAt I x x)]
        fun z => cotangentLocalRep theta htheta x z (fun _ : Fin 1 => vE) at heventv
  have htheta' : Geometry.Connection.MDiffAtCotangent theta x := by
    exact (htheta x).mdifferentiableAt (by simp)
  have hpairw : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => theta y (FiberBundle.extend E w y)) x :=
    Geometry.Connection.mdifferentiableAt_pairing htheta'
      (mdifferentiableAt_extend I E w)
  have hpairv : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => theta y (FiberBundle.extend E v y)) x :=
    Geometry.Connection.mdifferentiableAt_pairing htheta'
      (mdifferentiableAt_extend I E v)
  have hderivw := mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    hpairw heventw v
  have hderivv := mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    hpairv heventv w
  have hderivw' :
      mvfderiv (I := I) (fun y : M => theta y (FiberBundle.extend E w y)) x v =
        fderiv Real (fun z => cotangentLocalRep theta htheta x z
          (fun _ : Fin 1 => wE)) (extChartAt I x x) vE := by
    rw [hvE]
    exact hderivw
  have hderivv' :
      mvfderiv (I := I) (fun y : M => theta y (FiberBundle.extend E v y)) x w =
        fderiv Real (fun z => cotangentLocalRep theta htheta x z
          (fun _ : Fin 1 => vE)) (extChartAt I x x) wE := by
    rw [hwE]
    exact hderivv
  rw [exteriorDerivative_apply, hstep]
  change (ed ⟨x, exteriorDerivativeAt alpha x⟩).2 ![vE, wE] = _
  rw [hloc']
  rw [extDeriv_apply hrep ![vE, wE], Fin.sum_univ_two, hremove₀, hremove₁]
  norm_num
  simpa [sub_eq_add_neg] using congrArg₂ (fun a b : Real => a - b)
    hderivw'.symm hderivv'.symm

theorem exteriorDerivative_ofCotangent_apply
    [BoundarylessManifold I M] [FiniteDimensional Real E]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x)))
    (x : M) (v w : TangentSpace I x) :
    exteriorDerivative (ofCotangent theta htheta) x ![v, w] =
      ((Geometry.Connection.cotangentCov cov).toFun theta x v) w -
        ((Geometry.Connection.cotangentCov cov).toFun theta x w) v +
          theta x (cov.torsion x v w) := by
  rw [exteriorDerivative_ofCotangent_apply_eq_mvfderiv_sub]
  have htheta' : Geometry.Connection.MDiffAtCotangent theta x :=
    (htheta x).mdifferentiableAt (by simp)
  have hpairw := Geometry.Connection.cotangentCov_dualPairing cov htheta'
    (mdifferentiableAt_extend I E w) v
  have hpairv := Geometry.Connection.cotangentCov_dualPairing cov htheta'
    (mdifferentiableAt_extend I E v) w
  simp only [FiberBundle.extend_apply_self] at hpairw hpairv
  rw [hpairw, hpairv]
  have ht := cov.torsion_apply_eq_extend v w
  rw [mlieBracket_extend_extend_eq_zero] at ht
  simp only [FiberBundle.extend_apply_self, sub_zero] at ht
  rw [ht, map_sub]
  ring

theorem isClosed_of_cotangentCov_eq_zero_of_torsion_eq_zero
    [BoundarylessManifold I M] [FiniteDimensional Real E]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x)))
    (hcovtheta : (Geometry.Connection.cotangentCov cov).toFun theta = 0)
    (htorsion : cov.torsion = 0) :
    isClosed (ofCotangent theta htheta) := by
  rw [isClosed]
  apply ContMDiffSection.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu, exteriorDerivative_ofCotangent_apply cov theta htheta]
  simp [hcovtheta, htorsion]

end DifferentialForm
end DifferentialGeometry
