import RicciFlower.Tensor.RSTensor.NablaOnTensors.RawDefs
import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.RSTensor.Components
import RicciFlower.Tensor.RSTensor.Basis
import RicciFlower.Tensor.Multilinear.Basis
import RicciFlower.VectorBundle.PartialMfderiv

/-!
# Local scalar derivation formulas for tensor nabla
-/
namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

private theorem fderivWithin_eq_sum_basis_coord
    {F : E -> E} {u : Set E} {y Xy : E}
    (hF : DifferentiableWithinAt 𝕜 F u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 F u y Xy =
      ∑ i : Fin (Module.finrank 𝕜 E),
        fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord i (F z)) u y Xy •
          (Module.finBasis 𝕜 E) i := by
  classical
  let b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  apply b.ext_elem
  intro i
  let L : E →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap (b.coord i)
  have hcomp :
      fderivWithin 𝕜 (fun z : E => L (F z)) u y =
        L.comp (fderivWithin 𝕜 F u y) := by
    have hlin :
        DifferentiableAt 𝕜 (fun w : E => L w) (F y) :=
      L.differentiableAt
    have hcomp0 :=
      (fderivWithin_comp (x := y) (f := F)
        (g := fun w : E => L w) (s := u) (t := Set.univ)
        (by simpa using hlin.differentiableWithinAt)
        hF (by intro z hz; simp) hu)
    rw [L.fderivWithin (s := Set.univ) (x := F y) uniqueDiffWithinAt_univ] at hcomp0
    simpa [L, b, Function.comp_def] using hcomp0
  have hcoord' :
      b.coord i ((fderivWithin 𝕜 F u y) Xy) =
        fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y Xy := by
    change L ((fderivWithin 𝕜 F u y) Xy) =
      fderivWithin 𝕜 (fun z : E => L (F z)) u y Xy
    rw [hcomp]
    simp [L, LinearMap.coe_toContinuousLinearMap']
  have hcoord :
      b.repr ((fderivWithin 𝕜 F u y) Xy) i =
        fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y Xy := by
    simpa [Module.Basis.coord_apply] using hcoord'
  rw [hcoord]
  change (fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y) Xy =
    b.coord i
      (∑ j : Fin (Module.finrank 𝕜 E),
        (fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord j (F z)) u y) Xy •
          (Module.finBasis 𝕜 E) j)
  rw [map_sum]
  simp only [b, Module.Basis.coord_apply, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hrepr :
        ((Module.finBasis 𝕜 E).repr ((Module.finBasis 𝕜 E) j)) i = 0 := by
      have hji : i ≠ j := fun h => hj h.symm
      rw [(Module.finBasis 𝕜 E).repr_self j]
      exact Finsupp.single_eq_of_ne hji
    rw [hrepr]
    simp
  · intro hi
    simp at hi

private theorem fderivWithin_chart_scalar_eq_extDerivFun
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (φ : E -> 𝕜) (f : M -> 𝕜)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀)
    (heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) :
    fderivWithin 𝕜 φ (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) f x₀ (X x₀) := by
  let z₀ : E := extChartAt I x₀ x₀
  have hzRange : z₀ ∈ Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hX :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hfd :
      fderivWithin 𝕜 φ (Set.range I) z₀ =
        fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f)
          (Set.range I) z₀ :=
    heq.fderivWithin_eq_of_mem hzRange
  change
    fderivWithin 𝕜 φ (Set.range I) z₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀) =
      (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (X x₀)
  rw [hX, hf.mfderiv, hfd]
  rfl

private theorem tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I)
          (fun p : M =>
            (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p))) x₀ (X x₀) •
          (Module.finBasis 𝕜 E) i := by
  classical
  let F : E -> E := tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
  let b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  have hbasis := fderivWithin_eq_sum_basis_coord
    (F := F) (u := Set.range I) (y := extChartAt I x₀ x₀)
    (Xy := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))
    hVmodel (I.uniqueDiffOn (extChartAt I x₀ x₀)
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  rw [hbasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  let f : M -> 𝕜 := fun p : M => b.coord i (F (extChartAt I x₀ p))
  let φ : E -> 𝕜 := fun y : E => b.coord i (F y)
  have hφ : DifferentiableWithinAt 𝕜 φ (Set.range I) (extChartAt I x₀ x₀) := by
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp_differentiableWithinAt
      (x := extChartAt I x₀ x₀) hVmodel
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hright : extChartAt I x₀ ((extChartAt I x₀).symm y) = y :=
      (extChartAt I x₀).right_inv hy
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    change b.coord i (F y) =
      b.coord i (F (extChartAt I x₀ ((extChartAt I x₀).symm y)))
    rw [hright]
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f (hcoord i) heq

theorem covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀) =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
  classical
  let b := Module.finBasis 𝕜 E
  let zfun : Fin (Module.finrank 𝕜 E) -> M -> 𝕜 :=
    fun i p =>
      b.coord i
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ p))
  have hsum := covariantDerivative_modelInChart_center_eq_sum
    (𝕜 := 𝕜) (I := I) cov (fun x => X x) V x₀ hV hcoord
  have hderiv :=
    tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
      (I := I) X V x₀ hVmodel hcoord
  calc
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀)
        =
      (∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I) (zfun i) x₀ (X x₀) • b i) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
          simpa [b, zfun] using hsum
    _ =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
          rw [hderiv]

private theorem tangentFieldModelInChart_center_symmL
    (V : (x : M) -> TangentSpace I x) (x₀ : M) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) =
      V x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  unfold tangentFieldModelInChart
  change e.symmL 𝕜 x₀
      (e.continuousLinearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (V ((extChartAt I x₀).symm (extChartAt I x₀ x₀)))) =
    V x₀
  rw [extChartAt_to_inv]
  exact e.symmL_continuousLinearMapAt
    (R := 𝕜) (FiberBundle.mem_baseSet_trivializationAt' x₀) (V x₀)

private theorem tensor0SModelInChart_apply_modelSlots_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
            (extChartAt I x₀ x₀)) =
      A x₀ (fun a : Fin s => V a x₀) := by
  rw [tensor0SModelInChart_apply]
  rw [extChartAt_to_inv]
  congr
  funext a
  exact tangentFieldModelInChart_center_symmL (I := I) (V a) x₀

private theorem tensor0SModelInChart_apply_update_modelSlot_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      A x₀ (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  rw [tensor0SModelInChart_apply]
  rw [extChartAt_to_inv]
  congr
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      Function.comp_apply, Function.update_self, Trivialization.symmL_apply]
    exact tangentFieldModelInChart_center_symmL (I := I) W x₀
  · simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      Function.comp_apply, Function.update_of_ne hb, Trivialization.symmL_apply]
    exact tangentFieldModelInChart_center_symmL (I := I) (V b) x₀

private theorem fderivWithin_tensor0S_eval_modelSlots_center_eq_extDerivFun {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ (fun x => α x) y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  let φ : E -> 𝕜 :=
    fun y : E =>
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) s x₀ (fun x => α x) y
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => α p (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

private theorem fderivWithin_localTensor0S_eval_modelSlots_center_eq_extDerivFun {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ β y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  let φ : E -> 𝕜 :=
    fun y : E =>
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) s x₀ β y
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => β p (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

set_option backward.isDefEq.respectTransparency false in
private theorem fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r s x₀ (fun x => T x) y
            (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r x₀ β y))
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  letI : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) := inferInstance
  let φ : E -> 𝕜 :=
    fun y : E =>
      (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r s x₀ (fun x => T x) y
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β y))
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => (T p (β p)) (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    unfold tensorRSModelInChart tensorRSModelAt
    rw [TensorRSSpace.trivializationAt_apply]
    · congr 2
      · unfold tensor0SModelInChart tensor0SModelAt
        let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀
        let p := (extChartAt I x₀).symm y
        have hbaseβ : p ∈ eβ.baseSet := hbase
        change eβ.symmL 𝕜 p ((eβ ⟨p, β p⟩).2) = β p
        have hcoord : (eβ ⟨p, β p⟩).2 = eβ.continuousLinearMapAt 𝕜 p (β p) := by
          rw [Bundle.Trivialization.continuousLinearMapAt_apply]
          rw [eβ.coe_linearMapAt_of_mem (R := 𝕜) hbaseβ]
        rw [hcoord]
        exact eβ.symmL_continuousLinearMapAt (R := 𝕜) hbaseβ (β p)
      · funext a
        unfold tangentFieldModelInChart
        exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
          (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
    · exact hbase
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

noncomputable def localCovariantDerivTensor0SAt (r : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M) : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ :=
  (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symm x₀
    (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (fun x => X x) (Set.range I))
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))

set_option backward.isDefEq.respectTransparency false in
theorem localCovariantDerivTensor0SAt_eval_moving_raw {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀) =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
        x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let βm : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) r :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x₀ β
  let Vm : Fin r -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin r -> E := fun a => Vm a y₀
  have hprod :=
    fderivWithin_tensor0SModel_eval_slots
      (𝕜 := 𝕜) (E := E) (s := r) βm Vm (Set.range I) y₀ Xmodel
      hβmodel hVmodel
      (I.uniqueDiffOn y₀
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => βm y (fun a : Fin r => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) := by
    simpa [βm, Vm, Xmodel, y₀] using
      fderivWithin_localTensor0S_eval_modelSlots_center_eq_extDerivFun
        (I := I) X β V x₀ hpair
  have hcov_model : ∀ a : Fin r,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hslots_center :
      (fun a : Fin r =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          (slots a)) =
        fun a : Fin r => V a x₀ := by
    funext a
    simpa [slots, Vm] using tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hleft_model :
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        (fun a : Fin r => V a x₀) =
      (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀) slots := by
    let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀
    let Mβ : Tensor0SModel r 𝕜 E :=
      covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀
    have hcoordEval :
        ((eβ ⟨x₀, localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2)
            slots =
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
            (fun a : Fin r => V a x₀) := by
      have h := Tensor0SSpace.trivializationAt_apply
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        slots
      rw [hslots_center] at h
      exact h
    have hmodel :
        (eβ ⟨x₀, localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2 =
          Mβ := by
      unfold localCovariantDerivTensor0SAt
      change (eβ ⟨x₀, eβ.symm x₀ Mβ⟩).2 = Mβ
      rw [eβ.apply_mk_symm
        (mem_baseSet_trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀)]
    calc
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        (fun a : Fin r => V a x₀)
          = ((eβ ⟨x₀, localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2)
              slots := hcoordEval.symm
      _ = Mβ slots := by rw [hmodel]
  have hcorr_sum :
      ∑ a : Fin r,
        βm y₀
          (Function.update slots a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) =
      ∑ a : Fin r,
        β x₀
          (Function.update (fun b : Fin r => V b x₀) a
            ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    exact tensor0SModelInChart_apply_update_modelSlot_center
      (I := I) β V (fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀)
        =
      (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀) slots := hleft_model
    _ =
      fderivWithin 𝕜 βm (Set.range I) y₀ Xmodel slots -
        ∑ a : Fin r, βm y₀ (Function.update slots a (Γ (slots a))) := by
          simp [covariantDeriv_tensor0SModelWithin_apply_slots, βm, Xmodel, Γ, slots, y₀]
    _ =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) -
        ∑ a : Fin r,
          βm y₀
            (Function.update slots a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) := by
          rw [← hpair_deriv]
          rw [hprod]
          simp_rw [(βm y₀).map_update_add]
          rw [Finset.sum_add_distrib]
          abel
    _ =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hcorr_sum]

/-- Subtracting two local covariant derivatives of the same moving covariant
input tensor cancels the exterior derivative term and leaves only the
connection-difference action on the input slots. -/
theorem localCovDeriv0S_sub {r : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀
        (fun a : Fin r => V a x₀) -
      localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀
        (fun a : Fin r => V a x₀)) =
      -∑ a : Fin r,
        β x₀
          (Function.update (fun b : Fin r => V b x₀) a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
  classical
  let slots : Fin r -> TangentSpace I x₀ := fun a => V a x₀
  have hcov := localCovariantDerivTensor0SAt_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X β V x₀ hpair hβmodel hV hVmodel hcoord
  have hcov' := localCovariantDerivTensor0SAt_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov' X β V x₀ hpair hβmodel hV hVmodel hcoord
  have hdiff (a : Fin r) :
      β x₀
          (Function.update slots a ((cov (V a) x₀) (X x₀))) -
        β x₀
          (Function.update slots a ((cov' (V a) x₀) (X x₀))) =
        β x₀
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
    have hconn :
        ((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀) =
          ((cov (V a) x₀) (X x₀)) - ((cov' (V a) x₀) (X x₀)) := by
      have h :=
        IsCovariantDerivativeOn.difference_apply
          (hcov := cov.isCovariantDerivativeOnUniv)
          (hcov' := cov'.isCovariantDerivativeOnUniv)
          (σ := V a) (x := x₀) (hx := by trivial) (hV a)
      exact congrArg (fun L : TangentSpace I x₀ →L[𝕜] TangentSpace I x₀ => L (X x₀)) h
    rw [hconn]
    exact ((β x₀).map_update_sub slots a
      ((cov (V a) x₀) (X x₀))
      ((cov' (V a) x₀) (X x₀))).symm
  let D : 𝕜 :=
    extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
      x₀ (X x₀)
  let S : (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) -> 𝕜 :=
    fun cov =>
      ∑ a : Fin r,
        β x₀
          (Function.update slots a ((cov (V a) x₀) (X x₀)))
  rw [hcov, hcov']
  change (D - S cov) - (D - S cov') =
    -∑ a : Fin r,
      β x₀
        (Function.update slots a
          (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀)))
  have hS :
      S cov - S cov' =
        ∑ a : Fin r,
          β x₀
            (Function.update slots a
              (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
    simp only [S]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => hdiff a
  rw [← hS]
  abel

/-- Component form of `localCovDeriv0S_sub`, after expanding the changed input
slot in a pointwise tangent basis. -/
theorem component0S_localCovDeriv0S_sub {r : ℕ}
    {Idx : Type*} [Fintype Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x₀))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpair : forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M => β p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord j
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀)
    (slots : Fin r -> Idx) :
    component0S (I := I) basis
        (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀ -
          localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀)
        slots =
      -∑ a : Fin r, ∑ k : Idx,
        basis.coord k
          (((CovariantDerivative.difference cov cov' x₀) (basis (slots a))) (X x₀)) *
          component0S (I := I) basis (β x₀) (Function.update slots a k) := by
  classical
  let Vslots : Fin r -> (x : M) -> TangentSpace I x := fun a => V (slots a)
  have hraw := localCovDeriv0S_sub
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) cov cov' X β Vslots x₀
    (hpair slots) hβmodel
    (fun a => hV (slots a))
    (fun a => hVmodel (slots a))
    (fun a j => hcoord (slots a) j)
  have hraw_basis :
      (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
          (fun a : Fin r => basis (slots a)) -
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀)
          (fun a : Fin r => basis (slots a)) =
        -∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => basis (slots b)) a
              (((CovariantDerivative.difference cov cov' x₀) (basis (slots a))) (X x₀))) := by
    simpa [Vslots, hV_at] using hraw
  change
      (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
          (fun a : Fin r => basis (slots a)) -
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀)
          (fun a : Fin r => basis (slots a)) =
      -∑ a : Fin r, ∑ k : Idx,
        basis.coord k
          (((CovariantDerivative.difference cov cov' x₀) (basis (slots a))) (X x₀)) *
          component0S (I := I) basis (β x₀) (Function.update slots a k)
  rw [hraw_basis]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  exact component0S_update_basis_sum (I := I) basis (β x₀) slots a
    (((CovariantDerivative.difference cov cov' x₀) (basis (slots a))) (X x₀))

/-- Tensor form of `component0S_localCovDeriv0S_sub` for a local extension of a
single basis covariant tensor. -/
theorem localCovDeriv0S_sub_basisTensor {r : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x₀))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (upper : Fin r -> Idx)
    (hβ_at : β x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpair : forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M => β p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord j
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀ -
      localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀ =
      -∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) •
          basisTensor0S (I := I) basis (Function.update upper a k) := by
  classical
  apply ext0S_basis (I := I) basis
  intro slots
  have hcomp := component0S_localCovDeriv0S_sub
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) cov cov' X β x₀ basis V hV_at hpair hβmodel
    hV hVmodel hcoord slots
  rw [hcomp]
  have hdelta (a : Fin r) :
      (∑ k : Idx,
          basis.coord k
            (((CovariantDerivative.difference cov cov' x₀) (basis (slots a))) (X x₀)) *
            (if upper = Function.update slots a k then (1 : 𝕜) else 0)) =
        ∑ k : Idx,
          basis.coord (upper a)
            (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
            (if Function.update upper a k = slots then (1 : 𝕜) else 0) := by
    simpa using
      update_delta_sum_comm
        (𝕜 := 𝕜) (Idx := Idx) (s := r)
        (A := fun k j : Idx =>
          basis.coord k
            (((CovariantDerivative.difference cov cov' x₀) (basis j)) (X x₀)))
        upper slots a
  have hleft :
      (∑ a : Fin r, ∑ k : Idx,
        basis.coord k
          (((CovariantDerivative.difference cov cov' x₀) (basis (slots a))) (X x₀)) *
          component0S (I := I) basis (β x₀) (Function.update slots a k)) =
      ∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
          (if Function.update upper a k = slots then (1 : 𝕜) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hβ_at]
    simp_rw [basisTensor0S_component]
    exact hdelta a
  rw [hleft]
  change
      -(∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
          (if Function.update upper a k = slots then (1 : 𝕜) else 0)) =
      component0S (I := I) basis
        (-(∑ a : Fin r, ∑ k : Idx,
          basis.coord (upper a)
            (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) •
            basisTensor0S (I := I) basis (Function.update upper a k))) slots
  rw [component0S_apply]
  simp only [ContinuousMultilinearMap.neg_apply]
  congr 1
  have hbasis (a : Fin r) (k : Idx) :
      (basisTensor0S (I := I) basis (Function.update upper a k))
          (fun b : Fin r => basis (slots b)) =
        if Function.update upper a k = slots then (1 : 𝕜) else 0 := by
    simpa [component0S_apply] using
      basisTensor0S_component (I := I) basis (Function.update upper a k) slots
  symm
  calc
    ((∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) •
          basisTensor0S (I := I) basis (Function.update upper a k))
        (fun a : Fin r => basis (slots a))) =
        ∑ a : Fin r, ∑ k : Idx,
          basis.coord (upper a)
            (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
            ((basisTensor0S (I := I) basis (Function.update upper a k))
              (fun b : Fin r => basis (slots b))) := by
          rw [tensor0S_sum_apply (I := I)
            (T := fun a : Fin r => ∑ k : Idx,
              basis.coord (upper a)
                (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) •
                basisTensor0S (I := I) basis (Function.update upper a k))
            (v := fun b : Fin r => basis (slots b))]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [tensor0S_sum_apply (I := I)
            (T := fun k : Idx =>
              basis.coord (upper a)
                (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) •
                basisTensor0S (I := I) basis (Function.update upper a k))
            (v := fun b : Fin r => basis (slots b))]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ContinuousMultilinearMap.smul_apply]
          rfl
    _ = ∑ a : Fin r, ∑ k : Idx,
          basis.coord (upper a)
            (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
            (if Function.update upper a k = slots then (1 : 𝕜) else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hbasis a k]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRSModelInChart_apply_modelSlots_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (βm : Tensor0SModel r 𝕜 E) (slots : Fin s -> E) (x₀ : M) :
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀) βm) slots =
      (A x₀
        ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ βm))
        (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
            (slots a)) := by
  rw [tensorRSModelInChart, extChartAt_to_inv]
  exact TensorRSSpace.trivializationAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r s
    (FiberBundle.mem_baseSet_trivializationAt' x₀) (A x₀) βm slots

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRSModelInChart_apply_update_modelOutputSlot_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀)
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β (extChartAt I x₀ x₀)))
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      (A x₀ (β x₀)) (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  rw [tensorRSModelInChart_apply_modelSlots_center]
  have hβ :
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
          (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β (extChartAt I x₀ x₀)) =
        β x₀ := by
    unfold tensor0SModelInChart tensor0SModelAt
    rw [extChartAt_to_inv]
    let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀
    change eβ.symmL 𝕜 x₀ ((eβ ⟨x₀, β x₀⟩).2) = β x₀
    have hcoord : (eβ ⟨x₀, β x₀⟩).2 = eβ.continuousLinearMapAt 𝕜 x₀ (β x₀) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [eβ.coe_linearMapAt_of_mem (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    rw [hcoord]
    exact eβ.symmL_continuousLinearMapAt (R := 𝕜)
      (FiberBundle.mem_baseSet_trivializationAt' x₀) (β x₀)
  have hslots :
      (fun b : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          ((Function.update
            (fun b : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
                (extChartAt I x₀ x₀))
            a
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
              (extChartAt I x₀ x₀))) b)) =
        Function.update (fun b : Fin s => V b x₀) a (W x₀) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Function.update_self]
      exact tangentFieldModelInChart_center_symmL (I := I) W x₀
    · simp only [Function.update_of_ne hb]
      exact tangentFieldModelInChart_center_symmL (I := I) (V b) x₀
  rw [hβ, hslots]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth mixed tensor field evaluated on a smooth covariant tensor input
and smooth moving tangent slots is smooth as a scalar function. -/
theorem tensorRSField_eval_smooth_input_slots_contMDiffAt {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x₀ : M) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀ := by
  let A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
    tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) (r := r) (s := s) T β
  have hA_top := A.contMDiff x₀
  have hV_top : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    exact (V a).contMDiff.contMDiffAt
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => A y) hA_top
    (v := fun a : Fin s => fun y : M => V a y)
    (hv := hV_top)
  simpa [A, tensorRSField_applyInput_apply, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv_apply] using hEval

set_option backward.isDefEq.respectTransparency false in
theorem nablaRSFun_eval_moving_raw {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let Tm : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x₀ (fun x => T x)
  let βm : E -> Tensor0SModel r 𝕜 E :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x₀ β
  let Vm : Fin s -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin s -> E := fun a => Vm a y₀
  have hTdiff : DifferentiableWithinAt 𝕜 Tm (Set.range I) y₀ := by
    have hcd := (T.contMDiff x₀)
    rw [contMDiffAt_section] at hcd
    have hsymm :
        ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
          (extChartAt I x₀).symm (Set.range I) y₀ := by
      simpa [y₀] using
        contMDiffWithinAt_extChartAt_symm_range_self
          (I := I) (n := (∞ : WithTop ℕ∞)) x₀
    have hmodel_center :
        ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) (∞ : WithTop ℕ∞)
          (fun x : M => tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ x (T x))
          ((extChartAt I x₀).symm y₀) := by
      simpa [tensorRSModelAt, y₀, extChartAt_to_inv] using hcd
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(𝕜, E)) (I' := I)
      (I'' := 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (x := y₀) hmodel_center hsymm
    have hdiff := hcomp.contDiffWithinAt.differentiableWithinAt (by simp)
    simpa [Tm, tensorRSModelInChart, y₀] using hdiff
  have hprod := covariantDeriv_tensorRSModelWithin_eval_derivation
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    Tm βm Vm
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I))
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (Set.range I) y₀ hTdiff hβmodel hVmodel
    (I.uniqueDiffOn y₀
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => (Tm y (βm y)) (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) := by
    simpa [Tm, βm, Vm, Xmodel, y₀] using
      fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun
        (I := I) X T β V x₀ hpair
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hslots_center :
      (fun a : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          (slots a)) =
        fun a : Fin s => V a x₀ := by
    funext a
    simpa [slots, Vm] using tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hleft_model :
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
        (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := by
    let eRS := trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀
    let F₀ : TensorRSSpace r s I x₀ :=
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀
    let MRS : TensorRSModel r s 𝕜 E :=
      covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        Tm (Set.range I) y₀
    have hβcenter :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ (βm y₀) =
          β x₀ := by
      unfold βm tensor0SModelInChart tensor0SModelAt
      rw [extChartAt_to_inv]
      let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀
      change eβ.symmL 𝕜 x₀ ((eβ ⟨x₀, β x₀⟩).2) = β x₀
      have hcoord : (eβ ⟨x₀, β x₀⟩).2 = eβ.continuousLinearMapAt 𝕜 x₀ (β x₀) := by
        rw [Bundle.Trivialization.continuousLinearMapAt_apply]
        rw [eβ.coe_linearMapAt_of_mem (R := 𝕜)
          (FiberBundle.mem_baseSet_trivializationAt' x₀)]
      rw [hcoord]
      exact eβ.symmL_continuousLinearMapAt (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt' x₀) (β x₀)
    have hcoordEval :
        ((eRS ⟨x₀, F₀⟩).2 (βm y₀)) slots =
          F₀ (β x₀) (fun a : Fin s => V a x₀) := by
      have h := TensorRSSpace.trivializationAt_apply
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r s
        (FiberBundle.mem_baseSet_trivializationAt' x₀) F₀ (βm y₀) slots
      rw [hβcenter, hslots_center] at h
      exact h
    have hmodel :
        (eRS ⟨x₀, F₀⟩).2 = MRS := by
      unfold F₀ MRS nablaRSFun TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection
        TensorLieDeriv.mcovariantDeriv_tensorRSWithin
      change (eRS ⟨x₀, eRS.symm x₀
        (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r s x₀ (fun x => T x))
          ((extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I)
          (extChartAt I x₀ x₀))⟩).2 = MRS
      rw [eRS.apply_mk_symm
        (mem_baseSet_trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)]
      simp [MRS, Tm, y₀]
    calc
      F₀ (β x₀) (fun a : Fin s => V a x₀)
          = ((eRS ⟨x₀, F₀⟩).2 (βm y₀)) slots := hcoordEval.symm
      _ = (MRS (βm y₀)) slots := by rw [hmodel]
  have hinput :
      (Tm y₀
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          βm (Set.range I) y₀)) slots =
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) := by
    have h := tensorRSModelInChart_apply_modelSlots_center
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) (A := fun x => T x)
      (βm := covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀)
      (slots := slots) x₀
    rw [hslots_center] at h
    simpa [Tm, βm, localCovariantDerivTensor0SAt, Xmodel, Γ, y₀] using h
  have houtput_sum :
      (∑ a : Fin s,
        (Tm y₀ (βm y₀))
          (Function.update (fun b : Fin s => Vm b y₀) a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (Vm a y₀)))) =
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    simpa [Tm, βm, Vm, slots, y₀] using
      tensorRSModelInChart_apply_update_modelOutputSlot_center
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (r := r) (s := s) (A := fun x => T x) (β := β)
        (V := V) (W := fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀)
        =
      (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := hleft_model
    _ =
      fderivWithin 𝕜 (fun y : E => (Tm y (βm y)) (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel -
        (Tm y₀
          (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              (fun x => X x) (Set.range I))
            (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
            βm (Set.range I) y₀))
          (fun a : Fin s => Vm a y₀) -
        ∑ a : Fin s,
          (Tm y₀ (βm y₀))
            (Function.update
              (fun b : Fin s => Vm b y₀)
              a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (Vm a y₀))) := by
          simpa [Xmodel, Γ, slots] using hprod
    _ =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hpair_deriv, hinput, houtput_sum]

set_option backward.isDefEq.respectTransparency false in
/-- Raw scalar-evaluation additivity for the mixed-tensor directional covariant
derivative.

This is the fixed-chart transfer form: once the scalar evaluation and moving
slots satisfy the regularity hypotheses required by `nablaRSFun_eval_moving_raw`,
the derivative is additive in the mixed tensor field. -/
theorem nablaRSFun_add_raw {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T U : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpairT : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hpairU : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (U p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X (T + U) x₀) (β x₀) (fun a : Fin s => V a x₀) =
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) +
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X U x₀) (β x₀) (fun a : Fin s => V a x₀) := by
  classical
  have hpairTU : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => ((T + U) p (β p)) (fun a : Fin s => V a p)) x₀ := by
    change MDifferentiableAt I 𝓘(𝕜, 𝕜)
      ((fun p : M => (T p (β p)) (fun a : Fin s => V a p)) +
        fun p : M => (U p (β p)) (fun a : Fin s => V a p)) x₀
    exact hpairT.add hpairU
  have hTU := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X (T + U) β V x₀ hpairTU hβmodel hV hVmodel hcoord
  have hT := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X T β V x₀ hpairT hβmodel hV hVmodel hcoord
  have hU := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X U β V x₀ hpairU hβmodel hV hVmodel hcoord
  have hext :
      extDerivFun (I := I)
          (fun p : M => ((T + U) p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) =
        extDerivFun (I := I)
            (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
            x₀ (X x₀) +
        extDerivFun (I := I)
            (fun p : M => (U p (β p)) (fun a : Fin s => V a p))
            x₀ (X x₀) := by
    change
      extDerivFun (I := I)
          ((fun p : M => (T p (β p)) (fun a : Fin s => V a p)) +
            fun p : M => (U p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) =
        extDerivFun (I := I)
            (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
            x₀ (X x₀) +
        extDerivFun (I := I)
            (fun p : M => (U p (β p)) (fun a : Fin s => V a p))
            x₀ (X x₀)
    rw [extDerivFun_add hpairT hpairU]
    simp
  rw [hTU, hT, hU, hext]
  simp [Finset.sum_add_distrib]
  ring

set_option linter.unusedSectionVars false in
private theorem extDerivFun_const_smul_raw
    (c : 𝕜) {f : M -> 𝕜} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x) :
    extDerivFun (I := I) (c • f) x =
      c • extDerivFun (I := I) f x := by
  ext v
  have hmul := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => c) (g := f)
    (by exact mdifferentiableAt_const (c := c)) hf v
  simpa [extDerivFun] using hmul

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- Raw scalar-evaluation homogeneity for the mixed-tensor directional
covariant derivative. -/
theorem nablaRSFun_smul_raw {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (c : 𝕜)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpairT : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X (c • T) x₀) (β x₀) (fun a : Fin s => V a x₀) =
      c *
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) := by
  classical
  have hpairc : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => ((c • T) p (β p)) (fun a : Fin s => V a p)) x₀ := by
    change MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (c • fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀
    exact hpairT.const_smul c
  have hcT := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X (c • T) β V x₀ hpairc hβmodel hV hVmodel hcoord
  have hT := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X T β V x₀ hpairT hβmodel hV hVmodel hcoord
  have hext :
      extDerivFun (I := I)
          (fun p : M => ((c • T) p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) =
        c * extDerivFun (I := I)
            (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
            x₀ (X x₀) := by
    change
      extDerivFun (I := I)
          (c • fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) =
        c * extDerivFun (I := I)
            (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
            x₀ (X x₀)
    have h := extDerivFun_const_smul_raw
      (I := I) (M := M) c hpairT
    exact DFunLike.congr_fun h (X x₀)
  rw [hcT, hT, hext]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorRSField_finset_sum_apply {ι : Type} {r s : ℕ}
    (S : Finset ι)
    (T : ι -> TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) :
    (Finset.sum S T) x = Finset.sum S fun i => T i x := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  change (ContMDiffSection.coeAddHom I (TensorRSModel r s 𝕜 E) (∞ : WithTop ℕ∞)
      (fun x : M => TensorRSSpace r s I x) (Finset.sum S T)) x =
    Finset.sum S fun i => T i x
  rw [map_sum]
  simp [ContMDiffSection.coeAddHom_apply, Finset.sum_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorRS_eval_sum_mdiffAt {ι : Type} {r s : ℕ}
    (S : Finset ι)
    (T : ι -> TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : ∀ i : ι, i ∈ S -> MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T i p (β p)) (fun a : Fin s => V a p)) x₀) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => ((Finset.sum S T) p (β p))
        (fun a : Fin s => V a p)) x₀ := by
  have hraw : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (Finset.sum S fun i : ι =>
        fun p : M => (T i p (β p)) (fun a : Fin s => V a p)) x₀ := by
    refine MDifferentiableAt.sum (𝕜 := 𝕜) (I := I) (t := S) ?_
    intro i hi
    exact hpair i hi
  exact hraw.congr_of_eventuallyEq
    (by
      filter_upwards with p
      rw [tensorRSField_finset_sum_apply (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) S T p]
      simp [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply])

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- Raw scalar-evaluation finite-sum linearity for the mixed-tensor
directional covariant derivative. -/
theorem nablaRSFun_sum_raw {ι : Type} {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (S : Finset ι)
    (T : ι -> TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : ∀ i : ι, i ∈ S -> MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T i p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X (Finset.sum S T) x₀) (β x₀) (fun a : Fin s => V a x₀) =
      Finset.sum S fun i =>
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X (T i) x₀) (β x₀) (fun a : Fin s => V a x₀) := by
  classical
  have hSum : ∀ S : Finset ι,
      (∀ i : ι, i ∈ S -> MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M => (T i p (β p)) (fun a : Fin s => V a p)) x₀) ->
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X (Finset.sum S T) x₀) (β x₀) (fun a : Fin s => V a x₀) =
        Finset.sum S fun i =>
          (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s cov X (T i) x₀) (β x₀) (fun a : Fin s => V a x₀) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hpair_empty
      have hzeroPair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
          (fun p : M => ((0 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r s) p (β p))
            (fun a : Fin s => V a p)) x₀ := by
        simpa using mdifferentiableAt_const
          (I := I) (I' := 𝓘(𝕜, 𝕜)) (x := x₀) (c := (0 : 𝕜))
      have hzero := nablaRSFun_eval_moving_raw
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        cov X (0 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) (n := (∞ : WithTop ℕ∞)) r s)
        β V x₀ hzeroPair hβmodel hV hVmodel hcoord
      rw [Finset.sum_empty]
      rw [hzero]
      simp
    · intro i A hi ih hpair_insert
      have hi_pair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
          (fun p : M => (T i p (β p)) (fun a : Fin s => V a p)) x₀ :=
        hpair_insert i (Finset.mem_insert_self i A)
      have hA_pair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
          (fun p : M => ((Finset.sum A T) p (β p))
            (fun a : Fin s => V a p)) x₀ :=
        tensorRS_eval_sum_mdiffAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          A T β V x₀ fun j hj => hpair_insert j (Finset.mem_insert_of_mem hj)
      have hadd := nablaRSFun_add_raw
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        cov X (T i) (Finset.sum A T) β V x₀
        hi_pair hA_pair hβmodel hV hVmodel hcoord
      rw [Finset.sum_insert hi]
      rw [hadd]
      rw [ih (fun j hj => hpair_insert j (Finset.mem_insert_of_mem hj))]
      rw [Finset.sum_insert hi]
  exact hSum S hpair

/-- Subtracting two mixed-tensor covariant derivatives cancels the scalar
directional derivative and leaves the upper-input and lower-output
connection-difference corrections.  This is still the raw moving-slot scalar
form; the component/norm version is built on top of it. -/
theorem nablaRSFun_sub_raw {r s : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀ (β x₀) (fun a : Fin s => V a x₀) -
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov' X T x₀ (β x₀) (fun a : Fin s => V a x₀)) =
      -(((T x₀
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀)) -
        ((T x₀
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀))
          (fun a : Fin s => V a x₀))) -
      ∑ a : Fin s,
        (T x₀ (β x₀))
          (Function.update (fun b : Fin s => V b x₀) a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
  classical
  let slots : Fin s -> TangentSpace I x₀ := fun a => V a x₀
  let inputTerm :
      CovariantDerivative I E (TangentSpace I : M -> Type _) -> 𝕜 :=
    fun cov =>
      (T x₀
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
        slots
  let outputTerm :
      CovariantDerivative I E (TangentSpace I : M -> Type _) -> 𝕜 :=
    fun cov =>
      ∑ a : Fin s,
        (T x₀ (β x₀))
          (Function.update slots a ((cov (V a) x₀) (X x₀)))
  have hcov := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X T β V x₀ hpair hβmodel hV hVmodel hcoord
  have hcov' := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov' X T β V x₀ hpair hβmodel hV hVmodel hcoord
  have hdiff (a : Fin s) :
      (T x₀ (β x₀))
          (Function.update slots a ((cov (V a) x₀) (X x₀))) -
        (T x₀ (β x₀))
          (Function.update slots a ((cov' (V a) x₀) (X x₀))) =
        (T x₀ (β x₀))
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
    have hconn :
        ((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀) =
          ((cov (V a) x₀) (X x₀)) - ((cov' (V a) x₀) (X x₀)) := by
      have h :=
        IsCovariantDerivativeOn.difference_apply
          (hcov := cov.isCovariantDerivativeOnUniv)
          (hcov' := cov'.isCovariantDerivativeOnUniv)
          (σ := V a) (x := x₀) (hx := by trivial) (hV a)
      exact congrArg (fun L : TangentSpace I x₀ →L[𝕜] TangentSpace I x₀ => L (X x₀)) h
    rw [hconn]
    exact ((T x₀ (β x₀)).map_update_sub slots a
      ((cov (V a) x₀) (X x₀))
      ((cov' (V a) x₀) (X x₀))).symm
  let D : 𝕜 :=
    extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
      x₀ (X x₀)
  rw [hcov, hcov']
  change (D - inputTerm cov - outputTerm cov) -
      (D - inputTerm cov' - outputTerm cov') =
    -((inputTerm cov) - (inputTerm cov')) -
      ∑ a : Fin s,
        (T x₀ (β x₀))
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀)))
  have hS :
      outputTerm cov - outputTerm cov' =
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update slots a
              (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
    simp only [outputTerm]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => hdiff a
  rw [← hS]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- Component formula for the difference of two mixed-tensor covariant
derivatives in a pointwise tangent basis.  This is the manifold-level `p = 1`
connection-change identity behind MSM135 Chapter 4, Lemma "Norms of covariant
derivatives of tensors, I". -/
theorem componentRS_nablaRSFun_sub {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x₀))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx)
    (hX_at : X x₀ = basis (lower 0))
    (hβ_at : β x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M => β p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord j
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    componentRS (I := I) basis
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s cov X T x₀ -
          nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s cov' X T x₀)
        upper (fun b : Fin s => lower b.succ) =
      (∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (basis (lower 0))) *
          componentRS (I := I) basis (T x₀) (Function.update upper a k)
            (fun b : Fin s => lower b.succ)) -
      (∑ b : Fin s, ∑ k : Idx,
        basis.coord k
          (((CovariantDerivative.difference cov cov' x₀) (basis (lower b.succ)))
            (basis (lower 0))) *
          componentRS (I := I) basis (T x₀) upper
            (Function.update (fun c : Fin s => lower c.succ) b k)) := by
  classical
  let lowerTail : Fin s -> Idx := fun b => lower b.succ
  let Vlower : Fin s -> (x : M) -> TangentSpace I x := fun b => V (lowerTail b)
  let Lcov :=
    localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀
  let Lcov' :=
    localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀
  have hraw := nablaRSFun_sub_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov cov' X T β Vlower x₀
    hpairT hβmodel
    (fun a => hV (lowerTail a))
    (fun a => hVmodel (lowerTail a))
    (fun a j => hcoord (lowerTail a) j)
  have hraw_basis :
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀
          (basisTensor0S (I := I) basis upper)
          (fun b : Fin s => basis (lowerTail b)) -
        nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov' X T x₀
          (basisTensor0S (I := I) basis upper)
          (fun b : Fin s => basis (lowerTail b))) =
        -(((T x₀ Lcov) (fun b : Fin s => basis (lowerTail b))) -
          ((T x₀ Lcov') (fun b : Fin s => basis (lowerTail b)))) -
        ∑ b : Fin s,
          (T x₀ (basisTensor0S (I := I) basis upper))
            (Function.update (fun c : Fin s => basis (lowerTail c)) b
              (((CovariantDerivative.difference cov cov' x₀) (basis (lowerTail b)))
                (basis (lower 0)))) := by
    simpa [Vlower, lowerTail, Lcov, Lcov', hV_at, hβ_at, hX_at] using hraw
  have hL := localCovDeriv0S_sub_basisTensor
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) cov cov' X β x₀ basis V upper hβ_at hV_at
    hpairβ hβmodel hV hVmodel hcoord
  have hinput :
      ((T x₀ Lcov) (fun b : Fin s => basis (lowerTail b))) -
        ((T x₀ Lcov') (fun b : Fin s => basis (lowerTail b))) =
      -(∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
          componentRS (I := I) basis (T x₀) (Function.update upper a k) lowerTail) := by
    let S : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ :=
      ∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) •
          basisTensor0S (I := I) basis (Function.update upper a k)
    have hlin :
        ((T x₀ (Lcov - Lcov')) (fun b : Fin s => basis (lowerTail b))) =
          ((T x₀ Lcov) (fun b : Fin s => basis (lowerTail b))) -
            ((T x₀ Lcov') (fun b : Fin s => basis (lowerTail b))) := by
      have hmap := congrArg
        (fun A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ => A (fun b : Fin s => basis (lowerTail b)))
        ((T x₀).map_sub Lcov Lcov')
      simpa only [ContinuousMultilinearMap.sub_apply] using hmap
    have hS_eval :
        ((T x₀ S) (fun b : Fin s => basis (lowerTail b))) =
          ∑ a : Fin r, ∑ k : Idx,
            basis.coord (upper a)
              (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
              componentRS (I := I) basis (T x₀) (Function.update upper a k) lowerTail := by
      simp [S, componentRS_apply, map_sum, map_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hLC : Lcov - Lcov' = -S := by
      simpa [Lcov, Lcov', S] using hL
    rw [← hlin, hLC]
    have hneg_eval :
        ((T x₀ (-S)) (fun b : Fin s => basis (lowerTail b))) =
          -((T x₀ S) (fun b : Fin s => basis (lowerTail b))) := by
      have hneg := congrArg
        (fun A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ => A (fun b : Fin s => basis (lowerTail b)))
        ((T x₀).map_neg S)
      simpa only [ContinuousMultilinearMap.neg_apply] using hneg
    rw [hneg_eval, hS_eval]
  have hlower (b : Fin s) :
      (T x₀ (basisTensor0S (I := I) basis upper))
          (Function.update (fun c : Fin s => basis (lowerTail c)) b
            (((CovariantDerivative.difference cov cov' x₀) (basis (lowerTail b)))
              (basis (lower 0)))) =
        ∑ k : Idx,
          basis.coord k
            (((CovariantDerivative.difference cov cov' x₀) (basis (lowerTail b)))
              (basis (lower 0))) *
            componentRS (I := I) basis (T x₀) upper
              (Function.update lowerTail b k) := by
    exact component0S_update_basis_sum (I := I) basis
      (T x₀ (basisTensor0S (I := I) basis upper)) lowerTail b
      (((CovariantDerivative.difference cov cov' x₀) (basis (lowerTail b)))
        (basis (lower 0)))
  rw [componentRS_apply]
  have hsub :
      (((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀ -
        nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov' X T x₀)
          (basisTensor0S (I := I) basis upper))
          (fun b : Fin s => basis (lowerTail b))) =
        (((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
          (basisTensor0S (I := I) basis upper))
          (fun b : Fin s => basis (lowerTail b)) -
        ((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov' X T x₀)
          (basisTensor0S (I := I) basis upper))
          (fun b : Fin s => basis (lowerTail b))) := by
    let F :=
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀
    let G :=
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov' X T x₀
    let B : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ :=
      basisTensor0S (I := I) basis upper
    let v : Fin s -> TangentSpace I x₀ := fun b => basis (lowerTail b)
    have hmap := ContinuousLinearMap.sub_apply F G B
    have happ := congrArg
      (fun A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) s x₀ => A v) hmap
    simpa only [F, G, B, v, ContinuousMultilinearMap.sub_apply] using happ
  rw [hsub]
  change
      (((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
          (basisTensor0S (I := I) basis upper))
          (fun b : Fin s => basis (lowerTail b)) -
        ((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov' X T x₀)
          (basisTensor0S (I := I) basis upper))
          (fun b : Fin s => basis (lowerTail b))) =
      (∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (basis (lower 0))) *
          componentRS (I := I) basis (T x₀) (Function.update upper a k)
            lowerTail) -
      (∑ b : Fin s, ∑ k : Idx,
        basis.coord k
          (((CovariantDerivative.difference cov cov' x₀) (basis (lower b.succ)))
            (basis (lower 0))) *
          componentRS (I := I) basis (T x₀) upper
            (Function.update lowerTail b k))
  rw [hraw_basis, hinput]
  simp only [neg_neg]
  have hXsimp :
      (∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (X x₀)) *
          componentRS (I := I) basis (T x₀) (Function.update upper a k)
            lowerTail) =
      ∑ a : Fin r, ∑ k : Idx,
        basis.coord (upper a)
          (((CovariantDerivative.difference cov cov' x₀) (basis k)) (basis (lower 0))) *
          componentRS (I := I) basis (T x₀) (Function.update upper a k)
            lowerTail := by
    simp [hX_at]
  rw [hXsimp]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  exact hlower b

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise moving-slot derivation formula for `nabla0SFun` in arbitrary
covariant valence.

This is the `(0,s)` version of
`nabla0SFun_one_eval_coordFrame_moving_raw`. The hypotheses are deliberately
local: the moving slots only need the fixed-chart model differentiability needed
by the product rule and the vector-field covariant-derivative chart formula. -/
theorem nabla0SFun_eval_coordFrame_moving_raw {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀)
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let αm : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x₀ (fun x => α x)
  let Vm : Fin s -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin s -> E := fun a => Vm a y₀
  have hαdiff : DifferentiableWithinAt 𝕜 αm (Set.range I) y₀ := by
    have hcd := tensor0SModelInChart_contMDiffWithinAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s x₀ α
    have hdiff := hcd.contDiffWithinAt.differentiableWithinAt (by simp)
    simpa [αm, y₀] using hdiff
  have hprod :=
    fderivWithin_tensor0SModel_eval_slots
      (𝕜 := 𝕜) (E := E) (s := s) αm Vm (Set.range I) y₀ Xmodel
      hαdiff hVmodel
      (I.uniqueDiffOn y₀
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => αm y (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) := by
    simpa [αm, Vm, Xmodel, y₀] using
      fderivWithin_tensor0S_eval_modelSlots_center_eq_extDerivFun
        (I := I) X α V x₀ hpair
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hfixed := fixedChartNabla0SModel_apply_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) s cov X α x₀ y₀ slots
  have hself := nabla0SFun_apply_selfChart_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov X α x₀ slots
  have hslot :
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀) =
        fun a : Fin s => V a x₀ := by
    funext a
    simpa [slots, Vm, tangentConstInChart] using
      tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hcorr_sum :
      ∑ a : Fin s,
        αm y₀
          (Function.update slots a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) =
      ∑ a : Fin s,
        α x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    exact tensor0SModelInChart_apply_update_modelSlot_center
      (I := I) (fun x => α x) V (fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀)
        =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x₀)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀) := by
          rw [hslot]
    _ = fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x₀ y₀ slots := hself
    _ =
      fderivWithin 𝕜 αm (Set.range I) y₀ Xmodel slots -
        ∑ a : Fin s, αm y₀ (Function.update slots a (Γ (slots a))) := by
          simpa [αm, Xmodel, Γ, y₀] using hfixed
    _ =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
        ∑ a : Fin s,
          αm y₀
            (Function.update slots a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) := by
          rw [← hpair_deriv]
          rw [hprod]
          simp_rw [(αm y₀).map_update_add]
          rw [Finset.sum_add_distrib]
          abel
    _ =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hcorr_sum]
end Tensor0SBundle
