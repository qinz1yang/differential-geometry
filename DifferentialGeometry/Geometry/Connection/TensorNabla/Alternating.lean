import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SNabla
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Alternating.Basis
import DifferentialGeometry.Tensor.Alternating.Section

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

noncomputable local instance alternatingModelFiniteDimensional (s : ℕ) :
    FiniteDimensional Real (E [⋀^Fin s]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := s)
    (Module.finBasis Real E)).finiteDimensional_of_finite

omit [CompleteSpace E] [T2Space M] in
private theorem mdifferentiableAt_toMultilinearMap
    {s : ℕ}
    (a : ∀ x : M, TangentSpace I x [⋀^Fin s]→L[Real] Real)
    {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(Real, E [⋀^Fin s]→L[Real] Real))
      (fun y => TotalSpace.mk' (E [⋀^Fin s]→L[Real] Real)
        (E := Bundle.continuousAlternatingMap Real (Fin s) E
          (TangentSpace I) Real (Bundle.Trivial M Real)) y (a y)) x) :
    MDifferentiableAt I
      (I.prod 𝓘(Real, ContinuousMultilinearMap Real (fun _ : Fin s => E) Real))
      (fun y => TotalSpace.mk'
        (ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
        (E := Bundle.continuousMultilinearMap Real s E (TangentSpace I))
        y (a y).toContinuousMultilinearMap) x := by
  let ea := trivializationAt (E [⋀^Fin s]→L[Real] Real)
    (Bundle.continuousAlternatingMap Real (Fin s) E (TangentSpace I) Real
      (Bundle.Trivial M Real)) x
  let em := trivializationAt (ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
    (Bundle.continuousMultilinearMap Real s E (TangentSpace I)) x
  rw [em.mdifferentiableAt_section_iff I _
    (mem_baseSet_trivializationAt _ _ x)]
  have ha' : MDifferentiableAt I
      𝓘(Real, E [⋀^Fin s]→L[Real] Real)
      (fun y => (ea ⟨y, a y⟩).2) x :=
    (ea.mdifferentiableAt_section_iff I _
      (mem_baseSet_trivializationAt _ _ x)).mp ha
  let L : (E [⋀^Fin s]→L[Real] Real) →L[Real]
      ContinuousMultilinearMap Real (fun _ : Fin s => E) Real :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM Real
  have hmap : MDifferentiableAt
      𝓘(Real, E [⋀^Fin s]→L[Real] Real)
      𝓘(Real, ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
      L
      ((ea ⟨x, a x⟩).2) :=
    (L.contMDiff (n := (1 : WithTop ℕ∞))).mdifferentiable (by norm_num) _
  have hconv : MDifferentiableAt I
      𝓘(Real, ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
      (fun y => L ((ea ⟨y, a y⟩).2)) x :=
    hmap.comp x ha'
  refine hconv.congr_of_eventuallyEq ?_
  filter_upwards with y
  change (em ⟨y, (a y).toContinuousMultilinearMap⟩).2 =
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM Real ((ea ⟨y, a y⟩).2)
  have hem :
      (em ⟨y, (a y).toContinuousMultilinearMap⟩).2 =
        (a y).toContinuousMultilinearMap.compContinuousLinearMap
          (fun _ => (trivializationAt E (TangentSpace I) x).symmL Real y) := by
    rfl
  have hea :
      (ea ⟨y, a y⟩).2 =
        (a y).compContinuousLinearMap
          ((trivializationAt E (TangentSpace I) x).symmL Real y) := by
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
    ext v
    simp [ContinuousAlternatingMap.inCoordinates]
  rw [hem, hea]
  rfl

def alternatingCovariantDerivative
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (E [⋀^Fin s]→L[Real] Real)
      (fun x : M ↦ TangentSpace I x [⋀^Fin s]→L[Real] Real) where
  toFun a x :=
    ContinuousLinearMap.comp
      ContinuousMultilinearMap.alternatizationCLM
      (ContinuousLinearMap.comp
        (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
          (I := I) s x).toContinuousLinearMap
        ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
          (fun y ↦ (a y).toContinuousMultilinearMap) x))
  isCovariantDerivativeOnUniv := by
    constructor
    · intro a b x ha hb hx
      let ta : ∀ y : M, Tensor0SBundle.Tensor0SSpace s I y :=
        fun y => (a y).toContinuousMultilinearMap
      let tb : ∀ y : M, Tensor0SBundle.Tensor0SSpace s I y :=
        fun y => (b y).toContinuousMultilinearMap
      have ha' := mdifferentiableAt_toMultilinearMap (I := I) a ha
      have hb' := mdifferentiableAt_toMultilinearMap (I := I) b hb
      change ContinuousLinearMap.comp
          ContinuousMultilinearMap.alternatizationCLM
          (ContinuousLinearMap.comp
            (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
              (I := I) s x).toContinuousLinearMap
            ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov) (ta + tb) x)) =
        ContinuousLinearMap.comp
            ContinuousMultilinearMap.alternatizationCLM
            (ContinuousLinearMap.comp
              (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
                (I := I) s x).toContinuousLinearMap
              ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov) ta x)) +
          ContinuousLinearMap.comp
            ContinuousMultilinearMap.alternatizationCLM
            (ContinuousLinearMap.comp
              (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
                (I := I) s x).toContinuousLinearMap
              ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov) tb x))
      rw [
        (Tensor0SNabla.tensor0SCovariantDerivative I M s cov).isCovariantDerivativeOn.add
          ha' hb' hx]
      ext v w
      simp [ta, tb]
    · intro a f x ha hf hx
      let ta : ∀ y : M, Tensor0SBundle.Tensor0SSpace s I y :=
        fun y => (a y).toContinuousMultilinearMap
      have ha' := mdifferentiableAt_toMultilinearMap (I := I) a ha
      change ContinuousLinearMap.comp
          ContinuousMultilinearMap.alternatizationCLM
          (ContinuousLinearMap.comp
            (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
              (I := I) s x).toContinuousLinearMap
            ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov) (f • ta) x)) =
        f x • ContinuousLinearMap.comp
          ContinuousMultilinearMap.alternatizationCLM
          (ContinuousLinearMap.comp
            (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv
              (I := I) s x).toContinuousLinearMap
            ((Tensor0SNabla.tensor0SCovariantDerivative I M s cov) ta x)) +
          (d% f x).smulRight (a x)
      rw [
        (Tensor0SNabla.tensor0SCovariantDerivative I M s cov).isCovariantDerivativeOn.leibniz
          ha' hf hx]
      ext v w
      dsimp only [ta]
      simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ,
        RingHom.id_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.coe_smul, Pi.smul_apply, smul_eq_mul,
        ContinuousLinearMap.smulRight_apply]
      congr 1
      change (ContinuousMultilinearMap.alternatizationCLM
        ((d% f x) v • (a x).toContinuousMultilinearMap)) w =
          (d% f x) v * (a x) w
      rw [map_smul,
        ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap]
      rfl

noncomputable instance alternatingCovariantDerivative_contMDiff
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative.ContMDiffCovariantDerivative
      (alternatingCovariantDerivative (I := I) s cov) ∞ where
  contMDiff := {
    contMDiff := by
      intro a ha
      have haSmooth : ContMDiff I
          (I.prod 𝓘(Real, E [⋀^Fin s]→L[Real] Real)) ∞
          (fun x => TotalSpace.mk' (E [⋀^Fin s]→L[Real] Real)
            (E := Bundle.continuousAlternatingMap Real (Fin s) E
              (TangentSpace I) Real (Bundle.Trivial M Real)) x (a x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at ha
        rwa [← contMDiffOn_univ]
      let aSection : AlternatingSection Real E I (TangentSpace I) ∞ s :=
        ⟨a, haSmooth⟩
      let tensorSection : ContMDiffSection I
          (Tensor0SBundle.Tensor0SModel s Real E) ∞
          (fun x : M => Tensor0SBundle.Tensor0SSpace s I x) :=
        ⟨fun x => (aSection x).toContinuousMultilinearMap,
          aSection.toMultilinearSection.contMDiff⟩
      let tensorCov := Tensor0SNabla.tensor0SCovariantDerivative I M s cov
      have hTensorSection : ContMDiffOn I
          (I.prod 𝓘(Real, Tensor0SBundle.Tensor0SModel s Real E)) (∞ + 1)
          (fun x => TotalSpace.mk'
            (Tensor0SBundle.Tensor0SModel s Real E)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
            x (tensorSection x)) Set.univ := by
        rw [contMDiffOn_univ]
        simpa using tensorSection.contMDiff
      have hTensorCov : ContMDiff I
          (I.prod 𝓘(Real, E →L[Real]
            ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)) ∞
          (fun x => TotalSpace.mk'
            (E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
            (E := fun x : M => TangentSpace I x →L[Real]
              Tensor0SBundle.Tensor0SSpace s I x) x
            (tensorCov tensorSection x)) := by
        rw [← contMDiffOn_univ]
        exact (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative
          tensorCov ∞).contMDiff.contMDiff hTensorSection
      rw [contMDiffOn_univ]
      apply DifferentialGeometry.Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
        (I := I) (M := M)
      intro Y
      have hApply : ContMDiff I
          (I.prod 𝓘(Real,
            ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)) ∞
          (fun x => TotalSpace.mk'
            (ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace s I x) x
            (tensorCov tensorSection x (Y x))) :=
        ContMDiff.clm_bundle_apply hTensorCov Y.contMDiff
      let result : MultilinearSection Real E I (TangentSpace I) ∞ s :=
        ⟨fun x => tensorCov tensorSection x (Y x), hApply⟩
      refine result.alternatization.contMDiff.congr ?_
      intro x
      congr 1
  }

end DifferentialGeometry.Geometry.Connection
