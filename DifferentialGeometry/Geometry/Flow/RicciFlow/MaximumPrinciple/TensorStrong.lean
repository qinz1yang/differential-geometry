import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.Final

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Bundle Tensor0SBundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

def metricShiftedReaction
    (N : TwoTensorReaction (I := I) (M := M)) (eta : Real) :
    TwoTensorReaction (I := I) (M := M) :=
  fun t g A x v w ↦ N t g A x v w - eta * g.inner x v w

def TensorNullEigenvectorLowerBound
    (G : Real → SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (eta : Real) (U : Set Real) : Prop :=
  ∀ t, t ∈ U → ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
    TwoTensorSymmetricAt (I := I) (M := M) A x →
    TwoTensorBilinearAt (I := I) (M := M) A x →
    TwoTensorNonnegativeAt (I := I) (M := M) A x →
    ∀ v : TangentSpace I x, A x v v = 0 →
      eta * (G t).inner x v v ≤ N t (G t) A x v v

theorem tensor_positive_definite_on_of_nonnegative_of_strict_supersolution
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    {G : Real → SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real → CovariantDerivative I E (TangentSpace I : M → Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (hnonnegative : TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hsymmetric : TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hstrict : TensorParabolicStrictInequalityWithDriftOn
      (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x ↦ nabla2S t x) (fun t x ↦ nablaS t x) (Set.Ioc 0 T))
    (hnullAll : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc 0 T))
    (hcov1 : ∀ t : Real, CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov t) (1 : WithTop ℕ∞))
    (hcovInf : ∀ t : Real, CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov t) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      DifferentialGeometry.Geometry.Connection.IsMetricCompatible_gen
        (I := I) (cov t) (G t))
    (hspatial : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    TwoTensorFamilyPositiveDefiniteOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Ioc 0 T) := by
  let Sraw := twoTensorSecToFamily (I := I) (M := M) S
  intro t ht x v hv
  have hSnonnegative : 0 ≤ Sraw t x v v :=
    hnonnegative t ⟨le_of_lt ht.1, ht.2⟩ x v
  by_contra hSpositive
  have hSzero : Sraw t x v v = 0 :=
    le_antisymm (not_lt.mp hSpositive) hSnonnegative
  let r : Real := (G t).inner x v v
  have hr : 0 < r := (G t).pos x v hv
  let s : Real := Real.sqrt r
  have hs : 0 < s := Real.sqrt_pos.mpr hr
  let a : Real := s⁻¹
  let w : TangentSpace I x := a • v
  have ha : a ≠ 0 := inv_ne_zero (ne_of_gt hs)
  have hw : w ≠ 0 := smul_ne_zero ha hv
  have hunit : (G t).inner x w w = 1 := by
    have hsq : s * s = r := by
      simpa [sq] using Real.sq_sqrt hr.le
    change (G t).inner x (a • v) (a • v) = 1
    rw [metric_smul2]
    have has : a * s = 1 := by simp [a, ne_of_gt hs]
    calc
      a * a * r = (a * s) * (a * s) := by rw [← hsq]; ring
      _ = 1 := by rw [has]; norm_num
  have hSzeroUnit : Sraw t x w w = 0 := by
    have hbilin := twoTensorSecToFamily_bilin (I := I) (M := M) S t x
    calc
      Sraw t x w w = Sraw t x (a • v) (a • v) := rfl
      _ = a * Sraw t x v (a • v) := hbilin.smul_left a v (a • v)
      _ = a * (a * Sraw t x v v) :=
        congrArg (fun z ↦ a * z) (hbilin.smul_right a v v)
      _ = 0 := by rw [hSzero]; ring
  have hbarrier :
      tensorBarrierFamily (I := I) (M := M) G Sraw 0 t 0 = Sraw := by
    funext q y z w'
    simp [tensorBarrierFamily]
  let d : TensorFirstNullData (I := I) (M := M) G Sraw 0 t 0 :=
    { t1 := t
      x1 := x
      v := w
      t1_mem := by simpa using ht.1
      v_ne_zero := hw
      unit := hunit
      nonnegative_until := by
        intro q hq y
        rw [hbarrier]
        exact hnonnegative q ⟨hq.1, hq.2.trans ht.2⟩ y
      null := by rw [hbarrier]; exact hSzeroUnit }
  have hsubIoc : Set.Ioc 0 t ⊆ Set.Ioc 0 T := by
    intro q hq
    exact ⟨hq.1, hq.2.trans ht.2⟩
  have hstrictSlab : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G Sraw X N (fun q y ↦ nabla2S q y) (fun q y ↦ nablaS q y) 0 t 0 := by
    unfold TensorBarrierStrictSupersolutionOn
    rw [hbarrier]
    simp only [zero_add]
    rcases hstrict with ⟨timeDeriv, htime, hinequality⟩
    refine ⟨timeDeriv, ?_, ?_⟩
    · intro q hq y z
      exact (htime q (hsubIoc hq) y z).mono hsubIoc
    · intro q hq y z hz
      exact hinequality q (hsubIoc hq) y z hz
  have hsubIcc : Set.Icc 0 t ⊆ Set.Icc 0 T := by
    intro q hq
    exact ⟨hq.1, hq.2.trans ht.2⟩
  have hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc 0 t) := by
    intro q hq A y hsym hbilin hA z hz
    exact hnullAll q (hsubIcc hq) A y hsym hbilin hA z hz
  have hsym : TwoTensorFamilySymmetricOn (I := I) (M := M)
      Sraw (Set.Icc 0 t) := by
    intro q hq y
    exact hsymmetric q (hsubIcc hq) y
  have hnullSlab : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc 0 (0 + t)) := by simpa only [zero_add] using hnull
  have hsymSlab : TwoTensorFamilySymmetricOn (I := I) (M := M)
      Sraw (Set.Icc 0 (0 + t)) := by simpa only [zero_add] using hsym
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (X t x)
  have hsigns : TensorFirstNullScalarSigns (I := I) (M := M)
      G Sraw X N 0 t 0 d :=
    scalarSigns_secHess (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
      hstrictSlab hnullSlab hsymSlab d (hcov1 t) (hcovInf t)
      hmc hspatial Xsec
      (laplacianNonnegativeAtSpatialMin_of_metricCompatible
        (I := I) (cov t) (G t) (hmc t)) hXsec.symm
  exact tensor_first_null_contradiction (I := I) (M := M)
    (G := G) (S := Sraw) (X := X) (N := N)
    (nabla2Barrier := fun q y ↦ nabla2S q y)
    (nablaBarrier := fun q y ↦ nablaS q y)
    hstrictSlab hnullSlab hsymSlab
    (fun q _ y ↦ twoTensorSecToFamily_bilin (I := I) (M := M) S q y)
    d hsigns

theorem tensor_positive_definite_on_of_strict_supersolution
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    {G : Real → SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real → CovariantDerivative I E (TangentSpace I : M → Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (data : TensorWMPInput (I := I) (M := M) G S X N cov nablaS nabla2S T)
    (hstrict : TensorParabolicStrictInequalityWithDriftOn
      (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x ↦ nabla2S t x) (fun t x ↦ nablaS t x) (Set.Ioc 0 T)) :
    TwoTensorFamilyPositiveDefiniteOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Ioc 0 T) := by
  exact tensor_positive_definite_on_of_nonnegative_of_strict_supersolution
    (I := I) (M := M) (G := G) (S := S) (X := X) (N := N)
    (cov := cov) (nablaS := nablaS) (nabla2S := nabla2S)
    (tensor_wmp (I := I) (M := M) data) data.reg.symmetric hstrict
    data.null data.hcov1 data.hcovInf data.hmc data.spatial

theorem tensor_positive_definite_on_of_null_reaction_lower_bound
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    {G : Real → SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real → CovariantDerivative I E (TangentSpace I : M → Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T eta : Real}
    (data : TensorWMPInput (I := I) (M := M) G S X N cov nablaS nabla2S T)
    (heta : 0 < eta)
    (hreaction : TensorNullEigenvectorLowerBound (I := I) (M := M)
      G N eta (Set.Icc 0 T)) :
    TwoTensorFamilyPositiveDefiniteOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Ioc 0 T) := by
  let Nshift := metricShiftedReaction (I := I) (M := M) N eta
  have hstrict : TensorParabolicStrictInequalityWithDriftOn
      (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X Nshift
      (fun t x ↦ nabla2S t x) (fun t x ↦ nablaS t x) (Set.Ioc 0 T) := by
    rcases data.parabolic.evaluatedInequality with ⟨timeDeriv, htime, hinequality⟩
    refine ⟨timeDeriv, ?_, ?_⟩
    · intro t ht x v
      exact (htime t ht x v).mono Set.Ioc_subset_Icc_self
    · intro t ht x v hv
      have hmetric : 0 < eta * (G t).inner x v v :=
        mul_pos heta ((G t).pos x v hv)
      have hbase := hinequality t ht x v
      unfold Nshift metricShiftedReaction
      linarith
  have hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G Nshift (Set.Icc 0 T) := by
    intro t ht A x hsym hbilin hA v hv
    exact sub_nonneg.mpr (hreaction t ht A x hsym hbilin hA v hv)
  exact tensor_positive_definite_on_of_nonnegative_of_strict_supersolution
    (I := I) (M := M) (G := G) (S := S) (X := X) (N := Nshift)
    (cov := cov) (nablaS := nablaS) (nabla2S := nabla2S)
    (tensor_wmp (I := I) (M := M) data) data.reg.symmetric hstrict hnull
    data.hcov1 data.hcovInf data.hmc data.spatial

end

end DifferentialGeometry.PDE.RicciFlow
