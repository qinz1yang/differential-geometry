import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCovariantContinuity
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ancientTensorConnectionC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance ancientTensorConnectionC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem solution_nabla0S_eval_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (n : ℕ)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (α : Tensor0SField (I := I) (M := M) (n := ∞) n)
    (x : M) (slots : Fin n → TangentSpace I x) :
    ContinuousWithinAt
      (fun s => nabla0SFun n (S.family.connection s) X α x slots) (Iic b) t := by
  classical
  have hex (i : Fin n) := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x (slots i)
  choose V hV using hex
  have hslots : (fun i => V i x) = slots := funext hV
  have heq : (fun s => nabla0SFun n (S.family.connection s) X α x slots) =
      (fun s => mvfderiv (I := I) (fun p => α p (fun i => V i p)) x (X x) -
        ∑ i : Fin n, α x (Function.update (fun j => V j x) i
          (S.family.connection s (fun p => V i p) x (X x)))) := by
    funext s
    rw [← hslots]
    exact nabla0SFun_eval_smooth_slots (S.family.connection s) X V α x
  rw [heq]
  apply continuousWithinAt_const.sub
  refine tendsto_finsetSum _ fun i _ => ?_
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) n x (α x)).cont.continuousAt.comp_continuousWithinAt
  apply continuousWithinAt_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact solution_leviCivita_continuousWithinAt S hS hcarrier hregular ht
      (fun p => V i p) x (V i).mdifferentiableAt (X x)
  · simpa only [Function.update_of_ne hji] using
      (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => V j x) (Iic b) t)


theorem solution_nabla0S_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (n : ℕ)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (α : Tensor0SField (I := I) (M := M) (n := ∞) n) (x : M) :
    ContinuousWithinAt (fun s => nabla0SFun n (S.family.connection s) X α x) (Iic b) t := by
  classical
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) n x
  let basis := Module.finBasis ℝ (TangentSpace I x)
  let B := continuousMultilinearMapBasis basis n
  let f : ℝ → Tensor0SSpace n I x := fun s => nabla0SFun n (S.family.connection s) X α x
  change ContinuousWithinAt f (Iic b) t
  rw [e.toHomeomorph.isInducing.continuousWithinAt_iff]
  change ContinuousWithinAt (fun s => e (f s)) (Iic b) t
  have heq : (fun s => e (f s)) =
      (fun s => ∑ j : Fin n → Fin (Module.finrank ℝ (TangentSpace I x)),
        e (f s) (fun i => basis (j i)) • B j) := by
    funext s
    symm
    simpa only [B, continuousMultilinearMapBasis_repr] using B.sum_repr (e (f s))
  rw [heq]
  refine tendsto_finsetSum _ fun j _ => ?_
  exact (solution_nabla0S_eval_continuousWithinAt S hS hcarrier hregular ht n X α x
    (fun i => basis (j i))).smul tendsto_const_nhds


theorem solution_nabla0S_mem_at_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b)
    (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (n : ℕ) (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (α : Tensor0SField (I := I) (M := M) (n := ∞) n)
    (x : M) (K : Submodule ℝ (Tensor0SSpace n I x))
    (hmem : ∀ t ∈ Ioo a b, nabla0SFun n (S.family.connection t) X α x ∈ K) :
    nabla0SFun n (S.family.connection b) X α x ∈ K := by
  apply K.closed_of_finiteDimensional.mem_of_tendsto
    ((solution_nabla0S_continuousWithinAt S hS hcarrier hregular le_rfl n X α x).mono
      Iio_subset_Iic_self)
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  exact hmem t ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
