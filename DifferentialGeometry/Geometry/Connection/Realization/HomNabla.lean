import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla

noncomputable section


open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

namespace DifferentialGeometry
namespace HomConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

private abbrev MDiffAtHom
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x)) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
    (fun y => TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) y (τ y)) x

private abbrev MDiffAtVec
    (Y : Π x : M, TangentSpace I x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x

private def Psi
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    (V_field Y : Π x : M, TangentSpace I x) (x : M) : V x :=
  cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_TM Y x (V_field x))

noncomputable def homBundleCovariantDerivativeFun
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] V x) :=
  HomConnectionGen.homBundleCovariantDerivativeGenFun I M E (TangentSpace I) F V
    cov_TM cov_V τ x

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [ContMDiffVectorBundle ∞ F V I] in
theorem homBundleCovariantDerivativeFun_apply
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x)
    {V_field Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V_field x) (hY : MDiffAtVec I M Y x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x (V_field x) (Y x) =
      Psi I M F V cov_TM cov_V τ V_field Y x := by
  classical
  unfold homBundleCovariantDerivativeFun HomConnectionGen.homBundleCovariantDerivativeGenFun
  split_ifs with hτ'
  · exact TensorialAt.mkHom₂_apply _ _ hV hY
  · exact (hτ' hτ).elim

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [ContMDiffVectorBundle ∞ F V I] in
theorem homBundleCovariantDerivativeFun_apply_eq
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (TangentSpace I x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M F V τ x)
    {V_field Y : Π x : M, TangentSpace I x}
    (hV : MDiffAtVec I M V_field x) (hY : MDiffAtVec I M Y x) :
    homBundleCovariantDerivativeFun I M F V cov_TM cov_V τ x (V_field x) (Y x) =
      cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_TM Y x (V_field x)) := by
  rw [homBundleCovariantDerivativeFun_apply I M F V cov_TM cov_V τ hτ hV hY]
  rfl

noncomputable def homBundleCovariantDerivative
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V) :
    CovariantDerivative I (E →L[ℝ] F)
      (fun x => TangentSpace I x →L[ℝ] V x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M E (TangentSpace I) F V cov_TM cov_V

noncomputable instance homBundleCovariantDerivative_contMDiff
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov_TM ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞] :
    ContMDiffCovariantDerivative (homBundleCovariantDerivative I M F V cov_TM cov_V) ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M E (TangentSpace I) F V
    cov_TM cov_V

omit [CompleteSpace E] [SigmaCompactSpace M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [ContMDiffVectorBundle ∞ F V I] in
theorem homBundleCovariantDerivative_apply
    (cov_TM : CovariantDerivative I E (TangentSpace I : M → Type _))
    (cov_V : CovariantDerivative I F V)
    (τ : Cₛ^∞⟮I; E →L[ℝ] F, (fun x => TangentSpace I x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (homBundleCovariantDerivative I M F V cov_TM cov_V τ x v) (Y x) =
      cov_V (fun y => τ y (Y y)) x v - τ x (cov_TM Y x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M E (TangentSpace I) F V
    cov_TM cov_V τ Y x v

end HomConnection

end DifferentialGeometry

end
