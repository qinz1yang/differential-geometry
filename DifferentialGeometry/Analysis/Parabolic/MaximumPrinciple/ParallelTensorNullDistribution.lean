import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.DualConeStrong
import DifferentialGeometry.Analysis.Convex.Tensor02PositiveSemidefiniteCone

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance nullTensor02NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor0SSpace 2 I x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 2 x

private local instance nullTensor02NormedSpace (x : M) :
    NormedSpace Real (Tensor0SSpace 2 I x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 2 x

private local instance nullTensor02AddCommGroup (x : M) :
    AddCommGroup (Tensor0SSpace 2 I x) :=
  @NormedAddCommGroup.toAddCommGroup _ (nullTensor02NormedAddCommGroup (I := I) x)

private local instance nullTensor02Module (x : M) :
    Module Real (Tensor0SSpace 2 I x) :=
  @NormedSpace.toModule _ _ _ _ (nullTensor02NormedSpace (I := I) x)

private local instance nullTensor02TopologicalSpace (x : M) :
    TopologicalSpace (Tensor0SSpace 2 I x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (nullTensor02NormedAddCommGroup (I := I) x))))

def ParallelNullDistribution
    {F : M → Type _} [∀ x, NormedAddCommGroup (F x)]
    [∀ x, NormedSpace Real (F x)]
    (tr : ∀ x y, F x ≃L[Real] F y) (N : ∀ x, Submodule Real (F x)) : Prop :=
  ∀ x y, (N x).map (tr x y : F x →ₗ[Real] F y) = N y

theorem parallelTensorNullDirection_of_terminal_null
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (tr : ∀ x y : M, Tensor0SSpace 2 I x ≃L[Real] Tensor0SSpace 2 I y)
    (hC : ∀ x y : M,
      (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 2 I x)).map
          (tr x y : Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 2 I y) =
        (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
          ProperCone Real (Tensor0SSpace 2 I y)))
    (x₀ : M)
    (u : Real → ∀ x : M, Tensor0SSpace 2 I x)
    (v₀ : TangentSpace I x₀)
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (dualScalarization (fun t : Real => fun x : M => tr x x₀ (u t x))
          (tensor02EvalSelfCLM (I := I) (M := M) v₀ :
            StrongDual Real (Tensor0SSpace 2 I x₀))))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M))
    (hgrad_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) tau))
    (hlaplacian_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) tau))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₁ : M}
    (hzero : quad02 (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) v₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      v₀ ∈ twoTensorLeftKernel (I := I) (M := M) (tr x x₀ (u t x)) ∧
        tr x x₀ (u t x) ∈
          tensor02PositiveSemidefiniteCone (I := I) (M := M) := by
  classical
  let C : ∀ x : M, ProperCone Real (Tensor0SSpace 2 I x) := fun x =>
    tensor02PositiveSemidefiniteCone (I := I) (M := M)
  let phi : StrongDual Real (Tensor0SSpace 2 I x₀) :=
    tensor02EvalSelfCLM (I := I) (M := M) v₀
  let u₀ : Real → M → Tensor0SSpace 2 I x₀ := fun t x => tr x x₀ (u t x)
  have hphi : ProperCone.IsDualElement (C x₀) phi := by
    simpa [C, phi] using
      (tensor02EvalSelfCLM_isDualElement (I := I) (M := M) v₀)
  have hzero' : dualScalarization u₀ phi tau x₁ = 0 := by
    simpa [dualScalarization, u₀, phi] using hzero
  have hfixed_mem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u₀ t x ∈ C x₀ := by
    intro t ht x
    change tr x x₀ (u t x) ∈ C x₀
    change tr x x₀ (u t x) ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M)
    rw [← hC x x₀]
    exact (ProperCone.mem_map_continuousLinearEquiv_iff
      (C x) (tr x x₀) (tr x x₀ (u t x))).2 (by simpa [C] using hmem t ht x)
  have hfixed_face := properCone_mem_dualZeroFace_of_terminal_eq_zero
    (I := I) G hT (C x₀) u₀ phi hphi V hsol htau hfixed_mem
      hgrad_cont hlaplacian_cont L hV hzero'
  intro t ht x
  have hface0 := hfixed_face t ht x
  have hmem2 : u₀ t x ∈ C x₀ := (ProperCone.mem_dualZeroFace.mp hface0).1
  have hzero2 : phi (u₀ t x) = 0 := (ProperCone.mem_dualZeroFace.mp hface0).2
  let A : Tensor0SSpace 2 I x₀ := tr x x₀ (u t x)
  have hA_mem : A ∈ C x₀ := by
    simpa [A, u₀] using hmem2
  have hquad : quad02 (I := I) (M := M) A v₀ = 0 := by
    simpa [A, u₀, phi] using hzero2
  have hA_symm : ∀ v w : TangentSpace I x₀,
      eval02 (I := I) (M := M) A v w = eval02 (I := I) (M := M) A w v :=
    (mem_tensor02PositiveSemidefiniteCone.mp (by simpa [C] using hA_mem)).1
  have hA_nonneg : ∀ v : TangentSpace I x₀, 0 ≤ quad02 (I := I) (M := M) A v :=
    (mem_tensor02PositiveSemidefiniteCone.mp (by simpa [C] using hA_mem)).2
  have hkernel : v₀ ∈ twoTensorLeftKernel (I := I) (M := M) A :=
    (quad02_eq_zero_iff_mem_twoTensorLeftKernel (I := I) (M := M) A hA_symm hA_nonneg).mp hquad
  exact ⟨hkernel, by simpa [A, C] using hA_mem⟩

theorem parallelTensorNullSpace_of_terminal_null
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (tr : ∀ x y : M, Tensor0SSpace 2 I x ≃L[Real] Tensor0SSpace 2 I y)
    (hC : ∀ x y : M,
      (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 2 I x)).map
          (tr x y : Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 2 I y) =
        (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
          ProperCone Real (Tensor0SSpace 2 I y)))
    (x₀ : M)
    (u : Real → ∀ x : M, Tensor0SSpace 2 I x)
    (v₀ : TangentSpace I x₀)
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (dualScalarization (fun t : Real => fun x : M => tr x x₀ (u t x))
          (tensor02EvalSelfCLM (I := I) (M := M) v₀ :
            StrongDual Real (Tensor0SSpace 2 I x₀))))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M))
    (hgrad_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) tau))
    (hlaplacian_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) tau))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₁ : M}
    (hnull : v₀ ∈ twoTensorLeftKernel (I := I) (M := M)
      (tr x₁ x₀ (u tau x₁))) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      v₀ ∈ twoTensorLeftKernel (I := I) (M := M) (tr x x₀ (u t x)) := by
  classical
  let C : ∀ x : M, ProperCone Real (Tensor0SSpace 2 I x) := fun x =>
    tensor02PositiveSemidefiniteCone (I := I) (M := M)
  have hmem_tau : u tau x₁ ∈ C x₁ := by
    simpa [C] using hmem tau ⟨le_of_lt htau.1, le_rfl⟩ x₁
  have htransported_mem : tr x₁ x₀ (u tau x₁) ∈ C x₀ := by
    change tr x₁ x₀ (u tau x₁) ∈ C x₀
    change tr x₁ x₀ (u tau x₁) ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M)
    rw [← hC x₁ x₀]
    exact (ProperCone.mem_map_continuousLinearEquiv_iff
      (C x₁) (tr x₁ x₀) (tr x₁ x₀ (u tau x₁))).2 (by simpa using hmem_tau)
  have hA_symm : ∀ v w : TangentSpace I x₀,
      eval02 (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) v w =
        eval02 (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) w v :=
    (mem_tensor02PositiveSemidefiniteCone.mp (by simpa [C] using htransported_mem)).1
  have hA_nonneg : ∀ v : TangentSpace I x₀,
      0 ≤ quad02 (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) v :=
    (mem_tensor02PositiveSemidefiniteCone.mp (by simpa [C] using htransported_mem)).2
  have hzero : quad02 (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) v₀ = 0 :=
    (quad02_eq_zero_iff_mem_twoTensorLeftKernel (I := I) (M := M)
      (tr x₁ x₀ (u tau x₁)) hA_symm hA_nonneg).mpr hnull
  intro t ht x
  exact (parallelTensorNullDirection_of_terminal_null
    (I := I) G hT tr hC x₀ u v₀ V hsol htau hmem
      hgrad_cont hlaplacian_cont L hV hzero) t ht x |>.1

theorem parallelTensorNullSpace_eq_transported_terminal_of_constant_finrank
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (tr : ∀ x y : M, Tensor0SSpace 2 I x ≃L[Real] Tensor0SSpace 2 I y)
    (hC : ∀ x y : M,
      (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 2 I x)).map
          (tr x y : Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 2 I y) =
        (tensor02PositiveSemidefiniteCone (I := I) (M := M) :
          ProperCone Real (Tensor0SSpace 2 I y)))
    (x₀ : M)
    (u : Real → ∀ x : M, Tensor0SSpace 2 I x)
    (V : Real → M → Real)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    {x₁ : M}
    (hsol : ∀ v₀ : TangentSpace I x₀,
      v₀ ∈ twoTensorLeftKernel (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) →
      IsHeatPotSupersolutionOn
        (RealTimeInterval.closed 0 T hT) G V
        (dualScalarization (fun t : Real => fun x : M => tr x x₀ (u t x))
          (tensor02EvalSelfCLM (I := I) (M := M) v₀ :
            StrongDual Real (Tensor0SSpace 2 I x₀))))
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ tensor02PositiveSemidefiniteCone (I := I) (M := M))
    (hgrad_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) tau))
    (hlaplacian_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) tau))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    (hfinrank : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      Module.finrank Real (twoTensorLeftKernel (I := I) (M := M) (tr x x₀ (u t x))) =
      Module.finrank Real (twoTensorLeftKernel (I := I) (M := M) (tr x₁ x₀ (u tau x₁)))) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      twoTensorLeftKernel (I := I) (M := M) (tr x x₀ (u t x)) =
      twoTensorLeftKernel (I := I) (M := M) (tr x₁ x₀ (u tau x₁)) := by
  classical
  intro t ht x
  let Kterm : Submodule Real (TangentSpace I x₀) :=
    twoTensorLeftKernel (I := I) (M := M) (tr x₁ x₀ (u tau x₁))
  let Ktx : Submodule Real (TangentSpace I x₀) :=
    twoTensorLeftKernel (I := I) (M := M) (tr x x₀ (u t x))
  change Ktx = Kterm
  have hdim : Module.finrank Real Ktx = Module.finrank Real Kterm := by
    simpa [Kterm, Ktx] using hfinrank t ht x
  have hle : Kterm ≤ Ktx := by
    intro v₀ hv₀
    exact parallelTensorNullSpace_of_terminal_null
      (I := I) G hT tr hC x₀ u v₀ V (hsol v₀ (by simpa [Kterm] using hv₀))
      htau hmem hgrad_cont hlaplacian_cont L hV
      (by simpa [Kterm] using hv₀) t ht x
  apply le_antisymm
  · by_contra hnot
    have hne : Kterm ≠ Ktx := by
      intro hEq
      exact hnot (le_of_eq hEq.symm)
    have hlt : Kterm < Ktx := lt_of_le_of_ne hle hne
    have hltfin : Module.finrank Real Kterm < Module.finrank Real Ktx :=
      Submodule.finrank_lt_finrank_of_lt hlt
    omega
  · exact hle

end

end DifferentialGeometry.Analysis.Parabolic
