import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Smoothness
import DifferentialGeometry.Geometry.Curvature.MetricPairing
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem tensor04_apply_basis_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    {n : ℕ}
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {v : TangentSpace I x}
    (hv : v ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x A)
    (i j : Fin n) (w : TangentSpace I x) :
    (A : Tensor0SSpace 4 I x) ![basis i,basis j,v,w] = 0 := by
  let a := ContinuousAlternatingMap.elementaryCovector basis.cDualBasis ![i,j]
  have hmem : curvatureOperatorEndomorphismAt (I := I) g x A a ∈
      curvatureOperatorImageAt (I := I) g x A := ⟨a, rfl⟩
  have hzero := ContinuousAlternatingMap.mem_contractionAnnihilator_iff.mp hv _ hmem
  have happ := congrArg
    (fun f : TangentSpace I x [⋀^Fin 1]→L[Real] Real => f ![w]) hzero
  change curvatureOperatorEndomorphismAt (I := I) g x A a ![v,w] = 0 at happ
  rw [curvatureOperatorEndomorphismAt_elementaryCovector_apply g x basis horth A] at happ
  exact neg_eq_zero.mp happ


omit [FiniteDimensional Real E] in
private theorem tensor04_apply_eq_zero_of_basis {Idx : Type*} (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Tensor0SSpace 4 I x) (v w a b : TangentSpace I x)
    (hA : ∀ i j, A ![basis i, basis j, v, w] = 0) :
    A ![a, b, v, w] = 0 := by
  classical
  have hsecond (i : Idx) : A ![basis i, b, v, w] = 0 := by
    have hlin : A.toMultilinearMap.toLinearMap ![basis i, b, v, w] 1 = 0 := by
      apply basis.ext
      intro j
      have hu : Function.update ![basis i, b, v, w] 1 (basis j) =
          ![basis i, basis j, v, w] := by
        funext k; fin_cases k <;> simp
      rw [MultilinearMap.toLinearMap_apply, hu]
      exact hA i j
    have hu : Function.update ![basis i, b, v, w] 1 b =
        ![basis i, b, v, w] := by funext k; fin_cases k <;> simp
    have hval := congrArg (fun f => f b) hlin
    change A (Function.update ![basis i, b, v, w] 1 b) = 0 at hval
    rw [hu] at hval
    exact hval
  have hlin : A.toMultilinearMap.toLinearMap ![a, b, v, w] 0 = 0 := by
    apply basis.ext
    intro i
    have hu : Function.update ![a, b, v, w] 0 (basis i) =
        ![basis i, b, v, w] := by funext k; fin_cases k <;> simp
    rw [MultilinearMap.toLinearMap_apply, hu]
    exact hsecond i
  have hu : Function.update ![a, b, v, w] 0 a = ![a, b, v, w] := by
    funext k; fin_cases k <;> simp
  have hval := congrArg (fun f => f a) hlin
  change A (Function.update ![a, b, v, w] 0 a) = 0 at hval
  rw [hu] at hval
  exact hval


theorem tensor04StdAt_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {v : TangentSpace I x}
    (hv : v ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x A)
    (a b w : TangentSpace I x) :
    tensor04StandardAt (A : Tensor0SSpace 4 I x) a b v w = 0 := by
  obtain ⟨basis, horth⟩ : ∃ basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x),
      ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    let D := (tangentMetricData (I := I) g x).metric
    let _ : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
    let _ : NormedAddCommGroup (TangentSpace I x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
    let _ : InnerProductSpace Real (TangentSpace I x) :=
      @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
    let ob := stdOrthonormalBasis Real (TangentSpace I x)
    refine ⟨ob.toBasis, ?_⟩
    intro i j
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← D.toCore_inner]
    exact ob.inner_eq_ite i j
  have h0 := tensor04_apply_eq_zero_of_basis x basis A v w a b
    (fun i j => tensor04_apply_basis_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
      g x basis horth A hv i j w)
  have hvec : vec4 (I := I) a b v w = ![a,b,v,w] := by
    funext k; fin_cases k <;> rfl
  simpa [tensor04StandardAt, hvec] using h0

theorem mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StandardAt_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (v : TangentSpace I x) :
    v ∈ curvatureOperatorImageAnnihilatorAt g x A ↔
      ∀ a b w, tensor04StandardAt (A : Tensor04At (I := I) (M := M) x) a b v w = 0 := by
  constructor
  · intro hv a b w
    exact tensor04StdAt_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt g x A hv a b w
  · intro hzero
    obtain ⟨basis, horth⟩ : ∃ basis : Module.Basis
        (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x),
        ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
      let D := (tangentMetricData (I := I) g x).metric
      let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
      let _ : NormedAddCommGroup (TangentSpace I x) :=
        @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
      let _ : InnerProductSpace ℝ (TangentSpace I x) :=
        @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
      let ob := stdOrthonormalBasis ℝ (TangentSpace I x)
      refine ⟨ob.toBasis, ?_⟩
      intro i j
      change D.inner (ob i) (ob j) = if i = j then (1 : ℝ) else 0
      rw [← D.toCore_inner]
      exact ob.inner_eq_ite i j
    apply ContinuousAlternatingMap.mem_contractionAnnihilator_iff.mpr
    intro beta hbeta
    rcases hbeta with ⟨α, hα⟩
    apply ContinuousAlternatingMap.ext
    intro w
    have hw : w = ![w 0] := by ext i; fin_cases i; rfl
    rw [hw]
    rw [← hα]
    change curvatureOperatorEndomorphismAt g x A α ![v, w 0] = 0
    rw [curvatureOperatorEndomorphismAt_apply_orthonormal g x basis horth A]
    have hz (i j) : (A : Tensor04At (I := I) (M := M) x) ![basis i, basis j, v, w 0] = 0 := by
      have h := hzero (basis i) (basis j) (w 0)
      unfold tensor04StandardAt at h
      have hvec : vec4 (I := I) (basis i) (basis j) v (w 0) =
          ![basis i, basis j, v, w 0] := by
        funext k
        fin_cases k <;> rfl
      rwa [hvec] at h
    simp only [hz, zero_mul, Finset.sum_const_zero, mul_zero]

variable [T2Space M] [BoundarylessManifold I M]

theorem riemannOp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    {v : TangentSpace I x}
    (hv : v ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x
      ⟨metricRm04At (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)
    (a b : TangentSpace I x) :
    riemannOp (LeviCivita (I := I) g) x a b v = 0 := by
  apply tangentFlatLinear_injective_gen (I := I) g x
  ext c
  rw [tangentFlatLinear_apply_gen, tangentFlatLinear_apply_gen]
  have h := tensor04StdAt_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    g x ⟨metricRm04At (I := I) g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ hv a b c
  unfold tensor04StandardAt at h
  rw [DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner] at h
  simpa [metricCov, LeviCivita] using h

theorem ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    {v : TangentSpace I x}
    (hv : v ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x
      ⟨metricRm04At (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)
    (w : TangentSpace I x) :
    ricciTensor (I := I) g x v w = 0 := by
  rw [ricciTensor_symm, ricciTensor_apply]
  have hendo : ricciEndo (I := I) g x w v = 0 := by
    ext a
    exact riemannOp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt g x hv a w
  rw [hendo, map_zero]

theorem ricciSharp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    {v : TangentSpace I x}
    (hv : v ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x
      ⟨metricRm04At (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) :
    ricciSharp (I := I) g x v = 0 := by
  apply tangentFlatLinear_injective_gen (I := I) g x
  ext w
  rw [tangentFlatLinear_apply_gen, tangentFlatLinear_apply_gen, inner_ricciSharp,
    ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt g x hv w]
  simp


theorem riemannOp_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hzero : ∀ x, Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 0) :
    ∀ x (u v w : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x u v w = 0 := by
  intro x u v w
  let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
      (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
  have hz := hzero x
  have hnull : w ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ := by
    apply ContinuousAlternatingMap.mem_contractionAnnihilator_iff.mpr
    intro beta hbeta
    rw [Submodule.finrank_eq_zero.mp hz] at hbeta
    simp only [Submodule.mem_bot] at hbeta
    simp [hbeta]
  exact riemannOp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt g x hnull u v

theorem curvatureOperatorImageAt_finrank_eq_zero_of_riemannOp_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hzero : ∀ x (u v w : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x u v w = 0) :
    ∀ x, Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 0 := by
  intro x
  have hnull (v : TangentSpace I x) : v ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ := by
    apply (mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StandardAt_eq_zero g x _ v).mpr
    intro a b w
    unfold tensor04StandardAt
    rw [DifferentialGeometry.PDE.RicciFlow.metricRm04At_inner]
    change g.inner x (riemannOp (LeviCivita g) x a b v) w = 0
    rw [hzero x a b v]
    simp
  have hrange : curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    apply ContinuousAlternatingMap.ext
    intro c
    have hc : c = ![c 0, c 1] := by ext i; fin_cases i <;> rfl
    have hz := ContinuousAlternatingMap.mem_contractionAnnihilator_iff.mp (hnull (c 0)) a ha
    have he := congrArg (fun f : TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ => f ![c 1]) hz
    change a ![c 0, c 1] = 0 at he
    rw [hc]
    exact he
  rw [hrange]
  exact finrank_bot ℝ _

end DifferentialGeometry.Geometry.Curvature
