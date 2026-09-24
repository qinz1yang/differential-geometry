import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.Construction.TensorBumpTimeJets
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private local instance partialTensorSourceC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance partialTensorTargetC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace F] [T2Space M] in
theorem exists_partial_pullback_tensor_time_tower
    (Phi : PartialDiffeomorph J I N M ∞)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ Phi.source)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (chi : N → ℝ) (hchi : ContMDiff J 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ (U : Set N)) (times : Set ℝ)
    (hA : ∀ q t, t ∈ times → ∀ x ∈ Phi '' (U : Set N),
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) times t) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2,
      (∀ q t, ∀ y ∈ (U : Set N), ∀ v : Fin 2 → TangentSpace J y,
        B q t y v = chi y * A q t (Phi y) (fun j => mfderiv J I Phi y (v j))) ∧
      (∀ q t, ∀ y : N, y ∉ (U : Set N) → B q t y = 0) ∧
      ∀ q t, t ∈ times → ∀ y : N,
        HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) times t := by
  let V : TopologicalSpace.Opens M := ⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩
  let psi : Diffeomorph J I U V ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let C : ℕ → ℝ → Tensor0SField (I := J) (M := U) (n := ∞) 2 :=
    fun q t => pullbackTensor02FieldCross psi (restrictOpen0S (I := I) 2 (V := V) (A q t))
  have hC (q : ℕ) (t : ℝ) (ht : t ∈ times) (y : U) :
      HasDerivWithinAt (fun s => C q s y) (C (q + 1) t y) times t := by
    apply hasDerivWithinAt_pullbackTensor02FieldCross psi
      (fun s => restrictOpen0S (I := I) 2 (V := V) (A q s))
      (restrictOpen0S (I := I) 2 (V := V) (A (q + 1) t)) y
    let basis := Module.finBasis ℝ (TangentSpace I (psi y))
    apply tensor0S_hasDerivWithinAt_of_components basis
    intro slots
    apply hasDerivWithinAt_restrictOpenTensor02Field V (fun s => A q s) (A (q + 1) t)
      (psi y) (fun j => basis (slots j))
    exact (tensor0SEvalCLM (I := I) (M := M) (x := (psi y : M))
      (fun j => basis (slots j))).hasFDerivAt.comp_hasDerivWithinAt t (hA q t ht (psi y : M) (psi y).property)
  obtain ⟨B, hvalue, hout, hderiv⟩ :=
    exists_tensor_bump_time_tower U 2 C chi hchi hsupp times hC
  refine ⟨B, ?_, hout, hderiv⟩
  intro q t y hy v
  have hc : C q t ⟨y, hy⟩ v =
      A q t (Phi y) (fun j => mfderiv J I Phi y (v j)) := by
    change pullbackTensor02FieldCross psi
      (restrictOpen0S (I := I) 2 (V := V) (A q t)) ⟨y, hy⟩ v = _
    refine (pullbackTensor02FieldCross_apply psi
      (restrictOpen0S (I := I) 2 (V := V) (A q t)) (⟨y, hy⟩ : U) v).trans ?_
    refine (restrictOpenTensor02Field_apply V (A q t) (psi (⟨y, hy⟩ : U))
      (fun j => mfderiv J I psi (⟨y, hy⟩ : U) (v j))).trans ?_
    change A q t (Phi y) (fun j => mfderiv J I psi (⟨y, hy⟩ : U) (v j)) = _
    congr 1
    funext j
    exact DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      Phi hU (⟨y, hy⟩ : U) (v j)
  exact (hvalue q t y hy v).trans (congrArg (fun z => chi y * z) hc)


end DifferentialGeometry
