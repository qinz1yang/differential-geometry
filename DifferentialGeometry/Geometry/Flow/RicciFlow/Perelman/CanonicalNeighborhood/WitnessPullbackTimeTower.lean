import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenTensorJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorBumpTimeJets
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private local instance pullbackTimeSourceC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance pullbackTimeTargetC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [T2Space M] in
theorem exists_partial_pullback_time_tower
    (Phi : PartialDiffeomorph I I N M ∞)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (chi : N → ℝ) (hchi : ContMDiff I 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ Phi.source) (J : Set ℝ)
    (hA : ∀ q t, t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) J t) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2,
      (∀ q t, ∀ y ∈ Phi.source, ∀ v : Fin 2 → TangentSpace I y,
        B q t y v = chi y * A q t (Phi y) (fun j => mfderiv I I Phi y (v j))) ∧
      (∀ q t, ∀ y : N, y ∉ Phi.source → B q t y = 0) ∧
      ∀ q t, t ∈ J → ∀ y : N,
        HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) J t := by
  let U : TopologicalSpace.Opens N := ⟨Phi.source, Phi.open_source⟩
  have hU : (U : Set N) ⊆ Phi.source := Subset.rfl
  let V : TopologicalSpace.Opens M := ⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩
  let psi : Diffeomorph I I U V ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let C : ℕ → ℝ → Tensor0SField (I := I) (M := U) (n := ∞) 2 :=
    fun q t => pullbackTensor02FieldCross psi (restrictOpen0S (I := I) 2 (V := V) (A q t))
  have hC (q : ℕ) (t : ℝ) (ht : t ∈ J) (y : U) :
      HasDerivWithinAt (fun s => C q s y) (C (q + 1) t y) J t := by
    apply hasDerivWithinAt_pullbackTensor02FieldCross psi
      (fun s => restrictOpen0S (I := I) 2 (V := V) (A q s))
      (restrictOpen0S (I := I) 2 (V := V) (A (q + 1) t)) y
    let basis := Module.finBasis ℝ (TangentSpace I (psi y))
    apply tensor0S_hasDerivWithinAt_of_components basis
    intro slots
    apply hasDerivWithinAt_restrictOpenTensor02Field V (fun s => A q s) (A (q + 1) t)
      (psi y) (fun j => basis (slots j))
    exact (tensor0SEvalCLM (I := I) (M := M) (x := (psi y : M))
      (fun j => basis (slots j))).hasFDerivAt.comp_hasDerivWithinAt t (hA q t ht (psi y : M))
  obtain ⟨B, hvalue, hout, hderiv⟩ :=
    exists_tensor_bump_time_tower U 2 C chi hchi hsupp J hC
  refine ⟨B, ?_, hout, hderiv⟩
  intro q t y hy v
  have hc : C q t ⟨y, hy⟩ v =
      A q t (Phi y) (fun j => mfderiv I I Phi y (v j)) := by
    change pullbackTensor02FieldCross psi
      (restrictOpen0S (I := I) 2 (V := V) (A q t)) ⟨y, hy⟩ v = _
    refine (pullbackTensor02FieldCross_apply psi
      (restrictOpen0S (I := I) 2 (V := V) (A q t)) (⟨y, hy⟩ : U) v).trans ?_
    refine (restrictOpenTensor02Field_apply V (A q t) (psi (⟨y, hy⟩ : U))
      (fun j => mfderiv I I psi (⟨y, hy⟩ : U) (v j))).trans ?_
    change A q t (Phi y) (fun j => mfderiv I I psi (⟨y, hy⟩ : U) (v j)) = _
    congr 1
    funext j
    exact DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      Phi hU (⟨y, hy⟩ : U) (v j)
  exact (hvalue q t y hy v).trans (congrArg (fun z => chi y * z) hc)


theorem exists_closedWindow_pullback_metric_time_tower
    [I.Boundaryless] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (Phi : PartialDiffeomorph I I N M ∞)
    (chi : N → ℝ) (hchi : ContMDiff I 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ Phi.source) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2,
      (∀ t, ∀ y ∈ Phi.source, ∀ v : Fin 2 → TangentSpace I y,
        B 0 t y v = chi y * (S.base.metric t).inner (Phi y)
          (mfderiv I I Phi y (v 0)) (mfderiv I I Phi y (v 1))) ∧
      (∀ q t, ∀ y : N, y ∉ Phi.source → B q t y = 0) ∧
      ∀ q t, t ∈ Icc c b → ∀ y : N,
        HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) (Icc c b) t := by
  obtain ⟨A, hzero, hA⟩ := exists_closedWindow_metric_time_fields S hS hac hcb hslab hreg
  obtain ⟨B, hvalue, hout, hderiv⟩ := exists_partial_pullback_time_tower Phi A chi hchi hsupp
    (Icc c b) (fun q t ht x => (hA q t ht x).2)
  refine ⟨B, ?_, hout, hderiv⟩
  intro t y hy v
  rw [hvalue 0 t y hy v, hzero t, metricTensorField_apply]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
