import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCovariantContinuity
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Derivation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Endomorphism


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ancientLocalTensorC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance ancientLocalTensorC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem solution_localCovariantTensor_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (n : ℕ)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace n I x) (x : M) :
    ContinuousWithinAt
      (fun s => localCovariantDerivTensor0SAt n (S.family.connection s) X α x) (Iic b) t := by
  have hGamma : ContinuousWithinAt
      (fun s => connectionEndomorphismInChart (S.family.connection s) (fun p => X p) x
        (extChartAt I x x)) (Iic b) t := by
    apply continuousWithinAt_clm_apply.mpr
    intro v
    simp only [← connectionEndomorphismInChartL_apply_center_modelVector]
    exact ((solution_connectionEndomorphism_continuousWithinAt S hS hcarrier hregular ht
      x (extChartAt I x x)).clm_apply continuousWithinAt_const).clm_apply
        continuousWithinAt_const
  unfold localCovariantDerivTensor0SAt covariantDerivTensor0SModelWithin
    covariantDerivTensor0SModelAt
  simp only [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt (Tensor0SModel n ℝ E) (fun p : M => Tensor0SSpace n I p) x)
    (FiberBundle.mem_baseSet_trivializationAt' x)]
  apply ((trivializationAt (Tensor0SModel n ℝ E)
    (fun p : M => Tensor0SSpace n I p) x).symmL ℝ x).continuous.continuousAt.comp_continuousWithinAt
  apply continuousWithinAt_const.sub
  have hCorrection := ((lieDerivCorrectionOpL (𝕜 := ℝ) (E := E) n).continuous.continuousAt.comp_continuousWithinAt
    hGamma).clm_apply
      (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : ℝ => tensor0SModelInChart n x α (extChartAt I x x)) (Iic b) t)
  simpa only [Function.comp_apply, lieDeriv_correctionOpL_apply,
    lieDeriv_correctionL_apply] using hCorrection


theorem solution_localCovariantTensor_mem_at_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b)
    (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (n : ℕ) (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace n I x) (x : M)
    (K : Submodule ℝ (Tensor0SSpace n I x))
    (hmem : ∀ t ∈ Ioo a b,
      localCovariantDerivTensor0SAt n (S.family.connection t) X α x ∈ K) :
    localCovariantDerivTensor0SAt n (S.family.connection b) X α x ∈ K := by
  apply K.closed_of_finiteDimensional.mem_of_tendsto
    ((solution_localCovariantTensor_continuousWithinAt S hS hcarrier hregular le_rfl
      n X α x).mono Iio_subset_Iic_self)
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  exact hmem t ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
