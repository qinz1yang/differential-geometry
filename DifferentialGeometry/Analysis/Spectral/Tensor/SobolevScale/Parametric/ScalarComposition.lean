import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarComposition
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarNorm
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarMultiplication
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Tensor.RSTensor.RankZero
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative

section

open Set
open scoped ContDiff Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem ContDiffOn.exists_norm_fderiv_apply_sub_le_of_isCompact
    {F : V → W} {U K : Set V} (hF : ContDiffOn ℝ 2 F U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ p q : V,
        ‖fderiv ℝ F x p - fderiv ℝ F y q‖ ≤
          A * ‖p - q‖ + B * ‖x - y‖ * ‖q‖ := by
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hlocal : LocallyLipschitzOn K (fderiv ℝ F) := by
    intro x hx
    obtain ⟨B, s, hs, hB⟩ := (hDF.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
    exact ⟨B, s, mem_nhdsWithin_of_mem_nhds hs, hB⟩
  obtain ⟨B, hB⟩ := hlocal.exists_lipschitzOnWith_of_compact hK
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hDF.continuousOn.mono hKU)
  refine ⟨max A 0, B, le_max_right _ _, B.coe_nonneg, ?_⟩
  intro x hx y hy p q
  have hAx : ‖fderiv ℝ F x‖ ≤ max A 0 := (hA x hx).trans (le_max_left _ _)
  have hBxy : ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ B * ‖x - y‖ :=
    hB.norm_sub_le hx hy
  calc
    ‖fderiv ℝ F x p - fderiv ℝ F y q‖ =
      ‖fderiv ℝ F x (p - q) + (fderiv ℝ F x - fderiv ℝ F y) q‖ := by
        congr 1
        simp only [map_sub, sub_apply]
        abel
    _ ≤ ‖fderiv ℝ F x (p - q)‖ + ‖(fderiv ℝ F x - fderiv ℝ F y) q‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ F x‖ * ‖p - q‖ + ‖fderiv ℝ F x - fderiv ℝ F y‖ * ‖q‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ max A 0 * ‖p - q‖ + B * ‖x - y‖ * ‖q‖ := by gcongr

end

section

open Set

variable {ι : Type*} [Fintype ι]

open scoped Classical in
private theorem ContDiffOn.exists_partial_fderiv_bounds_of_isCompact
    {F : (ι → ℝ) → ℝ} {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ 2 F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ z ∈ K, ∀ i : ι, ‖fderiv ℝ F z (Pi.single i 1)‖ ≤ A) ∧
      (∀ z ∈ K, ∀ w ∈ K, ∀ i : ι,
        ‖fderiv ℝ F z (Pi.single i 1) - fderiv ℝ F w (Pi.single i 1)‖ ≤ B * ‖z - w‖) := by
  obtain ⟨A, B, hA, hB, hbound⟩ :=
    hF.exists_norm_fderiv_apply_sub_le_of_isCompact hU hK hKU
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro z hz i
    have h := hbound z hz z hz (Pi.single i 1) 0
    simpa [Pi.norm_single] using h
  · intro z hz w hw i
    have h := hbound z hz w hw (Pi.single i 1) (Pi.single i 1)
    simpa [Pi.norm_single] using h

end

section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {V W α : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [MeasurableSpace α]

private theorem LipschitzOnWith.eLpNorm_comp_sub_le
    {F : V → W} {K : Set V} {L : ℝ≥0} (hF : LipschitzOnWith L F K)
    (μ : Measure α) (p : ENNReal) (u v : α → V)
    (hu : ∀ᵐ x ∂μ, u x ∈ K) (hv : ∀ᵐ x ∂μ, v x ∈ K) :
    eLpNorm (fun x => F (u x) - F (v x)) p μ ≤
      (L : ENNReal) * eLpNorm (fun x => u x - v x) p μ := by
  have hbound : ∀ᵐ x ∂μ, ‖F (u x) - F (v x)‖ ≤ (L : ℝ) * ‖u x - v x‖ := by
    filter_upwards [hu, hv] with x hux hvx
    exact hF.norm_sub_le hux hvx
  simpa only [ENNReal.ofReal_coe_nnreal] using
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hbound p


end


section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private theorem covGrad_scalar0_apply (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) (x : M) (X : TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (covGrad (I := I) (M := M) g 0 0 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 => X) =
      mvfderiv (I := I) (TensorRSField.scalar0 S.toSection) x X := by
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g 0 0 S x
    (unitZeroSec (I := I) (M := M) x) (fun _ : Fin 1 => X)]
  rw [tensorCovDerivAt_def,
    tensorRSCovariantDerivative_zeroS_unit_eval,
    Tensor0SNabla.tensor0SCovariantDerivative_apply_zero]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (mvfderiv (I := I)
          (Tensor0SNabla.scalarFn I M (fun y => S.toSection y
            (unitZeroSec (I := I) (M := M) y))) x X)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  congr 2
  funext y
  rw [Tensor0SNabla.scalarFn_eq_apply_zero]
  simp only [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply]
  change Tensor0SSpace.toModel (S.toSection y (unitZeroSec (I := I) y)) 0 =
    Tensor0SSpace.toModel (S.toSection y
      (Tensor0SField.one0 (I := I) (M := M) ∞ y)) Fin.elim0
  congr 2
  exact Subsingleton.elim _ _

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral

end

section

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal BigOperators

namespace DifferentialGeometry.Integral.L2.SmoothCcTensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable {ι : Type*} [Fintype ι]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem norm_scalarCompOn_sub_le_of_lipschitzOnWith
    (g : SmoothRiemannianMetric I M) (u v : ι → SmoothCcTensor g 0 0)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U)
    (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ U)
    {L : NNReal} (hL : LipschitzOnWith L F K)
    (huK : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
    (hvK : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K) :
    ‖scalarCompOn u F hF hu - scalarCompOn v F hF hv‖ ≤
      (L : ℝ) * ∑ i, ‖u i - v i‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let a : M → ι → ℝ := fun x i => TensorRSField.scalar0 (u i).toSection x
  let b : M → ι → ℝ := fun x i => TensorRSField.scalar0 (v i).toSection x
  let d : ι → M → ℝ := fun i x => a x i - b x i
  have hd (i : ι) : MemLp (d i) 2 μ :=
    (memLp_scalar0 g (u i) 2).sub (memLp_scalar0 g (v i) 2)
  have hpn : ∀ x, ‖a x - b x‖ ≤ ∑ i, ‖d i x‖ := by
    intro x
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg (d i x)))).2
    intro i
    exact Finset.single_le_sum (fun j _ => norm_nonneg (d j x)) (Finset.mem_univ i)
  have hsum : eLpNorm (fun x => a x - b x) 2 μ ≤ ∑ i, eLpNorm (d i) 2 μ := by
    calc
      _ ≤ eLpNorm (fun x => ∑ i, ‖d i x‖) 2 μ :=
        eLpNorm_mono_ae_real (Filter.Eventually.of_forall hpn)
      _ ≤ ∑ i, eLpNorm (fun x => ‖d i x‖) 2 μ := by
        have heq : (fun x => ∑ i, ‖d i x‖) = ∑ i, (fun x => ‖d i x‖) := by
          funext x
          simp only [Finset.sum_apply]
        rw [heq]
        exact eLpNorm_sum_le (fun i _ => (hd i).aestronglyMeasurable.norm)
          (by norm_num : (1 : ENNReal) ≤ 2)
      _ = _ := by simp only [eLpNorm_norm]
  have hbound := (hL.eLpNorm_comp_sub_le μ 2 a b
    (Filter.Eventually.of_forall huK) (Filter.Eventually.of_forall hvK)).trans
      (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hrhs : (L : ENNReal) * ∑ i, eLpNorm (d i) 2 μ ≠ (∞ : ENNReal) := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact ENNReal.sum_ne_top.mpr (fun i _ => (hd i).eLpNorm_ne_top)
  have hreal := ENNReal.toReal_mono hrhs hbound
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun i _ => (hd i).eLpNorm_ne_top)] at hreal
  have hnorm (i : ι) : (eLpNorm (d i) 2 μ).toReal = ‖u i - v i‖ := by
    rw [norm_eq_scalar0_eLpNorm]
    simp only [toSection_sub, TensorRSField.scalar0_sub]
    rfl
  rw [norm_eq_scalar0_eLpNorm]
  simp only [toSection_sub, TensorRSField.scalar0_sub, scalar0_scalarCompOn]
  simpa only [hnorm, a, b, μ, Pi.sub_def] using hreal

theorem exists_norm_scalarCompOn_sub_le_of_isCompact
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (g : SmoothRiemannianMetric I M)
      (u v : ι → SmoothCcTensor g 0 0)
      (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
      (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K),
      ‖scalarCompOn u F hF (fun x => hKU (hu x)) -
        scalarCompOn v F hF (fun x => hKU (hv x))‖ ≤
          L * ∑ i, ‖u i - v i‖ := by
  have hF1 : ContDiffOn ℝ 1 F U := hF.of_le (by norm_num)
  have hlocal : LocallyLipschitzOn K F := by
    intro x hx
    obtain ⟨L, s, hs, hL⟩ := (hF1.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
    exact ⟨L, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩
  obtain ⟨L, hL⟩ := hlocal.exists_lipschitzOnWith_of_compact hK
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro g u v hu hv
  exact norm_scalarCompOn_sub_le_of_lipschitzOnWith g u v F hF
    (fun x => hKU (hu x)) (fun x => hKU (hv x)) hL hu hv

end DifferentialGeometry.Integral.L2.SmoothCcTensor
end

end

section

noncomputable section
open Manifold
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g : SmoothRiemannianMetric I M}
variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mvfderiv_pi_apply
    (u : M → (ι → ℝ)) (hu : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ u)
    (x : M) (X : TangentSpace I x) (i : ι) :
    mvfderiv I u x X i = mvfderiv I (fun y => u y i) x X := by
  let P : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := (mdifferentiableAt_const (c := P)).mvfderiv_clm_apply
    (hu.mdifferentiable (by simp) x)
  have h' := congrArg (fun L => L X) h
  simpa only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply, P, ContinuousLinearMap.proj_apply] using h'.symm

open scoped Classical in
private theorem mvfderiv_scalar_compOn
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U)
    (x : M) (X : TangentSpace I x) :
    mvfderiv I (fun y => F (fun i => TensorRSField.scalar0 (u i).toSection y)) x X =
      ∑ i, fderiv ℝ F (fun i => TensorRSField.scalar0 (u i).toSection x)
        ((mvfderiv I (TensorRSField.scalar0 (u i).toSection) x X) • Pi.single i 1) := by
  classical
  let v : M → (ι → ℝ) := fun y i => TensorRSField.scalar0 (u i).toSection y
  have hv : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ v :=
    contMDiff_pi_space.mpr (fun i => TensorRSField.scalar0_smooth (u i).toSection)
  have hFx : DifferentiableAt ℝ F (v x) :=
    (hF.contDiffAt (hU.mem_nhds (hu x))).differentiableAt (by simp)
  have hchain := hFx.mdifferentiableAt.mvfderiv_comp_apply
    (hv.mdifferentiable (by simp) x) X
  change mvfderiv I (F ∘ v) x X = _
  rw [hchain, DifferentialGeometry.mvfderiv_model_apply_eq_fderiv]
  change fderiv ℝ F (v x) (mvfderiv I v x X) = _
  rw [pi_eq_sum_univ' (mvfderiv I v x X), map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, mvfderiv_pi_apply v hv x X i, map_smul]

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end

section

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {ι : Type*} [Fintype ι]

omit [SigmaCompactSpace M] in
open scoped Classical in
private theorem covGrad_scalarCompOn_eval
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U)
    (x : M) (X : TangentSpace I x) :
    Tensor0SSpace.eval
      ((covGrad (I := I) (M := M) g 0 0
        (DifferentialGeometry.Integral.L2.SmoothCcTensor.scalarCompOn u F hF hu)).toSection x
        (unitZeroSec (I := I) (M := M) x))
      (fun _ : Fin 1 => X) =
      ∑ i, fderiv ℝ F (fun i => TensorRSField.scalar0 (u i).toSection x)
        ((mvfderiv I (TensorRSField.scalar0 (u i).toSection) x X) • Pi.single i 1) := by
  rw [covGrad_scalar0_apply, DifferentialGeometry.Integral.L2.SmoothCcTensor.scalar0_scalarCompOn]
  exact mvfderiv_scalar_compOn (u := u) (F := F) hF hU hu x X

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end

section

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g : SmoothRiemannianMetric I M}

private theorem ccTensor01_ext {S T : SmoothCcTensor g 0 1}
    (h : ∀ x X, Tensor0SSpace.eval (S.toSection x (unitZeroSec (I := I) x)) (fun _ : Fin 1 => X) =
      Tensor0SSpace.eval (T.toSection x (unitZeroSec (I := I) x)) (fun _ : Fin 1 => X)) : S = T := by
  apply SmoothCcTensor.ext
  rw [← TensorRSField.toRS0_rs0 S.toSection, ← TensorRSField.toRS0_rs0 T.toSection]
  congr 1
  apply ContMDiffSection.ext
  intro x
  apply tensor0SSpace_ext 1 x
  intro v
  change (S.toSection x (Tensor0SField.one0 (I := I) (M := M) ∞ x)) v =
    (T.toSection x (Tensor0SField.one0 (I := I) (M := M) ∞ x)) v
  have hv : v = fun _ : Fin 1 => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv]
  exact h x (v 0)
end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end

section

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
variable {g : SmoothRiemannianMetric I M} {ι : Type*} [Fintype ι]

open scoped Classical in
private noncomputable def scalarCompPartial
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) (i : ι) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x => fderiv ℝ F (fun j => TensorRSField.scalar0 (u j).toSection x) (Pi.single i 1),
    ((hF.fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).contMDiffOn.comp_contMDiff
      (contMDiff_pi_space.mpr (fun j => TensorRSField.scalar0_smooth (u j).toSection)) hu).clm_apply
        contMDiff_const⟩

private theorem covGrad_scalarCompOn_eq_sum
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    covGrad (I := I) (M := M) g 0 0 (SmoothCcTensor.scalarCompOn u F hF hu) =
      ∑ i, scalarSmul (I := I) (M := M) g 0 1 (scalarCompPartial u F hF hU hu i)
        (covGrad (I := I) (M := M) g 0 0 (u i)) := by
  classical
  apply ccTensor01_ext
  intro x X
  rw [covGrad_scalarCompOn_eval u F hF hU hu x X]
  have hsum : (∑ i, scalarSmul g 0 1 (scalarCompPartial u F hF hU hu i)
      (covGrad g 0 0 (u i))).toSection =
      ∑ i, (scalarSmul g 0 1 (scalarCompPartial u F hF hU hu i)
        (covGrad g 0 0 (u i))).toSection :=
    map_sum (SmoothCcTensor.toSectionAddHom) _ _
  rw [hsum]
  have hcoe := map_sum (ContMDiffSection.coeAddHom I (TensorRSModel 0 1 ℝ E) ∞
    (fun x : M => TensorRSSpace 0 1 I x))
    (fun i => (scalarSmul g 0 1 (scalarCompPartial u F hF hU hu i)
      (covGrad g 0 0 (u i))).toSection) Finset.univ
  change _ = ((ContMDiffSection.coeAddHom I (TensorRSModel 0 1 ℝ E) ∞
    (fun x : M => TensorRSSpace 0 1 I x)) _ x _).eval _
  rw [hcoe]
  simp only [Finset.sum_apply, sum_apply]
  rw [Tensor0SSpace.eval_eq, sum_apply]
  change _ = ∑ i, (((scalarCompPartial u F hF hU hu i) x) •
    ((covGrad g 0 0 (u i)).toSection x (unitZeroSec (I := I) x))).eval (fun _ => X)
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, smul_eq_mul]
  change _ = (scalarCompPartial u F hF hU hu i x) *
    ((covGrad g 0 0 (u i)).toSection x (unitZeroSec (I := I) x)).eval (fun _ => X)
  rw [covGrad_scalar0_apply]
  exact mul_comm _ _
end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end

section

noncomputable section
open Manifold
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {ι : Type*} [Fintype ι]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem scalarSmul_sub_eq {r s : ℕ} (ζ η : C^∞⟮I, M; ℝ⟯)
    (S T : SmoothCcTensor g r s) :
    scalarSmul g r s ζ S - scalarSmul g r s η T =
      scalarSmul g r s ζ (S - T) + scalarSmul g r s (ζ - η) T := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change ζ x • S.toSection x - η x • T.toSection x =
    ζ x • (S.toSection x - T.toSection x) + (ζ x - η x) • T.toSection x
  rw [smul_sub, sub_smul]
  abel

theorem exists_norm_covGrad_scalarCompOn_sub_le_of_isCompact
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (u v : ι → SmoothCcTensor g 0 0)
        (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
        (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K)
        (D : ℝ), 0 ≤ D →
        (∀ x, ‖(fun i => TensorRSField.scalar0 (u i).toSection x) -
          (fun i => TensorRSField.scalar0 (v i).toSection x)‖ ≤ D) →
        ‖covGrad g 0 0 (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖ ≤
          A * ∑ i, ‖covGrad g 0 0 (u i - v i)‖ +
            (B * D) * ∑ i, ‖covGrad g 0 0 (v i)‖ := by
  classical
  obtain ⟨A, B, hA, hB, habs, hdiff⟩ :=
    (hF.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).exists_partial_fderiv_bounds_of_isCompact hU hK hKU
  refine ⟨A, B, hA, hB, ?_⟩
  intro u v hu hv D hD huv
  let ζ := fun i => scalarCompPartial u F hF hU (fun x => hKU (hu x)) i
  let η := fun i => scalarCompPartial v F hF hU (fun x => hKU (hv x)) i
  have hz (i : ι) : ∀ x : M, |ζ i x| ≤ A := fun x => by
    exact (Real.norm_eq_abs _).symm ▸ habs _ (hu x) i
  have hd (i : ι) : ∀ x : M, |(ζ i - η i) x| ≤ B * D := by
    intro x
    have h := hdiff _ (hu x) _ (hv x) i
    change |fderiv ℝ F _ _ - fderiv ℝ F _ _| ≤ _
    rw [← Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_left (huv x) hB)
  rw [DifferentialGeometry.Analysis.Spectral.covGrad_sub, covGrad_scalarCompOn_eq_sum u F hF hU,
    covGrad_scalarCompOn_eq_sum v F hF hU, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖scalarSmul g 0 1 (ζ i) (covGrad g 0 0 (u i)) -
        scalarSmul g 0 1 (η i) (covGrad g 0 0 (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, (A * ‖covGrad g 0 0 (u i - v i)‖ +
        (B * D) * ‖covGrad g 0 0 (v i)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [scalarSmul_sub_eq]
      exact (norm_add_le _ _).trans (add_le_add
        (by
          rw [DifferentialGeometry.Analysis.Spectral.covGrad_sub]
          exact norm_scalarSmul_le g 0 1 (ζ i) hA (hz i)
            (covGrad g 0 0 (u i) - covGrad g 0 0 (v i)))
        (norm_scalarSmul_le g 0 1 (ζ i - η i) (mul_nonneg hB hD) (hd i)
          (covGrad g 0 0 (v i))))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end

section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open Manifold
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private theorem exists_norm_ccTensorToHs_one_le_add (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖ccTensorToHs (I := I) (M := M) g s (1 : ℝ) S‖ ≤
        C * (‖S‖ + ‖covGrad (I := I) (M := M) g 0 s S‖) := by
  obtain ⟨C, hC, h⟩ := hs_le_jet (I := I) (M := M) g s 1
  have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hcast] at h
  refine ⟨C, hC, fun S => ?_⟩
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add, Nat.add_zero,
    Nat.cast_one] using h S

end DifferentialGeometry.Analysis.Spectral

end

section

noncomputable section
open Manifold
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
variable {ι : Type*} [Fintype ι]

theorem exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact
    (g : SmoothRiemannianMetric I M) (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u v : ι → SmoothCcTensor g 0 0)
        (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ K)
        (hv : ∀ x, (fun i => TensorRSField.scalar0 (v i).toSection x) ∈ K)
        (D : ℝ), 0 ≤ D →
        (∀ x, ‖(fun i => TensorRSField.scalar0 (u i).toSection x) -
          (fun i => TensorRSField.scalar0 (v i).toSection x)‖ ≤ D) →
        ‖ccTensorToHs g 0 1 (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖ ≤
          C * (∑ i, ‖ccTensorToHs g 0 1 (u i - v i)‖ +
            D * ∑ i, ‖ccTensorToHs g 0 1 (v i)‖) := by
  classical
  obtain ⟨L, hL, hl⟩ := SmoothCcTensor.exists_norm_scalarCompOn_sub_le_of_isCompact
    (I := I) (M := M) F hF hU hK hKU
  obtain ⟨A, B, hA, hB, hab⟩ := exists_norm_covGrad_scalarCompOn_sub_le_of_isCompact
    (g := g) F hF hU hK hKU
  obtain ⟨Ch, hCh, hh⟩ := exists_norm_ccTensorToHs_one_le_add g 0
  obtain ⟨Cj, hCj, hj⟩ := hsJet_le (I := I) (M := M) g 0 1
  have hjet (S : SmoothCcTensor g 0 0) :
      ‖S‖ + ‖covGrad g 0 0 S‖ ≤ Cj * ‖ccTensorToHs g 0 1 S‖ := by
    have h := hj S
    have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hcast] at h
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Sobolev.iteratedCovGrad_zero, Sobolev.iteratedCovGrad_succ, Nat.zero_add, Nat.add_zero, one_mul] using h
  refine ⟨Ch * ((L + A + B) * Cj), mul_nonneg hCh (mul_nonneg (by positivity) hCj), ?_⟩
  intro u v hu hv D hD huv
  let X := ∑ i, ‖ccTensorToHs g 0 1 (u i - v i)‖
  let Y := ∑ i, ‖ccTensorToHs g 0 1 (v i)‖
  have hzero : ∑ i, ‖u i - v i‖ ≤ Cj * X := by
    calc
      _ ≤ ∑ i, Cj * ‖ccTensorToHs g 0 1 (u i - v i)‖ :=
        Finset.sum_le_sum (fun i _ => (le_add_of_nonneg_right (norm_nonneg _)).trans (hjet _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hgrad : ∑ i, ‖covGrad g 0 0 (u i - v i)‖ ≤ Cj * X := by
    calc
      _ ≤ ∑ i, Cj * ‖ccTensorToHs g 0 1 (u i - v i)‖ :=
        Finset.sum_le_sum (fun i _ => (le_add_of_nonneg_left (norm_nonneg _)).trans (hjet _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hvgrad : ∑ i, ‖covGrad g 0 0 (v i)‖ ≤ Cj * Y := by
    calc
      _ ≤ ∑ i, Cj * ‖ccTensorToHs g 0 1 (v i)‖ :=
        Finset.sum_le_sum (fun i _ => (le_add_of_nonneg_left (norm_nonneg _)).trans (hjet _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ Ch * (‖SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x))‖ +
        ‖covGrad g 0 0 (SmoothCcTensor.scalarCompOn u F hF (fun x => hKU (hu x)) -
          SmoothCcTensor.scalarCompOn v F hF (fun x => hKU (hv x)))‖) := hh _
    _ ≤ Ch * (L * (Cj * X) + (A * (Cj * X) + (B * D) * (Cj * Y))) := by
      apply mul_le_mul_of_nonneg_left _ hCh
      exact add_le_add ((hl g u v hu hv).trans (mul_le_mul_of_nonneg_left hzero hL))
        ((hab u v hu hv D hD huv).trans (add_le_add (mul_le_mul_of_nonneg_left hgrad hA)
          (mul_le_mul_of_nonneg_left hvgrad (mul_nonneg hB hD))))
    _ ≤ _ := by
      change _ ≤ Ch * ((L + A + B) * Cj) * (X + D * Y)
      rw [mul_assoc Ch]
      apply mul_le_mul_of_nonneg_left _ hCh
      nlinarith [mul_nonneg (mul_nonneg hB hCj) hX,
        mul_nonneg (mul_nonneg (add_nonneg hL hA) hCj) (mul_nonneg hD hY)]
end DifferentialGeometry.Analysis.Spectral
end

end
