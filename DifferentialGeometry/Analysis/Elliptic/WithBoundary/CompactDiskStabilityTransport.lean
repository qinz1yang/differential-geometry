import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Metric.Pullback.CompactDiskDomain
import DifferentialGeometry.Geometry.Operator.Gradient.PullbackAt
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.FunctionExtension
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open DifferentialGeometry Set MeasureTheory
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

local notation "D" =>
  (TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball :
    TopologicalSpace.Opens ℂ)
local notation "C" => DifferentialGeometry.Topology.ClosedCell 2
private local instance : ChartedSpace (EuclideanHalfSpace 2) C :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1
private local instance : IsManifold (𝓡∂ 2) ∞ C :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1
private local instance : MeasurableSpace C := borel C
private local instance : BorelSpace C := ⟨rfl⟩
private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

theorem integral_stability_closedCell_pullback_of_compact_tests
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℂ) D)
    (W : C^∞⟮𝓘(ℝ, ℂ), D; ℝ⟯)
    (hstable : ∀ f : D → ℝ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ f → HasCompactSupport f →
        0 ≤ ∫ z, g.inner z (gradFun g f z) (gradFun g f z) +
          W z * f z ^ 2 ∂(riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) g))
    (j : C → D)
    (hj : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ j)
    (himm : ∀ x : C,
      Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) j x))
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡∂ 2) D C ∞)
    (htarget : Φ.target = (𝓡∂ 2).interior C)
    (hinverse : ∀ x ∈ Φ.target, Φ.symm x = j x)
    (hinner : ∀ z ∈ Φ.source, ∀ v w : TangentSpace 𝓘(ℝ, ℂ) z,
      g.inner z v w = (g.pullback j hj himm).inner (Φ z)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡∂ 2) Φ z v)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡∂ 2) Φ z w)) :
    let gAux := g.pullback j hj himm
    ∀ f : SmoothScalarDirichlet gAux,
      0 ≤ ∫ x, gAux.inner x (gradFun gAux f.toFun x) (gradFun gAux f.toFun x) +
        W (j x) * f.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := 𝓡∂ 2) (M := C) gAux) := by
  classical
  let gAux := g.pullback j hj himm
  change ∀ f : SmoothScalarDirichlet gAux,
    0 ≤ ∫ x, gAux.inner x (gradFun gAux f.toFun x) (gradFun gAux f.toFun x) +
      W (j x) * f.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := 𝓡∂ 2) (M := C) gAux)
  intro f
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) g
  let μAux := riemannianVolumeMeasure (I := 𝓡∂ 2) (M := C) gAux
  have hft : tsupport f.toFun ⊆ Φ.target := by
    rw [htarget]
    exact f.interior_support
  obtain ⟨e, he, hec, heq, _hsupport, hes, _hezero⟩ :=
    _root_.PartialDiffeomorph.exists_contMDiff_extension_of_hasCompactSupport Φ
      f.smooth.contMDiffOn (HasCompactSupport.of_compactSpace f.toFun) hft
  let A : D → ℝ := fun z => normGradSqFun g e z + W z * e z ^ 2
  let B : C → ℝ := fun x => normGradSqFun gAux f.toFun x + W (j x) * f.toFun x ^ 2
  have hAcontinuous : Continuous A :=
    (normGradSqFun_continuous g he).add
      (W.contMDiff.continuous.mul (he.continuous.pow 2))
  have hAΦ : ∀ z ∈ Φ.source, A z = B (Φ z) := by
    intro z hz
    have hevent : e =ᶠ[𝓝 z] (f.toFun ∘ Φ) :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hz) heq
    have hgrad : gradFun g e z = gradFun g (f.toFun ∘ Φ) z := by
      have hderiv : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) e z : ℂ →L[ℝ] ℝ) =
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (f.toFun ∘ Φ) z := hevent.mfderiv_eq
      simp only [gradFun_def, hderiv]
    have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, ℂ) (𝓡∂ 2) Φ z) :=
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) (𝓡∂ 2) ∞ hz).mfderivToContinuousLinearEquiv
        (by simp)).surjective
    have hnorm : normGradSqFun g e z = normGradSqFun gAux f.toFun (Φ z) := by
      calc
        normGradSqFun g e z = normGradSqFun g (f.toFun ∘ Φ) z := by
          simp only [normGradSqFun_def, hgrad]
        _ = normGradSqFun gAux f.toFun (Φ z) :=
          normGradSqFun_comp_of_pullback_inner g gAux
            (Φ.mdifferentiableAt (by simp) hz) (hinner z hz) hsurj
            (f.smooth.mdifferentiableAt (by simp))
    have hjΦ : j (Φ z) = z :=
      (hinverse (Φ z) (Φ.map_source' hz)).symm.trans (Φ.left_inv' hz)
    change normGradSqFun g e z + W z * e z ^ 2 =
      normGradSqFun gAux f.toFun (Φ z) + W (j (Φ z)) * f.toFun (Φ z) ^ 2
    simp only [hnorm, heq hz, hjΦ, Function.comp_apply]
  have hAoff : ∀ z, z ∉ Φ.source → A z = 0 := by
    intro z hz
    have hze : z ∉ tsupport e := fun h => hz (hes h)
    have he0 : e z = 0 := image_eq_zero_of_notMem_tsupport hze
    have hg0 : gradFun g e z = 0 := by
      by_contra hne
      exact hze (support_gradFun_subset g e hne)
    change g.inner z (gradFun g e z) (gradFun g e z) + W z * e z ^ 2 = 0
    rw [hg0, he0]
    simp
  have hBoff : ∀ x, x ∉ Φ.target → B x = 0 := by
    intro x hx
    have hxf : x ∉ tsupport f.toFun := fun h => hx (hft h)
    have hf0 : f.toFun x = 0 := image_eq_zero_of_notMem_tsupport hxf
    have hg0 : gradFun gAux f.toFun x = 0 := by
      by_contra hne
      exact hxf (support_gradFun_subset gAux f.toFun hne)
    change gAux.inner x (gradFun gAux f.toFun x) (gradFun gAux f.toFun x) +
      W (j x) * f.toFun x ^ 2 = 0
    rw [hg0, hf0]
    simp
  let Φ1 : PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡∂ 2) D C 1 :=
    DifferentialGeometry.PartialDiffeomorph.ofLE Φ (by simp)
  have hvol : μ.restrict Φ.source = Measure.map Φ.symm (μAux.restrict Φ.target) :=
    riemannianVolumeMeasure_partialIsometry g gAux Φ1 hinner
  have hmeas : AEMeasurable Φ.symm (μAux.restrict Φ.target) :=
    Φ.contMDiffOn_invFun.continuousOn.aemeasurable Φ.open_target.measurableSet
  have henergy : (∫ x, B x ∂μAux) = ∫ z, A z ∂μ := by
    calc
      (∫ x, B x ∂μAux) = ∫ x in Φ.target, B x ∂μAux :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hBoff).symm
      _ = ∫ x in Φ.target, A (Φ.symm x) ∂μAux := by
        apply setIntegral_congr_fun Φ.open_target.measurableSet
        intro x hx
        have h := hAΦ (Φ.symm x) (Φ.symm.map_source' hx)
        have hΦ : Φ (Φ.symm x) = x := Φ.toPartialEquiv.right_inv hx
        rw [hΦ] at h
        exact h.symm
      _ = ∫ z, A z ∂Measure.map Φ.symm (μAux.restrict Φ.target) :=
        (integral_map hmeas hAcontinuous.aestronglyMeasurable).symm
      _ = ∫ z in Φ.source, A z ∂μ := by rw [← hvol]
      _ = ∫ z, A z ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hAoff
  change 0 ≤ ∫ x, B x ∂μAux
  rw [henergy]
  exact hstable e he hec

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
