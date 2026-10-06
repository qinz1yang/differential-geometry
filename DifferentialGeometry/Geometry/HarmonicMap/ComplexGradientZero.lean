import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientEquation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

set_option autoImplicit false
noncomputable section

open Set Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual complex coordinate gradient vanishes precisely where the map's
manifold differential vanishes. This does not require conformality or immersion. -/
theorem chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
    {U : ℂ → M} {z : ℂ} (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z)
    {p : M} (hsrc : U z ∈ (chartAt E p).source) :
    (∀ k : Fin (Module.finrank ℝ E), chartComplexGradient p U k z = 0) ↔
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  let C : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U z)
  have hchart := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hsrc
  have hX : ContDiffAt ℝ 1 X z := (hchart.comp z hU).contDiffAt
  have hcoord (k : Fin (Module.finrank ℝ E)) (v : ℂ) :
      fderiv ℝ (fun q => chartCoordCLM E k (X q)) z v =
        chartCoordCLM E k (fderiv ℝ X z v) := by
    have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      ((chartCoordCLM E k).hasFDerivAt.comp z
        (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using hh
  have hgrad (k : Fin (Module.finrank ℝ E)) :
      chartComplexGradient p U k z =
        (⟨chartCoordCLM E k (fderiv ℝ X z 1) / 2,
          -chartCoordCLM E k (fderiv ℝ X z Complex.I) / 2⟩ : ℂ) := by
    change (⟨fderiv ℝ (fun q => chartCoordCLM E k (X q)) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E k (X q)) z Complex.I / 2⟩ : ℂ) = _
    rw [hcoord, hcoord]
  have hchain (v : ℂ) : fderiv ℝ X z v = C (D v) := by
    have hh := mfderiv_comp_apply z
      (hchart.mdifferentiableAt (by norm_num)) (hU.mdifferentiableAt (by norm_num)) v
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hC : Function.Injective C :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (show U z ∈ (extChartAt 𝓘(ℝ, E) p).source by
        simpa only [extChartAt_source] using hsrc)).injective
  have hseparate (v : E) (hv : ∀ k : Fin (Module.finrank ℝ E),
      chartCoordCLM E k v = 0) : v = 0 := by
    apply (chartModelBasis E).equivFun.injective
    ext k
    simpa only [← chartCoordCLM_apply, map_zero] using hv k
  constructor
  · intro hzero
    have hparts (k : Fin (Module.finrank ℝ E)) :
        chartCoordCLM E k (fderiv ℝ X z 1) = 0 ∧
          chartCoordCLM E k (fderiv ℝ X z Complex.I) = 0 := by
      have hk := hzero k
      rw [hgrad k] at hk
      have hre := congrArg Complex.re hk
      have him := congrArg Complex.im hk
      change chartCoordCLM E k (fderiv ℝ X z 1) / 2 = 0 at hre
      change -chartCoordCLM E k (fderiv ℝ X z Complex.I) / 2 = 0 at him
      constructor <;> linarith
    have hOne : fderiv ℝ X z 1 = 0 := hseparate _ (fun k => (hparts k).1)
    have hI : fderiv ℝ X z Complex.I = 0 := hseparate _ (fun k => (hparts k).2)
    have hlinear : (fderiv ℝ X z).toLinearMap = 0 := by
      apply Complex.basisOneI.ext
      intro i
      fin_cases i
      · simpa using hOne
      · simpa using hI
    change D = 0
    apply ContinuousLinearMap.ext
    intro v
    change D v = 0
    apply hC
    calc
      C (D v) = fderiv ℝ X z v := (hchain v).symm
      _ = 0 := congrArg (fun L : ℂ →ₗ[ℝ] E => L v) hlinear
      _ = C 0 := (map_zero C).symm
  · intro hzero k
    change D = 0 at hzero
    have hDX (v : ℂ) : fderiv ℝ X z v = 0 := by
      calc
        fderiv ℝ X z v = C (D v) := hchain v
        _ = 0 := by rw [hzero]; exact map_zero C
    rw [hgrad k, hDX 1, hDX Complex.I]
    simp
    rfl

/-- For the original Morrey disk, chart-gradient zeros are exactly zeros of the
original disk extension's differential, including at possible branch points. -/
theorem IsMorreyDisk.chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {p : M}
    (hsrc : diskExtension u z ∈ (chartAt E p).source) :
    (∀ k : Fin (Module.finrank ℝ E), chartComplexGradient p (diskExtension u) k z = 0) ↔
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z = 0 := by
  apply DifferentialGeometry.Geometry.chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
    (hsrc := hsrc)
  exact (hu.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds hz)).of_le (by norm_num)

end DifferentialGeometry.Geometry
