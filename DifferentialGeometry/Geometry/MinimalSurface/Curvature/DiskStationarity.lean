import DifferentialGeometry.Geometry.Measure.Area.NormalFirstIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem SmoothDiskExtension.normal_scalar_trace_eq_zero_of_all_normal_flow_localMin
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) (U : ℂ → M)
    (hExt : SmoothDiskExtension (E := E) u U)
    (hImm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    (hUD : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : D => U q))
    (hiD : ∀ q : D, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : D => U p) q))
    (ν : ∀ q : D, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : Continuous
      (fun q : D => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hnormal : ∀ (q : D) (v : ℂ),
      g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : D => U p) q v) = 0)
    (hflows : ∀ (φ : D → ℝ),
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      ∃ (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
        (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) : E) =
              φ q • ν q) ∧
        IsLocalMin (fun t => riemannianDiskArea g
          ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
            (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u)) 0) :
    let f : D → M := fun q => U q
    let gD := g.pullback f hUD hiD
    let H : D → ℝ := fun q =>
      let II := secondFundamentalFormAmbientAt gD g f q
      let A := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
      let B := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
      let C := g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
      (C * g.inner (U q) (ν q) (II (1 : ℂ) (1 : ℂ)) +
          A * g.inner (U q) (ν q) (II Complex.I Complex.I) -
          2 * B * g.inner (U q) (ν q) (II (1 : ℂ) Complex.I)) /
        (A * C - B ^ 2)
    ∀ q : D, H q = 0 := by
  let f : D → M := fun q => U q
  let gD := g.pullback f hUD hiD
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
  let H : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g f q
    let A := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
    let B := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
    let C := g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
    (C * g.inner (U q) (ν q) (II (1 : ℂ) (1 : ℂ)) +
        A * g.inner (U q) (ν q) (II Complex.I Complex.I) -
        2 * B * g.inner (U q) (ν q) (II (1 : ℂ) Complex.I)) /
      (A * C - B ^ 2)
  change ∀ q : D, H q = 0
  let _ : IsLocallyFiniteMeasure μ := riemannianVolumeMeasure_isLocallyFiniteMeasure gD
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure gD
  have hH : Continuous H :=
    continuous_normal_scalar_secondFundamentalForm_disk_trace D g U hUD hiD ν hν hnormal
  have htest (φ : D → ℝ)
      (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ) :
      (∫ q : D, φ q * H q ∂μ) = 0 := by
    obtain ⟨X, hX, hXc, hvelocity, hmin⟩ := hflows φ hφ hφc
    have hderiv :=
      (SmoothDiskExtension.hasDerivAt_diskArea_normal_compactSupportFlow
        g u U hExt hImm hUD hiD ν hν hnormal φ hφ hφc).2 X hX hXc hvelocity
    have hzero : -(∫ q : D, φ q * H q ∂μ) = 0 := hmin.hasDerivAt_eq_zero hderiv
    exact neg_eq_zero.mp hzero
  have hae : H =ᵐ[μ] (fun _ : D => (0 : ℝ)) :=
    ae_eq_zero_of_integral_contMDiff_smul_eq_zero (𝓘(ℝ, ℂ))
      hH.locallyIntegrable (fun φ hφ hφc => by
        simpa only [smul_eq_mul] using htest φ hφ hφc)
  have hzero : H = (fun _ : D => (0 : ℝ)) :=
    MeasureTheory.Measure.eq_of_ae_eq hae hH continuous_const
  exact fun q => congrFun hzero q

end DifferentialGeometry.Geometry
