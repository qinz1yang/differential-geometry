import DifferentialGeometry.Geometry.Measure.Area.SecondIntegralDerivative
import DifferentialGeometry.Geometry.Measure.Area.NormalFirstIntegral
import DifferentialGeometry.Geometry.Measure.Area.NormalSecondVariation
import DifferentialGeometry.Geometry.Measure.Area.NormalJacobiSecondVariation
import DifferentialGeometry.Geometry.Measure.Area.InducedVolume
import DifferentialGeometry.Geometry.Submanifold.NormalBundle.DiskWeingartenNorm
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskJacobiPotential
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedTangentialTrace
import DifferentialGeometry.Geometry.Connection.LeviCivita.SelfDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology BigOperators

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

namespace DifferentialGeometry.Geometry

theorem SmoothDiskExtension.hasDerivAt_deriv_diskArea_normal_compactSupportFlow
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (u : C(closedDisk, M)) (U : ℂ → M)
    (hExt : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hImm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z))
    (hUD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q))
    (hiD : ∀ q : D, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q))
    (ν : ∀ q : D, TangentSpace (𝓡 3) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) ((𝓡 3).tangent) ∞
      (fun q : D => (⟨U q, ν q⟩ : TangentBundle (𝓡 3) M)))
    (hunit : ∀ q : D, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : D) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q v) = 0) :
    let gD := g.pullback (fun q : D => U q) hUD hiD
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
    (∀ (q : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0) →
        ∑ i : Fin 2, secondFundamentalFormAmbientAt gD g
          (fun p : D => U p) q (b i) (b i) = 0) →
    ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
    ∀ (X : ∀ x : M, TangentSpace (𝓡 3) x)
      (hX : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
        (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
      (hXc : HasCompactSupport X),
      (∀ q : D,
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
          (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) :
            EuclideanSpace ℝ (Fin 3)) = φ q • ν q) →
    ∀ (b : ∀ q : D, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ (q : D) (i j : Fin 2),
        gD.inner q (b q i) (b q j) = if i = j then 1 else 0) →
      let J : D → ℝ := fun q =>
        let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
        gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
          (metricScalarAt gD q / 2 -
            (metricScalarAt g (U q) +
              ∑ i : Fin 2, ∑ j : Fin 2,
                g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j))) / 2) * φ q ^ 2
      let L : ℝ → ℝ := fun t => riemannianDiskArea g
        ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
          (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u)
      Integrable J μ ∧ HasDerivAt L 0 0 ∧
        HasDerivAt (deriv L) (∫ q : D, J q ∂μ) 0 := by
  classical
  dsimp only
  intro hmean φ hφ hφc X hX hXc hvelocity b hb
  let gD := g.pullback (fun q : D => U q) hUD hiD
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let L : ℝ → ℝ := fun t => riemannianDiskArea g
    ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)
  let J : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
      (metricScalarAt gD q / 2 -
        (metricScalarAt g (U q) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j))) / 2) * φ q ^ 2
  let A : ∀ x : M, TangentSpace (𝓡 3) x := fun x =>
    (LeviCivita g).toFun X x (X x)
  let T : D → ℝ := fun q => ∑ i : Fin 2,
    g.inner (U q)
      (sourceSectionCovariantDerivative g U (fun p => A (U p)) q (b q i))
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U q (b q i))
  let J₀ : D → ℝ := fun q => riemannianAreaDensity g U q
  let d₂ : ℂ → ℝ := fun z =>
    deriv (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z)) 0
  change Integrable J μ ∧ HasDerivAt L 0 0 ∧
    HasDerivAt (deriv L) (∫ q : D, J q ∂μ) 0
  obtain ⟨_, _, henergy⟩ :=
    original_disk_normal_second_density_with_mean_and_acceleration
      g u U hExt hImm ν hν hunit hnormal
  have hpoint (q : D) : d₂ q = J₀ q * (J q + T q) := by
    let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
      g.inner (U q)
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    let P : Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i =>
      mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U q (b q i)
    let C : ℝ := ∑ i : Fin 2, B
      ((riemannOp (LeviCivita g) (U q)) (ν q) (P i) (P i)) (ν q)
    let S : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
      B (II (b q i) (b q j)) (II (b q i) (b q j))
    have hnormalMean : (∑ i : Fin 2, B (ν q) (II (b q i) (b q i))) = 0 := by
      have htrace : (∑ i : Fin 2, II (b q i) (b q i)) =
          (0 : EuclideanSpace ℝ (Fin 3)) := hmean q (b q) (hb q)
      calc
        (∑ i : Fin 2, B (ν q) (II (b q i) (b q i))) =
            B (ν q) (∑ i : Fin 2, II (b q i) (b q i)) :=
          (map_sum (B (ν q)) (fun i : Fin 2 => II (b q i) (b q i)) Finset.univ).symm
        _ = B (ν q) 0 :=
          congrArg (fun v : EuclideanSpace ℝ (Fin 3) => B (ν q) v) htrace
        _ = 0 := map_zero (B (ν q))
    have hcoefficient : C + S =
        (metricScalarAt g (U q) + S) / 2 - metricScalarAt gD q / 2 :=
      normal_jacobi_coefficient_eq_scalar_gauss_of_zero_mean_curvature_complex
        D g (by simp) U hUD hiD q (ν q) (hunit q) (hnormal q) (b q) (hb q)
        (hmean q (b q) (hb q))
    have hd := henergy φ hφ hφc X hX hXc hvelocity q (b q) (hb q)
    have hd₂ := hd.deriv
    change d₂ q = riemannianAreaDensity g U q *
      (gD.inner q (gradFun gD φ q) (gradFun gD φ q) - φ q ^ 2 * (C + S) +
        φ q ^ 2 * (∑ i : Fin 2, B (ν q) (II (b q i) (b q i))) ^ 2 + T q) at hd₂
    rw [hd₂]
    change riemannianAreaDensity g U q *
      (gD.inner q (gradFun gD φ q) (gradFun gD φ q) - φ q ^ 2 * (C + S) +
        φ q ^ 2 * (∑ i : Fin 2, B (ν q) (II (b q i) (b q i))) ^ 2 + T q) =
      riemannianAreaDensity g U q *
        (gD.inner q (gradFun gD φ q) (gradFun gD φ q) +
          (metricScalarAt gD q / 2 - (metricScalarAt g (U q) + S) / 2) * φ q ^ 2 + T q)
    rw [hnormalMean, hcoefficient]
    ring
  have hXsource (q : D) : (X (U q) : EuclideanSpace ℝ (Fin 3)) = φ q • ν q := by
    have hd := (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc (U q) 0).mfderiv
    have hv := congrArg (fun K : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) => K (1 : ℝ)) hd
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) :
        EuclideanSpace ℝ (Fin 3)) = (1 : ℝ) •
      X (Diffeomorph.compactSupportFlow X hX hXc 0 (U q)) at hv
    have hzero : Diffeomorph.compactSupportFlow X hX hXc 0 (U q) = U q :=
      DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero X hX hXc) (U q)
    rw [one_smul, hzero] at hv
    exact hv.symm.trans (hvelocity q)
  have hAc : HasCompactSupport (fun q : D => (A (U q) : EuclideanSpace ℝ (Fin 3))) := by
    apply hφc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro q hq hφq
    have hXq : X (U q) = 0 := by rw [hXsource q, hφq, zero_smul]
    apply hq
    change (LeviCivita g).toFun X (U q) (X (U q)) = 0
    rw [hXq, map_zero]
  have hA : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun x => (⟨x, A x⟩ : TangentBundle (𝓡 3) M)) :=
    contMDiff_leviCivita_self g X hX
  have hacc : Integrable T μ ∧ (∫ q : D, T q ∂μ) = 0 :=
    integral_tangential_trace_eq_zero_of_zero_mean_curvature
      D g U hUD hiD hmean A hA hAc b hb
  have hparent := hasDerivAt_deriv_diskArea_compactSupportFlow_integral
    g hExt hImm X hX hXc (0 : ℝ)
  change IntegrableOn d₂ (Metric.closedBall (0 : ℂ) 1) ∧
    HasDerivAt (deriv L) (∫ z in Metric.closedBall (0 : ℂ) 1, d₂ z) 0 at hparent
  let μD := Measure.comap (Subtype.val : D → ℂ) (volume : Measure ℂ)
  have hval : MeasurableEmbedding (Subtype.val : D → ℂ) :=
    (D : TopologicalSpace.Opens ℂ).isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
      (mα := borel D)
  have hd₂int : Integrable (fun q : D => d₂ q) μD := by
    have hm := hval.integrable_map_iff (μ := μD) (g := d₂)
    rw [hval.map_comap, Subtype.range_coe] at hm
    exact hm.mp (hparent.1.mono_set Metric.ball_subset_closedBall)
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U (D : Set ℂ) := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp
      (hUD.contMDiffAt (x := (⟨z, hz⟩ : D)))).contMDiffWithinAt
  have hJ₀c : Continuous J₀ :=
    (continuousOn_riemannianAreaDensity g (D : TopologicalSpace.Opens ℂ).isOpen
      (hUon.of_le (by simp))).domRestrict
  have hJ₀m : Measurable (fun q => ENNReal.ofReal (J₀ q)) :=
    ENNReal.measurable_ofReal.comp hJ₀c.measurable
  have hJ₀finite : ∀ᵐ q ∂μD, ENNReal.ofReal (J₀ q) < (⊤ : ENNReal) :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hJ₀real (q : D) : (ENNReal.ofReal (J₀ q)).toReal = J₀ q :=
    ENNReal.toReal_ofReal (riemannianAreaDensity_nonneg g U q)
  have hvol := riemannianVolumeMeasure_induced_complex_open D g U hUD hiD
  change μ = μD.withDensity (fun q => ENNReal.ofReal (J₀ q)) at hvol
  have hweighted : Integrable (fun q : D => J₀ q * (J q + T q)) μD :=
    hd₂int.congr (Eventually.of_forall hpoint)
  have hsum : Integrable (fun q : D => J q + T q) μ := by
    rw [hvol]
    apply (integrable_withDensity_iff_integrable_smul' hJ₀m hJ₀finite).mpr
    simpa only [hJ₀real, smul_eq_mul] using hweighted
  have hJint : Integrable J μ := by
    exact (hsum.sub hacc.1).congr (Eventually.of_forall fun q =>
      add_sub_cancel_right (J q) (T q))
  have hvolIntegral : (∫ q : D, J q + T q ∂μ) =
      ∫ q : D, J₀ q * (J q + T q) ∂μD := by
    rw [hvol, integral_withDensity_eq_integral_toReal_smul hJ₀m hJ₀finite]
    simp only [hJ₀real, smul_eq_mul]
  have hsubtype : (∫ q : D, d₂ q ∂μD) = ∫ z in Metric.ball (0 : ℂ) 1, d₂ z := by
    have hmap := hval.integral_map (μ := μD) d₂
    rw [hval.map_comap, Subtype.range_coe] at hmap
    exact hmap.symm
  have hnosphere : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hsets : Metric.closedBall (0 : ℂ) 1 =ᵐ[volume] Metric.ball (0 : ℂ) 1 := by
    filter_upwards [hnosphere] with z hz
    apply propext
    constructor
    · intro hzclosed
      exact lt_of_le_of_ne hzclosed hz
    · intro hzball
      exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hzball))
  have hintegral : (∫ z in Metric.closedBall (0 : ℂ) 1, d₂ z) =
      ∫ q : D, J q ∂μ := by
    calc
      (∫ z in Metric.closedBall (0 : ℂ) 1, d₂ z) =
          ∫ z in Metric.ball (0 : ℂ) 1, d₂ z := setIntegral_congr_set hsets
      _ = ∫ q : D, d₂ q ∂μD := hsubtype.symm
      _ = ∫ q : D, J₀ q * (J q + T q) ∂μD :=
        integral_congr_ae (Eventually.of_forall hpoint)
      _ = ∫ q : D, J q + T q ∂μ := hvolIntegral.symm
      _ = ∫ q : D, J q ∂μ := by rw [integral_add hJint hacc.1, hacc.2, add_zero]
  let H : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g (fun p : D => U p) q
    let a := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
    let c := g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
    let d := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
    (c * g.inner (U q) (ν q) (II (1 : ℂ) (1 : ℂ)) +
        a * g.inner (U q) (ν q) (II Complex.I Complex.I) -
        2 * d * g.inner (U q) (ν q) (II (1 : ℂ) Complex.I)) / (a * c - d ^ 2)
  have hHzero (q : D) : H q = 0 := by
    have htrace := (normal_scalar_secondFundamentalForm_disk_trace_eq_sum_orthonormal
      D g U hUD hiD q (ν q) (b q) (hb q)).2
    change H q = ∑ i : Fin 2, g.inner (U q) (ν q)
      (secondFundamentalFormAmbientAt gD g (fun p : D => U p) q (b q i) (b q i)) at htrace
    rw [htrace, ← map_sum, hmean q (b q) (hb q), map_zero]
  have hfirst : HasDerivAt L (-(∫ q : D, φ q * H q ∂μ)) 0 :=
    (SmoothDiskExtension.hasDerivAt_diskArea_normal_compactSupportFlow
      g u U hExt hImm hUD hiD ν hν.continuous hnormal φ hφ hφc).2
      X hX hXc hvelocity
  have hfirstZero : HasDerivAt L 0 0 := by
    simpa only [hHzero, mul_zero, integral_zero, neg_zero] using hfirst
  refine ⟨hJint, hfirstZero, ?_⟩
  exact hintegral ▸ hparent.2

end DifferentialGeometry.Geometry
