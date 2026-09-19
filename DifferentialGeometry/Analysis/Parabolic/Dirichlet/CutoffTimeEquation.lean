import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartMassPairing

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem deriv_ae_eq_of_cutoff_tensor_identity
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    {a b : ℝ} (hab : a < b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (H : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : Lp (H1ComplDirichlet q) 2 μ)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * H (t, z)))
    (hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z))
    (hℓ : ∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
          ∂μ.prod (volume.restrict Ω)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
          ∂μ.prod (volume.restrict Ω))
    (htensor : ∀ (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo a b →
      let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
      (∫ p, deriv τ p.1 * (η p.2 * (MetricExtension.densityOnEuclid q α p.2 * H p)) * ψ p.2
          ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
          ∫ p, τ p.1 * B p * ψ p.2
            ∂μ.prod (volume.restrict Ω)) :
    w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s) := by
  let : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
  let mass : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (H1ComplDirichletToLp q) (H1ComplDirichletToLp q)
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) (hηs.trans subset_closure)
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω)) := Lp.SecondCountableTopology
  obtain ⟨P, hP, _⟩ := Lp.exists_curry (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) H
  have hvP : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * P t z) := by
    filter_upwards [hv, hP] with t hvt hPt
    apply hvt.trans
    apply chartPullback_ae_eq_of_ae_eq q α
    have hall := (ae_restrict_iff' hΩ.measurableSet).mp hPt
    filter_upwards [hall] with x hx
    by_cases hxs : x ∈ tsupport η
    · exact congrArg (η x * ·) (hx (hηs hxs)).symm
    · simp only [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  refine timeH1.deriv_ae_eq_of_tensor_mass_dual (ν := volume.restrict Ω)
    (X := H1ComplDirichlet q) (S := SmoothScalarDirichlet q) hab μ hμ
    (smoothToH1ComplDirichlet q) (denseRange_smoothToH1ComplDirichlet q)
    mass v w ℓ hw
    (W := fun x => η x.2 * (σ x * H x)) (B := B) (Q := Q)
    (R := fun z x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q z)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)))
    (D := fun z j => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (smoothToH1ComplDirichlet q z)) ?_ ?_ ?_
  · intro τ z
    have h := integral_mass_inner_eq_integral_chart_prod q α hΩ hΩc hΩs hη hηc hηs
      τ v P H (hP.mono fun _ ht => ht.symm) (smoothToH1ComplDirichlet q z) hvP
    apply h.trans
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [σ]
    ring
  · intro τ z
    exact hℓ τ (smoothToH1ComplDirichlet q z)
  · intro z τ hτ hτc hτs
    exact integral_chart_tensor_test_of_smooth q α hΩ hΩc hΩs μ z τ (htensor z τ hτ hτc hτs)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
