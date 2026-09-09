import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientTensorEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientTimeDual
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientMassPairing
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem scalar_weak_deriv_of_tensor_integrals
    {X S E J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace E] [Fintype J]
    {ν : Measure E} {a b : ℝ}
    (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (ι : S → X) {p q : ℝ → X →L[ℝ] ℝ}
    {W B : ℝ × E → ℝ} {Q : J → ℝ × E → ℝ}
    {R : S → E → ℝ} {D : S → J → E → ℝ}
    (hmass : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * p t (ι x) ∂μ) =
        ∫ z, τ z.1 * W z * R x z.2 ∂μ.prod ν)
    (hdual : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * q t (ι x) ∂μ) =
        (∫ z, τ z.1 * B z * R x z.2 ∂μ.prod ν) -
          ∑ j, ∫ z, τ z.1 * Q j z * D x j z.2 ∂μ.prod ν)
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ z, deriv φ z.1 * W z * R x z.2 ∂μ.prod ν) =
        (∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂μ.prod ν) -
          ∫ z, φ z.1 * B z * R x z.2 ∂μ.prod ν) :
    ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t in Ioo a b, deriv φ t * p t (ι x)) = -∫ t in Ioo a b, φ t * q t (ι x) := by
  subst μ
  intro x φ hφ hφc hφs
  let μ := volume.restrict (Icc a b)
  have hφm : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hdφm : MemLp (deriv φ) 2 μ :=
    (hφ.continuous_deriv (by simp)).memLp_of_hasCompactSupport hφc.deriv
  have hτint (τ : ℝ → ℝ) (hτ : MemLp τ 2 μ) (L : ℝ → X →L[ℝ] ℝ) :
      (∫ t in Icc a b, hτ.toLp τ t * L t (ι x)) =
        ∫ t in Ioo a b, τ t * L t (ι x) := by
    apply Eq.trans ?_ (setIntegral_congr_set Ioo_ae_eq_Icc).symm
    apply integral_congr_ae
    filter_upwards [hτ.coeFn_toLp] with t ht
    rw [ht]
  have hτprod (τ : ℝ → ℝ) (hτ : MemLp τ 2 μ) (F : ℝ × E → ℝ) (V : E → ℝ) :
      (∫ z, hτ.toLp τ z.1 * F z * V z.2 ∂μ.prod ν) =
        ∫ z, τ z.1 * F z * V z.2 ∂μ.prod ν := by
    apply integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hτ.coeFn_toLp] with z hz
    rw [hz]
  have hM := hmass (hdφm.toLp (deriv φ)) x
  rw [hτint, hτprod] at hM
  have hQ := hdual (hφm.toLp φ) x
  rw [hτint, hτprod] at hQ
  have hsum : (∑ j, ∫ z, hφm.toLp φ z.1 * Q j z * D x j z.2 ∂(volume.restrict (Icc a b)).prod ν) =
      ∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂(volume.restrict (Icc a b)).prod ν := by
    apply Finset.sum_congr rfl
    intro j _
    exact hτprod φ hφm (Q j) (D x j)
  rw [hsum] at hQ
  have hW := hweak x φ hφ hφc hφs
  exact hM.trans (hW.trans (by linarith only [hQ]))

private theorem timeH1.deriv_ae_eq_of_tensor_mass_dual
    {X S E J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup S] [NormedSpace ℝ S]
    [MeasurableSpace E] [Fintype J] {ν : Measure E}
    {a b : ℝ} (hab : a < b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    (mass : X →L[ℝ] X →L[ℝ] ℝ) (v : Lp X 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a)) (q : Lp (X →L[ℝ] ℝ) 2 μ)
    (hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : X, w.toFun s z = mass (v (a + s)) z)
    {W B : ℝ × E → ℝ} {Q : J → ℝ × E → ℝ}
    {R : S → E → ℝ} {D : S → J → E → ℝ}
    (hmass : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * mass (v t) (ι x) ∂μ) = ∫ z, τ z.1 * W z * R x z.2 ∂μ.prod ν)
    (hdual : ∀ (τ : Lp ℝ 2 μ) (x : S),
      (∫ t, τ t * q t (ι x) ∂μ) = (∫ z, τ z.1 * B z * R x z.2 ∂μ.prod ν) -
        ∑ j, ∫ z, τ z.1 * Q j z * D x j z.2 ∂μ.prod ν)
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ z, _root_.deriv φ z.1 * W z * R x z.2 ∂μ.prod ν) =
        (∑ j, ∫ z, φ z.1 * Q j z * D x j z.2 ∂μ.prod ν) -
          ∫ z, φ z.1 * B z * R x z.2 ∂μ.prod ν) :
    w.deriv =ᵐ[timeMeasure (b - a)] fun s => q (a + s) := by
  have hp : MemLp (fun t => mass (v t)) 2 (volume.restrict (Icc a b)) := by
    rw [← hμ]
    exact mass.comp_memLp v
  have hq : MemLp (fun t => q t) 2 (volume.restrict (Icc a b)) := by
    rw [← hμ]
    exact Lp.memLp q
  have hrep : (fun s => mass (v (a + s))) =ᵐ[timeMeasure (b - a)] w.toFun := by
    filter_upwards [hw] with s hs
    exact ContinuousLinearMap.ext (fun z => (hs z).symm)
  exact w.deriv_ae_eq_of_dense_weak_dual_deriv_on hab ι hdense hp hq hrep
    (scalar_weak_deriv_of_tensor_integrals μ hμ ι hmass hdual hweak)

private theorem integral_timeH1_test_of_mass_dual
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {a b : ℝ} (hab : a ≤ b) (J : X →L[ℝ] Y)
    (v : ℝ → X) (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (ℓ : ℝ → X →L[ℝ] ℝ)
    (hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : X,
      w.toFun s z = inner ℝ (J (v (a + s))) (J z))
    (hd : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (ζ : timeH1 X (b - a)) (hζ0 : ζ.toFun 0 = 0) (hζ1 : ζ.toFun (b - a) = 0) :
    (∫ s, inner ℝ (J (v (a + s))) (J (ζ.deriv s)) ∂timeMeasure (b - a)) +
      (∫ s, ℓ (a + s) (ζ.toFun s) ∂timeMeasure (b - a)) = 0 := by
  have h := timeH1.integral_dual_deriv_add_deriv_dual (sub_nonneg.mpr hab) w ζ
  rw [hζ0, hζ1, map_zero, map_zero, sub_self] at h
  refine Eq.trans ?_ h
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply integral_congr_ae
    filter_upwards [hw] with s hs
    exact (hs (ζ.deriv s)).symm
  · apply integral_congr_ae
    filter_upwards [hd] with s hs
    exact (congrArg (fun L : X →L[ℝ] ℝ => L (ζ.toFun s)) hs).symm

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open Bundle Manifold
open scoped ContDiff Manifold NNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem canonical_gradient_tensor_test
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (μ : Measure ℝ) {W B : ℝ × EuStd → ℝ}
    {Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ)
    (hraw :
      let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
      (∫ p, deriv τ p.1 * W p * ψ p.2 ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
        ∫ p, τ p.1 * B p * ψ p.2 ∂μ.prod (volume.restrict Ω)) :
    (∫ p, deriv τ p.1 * W p *
      H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
        ∂μ.prod (volume.restrict Ω)) =
      (∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
        (smoothToH1ComplDirichlet q v) p.2 ∂μ.prod (volume.restrict Ω)) -
      ∫ p, τ p.1 * B p * H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
        ∂μ.prod (volume.restrict Ω) := by
  let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let R := fun z => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let ν := μ.prod (volume.restrict Ω)
  have hR : R =ᵐ[volume.restrict Ω] ψ := by
    rw [show R = (fun z => smoothToLpDirichlet q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) by
      funext z; simp only [R, H1ComplDirichletToLp_smoothToH1ComplDirichlet]]
    have h := ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) v.memLp_two.coeFn_toLp
    change (fun z => v.memLp_two.toLp v.toFun ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω] ψ
    exact h
  have hRp : (fun p : ℝ × EuStd => R p.2) =ᵐ[ν] fun p => ψ p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume.restrict Ω)).ae hR
  have hleft : (∫ p, deriv τ p.1 * W p * R p.2 ∂ν) =
      ∫ p, deriv τ p.1 * W p * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hRp] with p hp
    exact congrArg (fun r : ℝ => deriv τ p.1 * W p * r) hp
  have hright : (∫ p, τ p.1 * B p * R p.2 ∂ν) =
      ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hRp] with p hp
    exact congrArg (fun r : ℝ => τ p.1 * B p * r) hp
  have hflux : (∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (smoothToH1ComplDirichlet q v) p.2 ∂ν) =
      ∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν := by
    apply Finset.sum_congr rfl
    intro j _
    have hD := dirichletLocalWeakPartialLp_smoothToH1ComplDirichlet_coeFn q α hΩ hΩc hΩs j v
    have hDp := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume.restrict Ω)).ae hD
    apply integral_congr_ae
    filter_upwards [hDp] with p hp
    exact congrArg (fun r : ℝ => τ p.1 * Q j p * r) hp
  exact hleft.trans (hraw.trans (congrArg₂ (fun a b : ℝ => a - b) hflux hright).symm)

private theorem cutoff_gradient_dual_deriv
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω₀)
    {T t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T) (ht₀₁ : t₀ < t₁)
    (u : timeL2 (H1ComplDirichlet q) T)
    (v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc t₀ t₁)))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀))
    (ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 ((timeMeasure T).restrict (Icc t₀ t₁)))
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (k : Fin (Module.finrank ℝ EuN))
    (hv : ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁),
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z))
    (hw : ∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z))
    (hℓ : ∀ (τ : Lp ℝ 2 ((timeMeasure T).restrict (Icc t₀ t₁))) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂(timeMeasure T).restrict (Icc t₀ t₁)) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j z p.2
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀))
    (htensor : ∀ (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo t₀ t₁ →
      let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
      (∫ p, deriv τ p.1 * (η p.2 * (MetricExtension.densityOnEuclid q α p.2 *
          dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u p)) * ψ p.2
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)) -
          ∫ p, τ p.1 * B p * ψ p.2
            ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)) :
    w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s) := by
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
  let V := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u
  let mass : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (H1ComplDirichletToLp q) (H1ComplDirichletToLp q)
  have hμ : μ = volume.restrict (Icc t₀ t₁) :=
    Measure.restrict_restrict_of_subset (fun t ht => ⟨ht₀.trans ht.1, ht.2.trans ht₁⟩)
  refine timeH1.deriv_ae_eq_of_tensor_mass_dual (ν := volume.restrict Ω₀)
    (X := H1ComplDirichlet q) (S := SmoothScalarDirichlet q) ht₀₁ μ hμ
    (smoothToH1ComplDirichlet q) (denseRange_smoothToH1ComplDirichlet q)
    mass v w ℓ hw
    (W := fun x => η x.2 * (σ x * V x)) (B := B) (Q := Q)
    (R := fun z x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q z)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)))
    (D := fun z j => dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j (smoothToH1ComplDirichlet q z)) ?_ ?_ ?_
  · intro τ z
    have h := integral_mass_inner_eq_integral_spacetime_weak_partial_of_subset q α hΩ hΩc hΩs
      hΩ₀ hΩ₀c hΩ₀s hsub hη hηc hηs u v k hv τ
      (smoothToH1ComplDirichlet q z)
    apply h.trans
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [σ]
    ring
  · intro τ z
    exact hℓ τ (smoothToH1ComplDirichlet q z)
  · intro z τ hτ hτc hτs
    exact canonical_gradient_tensor_test q α hΩ₀ hΩ₀c hΩ₀s μ z τ (htensor z τ hτ hτc hτs)

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_gradient_dual_deriv
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ < t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, σ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * V k p)) * φ p ∂ν) ∧
      let C := fun k p => (r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * V k p)
      let Q := fun k j p => ∑ i, (η p.2 / r p) * A i j p * H k i p
      let B := fun k p => η p.2 * C k p -
        ∑ i, ∑ j, A i j p * H k i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      (∀ k j, MemLp (Q k j) 2 ν) ∧ (∀ k, MemLp (B k) 2 ν) ∧
      ∀ k, ∃ v : Lp (H1ComplDirichlet q) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u t) z)) ∧
        (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z)) ∧
        (w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s)) ∧
        (∀ ζ : timeH1 (H1ComplDirichlet q) (t₁ - t₀),
          ζ.toFun 0 = 0 → ζ.toFun (t₁ - t₀) = 0 →
          (∫ s, inner ℝ (H1ComplDirichletToLp q (v (t₀ + s)))
            (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (t₁ - t₀)) +
            (∫ s, ℓ (t₀ + s) (ζ.toFun s) ∂timeMeasure (t₁ - t₀)) = 0) ∧
        ∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t z ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν := by
  have hmass := fun k => hu.exists_timeH1_cutoff_gradient_mass_dual hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω hη hηc hηs k
  choose v w hv hw using hmass
  intro μ ν ρ σ r A U V
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hF, hfixed, hsource⟩ :=
    hu.exists_lp_cutoff_gradient_tensor_identity hXcont hacont α hΩ hΩc hΩs hXsmooth
      ht₀ ht₁ hΩ₀ hΩ₀Ω hη hηc hηs
  refine ⟨R, H, F, hR, hH, hHsym, hF, hfixed, ?_⟩
  intro C Q B
  obtain ⟨hQ, hB, hdual, htensor⟩ := hsource
  refine ⟨hQ, hB, ?_⟩
  intro k
  obtain ⟨ℓ, hℓ⟩ := hdual k
  have hd := cutoff_gradient_dual_deriv α hΩ hΩc hΩs hΩ₀
    (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
    (hΩ₀Ω.trans (subset_closure.trans hΩs)) (subset_closure.trans hΩ₀Ω)
    hη hηc hηs ht₀.le ht₁.le ht₀₁ u (v k) (w k) ℓ (Q k) (B k) k (hv k) (hw k) hℓ (htensor k)
  exact ⟨v k, w k, ℓ, hv k, hw k, hd,
    fun ζ hζ0 hζ1 => integral_timeH1_test_of_mass_dual ht₀₁.le
      (H1ComplDirichletToLp q) (v k) (w k) ℓ (hw k) hd ζ hζ0 hζ1, hℓ⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
