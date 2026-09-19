import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeProduct
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem exists_timeH1_localWeakPartial_of_spatial_weak_deriv_time_deriv
    (q : SmoothRiemannianMetric I_hs M) {T : ℝ}
    (u : timeL2 (H1ComplDirichlet q) T)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (0 : ℝ) T)
    (hΩ₀ : IsOpen Ω₀) (hsub : Ω₀ ⊆ Ω) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∀ R : Lp ℝ 2 ν, ∀ DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun x => DR i (t, x)) (fun x => R (t, x)) Ω₀) →
      ∀ i, ∃ w : timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (b - a),
        ∀ᵐ s ∂timeMeasure (b - a),
          ((w.toFun s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u (a + s))) ∧
          ((w.deriv s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun x => DR i (a + s, x)) := by
  intro μ ν U R DR hR hDR
  have hμ : (timeMeasure T).restrict (Icc a b) = μ :=
    Measure.restrict_restrict_of_subset hI
  have hμle : μ ≤ timeMeasure T := by
    rw [← hμ]
    exact Measure.restrict_le_self
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs
    (timeMeasure T) i u
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono hμle (Measure.restrict_mono hsub le_rfl)
  have hU : LocallyIntegrable U ν :=
    ((Lp.memLp U).mono_measure hmeasure).locallyIntegrable (by norm_num)
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hshift : MeasurePreserving (fun s : ℝ => a + s)
      (timeMeasure (b - a)) μ := by
    rw [← hμ]
    exact measurePreserving_add_right_timeMeasure_restrict hI
  intro i
  let V₀ : Lp ℝ 2 ν := (hV i).toLp (V i)
  have hfirst : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => V i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono hμle)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hspace : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ ψ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, V i p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      hU ((hV i).locallyIntegrable (by norm_num)) i hfirst ψ hψ hψc
      (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, V₀ p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DR i p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have hcomm := Sobolev.integral_weak_deriv_fderiv_comm
      (0, EuclideanSpace.single i 1) (1, 0) hspace hR hφ hφc hφs
    have hrspace := Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp R).locallyIntegrable (by norm_num))
      ((Lp.memLp (DR i)).locallyIntegrable (by norm_num)) i (hDR i) φ hφ hφc
      (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
    refine (integral_congr_ae ?_).trans (hcomm.trans hrspace)
    filter_upwards [(hV i).coeFn_toLp] with p hp
    exact congrArg (fun v => v * fderiv ℝ φ p (1, 0)) hp
  obtain ⟨w, hwae⟩ := exists_timeH1_of_spacetime_weak_deriv hab hΩ₀ V₀ (DR i) hweak
  have hP₀ : ∀ᵐ t ∂μ, (fun x => V₀ (t, x)) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) := by
    have hc := (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs
      (timeMeasure T) i u).filter_mono (ae_mono hμle)
    filter_upwards [Measure.ae_ae_of_ae_prod ((hV i).coeFn_toLp), hc] with t hvt hct
    exact Filter.EventuallyEq.trans hvt (ae_restrict_of_ae_restrict_of_subset hsub hct)
  refine ⟨w, ?_⟩
  filter_upwards [hwae, hshift.quasiMeasurePreserving.ae hP₀] with s hs hsP
  exact ⟨hs.1.trans hsP, hs.2⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
