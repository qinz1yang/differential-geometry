import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakPartialDual
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

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

theorem exists_timeH1_weighted_weak_partial_dual
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : tsupport c ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN)) {T : ℝ}
    (z : timeH1 (Lp ℝ 2 (volume.restrict Ω)) T)
    (H : ℝ × EuStd → ℝ)
    (hHmem : ∀ᵐ t ∂timeMeasure T, MemLp (fun x => H (t, x)) 2 (volume.restrict Ω))
    (hH : ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k
      (fun x => H (t, x)) (z.toFun t) Ω) :
    ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T,
      (∀ᵐ t ∂timeMeasure T, ∀ v : H1ComplDirichlet q,
        w.toFun t v = ∫ x in Ω, H (t, x) * c x *
          H1ComplDirichletToLp q v
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ v : H1ComplDirichlet q,
        w.deriv t v =
          -(∫ x in Ω, z.deriv t x * fderiv ℝ c x (EuclideanSpace.single k 1) *
            H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) -
          ∫ x in Ω, z.deriv t x * c x *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v x := by
  let R : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  have hdual := exists_lp_dual_weak_partial_eq_integral
    (n := n) (M := M) (Ω := Ω) (c := c) q α hΩ hΩc hΩs hc hcs k
  obtain ⟨L, hL, hLweak⟩ := hdual
  have hcomp := exists_timeH1_comp_clm
    (X := Lp ℝ 2 (volume.restrict Ω)) (Y := H1ComplDirichlet q →L[ℝ] ℝ) (T := T) L z
  obtain ⟨w, _, hw, hwd⟩ := hcomp
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hH, hHmem, ae_restrict_mem measurableSet_Icc] with t hHt hmem ht
    let Q := hmem.toLp (fun x => H (t, x))
    have hQ : (Q : EuStd → ℝ) =ᵐ[volume.restrict Ω] fun x => H (t, x) :=
      hmem.coeFn_toLp
    have hweak : DeGiorgi.HasWeakPartialDeriv k Q (z.toFun t) Ω := by
      intro φ hφ hφc hφs
      refine (hHt φ hφ hφc hφs).trans ?_
      congr 1
      apply integral_congr_ae
      filter_upwards [hQ] with x hx
      rw [hx]
    intro v
    rw [hw t ht]
    refine (hLweak (z.toFun t) Q hweak v).trans ?_
    apply integral_congr_ae
    filter_upwards [hQ, chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q v)] with x hx hRx
    change Q x * c x * R v x = _
    rw [hx]
    exact congrArg (fun y => H (t, x) * c x * y) hRx
  · filter_upwards [hwd] with t hwt
    intro v
    refine (congrArg (fun A : H1ComplDirichlet q →L[ℝ] ℝ => A v) hwt).trans ?_
    refine (hL (z.deriv t) v).trans ?_
    apply congrArg (fun r : ℝ => -r - ∫ x in Ω, z.deriv t x * c x *
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v x)
    apply integral_congr_ae
    filter_upwards [chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q v)] with x hx
    exact congrArg (fun y => z.deriv t x * fderiv ℝ c x (EuclideanSpace.single k 1) * y) hx

theorem exists_timeH1_mass_dual_of_chartPullback_weak_partial
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN)) {T : ℝ}
    (z : timeH1 (Lp ℝ 2 (volume.restrict Ω)) T)
    (H : ℝ × EuStd → ℝ)
    (hHmem : ∀ᵐ t ∂timeMeasure T, MemLp (fun x => H (t, x)) 2 (volume.restrict Ω))
    (hH : ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k
      (fun x => H (t, x)) (z.toFun t) Ω)
    (v : ℝ → H1ComplDirichlet q)
    (hv : ∀ᵐ t ∂timeMeasure T,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        Sobolev.Chart.chartPullback I_hs α (fun x => η x * H (t, x))) :
    ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T,
      ∀ᵐ t ∂timeMeasure T, ∀ y : H1ComplDirichlet q,
        w.toFun t y = inner ℝ (H1ComplDirichletToLp q (v t)) (H1ComplDirichletToLp q y) := by
  let c : EuStd → ℝ := fun x => Laplacian.MetricExtension.densityOnEuclid q α x * η x
  have hcs : tsupport c ⊆ Ω := tsupport_mul_subset_right.trans hηs
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (((Laplacian.MetricExtension.densityOnEuclid_contDiffOn q α).mono
      (subset_closure.trans (hΩs.trans (image_mono interior_subset)))).mul
        hη.contDiffOn).contDiff_of_tsupport_subset hΩ hcs
  obtain ⟨w, hw, _⟩ := exists_timeH1_weighted_weak_partial_dual q α hΩ hΩc hΩs
    hc hcs k z H hHmem hH
  refine ⟨w, ?_⟩
  filter_upwards [hw, hv, hHmem] with t hwt hvt hmem
  let P := hmem.toLp (fun x => H (t, x))
  have hP : (P : EuStd → ℝ) =ᵐ[volume.restrict Ω] fun x => H (t, x) := hmem.coeFn_toLp
  have hvP : (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_hs) (M := M) q]
        Sobolev.Chart.chartPullback I_hs α (fun x => η x * P x) := by
    apply hvt.trans
    apply Sobolev.Chart.chartPullback_ae_eq_of_ae_eq q α
    have hall := (ae_restrict_iff' hΩ.measurableSet).mp hP
    filter_upwards [hall] with x hx
    by_cases hxs : x ∈ tsupport η
    · exact congrArg (η x * ·) (hx (hηs hxs)).symm
    · simp only [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  intro y
  rw [hwt y, inner_eq_integral_chartPullback_mul q α hΩs hη hηs P (v t) y hvP]
  apply integral_congr_ae
  filter_upwards [hP] with x hx
  change H (t, x) * c x * _ = P x * c x * _
  rw [hx]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
