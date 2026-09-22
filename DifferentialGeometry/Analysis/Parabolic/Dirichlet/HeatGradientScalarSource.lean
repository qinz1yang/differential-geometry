import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatGradientTimeEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffForcing
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffScalarSource
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartFlux
import DifferentialGeometry.Analysis.Integration.Lp.Pairing

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_timeH1_cutoff_gradient_scalar_source_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a < b)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω₀) →
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      ∃ B : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ,
      let Q := fun k j p => ∑ i, (η p.2 / r p) * A i j p * H k i p
      let E := fun k j p => ∑ i,
        (σ p * invGramOnEuclid (g p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V k p
      let P := fun i j (p : ℝ × EuStd) =>
        (σ p * invGramOnEuclid (g p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      (∀ k j, MemLp (Q k j) 2 ν) ∧ (∀ k, MemLp (B k) 2 ν) ∧
      ∀ k, ∃ v : Lp (H1ComplDirichlet q) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
        ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∃ f : Lp ℝ 2 ν,
        (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u t) z)) ∧
        (∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z)) ∧
        (w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s)) ∧
        (∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t z ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν) ∧
        (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
          (∫ t, τ t * β t z ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) +
            ∑ j, ∫ p, τ p.1 * E k j p * dirichletLocalWeakPartialLp q α hΩ₀
              (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
              (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν) ∧
        (∀ z : Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
            ∫ t, (∑ i, ∑ j, ∫ y in Ω₀,
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) i (v t) y *
                (densityOnEuclid q α y *
                  invGramOnEuclid (g t) α i j y) *
                dirichletLocalWeakPartialLp q α hΩ₀
                  (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                  (hΩ₀Ω.trans (subset_closure.trans hΩs)) j (z t) y) ∂μ) ∧
        (f =ᵐ[ν] fun p => B k p - ∑ i, ∑ j,
          (P i j p * H k j p +
            fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V k p)) ∧
        (∀ z : Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, β t (z t) ∂μ) =
            ∫ t, (∫ x in Ω₀, f (t, x) * H1ComplDirichletToLp q (z t)
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ) := by
  intro μ ν ρ σ r A V F Df hDf
  classical
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport η)
      (hηs.trans (subset_closure.trans (hΩ₀Ω.trans subset_closure)))
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨R, H, S, hR, hH, hHsym, hSformula, hS, hfixed, hsource⟩ :=
    exists_timeH1_cutoff_gradient_dual_deriv_of_heat_timeH1 hG hT hreg q hCg hequiv Cv hCv0
      hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv hη hηc hηs Df hDf
  let C := fun k p => (r p)⁻¹ * S k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * V k p)
  let B := fun k p => η p.2 * C k p -
    ∑ i, ∑ j, A i j p * H k i p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have htime : Icc a b ⊆ Icc (0 : ℝ) T := fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hμ : μ = volume.restrict (Icc a b) := Measure.restrict_restrict_of_subset htime
  refine ⟨H, hH, hHsym, B, ?_⟩
  intro Q E P
  have hQ := hsource.1
  have hB := hsource.2.1
  have hpacket := hsource.2.2
  refine ⟨hQ, hB, ?_⟩
  intro k
  let v := Classical.choose (hpacket k)
  let w' := Classical.choose (Classical.choose_spec (hpacket k))
  let ℓ := Classical.choose (Classical.choose_spec (Classical.choose_spec (hpacket k)))
  have hp := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hpacket k)))
  have hv := hp.1
  have hw := hp.2.1
  have hd := hp.2.2.1
  have hℓ := hp.2.2.2.2
  have hν : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV : MemLp (V k) 2 ν := (Lp.memLp (V k)).mono_measure hν
  have hflux (j) : ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω₀,
      Q k j (t, z) = (∑ i, (σ (t, z) * invGramOnEuclid (g t) α i j z) *
        dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) z) - E k j (t, z) := by
    have hf := ae_cutoff_gradient_flux_eq_density_ratio q g α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s
      hsub u v k (H k) hv (hH k) hη hηc j
    have hVeq := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [hf, hVeq] with t ht hVt
    have he := hVt.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [ht, he] with z hz hVz
    simpa only [← hVz] using hz
  have hexForm := exists_local_dirichlet_bilinear_form_family q (G := G) hG
    isCompact_Icc (htime.trans hreg) α hΩ₀ hΩ₀c hΩ₀s
  let form := Classical.choose hexForm
  have hform := (Classical.choose_spec hexForm).1
  have hexLm := exists_cutoff_forcing_dual q (G := G) hG isCompact_Icc
    (htime.trans hreg) α hΩ₀ hΩ₀c hΩ₀s hμ.le (V k) hV hη v ℓ form hform (Q k) (B k) (hQ k) hℓ hflux
  let Lm := Classical.choose hexLm
  have hβ := (Classical.choose_spec hexLm).1
  have hLm := (Classical.choose_spec hexLm).2
  have hpair (z : Lp (H1ComplDirichlet q) 2 μ) :
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, (ℓ + Lm) t (z t) ∂μ) -
        ∫ t, form t (v t) (z t) ∂μ := by
    rw [Lp.integral_add_apply, hLm]
    exact (add_sub_cancel_right _ _).symm
  let W : Lp ℝ 2 ν := hV.toLp (V k)
  have hW : W =ᵐ[ν] V k := hV.coeFn_toLp
  have hweak (j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H k j (t, z)) (fun z => W (t, z)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [hH k j, Measure.ae_ae_of_ae_prod hW, hc] with t ht hwt hct
    have he : (fun z => W (t, z)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  have hexSource := exists_lp_scalar_source_of_cutoff_pairing q (G := G) hG isCompact_Icc
    (htime.trans hreg) α hΩ₀ hΩ₀c hΩ₀s hμ.le hη hηs (hB k) hV (H k) hweak (ℓ + Lm) hβ
  let f' := Classical.choose hexSource
  have hf := Classical.choose_spec hexSource
  refine ⟨v, w', ℓ, ℓ + Lm, f', hv, hw, hd, hℓ, hβ, ?_, hf⟩
  intro z
  exact (hpair z).trans (congrArg
    (fun x => (∫ t, (ℓ + Lm) t (z t) ∂μ) - x)
    (integral_congr_ae (Filter.Eventually.of_forall fun t => hform t (v t) (z t))))

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
