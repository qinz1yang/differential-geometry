import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatHessianTimeEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffScalarSource
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartFlux

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem exists_timeH1_cutoff_hessian_scalar_source_of_heat_timeH1
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
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω₀) :
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω) →
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let σ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω₀) →
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ S : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i j, H i j = H j i) ∧
      (∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
        (fun z => K i j l (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
      (∀ k i l, K k i l = K k l i) ∧
      (∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k l p * φ p ∂ν) ∧
      let C := fun k l p => (r p)⁻¹ * S k l p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * H k l p)
      let B := fun k l p => η p.2 * C k l p -
        ∑ i, ∑ j, A i j p * K k l i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      let P := fun i j (p : ℝ × EuStd) =>
        (σ p * invGramOnEuclid (g p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      ∃ v : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp (H1ComplDirichlet q) 2 μ,
        (∀ k l, ∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v k l t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            Sobolev.Chart.chartPullback I_hs α (fun z => η z * H k l (t, z))) ∧
        ∀ k l, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
          ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          ∃ f : Lp ℝ 2 ν,
            (∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
              w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v k l (a + s)))
                (H1ComplDirichletToLp q z)) ∧
            w.deriv =ᵐ[timeMeasure (b - a)] (fun s => ℓ (a + s)) ∧
            (∀ z : Lp (H1ComplDirichlet q) 2 μ,
              (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
                ∫ t, (∑ i, ∑ j, ∫ y in Ω₀,
                  dirichletLocalWeakPartialLp q α hΩ₀
                    (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                    (hΩ₀Ω.trans (subset_closure.trans hΩs)) i (v k l t) y *
                    (densityOnEuclid q α y *
                      invGramOnEuclid (g t) α i j y) *
                    dirichletLocalWeakPartialLp q α hΩ₀
                      (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                      (hΩ₀Ω.trans (subset_closure.trans hΩs)) j (z t) y) ∂μ) ∧
            (f =ᵐ[ν] fun p => B k l p - ∑ i, ∑ j,
              (P i j p * K k l j p +
                fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * H k l p)) ∧
            (∀ z : Lp (H1ComplDirichlet q) 2 μ,
              (∫ t, β t (z t) ∂μ) =
                ∫ t, (∫ x in Ω₀, f (t, x) * H1ComplDirichletToLp q (z t)
                  ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ) := by
  intro F Df hDf μ ν ρ σ r A DDf hDDf
  classical
  have hex := exists_timeH1_cutoff_hessian_dual_deriv_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv hη hηs Df hDf DDf hDDf
  let H := hex.choose
  let K := hex.choose_spec.choose
  let S := hex.choose_spec.choose_spec.choose
  have hp := hex.choose_spec.choose_spec.choose_spec
  have hH := hp.1
  have hHsym := hp.2.1
  have hK := hp.2.2.1
  have hKsym := hp.2.2.2.1
  have hS := hp.2.2.2.2.1
  have hsource := hp.2.2.2.2.2
  refine ⟨H, K, S, hH, hHsym, hK, hKsym, hS, ?_⟩
  intro C B P
  let Q := fun k l j p => ∑ i, (η p.2 / r p) * A i j p * K k l i p
  have hQ := hsource.1
  have hB := hsource.2.1
  let v := hsource.2.2.choose
  have hv := hsource.2.2.choose_spec.1
  have htime := hsource.2.2.choose_spec.2
  refine ⟨v, hv, ?_⟩
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  intro k l
  let ℓ := (htime k l).choose
  let w := (htime k l).choose_spec.choose
  have htime' := (htime k l).choose_spec.choose_spec
  have hℓ := htime'.1
  have hw := htime'.2.1
  have hd := htime'.2.2.1
  have hflux := ae_cutoff_flux_eq_density_ratio q g α hΩ₀ hΩ₀c hΩ₀s
    (H k l) (fun j p => K k l j p) (Lp.memLp (H k l)) (fun j => Lp.memLp (K k l j))
    (fun t => v k l t) (hv k l) (hK k l) hη
  obtain ⟨β, f, _, hpair, hf, hfsource⟩ := exists_lp_scalar_source_of_cutoff_flux q hG
    isCompact_Icc hreg α hΩ₀ hΩ₀c hΩ₀s (μ := μ) Measure.restrict_le_self
    (H k l) (K k l) (v k l) ℓ hη hηs (hK k l) (Q k l) (B k l)
    (hQ k l) (hB k l) hℓ hflux
  exact ⟨ℓ, w, β, f, hw, hd, hpair, hf, hfsource⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
