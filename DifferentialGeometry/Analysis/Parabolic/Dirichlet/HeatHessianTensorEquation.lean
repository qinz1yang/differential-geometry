import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatHessianEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffMetricEquation

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

theorem exists_lp_cutoff_hessian_tensor_identity_of_heat_timeH1
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
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a ≤ b)
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
      (∀ i j k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun z => K i j k (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
      (∀ k i l, K k i l = K k l i) ∧
      (∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k l p * φ p ∂ν) ∧
      let C := fun k l p => (r p)⁻¹ * S k l p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * H k l p)
      let Q := fun k l j p => ∑ i, (η p.2 / r p) * A i j p * K k l i p
      let B := fun k l p => η p.2 * C k l p -
        ∑ i, ∑ j, A i j p * K k l i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      (∀ k l j, MemLp (Q k l j) 2 ν) ∧ (∀ k l, MemLp (B k l) 2 ν) ∧
      (∀ k l, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∀ τ : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t v ∂μ) =
            (∫ p, τ p.1 * B k l p * H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k l j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j v p.2 ∂ν) ∧
      ∀ k l (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo a b →
        let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (∫ p, deriv τ p.1 * (η p.2 * (σ p * H k l p)) * ψ p.2 ∂ν) =
          (∑ j, ∫ p, τ p.1 * Q k l j p *
            fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
          ∫ p, τ p.1 * B k l p * ψ p.2 ∂ν := by
  intro F Df hDf μ ν ρ σ r A DDf hDDf
  obtain ⟨H, K, S, hH, hHsym, hK, hKsym, hS⟩ :=
    exists_lp_weak_hessian_equation_of_heat_timeH1
      hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
      hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf DDf hDDf
  refine ⟨H, K, S, hH, hHsym, hK, hKsym, hS, ?_⟩
  intro C Q B
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hcore (k l) := exists_lp_dual_of_cutoff_metric_divergence_equation
    hG q α hΩ (subset_closure.trans hΩs) hΩ₀ hΩ₀c hΩ₀Ω
    ((Icc_subset_Icc ha.le hb.le).trans hreg) hη hηs
    (Lp.memLp (H k l)) (Lp.memLp (S k l))
    (fun i => Lp.memLp (K k l i)) (hS k l)
  exact ⟨fun k l => (hcore k l).1, fun k l => (hcore k l).2.1,
    fun k l => (hcore k l).2.2.1, fun k l => (hcore k l).2.2.2⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
