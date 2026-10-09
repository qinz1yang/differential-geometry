import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientBounds
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

theorem exists_lp_divergence_localWeakPartial_of_hasWeakPartialDeriv
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {J : Set ℝ} (hJc : IsCompact J) (hreg : J ⊆ D.regular)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (hμ : ∀ᵐ t ∂μ, t ∈ J)
    (q : SmoothRiemannianMetric I_hs M) (u : Lp (H1ComplDirichlet q) 2 μ)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hsub : Ω₀ ⊆ Ω) (S : Set ℝ)
    (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((μ.restrict S).prod (volume.restrict Ω₀)))
    (hH : ∀ i j, ∀ᵐ t ∂μ.restrict S, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) :
    let A := fun i j (p : ℝ × EuStd) =>
      Laplacian.MetricExtension.weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i u
    ∃ F : Lp ℝ 2 ((μ.restrict S).prod (volume.restrict Ω₀)),
      (F =ᵐ[(μ.restrict S).prod (volume.restrict Ω₀)] fun p => ∑ i, ∑ j,
        (A i j p * H i j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V i p)) ∧
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, F p * φ p ∂(μ.restrict S).prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1)
              ∂(μ.restrict S).prod (volume.restrict Ω₀) := by
  intro A V
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hmeasure : (μ.restrict S).prod (volume.restrict Ω₀) ≤ μ.prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 ((μ.restrict S).prod (volume.restrict Ω₀)) :=
    (Lp.memLp (V i)).mono_measure hmeasure
  let W := fun i => (hV i).toLp (V i)
  have hW (i) : W i =ᵐ[(μ.restrict S).prod (volume.restrict Ω₀)] V i := (hV i).coeFn_toLp
  have hrestrict : μ.restrict J = μ := Measure.restrict_eq_self_of_ae_mem hμ
  have hA (i j) : MemLp (A i j) ∞ ((μ.restrict S).prod (volume.restrict Ω₀)) := by
    have hb := Laplacian.MetricExtension.weightedInvGramOnEuclid_family_memLp_top (G := G)
      hG hJc hreg α hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) i j
      (μ.prod volume)
    rw [← Measure.prod_restrict, hrestrict] at hb
    exact hb.mono_measure hmeasure
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ ((μ.restrict S).prod (volume.restrict Ω₀)) := by
    have hb := Laplacian.MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top
      (G := G) hG hJc hreg α hΩ.measurableSet hΩc hΩs i j j (μ.prod volume)
    rw [← Measure.prod_restrict, hrestrict] at hb
    exact hb.mono_measure hmeasure
  have hAsmooth (i j) : ∀ᵐ t ∂μ.restrict S,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω₀ :=
    Eventually.of_forall fun t =>
      (Laplacian.MetricExtension.weightedInvGramOnEuclid_contDiffOn (g t) α i j).mono
        (hsub.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hweak (i j) : ∀ᵐ t ∂μ.restrict S, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => W i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := S)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i u)
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hW i), hc] with t ht hwt hct
    have he : (fun x => W i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  obtain ⟨F, hFval, hF⟩ := Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
    (by norm_num) hΩ₀ W H hA hDA hAsmooth hweak
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [hFval, ae_all_iff.mpr hW] with p hp hWp
    simpa only [hWp] using hp
  · intro φ hφ hφc hφs
    rw [hF φ hφ hφc hφs]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hW i] with p hp
    rw [hp]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
