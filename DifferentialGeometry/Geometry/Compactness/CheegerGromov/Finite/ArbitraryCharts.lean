import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CheegerGromovLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartPullback

/-!
# LFR14 consumer adapter (e): metric convergence in arbitrary charts

The external review of the LFR14 design (`build-logs/inbox/review-lfr14.md` §2 on LFR18, LFR26,
LFR28; item 5(e) of the dispositions): T0 states the `C^{K-1}` convergence `jᵢ^* gᵢ → G` only in
the extended charts `extChartAt x` of the carrier `N`; the consumers (e.g. LFR18 at A:26261 with the
product charts of `ℝ × Z`) need it in ANY fixed `C^K` chart. This is I-CHART applied with the
roles of T0's transfer reversed.

* `mapCPConvergenceOn_pullback_of_extChart_convergence`: from convergence in every extended chart,
  convergence on every compact subset of the source of an arbitrary `C^K` chart parametrization
  `ψ : E → N` to the `ψ`-coefficients `ψ^* G` of the limit metric. The pieces are compact subsets
  of the OPEN overlaps `ψ.source ∩ ψ⁻¹(chart source at y ∩ B(y,1))`; on such an overlap the
  coordinate change `τ = extChartAt y ∘ ψ` is `C^K` into the open set
  `target ∩ chart⁻¹⁻¹ B(y,1)`, the common regularity tail comes from the compact `B̄(y,1)`, I-CHART
  (`mapCPConvergenceOn_pullbackMetricCoefficients_comp`) applies, and both identities (the maps
  and the limit coefficients, by the chain rule) hold on the open overlap.
* `exists_finite_cheeger_gromov_limit_in_charts`: T0 together with this arbitrary-chart clause.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

universe u

/-- **Metric convergence in an arbitrary chart.** Let `N` be proper, `G` a `C^{K-1}` metric, and
`j i : N → Y i` partial diffeomorphisms of order `K ≥ 1` whose sources eventually contain every
compact set, with `C^{K-1}` convergence of `j i^* g i` to `chartCoeff G x` on the compact subsets
of every extended chart target. Then for every `C^K` chart parametrization `ψ : E → N` the
pulled-back coefficients along `j i ∘ ψ` converge in `C^{K-1}` on every compact subset of
`ψ.source` to the `ψ`-coefficients of `G`. -/
theorem mapCPConvergenceOn_pullback_of_extChart_convergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N]
    [IsManifold 𝓘(ℝ, E) ∞ N] {K : ℕ} (hK : 1 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → Y i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K) {L : Set E} (hL : IsCompact L)
    (hLψ : L ⊆ ψ.source) :
    MapCPConvergenceOn L (K - 1)
      (fun i => pullbackMetricCoefficients (g i) ((j i : N → Y i) ∘ ψ))
      (fun u => (G.inner (ψ u) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ u : E →L[ℝ] E)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ u : E →L[ℝ] E)) := by
  have hKK : K - 1 + 1 = K := by omega
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  -- the open overlaps
  let U : N → Set E := fun y =>
    ψ.source ∩ ψ ⁻¹' ((extChartAt 𝓘(ℝ, E) y).source ∩ ball y 1)
  have hUo : ∀ y, IsOpen (U y) := fun y =>
    ψ.toOpenPartialHomeomorph.isOpen_inter_preimage
      ((isOpen_extChartAt_source y).inter isOpen_ball)
  refine GC.MetricGeometry.mapCPConvergenceOn_of_isCompact_subset_sUnion (S := range U)
    (by rintro _ ⟨y, rfl⟩; exact hUo y) ?_ hL ?_
  · rintro _ ⟨y, rfl⟩ Q hQ hQU
    set c := extChartAt 𝓘(ℝ, E) y with hc
    let τ : E → E := c ∘ ψ
    let V : Set E := c.target ∩ c.symm ⁻¹' ball y 1
    have hVo : IsOpen V :=
      (continuousOn_extChartAt_symm y).isOpen_inter_preimage (isOpen_extChartAt_target y)
        isOpen_ball
    -- the coordinate change is `C^K` on the open overlap
    have hτK : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K τ (U y) := by
      refine ((contMDiffOn_extChartAt (x := y)).of_le hKle).comp
        (ψ.contMDiffOn.mono inter_subset_left) ?_
      intro u hu
      have h1 : ψ u ∈ c.source := hu.2.1
      rwa [hc, extChartAt_source] at h1
    have hτ : ContDiffOn ℝ (K - 1 + 1 : ℕ) τ (U y) := by
      rw [hKK]
      exact contMDiffOn_iff_contDiffOn.mp hτK
    have hτUV : MapsTo τ (U y) V := by
      intro u hu
      have hψu : ψ u ∈ c.source := hu.2.1
      refine ⟨c.map_source hψu, ?_⟩
      change c.symm (c (ψ u)) ∈ ball y 1
      rw [c.left_inv hψu]
      exact hu.2.2
    -- the common regularity tail, from the compact `closedBall y 1`
    have hf : ∀ᶠ i in atTop,
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (K - 1 + 1 : ℕ) ((j i : N → Y i) ∘ c.symm) V := by
      filter_upwards [hexh _ (isCompact_closedBall y 1)] with i hi
      rw [hKK]
      exact (j i).contMDiffOn.comp
        (((contMDiffOn_extChartAt_symm y).of_le hKle).mono inter_subset_left)
        (fun v hv => hi (ball_subset_closedBall hv.2))
    have hcK : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ((K : ℕ) : ℕ∞ω) c.symm V :=
      ((contMDiffOn_extChartAt_symm y).of_le hKle).mono inter_subset_left
    have hB : ContDiffOn ℝ (K - 1 : ℕ) (chartCoeff G y) V :=
      Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner G
        (r := ((K - 1 : ℕ) : ℕ∞ω)) (s := ((K : ℕ) : ℕ∞ω)) le_rfl
        (by exact_mod_cast hKK.le) hVo hcK
    have hmain := mapCPConvergenceOn_pullbackMetricCoefficients_comp g
      (fun i => (j i : N → Y i) ∘ c.symm) τ (hUo y) hVo hτ hτUV hf (chartCoeff G y) hB
      (fun S hS hSV => hconv y S hS (hSV.trans inter_subset_left)) hQ hQU
    refine hmain.congr (hUo y) hQU (fun i u hu => ?_) ?_
    · -- the maps agree near every point of the open overlap
      have hgerm : ((j i : N → Y i) ∘ ψ) =ᶠ[𝓝 u] (((j i : N → Y i) ∘ c.symm) ∘ τ) := by
        filter_upwards [(hUo y).mem_nhds hu] with v hv
        change j i (ψ v) = j i (c.symm (c (ψ v)))
        rw [c.left_inv hv.2.1]
      exact pullbackMetricCoefficients_eq_of_eventuallyEq (g i) hgerm
    · -- the limit coefficients agree on the open overlap (chain rule)
      intro u hu
      have hψu : ψ u ∈ c.source := hu.2.1
      have hτu : τ u ∈ c.target := c.map_source hψu
      have hcτ : c.symm (τ u) = ψ u := c.left_inv hψu
      have hgerm : (ψ : E → N) =ᶠ[𝓝 u] c.symm ∘ τ := by
        filter_upwards [(hUo y).mem_nhds hu] with v hv
        exact (c.left_inv hv.2.1).symm
      have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (τ u) :=
        ((contMDiffOn_extChartAt_symm (n := 1) y).contMDiffAt
          ((isOpen_extChartAt_target y).mem_nhds hτu)).mdifferentiableAt one_ne_zero
      have hτd : DifferentiableAt ℝ τ u :=
        (hτ.differentiableOn (by simp) u hu).differentiableAt ((hUo y).mem_nhds hu)
      have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ u =
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (τ u)).comp (fderiv ℝ τ u) := by
        rw [hgerm.mfderiv_eq, mfderiv_comp u hcd hτd.mdifferentiableAt, mfderiv_eq_fderiv]
        rfl
      have key : ∀ z z' : N, z = z' → ∀ v w : E, G.inner z v w = G.inner z' v w := by
        rintro z _ rfl v w
        rfl
      ext v w
      change G.inner (ψ u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ u v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ u w) =
        chartCoeff G y (τ u) (fderiv ℝ τ u v) (fderiv ℝ τ u w)
      rw [chartCoeff_apply, hd]
      exact key _ _ hcτ.symm _ _
  · intro u hu
    exact ⟨U (ψ u), ⟨ψ u, rfl⟩, hLψ hu, mem_extChartAt_source (ψ u), mem_ball_self one_pos⟩

/-- **LFR14 with convergence in arbitrary charts (T0 + (c3′)).** The package of
`exists_finite_cheeger_gromov_limit`, and for every `C^K` chart parametrization
`ψ : ℝⁿ → N` the coefficients of `j i^* g (φ i)` in `ψ` converge in `C^{K-1}` on the compact
subsets of `ψ.source` to the coefficients of `G` in `ψ`. -/
theorem exists_finite_cheeger_gromov_limit_in_charts
    (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        ∀ (ψ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin n)) N K) (L : Set (EuclideanSpace ℝ (Fin n))),
          IsCompact L → L ⊆ ψ.source →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i)) ((j i : N → X (φ i)) ∘ ψ))
            (fun u => (G.inner (ψ u) : EuclideanSpace ℝ (Fin n) →L[ℝ]
                EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).bilinearComp
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ψ u :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ψ u :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov⟩ := exists_finite_cheeger_gromov_limit n K hn hK hr hv A hA g hmetric p hvol hcurv
  let := mN
  let := cN
  have := hMN
  have := hprop
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov,
    fun ψ L hL hLψ => mapCPConvergenceOn_pullback_of_extChart_convergence hK G
      (fun i => g (φ i)) j hexh hconv ψ hL hLψ⟩

end DifferentialGeometry.CheegerGromovCompactness
