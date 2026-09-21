import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingLensAngle
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff
namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem eventually_lt_comparisonAngle_of_compact_distance_lenses
    {M : Type*} [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K)
    (y p z : M) (u v : ℕ → M) (c : ℕ → ℝ) {r θ θ' : ℝ} (hr : 0 < r)
    (hmem : ∀ᶠ i in atTop, u i ∈ K ∧ v i ∈ K)
    (hyu : Tendsto (fun i => dist y (u i)) atTop (𝓝 r))
    (hyv : Tendsto (fun i => dist y (v i)) atTop (𝓝 r))
    (hup : Tendsto (fun i => dist (u i) p) atTop (𝓝 (dist y p - r)))
    (hvz : Tendsto (fun i => dist (v i) z) atTop (𝓝 (dist y z - r)))
    (hc : Tendsto (fun i => c i - dist (u i) (v i)) atTop (𝓝 0))
    (hcompare : ∀ q ∈ K, ∀ w ∈ K,
      dist y q = r → dist y w = r →
      dist q p = dist y p - r → dist w z = dist y z - r →
      θ ≤ comparisonAngle r r (dist q w))
    (hθ : θ' < θ) :
    ∀ᶠ i in atTop, θ' < comparisonAngle r r (c i) := by
  by_contra h
  have hbad : ∃ᶠ i in atTop, comparisonAngle r r (c i) ≤ θ' := by
    simpa only [not_eventually, not_lt] using h
  obtain ⟨ψ, hψ, hψbad⟩ := extraction_of_frequently_atTop hbad
  have hpair : ∀ᶠ i in atTop, (u (ψ i), v (ψ i)) ∈ K ×ˢ K :=
    hψ.tendsto_atTop.eventually hmem
  obtain ⟨qw, hqw, φ, hφ, hlim⟩ := (hK.prod hK).tendsto_subseq' hpair.frequently
  let χ := ψ ∘ φ
  have hχ : Tendsto χ atTop atTop := hψ.tendsto_atTop.comp hφ.tendsto_atTop
  have hu : Tendsto (u ∘ χ) atTop (𝓝 qw.1) :=
    (continuous_fst.tendsto qw).comp hlim
  have hv : Tendsto (v ∘ χ) atTop (𝓝 qw.2) :=
    (continuous_snd.tendsto qw).comp hlim
  have hyq : dist y qw.1 = r :=
    tendsto_nhds_unique (tendsto_const_nhds.dist hu) (hyu.comp hχ)
  have hyw : dist y qw.2 = r :=
    tendsto_nhds_unique (tendsto_const_nhds.dist hv) (hyv.comp hχ)
  have hqp : dist qw.1 p = dist y p - r :=
    tendsto_nhds_unique (hu.dist tendsto_const_nhds) (hup.comp hχ)
  have hwz : dist qw.2 z = dist y z - r :=
    tendsto_nhds_unique (hv.dist tendsto_const_nhds) (hvz.comp hχ)
  have hcχ : Tendsto (c ∘ χ) atTop (𝓝 (dist qw.1 qw.2)) := by
    have hh := (hc.comp hχ).add (hu.dist hv)
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh
  have hangle := tendsto_comparisonAngle tendsto_const_nhds tendsto_const_nhds hcχ hr hr
  have hle : comparisonAngle r r (dist qw.1 qw.2) ≤ θ' := by
    apply le_of_tendsto hangle
    exact Eventually.of_forall fun i => hψbad (φ i)
  exact (not_lt_of_ge ((hcompare qw.1 hqw.1 qw.2 hqw.2 hyq hyw hqp hwz).trans hle)) hθ


theorem eventually_lt_comparisonAngle_of_compact_riemannian_distance_lenses
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace M]
    [IsManifold DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.I3 ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.I3 M)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g)
    {K : Set M} (hK : IsCompact K)
    (y p z : M) (u v : ℕ → M) (c : ℕ → ℝ) {r θ : ℝ} (hr : 0 < r)
    (hrp : r < (riemannianEDistOf g y p).toReal)
    (hrz : r < (riemannianEDistOf g y z).toReal)
    (hmem : ∀ᶠ i in atTop, u i ∈ K ∧ v i ∈ K)
    (hyu : Tendsto (fun i => (riemannianEDistOf g y (u i)).toReal) atTop (𝓝 r))
    (hyv : Tendsto (fun i => (riemannianEDistOf g y (v i)).toReal) atTop (𝓝 r))
    (hup : Tendsto (fun i => (riemannianEDistOf g (u i) p).toReal)
      atTop (𝓝 ((riemannianEDistOf g y p).toReal - r)))
    (hvz : Tendsto (fun i => (riemannianEDistOf g (v i) z).toReal)
      atTop (𝓝 ((riemannianEDistOf g y z).toReal - r)))
    (hc : Tendsto (fun i => c i - (riemannianEDistOf g (u i) (v i)).toReal) atTop (𝓝 0))
    (hθ : θ < comparisonAngle (riemannianEDistOf g y p).toReal
      (riemannianEDistOf g y z).toReal (riemannianEDistOf g p z).toReal) :
    ∀ᶠ i in atTop, θ < comparisonAngle r r (c i) := by
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.I3 M
  let : RegularSpace M := inferInstance
  let : PseudoMetricSpace M := g.toPseudoMetricSpace
  exact eventually_lt_comparisonAngle_of_compact_distance_lenses hK y p z u v c hr
    hmem hyu hyv hup hvz hc (fun q _ w _ hq hw hqp hwz =>
      DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_le_of_equal_radius_minimizing_lenses
        g hcomplete hsec y p z q w hr hrp hrz hq hw hqp hwz) hθ

end DifferentialGeometry.Geometry.Comparison.Toponogov
