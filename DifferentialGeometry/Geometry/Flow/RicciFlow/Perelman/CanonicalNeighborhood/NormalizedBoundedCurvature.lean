import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedConeExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedNeckSequence

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_boundedAtDistance {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X := by
  obtain ⟨epsEnd, c, hepsEnd, _, hend⟩ :=
    exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence.{u}
      hkappa (A := 0) le_rfl (alpha := 1 / 4000000) (by norm_num) (by norm_num)
  obtain ⟨epsCone, hepsCone, hcone⟩ := normalized_end_cone_exclusion.{u} hkappa
  refine ⟨min epsEnd epsCone, lt_min hepsEnd hepsCone, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  by_contra hnot
  obtain ⟨f, hf, F, r, _, _, L, hL, hrest⟩ :=
    hend eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X hnot
  clear hend
  let _ : PathConnectedSpace L.M := hL
  obtain ⟨maps, C, hcanonical, _, hmetrics, _, _, _, hrest⟩ := hrest
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  obtain ⟨phi, γ, s, g, _, _, _, _, _, _, hblow, q, _, _, _, _, _,
    t, nk, htstrict, htend, _, _, _, _, eta, Ψ, hann, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, E, theta, _, _, _, _, D, _, hrest⟩ := hrest
  let W : TopologicalSpace.Opens L.M :=
    ⟨interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)), isOpen_interior⟩
  obtain ⟨gW, hgW, _, _, hW, hrest⟩ := hrest
  let _ : PathConnectedSpace W := hW
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, hqW, hdistW, _, _, _, _, _, _, _, hquantW, _, hupper,
    delta, hdelta, hcompact, hcover, happrox, _, _⟩ := hrest
  let u : ℕ → Ico (t 2 : ℝ) F.radius := fun n =>
    ⟨t (n + 2), htstrict.monotone (by omega), (t (n + 2)).property.2⟩
  let x : ℕ → W := fun n => gW (u n)
  have hux : ∀ n, (x n : L.M) = g (t (n + 2)) := fun n => hgW (u n)
  have hu : Tendsto u atTop
      (comap (Subtype.val : Ico (t 2 : ℝ) F.radius → ℝ) (𝓝 F.radius)) := by
    apply tendsto_comap_iff.mpr
    exact htend.comp (tendsto_add_atTop_nat 2)
  have hx : Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) :=
    hqW.comp hu
  have hQ : Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) atTop atTop := by
    simp only [hux]
    exact hblow.comp (tendsto_comap_iff.mpr (htend.comp (tendsto_add_atTop_nat 2)))
  have hxdist (n : ℕ) : dist (x n : UniformSpace.Completion W) qW =
      F.radius - (t (n + 2) : ℝ) := by
    rw [dist_comm]
    exact hdistW (u n)
  have hlower : ∀ᶠ n in atTop, 196 < metricScalarAt L.metric (x n : L.M) *
      dist (x n : UniformSpace.Completion W) qW ^ 2 := by
    apply Eventually.of_forall
    intro n
    have hmem : (x n : L.M) ∈ Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [hux]
      refine ⟨((nk (n + 2)).center, 0), ⟨mem_univ _, le_rfl, zero_le_one⟩, ?_⟩
      exact ((hann (n + 2)).2.1 _).trans (nk (n + 2)).center_eq
    have hquant := hquantW n (x n) hmem
    rw [metricScalarAt_restrictOpen, dist_comm qW] at hquant
    exact lt_of_lt_of_le (by norm_num) hquant
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt L.metric (x n : L.M) *
      dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupper
    refine ⟨B, ?_⟩
    simpa only [hux, hxdist] using hB
  exact hcone eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X f hf L maps
    C.metrics hcanonical hmetrics W hW qW delta hdelta hcompact hcover x hx hQ hlower hupper' happrox

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
