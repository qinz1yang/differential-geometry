import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProductChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
  {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {subseq : ℕ → ℕ}
  {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [ConnectedSpace N] [SigmaCompactSpace N]

theorem eventually_exists_localNeck_of_pointed_product_limit
    (Phi : PointedRiemannianConvergenceMaps X L subseq) (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete L)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ L.M)
    (hemetric : Diffeomorph.pullbackMetricCross L.metric e = h.prod (euclideanMetric (E := ℝ)))
    {q A C1 C2 : ℝ} (hq : 0 < q) :
    ∀ᶠ k in atTop, ∀ x : (X.obj (subseq k)).M,
      riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint x ≤
        ENNReal.ofReal A →
      q ≤ metricScalarAt (X.obj (subseq k)).metric x →
      ∀ {epsc eps : ℝ} (W : SpatialCanonicalWitness (X.obj (subseq k)).metric epsc C1 C2 x),
        W.capTubeHasNeckChart eps → eps ≤ 1 / 1000 →
        ∃ neck : SpatialLocalNeck (X.obj (subseq k)).metric epsc x W.domain.carrier,
          W.alternative = SpatialCanonicalAlternative.neck neck := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  set r : ℝ := max A 0 + 2 * (max C1 0 / Real.sqrt q) with hrdef
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hr0 : 0 ≤ r := by positivity
  have hLC : RiemannianMetricComplete L.metric := ⟨hcomplete⟩
  have hconvLarge : metricSourceConvergesOn Phi
      (CanonicalMetricCompactness.canonicalSourceData Phi)
      (riemannianClosedBallOf L.metric L.basepoint (3 * r + 1)) 0 := by
    intro ε hε
    obtain ⟨k, hk⟩ := C.converges _ (hLC.closedEBall_isCompact L.basepoint (3 * r + 1)) 0 ε hε
    refine ⟨k, fun j hj => ?_⟩
    have hh := hk j hj
    rw [hcanonical j] at hh
    exact hh
  have hcapture := pointed_metric_eventually_inverse_ball_capture L.basepoint (r := r)
    (factor := 2) hr0 (by norm_num) (by linarith : 2 * r < 3 * r + 1)
    (hLC.closedEBall_isCompact L.basepoint (3 * r + 1)) hconvLarge
  let KL : Set L.M := riemannianClosedBallOf L.metric L.basepoint (2 * r)
  have hKL : IsCompact KL := hLC.closedEBall_isCompact L.basepoint (2 * r)
  let K : Set (N × ℝ) := e.symm '' KL
  have hK : IsCompact K := hKL.image e.symm.continuous
  let _ : LocallyCompactSpace H := J.locallyCompactSpace
  let _ : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H N
  obtain ⟨B, hB, hKB⟩ := exists_compact_superset hK
  let O : TopologicalSpace.Opens (N × ℝ) := ⟨interior B, isOpen_interior⟩
  let A' : Set O := (Subtype.val : O → N × ℝ) ⁻¹' K
  have hA' : IsCompact A' := by
    apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
    have heq : (Subtype.val : O → N × ℝ) '' A' = K := by
      rw [image_preimage_eq_of_subset]
      intro z hz
      exact ⟨⟨z, hKB hz⟩, rfl⟩
    rwa [heq]
  set C2' : ℝ := max C2 1 with hC2'def
  have hC2' : 0 < C2' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let η : ℝ := min (1 / 8) (q / (23040 * C2'))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηquarter : η ≤ 1 / 4 := (min_le_left _ _).trans (by norm_num)
  obtain ⟨kclose, hclose⟩ := pointedMaps_eventually_fixedDomain_metric_close Phi C hcanonical
    e O B hB interior_subset A' hA' 2 η hη
  filter_upwards [hcapture, eventually_ge_atTop kclose] with k hkc hk
  intro x hxA hqx epsc eps W hW heps
  obtain ⟨f, hf, hfval, hfclose⟩ := hclose k hk
  have hfdim : Module.finrank ℝ (F × ℝ) = Module.finrank ℝ ThreeSpace := by
    simp only [Module.finrank_prod, hdim, Module.finrank_self]
    simp [ThreeSpace]
  obtain ⟨V, Ψ, hV, hΨ, _, hmetric⟩ :=
    exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric (X.obj (subseq k)).metric
      hf.isImmersion hf.isEmbedding.injective hfdim
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hC2eq : C2' = C2 := max_eq_left hC2
  have hRx := W.Q_pos
  have hsqx : 0 < Real.sqrt (metricScalarAt (X.obj (subseq k)).metric x) := Real.sqrt_pos.mpr hRx
  have hC1 : 1 ≤ C1 := by
    have h := W.radius_lower.trans W.radius_upper
    rw [inv_eq_one_div, div_le_div_iff_of_pos_right hsqx] at h
    exact h
  have hrad : 2 * W.radius ≤ 2 * (max C1 0 / Real.sqrt q) := by
    have h1 : C1 / Real.sqrt (metricScalarAt (X.obj (subseq k)).metric x) ≤ C1 / Real.sqrt q :=
      div_le_div_of_nonneg_left (by linarith) hsq (Real.sqrt_le_sqrt hqx)
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ C1)]
    linarith [W.radius_upper]
  have hbp : Phi.map k L.basepoint = (X.obj (subseq k)).basepoint := Phi.basepoint_map k
  have hdom : ∀ w ∈ W.domain.carrier, w ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
      (Phi.map k L.basepoint) r := by
    intro w hw
    change riemannianEDistOf (X.obj (subseq k)).metric (Phi.map k L.basepoint) w ≤ ENNReal.ofReal r
    rw [hbp]
    have hxw : riemannianEDistOf (X.obj (subseq k)).metric x w < ENNReal.ofReal (2 * W.radius) :=
      W.inside_ball hw
    refine (riemannianEDistOf_triangle _ _ x w).trans ?_
    rw [hrdef, ENNReal.ofReal_add (le_max_right _ _) (by positivity)]
    exact add_le_add (hxA.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      (hxw.le.trans (ENNReal.ofReal_le_ofReal hrad))
  have hpre : ∀ w ∈ W.domain.carrier, ∃ o : O, o.val ∈ K ∧ f o = w := by
    intro w hw
    obtain ⟨_, _, hinball, hright⟩ := hkc.2 w (hdom w hw)
    have hpK : e.symm ((Phi.partialDiffeomorph k).symm w) ∈ K := ⟨_, hinball, rfl⟩
    refine ⟨⟨_, hKB hpK⟩, hpK, ?_⟩
    rw [hfval]
    change Phi.map k (e (e.symm ((Phi.partialDiffeomorph k).symm w))) = w
    rw [e.apply_symm_apply]
    exact hright
  have hcapV : W.domain.carrier ⊆ V := by
    intro w hw
    rw [hV]
    obtain ⟨o, _, ho⟩ := hpre w hw
    exact ⟨o, ho⟩
  have hpreA : ∀ z : V, z.val ∈ W.domain.carrier → Ψ.symm z ∈ A' := by
    intro z hz
    obtain ⟨o, hoK, ho⟩ := hpre z.val hz
    have hoz : Ψ o = z := Subtype.ext ((hΨ o).trans ho)
    rw [← hoz, Ψ.symm_apply_apply]
    exact hoK
  have hsmall : 720 * η < C2⁻¹ * metricScalarAt (X.obj (subseq k)).metric x / 16 := by
    have h1 : 720 * η ≤ C2⁻¹ * q / 32 := by
      have hm : η ≤ q / (23040 * C2') := min_le_right _ _
      rw [hC2eq] at hm
      have heq : 720 * (q / (23040 * C2)) = C2⁻¹ * q / 32 := by
        field_simp
        ring
      linarith
    have hpos : 0 < C2⁻¹ * q := mul_pos (inv_pos.mpr (by linarith)) hq
    have h2 : C2⁻¹ * q ≤ C2⁻¹ * metricScalarAt (X.obj (subseq k)).metric x :=
      mul_le_mul_of_nonneg_left hqx (inv_nonneg.mpr (by linarith))
    linarith
  exact W.exists_localNeck_of_product_chart hW heps h hdim O V Ψ hcapV hηquarter hsmall (by
    intro z hz m hm
    rw [hmetric, ← hemetric]
    exact ((derivNorm_le_sup hA' hm _ _ _ (hpreA z hz)).trans_lt hfclose).le)

theorem SpatialCanonicalWitness.exists_neck_of_scaleMetric {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 c : ℝ} {x : M} (hc : 0 < c)
    (W : SpatialCanonicalWitness g eps C1 C2 x)
    (h : ∃ neck : SpatialLocalNeck (DifferentialGeometry.scaleMetric c hc g) eps x
      (W.scaleMetric c hc).domain.carrier,
      (W.scaleMetric c hc).alternative = SpatialCanonicalAlternative.neck neck) :
    ∃ neck : SpatialLocalNeck g eps x W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck := by
  obtain ⟨n, hn⟩ := h
  change W.alternative.scaleMetric c hc = _ at hn
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | cap data deep =>
    rw [halt] at hn
    cases hn
  | positive whole data sec =>
    rw [halt] at hn
    cases hn
  | round whole data =>
    rw [halt] at hn
    cases hn

theorem eventually_exists_localNeck_of_scaled_pointed_product_limit
    (Phi : PointedRiemannianConvergenceMaps X L subseq) (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete L)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ L.M)
    (hemetric : Diffeomorph.pullbackMetricCross L.metric e = h.prod (euclideanMetric (E := ℝ)))
    (g : ∀ k, SmoothRiemannianMetric I3 (X.obj k).M) {c : ℕ → ℝ} (hc : ∀ k, 0 < c k)
    (hX : ∀ k, (X.obj k).metric = DifferentialGeometry.scaleMetric (c k) (hc k) (g k))
    {q A C1 C2 : ℝ} (hq : 0 < q) :
    ∀ᶠ k in atTop, ∀ x : (X.obj (subseq k)).M,
      riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint x ≤
        ENNReal.ofReal A →
      q ≤ metricScalarAt (X.obj (subseq k)).metric x →
      ∀ {epsc eps : ℝ} (W : SpatialCanonicalWitness (g (subseq k)) epsc C1 C2 x),
        W.capTubeHasNeckChart eps → eps ≤ 1 / 1000 →
        ∃ neck : SpatialLocalNeck (g (subseq k)) epsc x W.domain.carrier,
          W.alternative = SpatialCanonicalAlternative.neck neck := by
  filter_upwards [eventually_exists_localNeck_of_pointed_product_limit (C1 := C1) (C2 := C2)
    Phi C hcanonical hcomplete h hdim e hemetric (A := A) hq] with k hk
  intro x hxA hqx epsc eps W hW heps
  rw [hX (subseq k)] at hk hxA hqx
  exact W.exists_neck_of_scaleMetric (hc (subseq k))
    (hk x hxA hqx (W.scaleMetric (c (subseq k)) (hc (subseq k)))
      (hW.scaleMetric (c (subseq k)) (hc (subseq k))) heps)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
