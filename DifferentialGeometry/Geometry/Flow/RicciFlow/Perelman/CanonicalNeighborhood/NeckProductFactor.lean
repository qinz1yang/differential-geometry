import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Neck.ProductCapExclusion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
  {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {subseq : ℕ → ℕ}
  {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [ConnectedSpace N]

private theorem nonempty_diffeomorph_sphere_of_pointed_product_limit_of_scalar_lower_bound
    (Phi : PointedRiemannianConvergenceMaps X L subseq) (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete L)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ L.M)
    (hemetric : Diffeomorph.pullbackMetricCross L.metric e = h.prod (euclideanMetric (E := ℝ)))
    (z : L.M) {q : ℝ} (hq : 0 < q)
    (hneck : ∀ᶠ k in atTop, ∃ eps : ℝ, eps ≤ 1 / 1000 ∧
      Nonempty (SpatialNeck (X.obj (subseq k)).metric eps (Phi.map k z)))
    (hscalar : ∀ᶠ k in atTop, q ≤ metricScalarAt (X.obj (subseq k)).metric (Phi.map k z)) :
    Nonempty (N ≃ₘ⟮J, (𝓡 2)⟯ Sphere 2) := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let proj : L.M → N := fun x => (e.symm x).1
  have hproj : Function.Surjective proj := fun y => ⟨e (y, 0), by simp [proj]⟩
  let _ : SigmaCompactSpace N := isSigmaCompact_univ_iff.mp (by
    rw [← hproj.range_eq]
    exact isSigmaCompact_range (continuous_fst.comp e.symm.continuous))
  let R : ℝ := 7 / Real.sqrt q
  have hR : 0 < R := div_pos (by norm_num) (Real.sqrt_pos.mpr hq)
  have hLC : RiemannianMetricComplete L.metric := ⟨hcomplete⟩
  let KL : Set L.M := riemannianClosedBallOf L.metric z (2 * R)
  have hKL : IsCompact KL := hLC.closedEBall_isCompact z (2 * R)
  have hconvLarge : metricSourceConvergesOn Phi (CanonicalMetricCompactness.canonicalSourceData Phi)
      (riemannianClosedBallOf L.metric z (3 * R)) 0 := by
    intro ε hε
    obtain ⟨k, hk⟩ := C.converges _ (hLC.closedEBall_isCompact z (3 * R)) 0 ε hε
    refine ⟨k, fun j hj => ?_⟩
    have hh := hk j hj
    rw [hcanonical j] at hh
    exact hh
  have hcapture := pointed_metric_eventually_inverse_ball_capture z (r := R) (factor := 2)
    hR.le (by norm_num) (by linarith : 2 * R < 3 * R)
    (hLC.closedEBall_isCompact z (3 * R)) hconvLarge
  obtain ⟨kcap, hcap⟩ := eventually_atTop.mp hcapture
  let K : Set (N × ℝ) := e.symm '' KL
  have hK : IsCompact K := hKL.image e.symm.continuous
  let _ : LocallyCompactSpace H := J.locallyCompactSpace
  let _ : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H N
  obtain ⟨B, hB, hKB⟩ := exists_compact_superset hK
  let O : TopologicalSpace.Opens (N × ℝ) := ⟨interior B, isOpen_interior⟩
  let A : Set O := (Subtype.val : O → N × ℝ) ⁻¹' K
  have hA : IsCompact A := by
    apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
    have heq : (Subtype.val : O → N × ℝ) '' A = K := by
      rw [image_preimage_eq_of_subset]
      intro x hx
      exact ⟨⟨x, hKB hx⟩, rfl⟩
    rwa [heq]
  let η : ℝ := min (1 / 8) (q / 23040)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηquarter : η ≤ 1 / 4 := (min_le_left _ _).trans (by norm_num)
  have hηq : 720 * η < q / 16 := by
    have hh : η ≤ q / 23040 := min_le_right _ _
    linarith
  obtain ⟨kclose, hclose⟩ := pointedMaps_eventually_fixedDomain_metric_close Phi C hcanonical e O
    B hB interior_subset A hA 2 η hη
  obtain ⟨k, hkneck, hkscalar, hkc, hkk⟩ :=
    (hneck.and (hscalar.and ((eventually_ge_atTop kcap).and (eventually_ge_atTop kclose)))).exists
  obtain ⟨eps, heps, ⟨nk⟩⟩ := hkneck
  obtain ⟨f, hf, hfval, hfclose⟩ := hclose k hkk
  have hfdim : Module.finrank ℝ (F × ℝ) = Module.finrank ℝ ThreeSpace := by
    simp only [Module.finrank_prod, hdim, Module.finrank_self]
    simp [ThreeSpace]
  obtain ⟨V, Ψ, hV, hΨ, hΨinv, hmetric⟩ :=
    exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric (X.obj (subseq k)).metric
      hf.isImmersion hf.isEmbedding.injective hfdim
  have hpre (a : Sphere 2) :
      ∃ w : O, w.val ∈ K ∧ f w = nk.map (a, 0) := by
    have hball := nk.central_sphere_subset_closedBall
      (show nk.map (a, 0) ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ)) from
        ⟨(a, 0), ⟨mem_univ _, mem_singleton 0⟩, rfl⟩)
    have hballR : nk.map (a, 0) ∈
        riemannianClosedBallOf (X.obj (subseq k)).metric (Phi.map k z) R := by
      apply hball.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hq)
        (Real.sqrt_le_sqrt hkscalar)
    obtain ⟨htarget, _, hinball, hright⟩ := (hcap k hkc).2 _ hballR
    let y := (Phi.partialDiffeomorph k).symm (nk.map (a, 0))
    have hyK : e.symm y ∈ K := ⟨y, hinball, rfl⟩
    refine ⟨⟨e.symm y, hKB hyK⟩, hyK, ?_⟩
    rw [hfval]
    change Phi.map k (e (e.symm y)) = _
    rw [e.apply_symm_apply]
    exact hright
  have himage (a : Sphere 2) : nk.map (a, 0) ∈ V := by
    change nk.map (a, 0) ∈ (V : Set (X.obj (subseq k)).M)
    rw [hV]
    obtain ⟨w, _, hw⟩ := hpre a
    exact ⟨w, hw⟩
  have hpreA (y : V) (hy : y.val ∈ range (fun a : Sphere 2 => nk.map (a, 0))) : Ψ.symm y ∈ A := by
    obtain ⟨a, ha⟩ := hy
    obtain ⟨w, hwK, hw⟩ := hpre a
    have hwy : Ψ w = y := Subtype.ext ((hΨ w).trans (hw.trans ha))
    rw [← hwy, Ψ.symm_apply_apply]
    exact hwK
  obtain ⟨ψ, _, _, _⟩ := nk.exists_diffeomorph_graph_in_product_chart heps
    (show (0 : ℝ) ∈ Ioo (-eps⁻¹) eps⁻¹ from
      ⟨neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos), inv_pos.mpr nk.eps_pos⟩)
    h hdim O V Ψ himage hηquarter
    (hηq.trans_le (div_le_div_of_nonneg_right hkscalar (by norm_num))) (by
      intro y hy m hm
      rw [hmetric, ← hemetric]
      exact ((derivNorm_le_sup hA hm _ _ _ (hpreA y hy)).trans_lt hfclose).le)
  exact ⟨ψ⟩

theorem nonempty_diffeomorph_sphere_of_pointed_product_limit_of_spatialNecks
    (Phi : PointedRiemannianConvergenceMaps X L subseq) (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete L)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ L.M)
    (hemetric : Diffeomorph.pullbackMetricCross L.metric e = h.prod (euclideanMetric (E := ℝ)))
    (z : L.M) (hz : 0 < metricScalarAt L.metric z)
    (hneck : ∀ᶠ k in atTop, ∃ eps : ℝ, eps ≤ 1 / 1000 ∧
      Nonempty (SpatialNeck (X.obj (subseq k)).metric eps (Phi.map k z))) :
    Nonempty (N ≃ₘ⟮J, (𝓡 2)⟯ Sphere 2) := by
  have hscalar : ∀ᶠ k in atTop,
      metricScalarAt L.metric z / 2 ≤ metricScalarAt (X.obj (subseq k)).metric (Phi.map k z) :=
    ((pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical z).eventually
      (Ioi_mem_nhds (show metricScalarAt L.metric z / 2 < metricScalarAt L.metric z by linarith))).mono
        (fun _ hi => hi.le)
  exact nonempty_diffeomorph_sphere_of_pointed_product_limit_of_scalar_lower_bound
    Phi C hcanonical hcomplete h hdim e hemetric z (by positivity) hneck hscalar

end DifferentialGeometry.CheegerGromovCompactness
