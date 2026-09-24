import DifferentialGeometry.Geometry.Metric.Construction.OpenExtension
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality
import DifferentialGeometry.Geometry.Curvature.Naturality.MetricLocality
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation
import DifferentialGeometry.Topology.GraphBand
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.Construction.Immersion
import DifferentialGeometry.Topology.Manifold.TransverseGraph
import Mathlib.Geometry.Manifold.SmoothEmbedding
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

set_option autoImplicit false
noncomputable section
open Set Bundle _root_.Manifold
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.CheegerGromovCompactness

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem vertical_not_mem_range_of_tangent_sectional_lower_bound_of_small_metric_derivatives
    (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric (J.prod 𝓘(ℝ)) (N × ℝ))
    (e : M → N × ℝ) (p : M)
    (hinj : Function.Injective (mfderiv I (J.prod 𝓘(ℝ)) e p))
    (hdim : 1 < Module.finrank ℝ E)
    {ε c : ℝ} (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      (h.prod (euclideanMetric (E := ℝ)))
      (h.prod (euclideanMetric (E := ℝ))) (e p) ≤ ε)
    (hsec : ∀ v w : TangentSpace I p,
      c * (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p v) *
        g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w) -
        (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)) ^ 2) ≤
        metricRm04StandardAt g (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v)
          (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
          (mfderiv I (J.prod 𝓘(ℝ)) e p v)) :
    (0, 1) ∉ range (mfderiv I (J.prod 𝓘(ℝ)) e p) := by
  let A : E →L[ℝ] F × ℝ := mfderiv I (J.prod 𝓘(ℝ)) e p
  rintro ⟨w, hw⟩
  have hw0 : w ≠ 0 := by
    intro hz
    have hh := congrArg Prod.snd hw
    simp only [hz, map_zero] at hh
    exact zero_ne_one hh
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := ℝ) (M := E)
    hdim (show (w : E) ≠ 0 from hw0)
  let wE : E := w
  have hwA : A wE = (0, 1) := hw
  let z : E := v - (A v).2 • wE
  have hzA : A z = ((A v).1, 0) := by
    dsimp only [z]
    rw [map_sub, map_smul, hwA]
    ext <;> simp
  have hu : (A v).1 ≠ 0 := by
    intro hzero
    have hAv : A v = A ((A v).2 • wE) := by
      rw [map_smul, hwA]
      exact Prod.ext (by simpa using hzero) (by simp)
    have hvw : v = (A v).2 • wE := hinj hAv
    have heq : -(A v).2 • wE + (1 : ℝ) • v = 0 := by
      calc
        _ = -(A v).2 • wE + (A v).2 • wE := by rw [one_smul]; exact congrArg _ hvw
        _ = 0 := by rw [neg_smul, neg_add_cancel]
    have hv' : LinearIndependent ℝ ![wE, v] := hv
    have hcoeff := LinearIndependent.pair_iff.mp hv' (-(A v).2) 1 heq
    exact one_ne_zero hcoeff.2
  have hlow := hsec (show TangentSpace I p from z) w
  change c * (g.inner (e p) (A z) (A z) * g.inner (e p) (A wE) (A wE) -
    (g.inner (e p) (A z) (A wE)) ^ 2) ≤
    metricRm04StandardAt g (e p) (A z) (A wE) (A wE) (A z) at hlow
  rw [hzA, hwA] at hlow
  exact (not_lt_of_ge hlow)
    (metricRm04_lt_mul_gram_product_vertical_of_small_metric_derivatives
      h g (e p) hε hc hsmall ((A v).1) hu)

theorem exists_diffeomorph_graph_of_tangent_sectional_lower_bound_of_small_metric_derivatives
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N]
    (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric (J.prod 𝓘(ℝ)) (N × ℝ))
    (e : M → N × ℝ) (he : IsSmoothEmbedding I (J.prod 𝓘(ℝ)) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hdim2 : 1 < Module.finrank ℝ E)
    {ε c : ℝ} (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ p : M, ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      (h.prod (euclideanMetric (E := ℝ)))
      (h.prod (euclideanMetric (E := ℝ))) (e p) ≤ ε)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      c * (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p v) *
        g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w) -
        (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)) ^ 2) ≤
        metricRm04StandardAt g (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v)
          (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
          (mfderiv I (J.prod 𝓘(ℝ)) e p v)) :
    ∃ (η : N ≃ₘ⟮J, I⟯ M) (f : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ f ∧
      ∀ p, e (η p) = (p, f p) := by
  let _ : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  exact DifferentialGeometry.Topology.Manifold.exists_diffeomorph_graph_of_transverse_embedding
    e he.contMDiff he.isEmbedding.injective (fun p => DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.immersionAt_mfderiv_injective (he.isImmersion.isImmersionAt p)) hdim
    (fun p => vertical_not_mem_range_of_tangent_sectional_lower_bound_of_small_metric_derivatives
      h g e p ((fun p => DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.immersionAt_mfderiv_injective (he.isImmersion.isImmersionAt p)) p) hdim2 hε hc (hsmall p) (hsec p))

theorem interior_eq_empty_of_frontier_sectional_lower_bound_of_small_metric_derivatives
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N]
    (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric (J.prod 𝓘(ℝ)) (N × ℝ))
    (e : M → N × ℝ) (he : IsSmoothEmbedding I (J.prod 𝓘(ℝ)) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hdim2 : 1 < Module.finrank ℝ E)
    {ε c : ℝ} (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ p : M, ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      (h.prod (euclideanMetric (E := ℝ)))
      (h.prod (euclideanMetric (E := ℝ))) (e p) ≤ ε)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      c * (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p v) *
        g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w) -
        (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)) ^ 2) ≤
        metricRm04StandardAt g (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v)
          (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
          (mfderiv I (J.prod 𝓘(ℝ)) e p v))
    {K : Set (N × ℝ)} (hK : IsCompact K) (hfront : frontier K = range e) :
    interior K = ∅ := by
  obtain ⟨η, f, _, hgraph⟩ := exists_diffeomorph_graph_of_tangent_sectional_lower_bound_of_small_metric_derivatives
    h g e he hdim hdim2 hε hc hsmall hsec
  apply DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph hK f
  rw [hfront]
  rintro _ ⟨x, rfl⟩
  exact ⟨η.symm x, by simpa only [η.apply_symm_apply] using (hgraph (η.symm x)).symm⟩

end DifferentialGeometry.Geometry.Curvature

end

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.CheegerGromovCompactness

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem exists_diffeomorph_graph_of_tangent_sectional_lower_bound_in_open_product
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N] [SigmaCompactSpace N]
    (h : SmoothRiemannianMetric J N) (O : TopologicalSpace.Opens (N × ℝ))
    (g : SmoothRiemannianMetric (J.prod 𝓘(ℝ)) O)
    (e : M → O) (he : Manifold.IsSmoothEmbedding I (J.prod 𝓘(ℝ)) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hdim2 : 1 < Module.finrank ℝ E)
    {ε c : ℝ} (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ p : M, ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (e p) ≤ ε)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      c * (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p v) *
        g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w) -
        (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)) ^ 2) ≤
        metricRm04StandardAt g (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v)
          (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
          (mfderiv I (J.prod 𝓘(ℝ)) e p v)) :
    ∃ (η : N ≃ₘ⟮J, I⟯ M) (f : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ f ∧
      ∀ p, (e (η p)).val = (p, f p) := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (J.prod 𝓘(ℝ)) O.isOpen)
  let R := h.prod (euclideanMetric (E := ℝ))
  let e' : M → N × ℝ := Subtype.val ∘ e
  have he' : Manifold.IsSmoothEmbedding I (J.prod 𝓘(ℝ)) ∞ e' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen I (J.prod 𝓘(ℝ)) O e he
  have hK : IsCompact (range e') := isCompact_range he'.contMDiff.continuous
  have hKO : range e' ⊆ O := by
    rintro _ ⟨p, rfl⟩
    exact (e p).property
  obtain ⟨G, V, hKV, hVO, hG, _⟩ :=
    exists_smooth_metric_agrees_on_neighborhood_of_is_compact R O g hK hKO
  have hmem (p : M) : (e p).val ∈ V := hKV (mem_range_self p)
  have hgerm (p : M) : ∀ᶠ y in 𝓝 (e p), ∀ v w : TangentSpace (J.prod 𝓘(ℝ)) y,
      (G.restrictOpen O).inner y v w = g.inner y v w := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (V.isOpen.mem_nhds (hmem p))] with y hy
    exact hG y.val hy
  have hinner (p : M) (v w : TangentSpace (J.prod 𝓘(ℝ)) (e p)) :
      G.inner (e' p) v w = g.inner (e p) v w := hG _ (hmem p) v w
  have hderiv (p : M) : mfderiv I (J.prod 𝓘(ℝ)) e' p = mfderiv I (J.prod 𝓘(ℝ)) e p :=
    DifferentialGeometry.mfderiv_subtypeVal_comp e p
  have hnorm (p : M) (m : ℕ) : metricDerivNorm m G R R (e' p) =
      metricDerivNorm m g (R.restrictOpen O) (R.restrictOpen O) (e p) := by
    erw [← metricDerivNorm_restrictOpen G R R O m (e p)]
    exact metricDerivNorm_eq_of_metric_eventuallyEq m (G.restrictOpen O) g
      (R.restrictOpen O) (R.restrictOpen O) (e p) (hgerm p)
  have hRm (p : M) (u v w z : TangentSpace (J.prod 𝓘(ℝ)) (e p)) :
      metricRm04StandardAt G (e' p) u v w z = metricRm04StandardAt g (e p) u v w z := by
    have hr := metricRm04StandardAt_restrictOpen G O (e p) u v w z
    simp only [mfderiv_subtype_val_apply] at hr
    refine hr.symm.trans ?_
    change metricRm04At (G.restrictOpen O) (e p) (vec4 u v w z) =
      metricRm04At g (e p) (vec4 u v w z)
    rw [metricRm04At_eq_of_metric_eventuallyEq _ _ _ (hgerm p)]
  exact exists_diffeomorph_graph_of_tangent_sectional_lower_bound_of_small_metric_derivatives
    h G e' he' hdim hdim2 hε hc
    (fun p m hm => (hnorm p m).trans_le (hsmall p m hm)) (by
      intro p v w
      erw [hderiv, hinner, hinner, hinner, hRm]
      exact hsec p v w)

theorem interior_eq_empty_of_frontier_sectional_lower_bound_in_open_product
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N] [SigmaCompactSpace N]
    (h : SmoothRiemannianMetric J N) (O : TopologicalSpace.Opens (N × ℝ))
    (g : SmoothRiemannianMetric (J.prod 𝓘(ℝ)) O)
    (e : M → O) (he : Manifold.IsSmoothEmbedding I (J.prod 𝓘(ℝ)) ∞ e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hdim2 : 1 < Module.finrank ℝ E)
    {ε c : ℝ} (hε : ε ≤ 1 / 4) (hc : 720 * ε < c)
    (hsmall : ∀ p : M, ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (e p) ≤ ε)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      c * (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p v) *
        g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w) -
        (g.inner (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)) ^ 2) ≤
        metricRm04StandardAt g (e p) (mfderiv I (J.prod 𝓘(ℝ)) e p v)
          (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
          (mfderiv I (J.prod 𝓘(ℝ)) e p v))
    {K : Set (N × ℝ)} (hK : IsCompact K)
    (hfront : frontier K = range (Subtype.val ∘ e)) : interior K = ∅ := by
  obtain ⟨η, f, _, hgraph⟩ := exists_diffeomorph_graph_of_tangent_sectional_lower_bound_in_open_product
    h O g e he hdim hdim2 hε hc hsmall hsec
  apply DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph hK f
  rw [hfront]
  rintro _ ⟨x, rfl⟩
  exact ⟨η.symm x, by simpa only [η.apply_symm_apply, Function.comp_apply] using (hgraph (η.symm x)).symm⟩

end DifferentialGeometry.Geometry.Curvature
