import DifferentialGeometry.Geometry.Neck.SectionCurvature
import DifferentialGeometry.Geometry.Curvature.ProductGraphPerturbation
import DifferentialGeometry.Topology.GraphBandChart
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Geometry.Metric.Construction.Immersion

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private local instance : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem SpatialNeck.exists_diffeomorph_graph_in_product_chart
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (himage : ∀ q : Sphere 2, nk.map (q, s) ∈ V)
    {η : ℝ} (hη : η ≤ 1 / 4) (hsmallη : 720 * η < metricScalarAt g p / 16)
    (hsmall : ∀ y : V, y.val ∈ range (fun q : Sphere 2 => nk.map (q, s)) → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ η) :
    ∃ (ψ : N ≃ₘ⟮J, I2⟯ Sphere 2) (a : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ a ∧
      ∀ z : N, (Φ.symm ⟨nk.map (ψ z, s), himage (ψ z)⟩).val = (z, a z) := by
  let f : Sphere 2 → M := fun q => nk.map (q, s)
  have hfm (q : Sphere 2) : f q ∈ V := himage q
  let fV : Sphere 2 → V := fun q => ⟨f q, hfm q⟩
  have hf : IsSmoothEmbedding I2 I3 ∞ f := nk.isSmoothEmbedding_level (abs_lt.mpr hs)
  have hfV : IsSmoothEmbedding I2 I3 ∞ fV :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I2 I3 V fV hf
  let e : Sphere 2 → O := Φ.symm ∘ fV
  have he : IsSmoothEmbedding I2 (J.prod 𝓘(ℝ)) ∞ e := by
    have hec : ContMDiff I2 (J.prod 𝓘(ℝ)) ∞ e := Φ.symm.contMDiff.comp hfV.contMDiff
    refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
      (by decide) hec ?_,
      (hec.continuous.isClosedEmbedding (Φ.symm.injective.comp hfV.isEmbedding.injective)).isEmbedding⟩
    intro q
    rw [mfderiv_comp q (Φ.symm.contMDiff.mdifferentiableAt (by decide))
      (hfV.contMDiff.mdifferentiableAt (by decide))]
    exact (Φ.symm.mfderivToContinuousLinearEquiv (by decide) (fV q)).injective.comp
      (KappaSolutions.immersionAt_mfderiv_injective (hfV.isImmersion.isImmersionAt q))
  let G := Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ
  have hpoint (q : Sphere 2) : Φ (e q) = fV q := Φ.apply_symm_apply (fV q)
  have hdf (q : Sphere 2) : mfderiv I2 I3 fV q = mfderiv I2 I3 f q := by
    exact (DifferentialGeometry.mfderiv_subtypeVal_comp fV q).symm
  have hcomp (q : Sphere 2) (v : TangentSpace I2 q) :
      mfderiv (J.prod 𝓘(ℝ)) I3 Φ (e q) (mfderiv I2 (J.prod 𝓘(ℝ)) e q v) =
        mfderiv I2 I3 f q v := by
    have hc := mfderiv_comp_apply q
      (Φ.contMDiff.mdifferentiableAt (by decide))
      (he.contMDiff.mdifferentiableAt (by decide)) v
    have heq : (Φ : O → V) ∘ e = fV := funext hpoint
    rw [heq, hdf] at hc
    exact hc.symm
  have hinner (q : Sphere 2) (v w : TangentSpace I2 q) :
      G.inner (e q) (mfderiv I2 (J.prod 𝓘(ℝ)) e q v)
        (mfderiv I2 (J.prod 𝓘(ℝ)) e q w) =
      g.inner (f q) (mfderiv I2 I3 f q v) (mfderiv I2 I3 f q w) := by
    rw [Diffeomorph.pullbackMetricCross_inner, hcomp, hcomp]
    change g.inner ((Φ (e q)).val) _ _ = _
    rw [hpoint]
  have hRm (q : Sphere 2) (u v : TangentSpace I2 q) :
      metricRm04StandardAt G (e q)
        (mfderiv I2 (J.prod 𝓘(ℝ)) e q u) (mfderiv I2 (J.prod 𝓘(ℝ)) e q v)
        (mfderiv I2 (J.prod 𝓘(ℝ)) e q v) (mfderiv I2 (J.prod 𝓘(ℝ)) e q u) =
      metricRm04StandardAt g (f q)
        (mfderiv I2 I3 f q u) (mfderiv I2 I3 f q v)
        (mfderiv I2 I3 f q v) (mfderiv I2 I3 f q u) := by
    have hp := metricRm04Standard_pullbackCross (g.restrictOpen V) Φ (e q)
      (mfderiv I2 (J.prod 𝓘(ℝ)) e q u) (mfderiv I2 (J.prod 𝓘(ℝ)) e q v)
      (mfderiv I2 (J.prod 𝓘(ℝ)) e q v) (mfderiv I2 (J.prod 𝓘(ℝ)) e q u)
    have hr := metricRm04StandardAt_restrictOpen g V (Φ (e q))
      (mfderiv (J.prod 𝓘(ℝ)) I3 Φ (e q) (mfderiv I2 (J.prod 𝓘(ℝ)) e q u))
      (mfderiv (J.prod 𝓘(ℝ)) I3 Φ (e q) (mfderiv I2 (J.prod 𝓘(ℝ)) e q v))
      (mfderiv (J.prod 𝓘(ℝ)) I3 Φ (e q) (mfderiv I2 (J.prod 𝓘(ℝ)) e q v))
      (mfderiv (J.prod 𝓘(ℝ)) I3 Φ (e q) (mfderiv I2 (J.prod 𝓘(ℝ)) e q u))
    simp only [mfderiv_subtype_val_apply] at hr
    have hh := hp.trans hr
    erw [hcomp, hcomp, hpoint] at hh
    exact hh
  obtain ⟨ψ, a, ha, hgraph⟩ :=
    exists_diffeomorph_graph_of_tangent_sectional_lower_bound_in_open_product
      h O G e he (by simpa using hdim.symm) (by simp) hη hsmallη
      (fun q m hm => hsmall (fV q) (mem_range_self q) m hm) (by
        intro q u v
        rw [hinner, hinner, hinner, hRm]
        exact nk.metricRm04_section_lower_bound heps hs q u v)
  exact ⟨ψ, a, ha, hgraph⟩

theorem SpatialNeck.interior_eq_empty_of_frontier_in_product_chart
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V)
    (hfront : frontier K = range (fun q : Sphere 2 => nk.map (q, s)))
    {η : ℝ} (hη : η ≤ 1 / 4) (hsmallη : 720 * η < metricScalarAt g p / 16)
    (hsmall : ∀ y : V, y.val ∈ frontier K → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ η) :
    interior K = ∅ := by
  have himage (q : Sphere 2) : nk.map (q, s) ∈ V :=
    hKV (hK.isClosed.frontier_subset (hfront.symm ▸ mem_range_self q))
  obtain ⟨ψ, a, _, hgraph⟩ := nk.exists_diffeomorph_graph_in_product_chart heps hs h hdim
    O V Φ himage hη hsmallη (fun y hy => hsmall y (hfront.symm ▸ hy))
  apply DifferentialGeometry.Topology.interior_eq_empty_of_frontier_graph_in_opens_product_chart
    O V Φ.toHomeomorph hK hKV a
  intro y hy
  obtain ⟨q, hq⟩ := hfront ▸ hy
  have hyq : y = ⟨nk.map (q, s), himage q⟩ := Subtype.ext hq.symm
  rw [hyq]
  refine ⟨ψ.symm q, ?_⟩
  change (ψ.symm q, a (ψ.symm q)) = (Φ.symm ⟨nk.map (q, s), himage q⟩).val
  simpa only [ψ.apply_symm_apply] using (hgraph (ψ.symm q)).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem eventually_interior_eq_empty_of_frontier_necks_of_product_convergence
    (g : ∀ i, SmoothRiemannianMetric I3 (M i)) (eps : ℕ → ℝ) (p : ∀ i, M i)
    (nk : ∀ i, SpatialNeck (g i) (eps i) (p i))
    (heps : ∀ᶠ i in atTop, eps i ≤ 1 / 1000)
    (s : ℕ → ℝ) (hs : ∀ i, s i ∈ Ioo (-(eps i)⁻¹) (eps i)⁻¹)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : ∀ i, TopologicalSpace.Opens (M i))
    (Φ : ∀ i, O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V i)
    (K : ∀ i, Set (M i)) (hK : ∀ i, IsCompact (K i)) (hKV : ∀ i, K i ⊆ V i)
    (hfront : ∀ i, frontier (K i) = range (fun q : Sphere 2 => (nk i).map (q, s i)))
    (A : Set O) (hA : IsCompact A)
    (hfrontA : ∀ᶠ i in atTop, ∀ y : V i, y.val ∈ frontier (K i) → (Φ i).symm y ∈ A)
    (hconv : MetricCPConvergenceOn A 2
      (fun i => Diffeomorph.pullbackMetricCross ((g i).restrictOpen (V i)) (Φ i))
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
      ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O))
    {q : ℝ} (hq : 0 < q)
    (hscalar : ∀ᶠ i in atTop, q ≤ metricScalarAt (g i) (p i)) :
    ∀ᶠ i in atTop, interior (K i) = ∅ := by
  let η : ℝ := min (1 / 8) (q / 23040)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηquarter : η ≤ 1 / 4 := (min_le_left _ _).trans (by norm_num)
  have hηq : 720 * η < q / 16 := by
    have hm : η ≤ q / 23040 := min_le_right _ _
    linarith
  obtain ⟨j, hj⟩ := hconv η hη
  filter_upwards [heps, hfrontA, hscalar, eventually_ge_atTop j] with i hei hAi hqi hji
  apply (nk i).interior_eq_empty_of_frontier_in_product_chart hei (hs i) h hdim O (V i) (Φ i)
    (hK i) (hKV i) (hfront i) hηquarter
    (hηq.trans_le (div_le_div_of_nonneg_right hqi (by norm_num)))
  intro y hy m hm
  exact ((derivNorm_le_sup hA hm _ _ _ (hAi y hy)).trans_lt (hj i hji)).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


open DifferentialGeometry
open scoped ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

omit [T2Space M] in
private theorem scale_metric_ratio (g : SmoothRiemannianMetric I3 M)
    {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q) :
    scaleMetric (Q / q) (div_pos hQ hq) (DifferentialGeometry.scaleMetric q hq g) = scaleMetric Q hQ g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner]
  field_simp

omit [T2Space M] in
private theorem cap_subset_ball_at_mem_of_scale_ratio
    (g : SmoothRiemannianMetric I3 M) {q Q A R : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) (hA : 0 < A) (hR : 0 < R)
    (hratio : Q / q ≤ A) {K : Set M} {x z : M} (hx : x ∈ K)
    (hball : K ⊆ riemannianBallOf (DifferentialGeometry.scaleMetric q hq g) z R) :
    K ⊆ riemannianBallOf (DifferentialGeometry.scaleMetric Q hQ g) x (2 * Real.sqrt A * R) := by
  have hqratio : 0 < Q / q := div_pos hQ hq
  intro y hy
  have hd : riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y < ENNReal.ofReal (2*R) := by
    have hxR := hball hx
    have hyR := hball hy
    change riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) z x < ENNReal.ofReal R at hxR
    change riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) z y < ENNReal.ofReal R at hyR
    have ht := (riemannianEDistOf_triangle (DifferentialGeometry.scaleMetric q hq g) x z y).trans_lt
      (ENNReal.add_lt_add (by rwa [riemannianEDistOf_comm] at hxR) hyR)
    rw [← ENNReal.ofReal_add hR.le hR.le] at ht
    convert ht using 1; congr 1; ring
  change riemannianEDistOf (DifferentialGeometry.scaleMetric Q hQ g) x y < ENNReal.ofReal (2 * Real.sqrt A * R)
  rw [← scale_metric_ratio g hq hQ,edistOf_scale]
  have hs : ENNReal.ofReal (Real.sqrt (Q / q)) ≤ ENNReal.ofReal (Real.sqrt A) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hratio)
  have hprod := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hA)) ENNReal.ofReal_ne_top hd
  have hb := (mul_le_mul' hs le_rfl).trans_lt hprod
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg A)] at hb
  convert hb using 1; congr 1; ring

theorem SpatialNeck.not_mem_interior_of_frontier_in_scaled_product_chart
    (g : SmoothRiemannianMetric I3 M) {q Q A b R eps : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) (hb : 0 ≤ b)
    (hratio : Q / q ≤ A) {p x z : M}
    (nk : SpatialNeck (DifferentialGeometry.scaleMetric q hq g) eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹)
    {K : Set M} (hK : IsCompact K)
    (hfront : frontier K = range (fun u : Sphere 2 => nk.map (u,s)))
    (hscalar : b ≤ metricScalarAt (DifferentialGeometry.scaleMetric q hq g) p)
    (hball : K ⊆ riemannianBallOf (DifferentialGeometry.scaleMetric q hq g) z R)
    {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
    (hprod : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : riemannianBallOf (DifferentialGeometry.scaleMetric Q hQ g) x (2 * Real.sqrt A * R) ⊆ V)
    {δ : ℝ} (hδ : δ ≤ 1/4) (hδsmall : 720*δ < (b/A)/16)
    (hproduct : ∀ y : V, y.val ∈ frontier K → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross ((DifferentialGeometry.scaleMetric Q hQ g).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δ) :
    x ∉ interior K := by
  intro hx
  have hc : 0 < Q / q := div_pos hQ hq
  have hA : 0 < A := hc.trans_le hratio
  have hR : 0 < R := by
    have hd := hball (interior_subset hx)
    exact ENNReal.ofReal_pos.mp (bot_le.trans_lt hd)
  let nk' := nk.scaleMetric (Q / q) hc
  have heq := scale_metric_ratio g hq hQ
  have hscaled : b/A ≤ metricScalarAt (DifferentialGeometry.scaleMetric Q hQ g) p := by
    rw [← heq,metricScalarAt_scaleMetric]
    rw [← div_eq_inv_mul]
    exact (div_le_div_of_nonneg_left hb hc hratio).trans
      (div_le_div_of_nonneg_right hscalar hc.le)
  have hKV := (cap_subset_ball_at_mem_of_scale_ratio g hq hQ hA hR hratio
    (interior_subset hx) hball).trans hcapture
  have hfront' : frontier K = range (fun u : Sphere 2 => nk'.map (u,s)) := hfront
  have hmetricClose : ∀ y : V, y.val ∈ frontier K → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross
        ((DifferentialGeometry.scaleMetric (Q / q) hc (DifferentialGeometry.scaleMetric q hq g)).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δ := by
    rw [heq]
    exact hproduct
  have hsmall : 720*δ < metricScalarAt (DifferentialGeometry.scaleMetric (Q / q) hc (DifferentialGeometry.scaleMetric q hq g)) p / 16 := by
    rw [heq]
    exact hδsmall.trans_le (div_le_div_of_nonneg_right hscaled (by norm_num))
  have hempty := nk'.interior_eq_empty_of_frontier_in_product_chart heps hs hprod hdim
    O V Φ hK hKV hfront' hδ hsmall hmetricClose
  simp only [hempty,mem_empty_iff_false] at hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
