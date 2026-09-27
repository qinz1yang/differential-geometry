import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalInitialFlowComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.AmbientSpatialCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowScalarBounds

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

private theorem initial_reference_comparison_parameters
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (D r : ℝ), r < D →
      ∀ t ∈ Icc 0 τ, ∀ g : SmoothRiemannianMetric ThreeModel (standardCapWindow D),
      (∀ S : StandardSolution,
        metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
          g ((S.val.metric t).restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) < ε/2) →
        metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
          g (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε := by
  obtain ⟨α,hα,Λ,hΛ,C,L,hC,hL,hstd⟩ := standard_uniform_fixed_cap_metric_bounds
  obtain ⟨αlife,hαlife,_,_,hlife,_⟩ := standard_uniform_initial_window
  let Lsum := ∑ j ∈ Finset.range (N+1), L j
  have hLsum : 0 ≤ Lsum := Finset.sum_nonneg fun j _ => hL j
  let τ := min α (min αlife (ε/(4*(Lsum+1))))
  have hτ : 0 < τ := lt_min hα (lt_min hαlife (by positivity))
  have hτα : τ ≤ α := min_le_left _ _
  have hτlife : τ ≤ αlife := (min_le_right _ _).trans (min_le_left _ _)
  have hτrate : τ ≤ ε/(4*(Lsum+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,?_⟩
  intro D r hrD t ht g hclose
  obtain ⟨S⟩ := standard_solution_nonempty
  have hl : ENNReal.ofReal τ < S.val.lifetime :=
    (ENNReal.ofReal_le_ofReal hτlife).trans_lt (hlife S)
  have hrate := (hstd S.val τ hτ.le hτα hl).2.2
  have hsmall : Lsum*t ≤ ε/4 := by
    have hp := (le_div_iff₀ (by positivity : 0 < 4*(Lsum+1))).mp (ht.2.trans hτrate)
    nlinarith
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ r}
  have hK : IsCompact K := by
    have hb : IsCompact {x : ThreeSpace | ‖x‖ ≤ r} := by
      simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hb (by
      intro x hx
      refine ⟨⟨x,?_⟩,rfl⟩
      change ‖x‖ < D+1
      change ‖x‖ ≤ r at hx
      linarith)
  have hbound : metricDerivNormSupOn K N g (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) ≤ 3*ε/4 := by
    apply metricDerivNormSupOn_le_of_forall K N _ _ _ _ (by positivity)
    intro j hj x hx
    have hg := (derivNorm_le_sup hK hj g ((S.val.metric t).restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) hx).trans_lt (hclose S)
    have hm := hrate j t ht 0 ⟨le_rfl,hτ.le⟩ x.val
    rw [S.val.initial,sub_zero,abs_of_nonneg ht.1] at hm
    have hLj : L j ≤ Lsum := Finset.single_le_sum (fun k _ => hL k)
      (Finset.mem_range.mpr (by omega))
    have hstdj : metricDerivNorm j ((S.val.metric t).restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x ≤ ε/4 := by
      rw [metricDerivNorm_restrictOpen]
      exact hm.trans ((mul_le_mul_of_nonneg_right hLj ht.1).trans hsmall)
    have htri := metricDerivNorm_triangle j g ((S.val.metric t).restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) (metric.restrictOpen (standardCapWindow D)) x
    linarith
  rw [metricDerivENormSupOn_eq_ofReal_of_isCompact hK]
  exact (ENNReal.ofReal_le_ofReal hbound).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))

theorem exists_uniform_initial_metric_closeness_of_local_curvature
    (D r T K ε : ℝ) (hr : 0 < r) (hfit : 64 * r < D)
    (hT : 0 < T) (hε : 0 < ε) (N : ℕ) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η ≤ T ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      N+2 ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 64*r →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ t ∈ Icc 0 (min η θ),
          metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
            (L.base.metric t) (standardCapMetric.restrictOpen (standardCapWindow D))
            (standardCapMetric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε := by
  obtain ⟨η₀,ε₀,hη₀,hη₀T,hε₀,hε₀half,hcompare⟩ :=
    exists_uniform_initial_standard_cap_comparison_of_local_curvature D r T K (ε/2)
      hr hfit hT (by positivity) N
  obtain ⟨τ,hτ,hreference⟩ := initial_reference_comparison_parameters N hε
  let η := min η₀ τ
  have hη : 0 < η := lt_min hη₀ hτ
  refine ⟨η,ε₀,hη,(min_le_left _ _).trans hη₀T,hε₀,hε₀half,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ
    J θ hθ hθT hcarrier hregular L hL hzero hgram hlocal t ht
  rw [standardCapMetric_eq_metric]
  apply hreference D r (by linarith) t
    ⟨ht.1, (ht.2.trans (min_le_left _ _)).trans (min_le_right _ _)⟩ (L.base.metric t)
  intro S
  simpa only [standardCapMetric_eq_metric] using
    hcompare w hm hζ J θ hθ hθT hcarrier hregular L hL hzero hgram hlocal S t
    ⟨ht.1, le_min ((ht.2.trans (min_le_left _ _)).trans (min_le_left _ _))
      (ht.2.trans (min_le_right _ _))⟩

private theorem spatial_cap_frontier_parameters
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D) :
    ∃ η C : ℝ, 0 < η ∧ 1 ≤ C ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I3 (standardCapWindow D))
        (h : SmoothRiemannianMetric I3 M) (Φ : standardCapWindow D → M),
        IsLocalDiffeomorph I3 I3 ∞ Φ → Injective Φ →
        (∀ (x : standardCapWindow D) (v w : TangentSpace I3 x),
          g.inner x v w = h.inner (Φ x) (mfderiv I3 I3 Φ x v) (mfderiv I3 I3 Φ x w)) →
        metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹}
          ⌈eps⁻¹⌉₊ g (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η →
            (∀ x : standardCapWindow D, ‖x.val‖ ≤ r+eps⁻¹ →
              1/2 < metricScalarAt h (Φ x) ∧
              metricScalarAt h (Φ x) < C) ∧
            ∀ s ∈ Ioo (-eps⁻¹) eps⁻¹,
              ∃ (p z : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ z.val = 0 ∧
                ∃ (nk : SpatialNeck h eps (Φ p))
                  (K : CompactDomain M),
                  K.carrier = Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ r+s} ∧
                  Nonempty (CapCore K.carrier) ∧ Φ z ∈ interior K.carrier ∧
                  (∀ x : standardCapWindow D, ‖x.val‖ < r+s →
                    Φ x ∈ interior K.carrier) ∧
                  (∀ v : neckBuffer eps, ∃ x : standardCapWindow D,
                    x.val = (r+v.val.2) • (v.val.1 : ThreeSpace) ∧
                    nk.map v.val = Φ x) ∧
                  frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,s)) ∧
                  IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,s)) ∧
                  (∀ q : Sphere 2, ∀ a : ℝ, s+a ∈ Ioo (-eps⁻¹) eps⁻¹ →
                    (nk.map (q,s+a) ∈ K.carrier ↔ a ≤ 0)) ∧
                  |metricScalarAt h (Φ p) - 1| < 1/8 ∧
                  K.carrier ⊆ riemannianBallOf h
                    (Φ z) (2*(r+s)) := by
  obtain ⟨δ,C,hδ,hC,hsc⟩ :=
    exists_uniform_window_scalar_bounds_of_metric_close D (r + eps⁻¹) (by linarith)
  let η := min (1/40000) (min (eps/20000) δ)
  have hη : 0 < η := lt_min (by norm_num) (lt_min (by positivity) hδ)
  have hηsmall : η ≤ 1/40000 := min_le_left _ _
  have hηeps : 20000*η ≤ eps := by
    have hb : η ≤ eps/20000 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hk : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have hb : (2:ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast hb.trans (Nat.le_ceil _)
  refine ⟨η,C,hη,hC,?_⟩
  intro M _ _ _ _ g h Φ hΦ hinj hmetric hclose
  constructor
  · intro x hx
    have hc := (metricDerivENormSupOn_mono (subset_refl _) hk g _ _).trans_lt hclose
    have hb := hsc g (hc.trans_le (ENNReal.ofReal_le_ofReal hηδ)) x hx
    have he := (curvature_of_injective_local_isometry g h Φ hΦ hinj hmetric x).1
    rwa [he] at hb
  · intro s hs
    obtain ⟨p,z,hp,hz,nk,K,hK,hcore,hzint,hint,hmap,hfront,hemb,hside,hscalar,hball⟩ :=
      exists_spatial_cap_frontier_of_window_metric_close D r eps heps hsmall hr
        hfit hs g h Φ hΦ hinj hmetric hη hηsmall hηeps hclose
    refine ⟨p,z,hp,hz,nk,K,hK,hcore,hzint,hint,hmap,hfront,hemb,hside,?_,hball⟩
    exact hscalar.trans_lt (by linarith)
theorem exists_uniform_spatial_cap_frontier_of_local_curvature
    (D r T K eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : 64 * (r + eps⁻¹) < D) (hT : 0 < T) :
    ∃ η ε₀ C : ℝ, 0 < η ∧ η ≤ T ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 1 ≤ C ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ⌈eps⁻¹⌉₊+2 ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 64*(r + eps⁻¹) →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ t ∈ Icc 0 (min η θ),
          ∀ {M' : Type*} [TopologicalSpace M'] [ChartedSpace ThreeSpace M']
            [IsManifold I3 ∞ M'] [T2Space M'] (h : SmoothRiemannianMetric I3 M')
            (Φ : standardCapWindow D → M'),
            IsLocalDiffeomorph I3 I3 ∞ Φ → Injective Φ →
            (∀ (x : standardCapWindow D) (v z : TangentSpace I3 x),
              (L.base.metric t).inner x v z =
                h.inner (Φ x) (mfderiv I3 I3 Φ x v) (mfderiv I3 I3 Φ x z)) →
            (∀ x : standardCapWindow D, ‖x.val‖ ≤ r+eps⁻¹ →
              1/2 < metricScalarAt h (Φ x) ∧
              metricScalarAt h (Φ x) < C) ∧
            ∀ s ∈ Ioo (-eps⁻¹) eps⁻¹,
              ∃ (p z : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ z.val = 0 ∧
                ∃ (nk : SpatialNeck h eps (Φ p))
                  (K : CompactDomain M'),
                  K.carrier = Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ r+s} ∧
                  Nonempty (CapCore K.carrier) ∧ Φ z ∈ interior K.carrier ∧
                  (∀ x : standardCapWindow D, ‖x.val‖ < r+s →
                    Φ x ∈ interior K.carrier) ∧
                  (∀ v : neckBuffer eps, ∃ x : standardCapWindow D,
                    x.val = (r+v.val.2) • (v.val.1 : ThreeSpace) ∧
                    nk.map v.val = Φ x) ∧
                  frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,s)) ∧
                  IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,s)) ∧
                  (∀ q : Sphere 2, ∀ a : ℝ, s+a ∈ Ioo (-eps⁻¹) eps⁻¹ →
                    (nk.map (q,s+a) ∈ K.carrier ↔ a ≤ 0)) ∧
                  |metricScalarAt h (Φ p) - 1| < 1/8 ∧
                  K.carrier ⊆ riemannianBallOf h
                    (Φ z) (2*(r+s)) := by
  have hi : 0 < eps⁻¹ := inv_pos.mpr heps
  have hr0 : 0 < r := by linarith [transitionEnd_pos]
  obtain ⟨δ,C,hδ,hC,hrecognize⟩ :=
    spatial_cap_frontier_parameters D r eps heps hsmall hr (by linarith [transitionEnd_pos])
  obtain ⟨η,ε₀,hη,hηT,hε₀,hε₀half,hclose⟩ :=
    exists_uniform_initial_metric_closeness_of_local_curvature D (r + eps⁻¹) T K δ
      (by positivity) hfit hT hδ ⌈eps⁻¹⌉₊
  refine ⟨η,ε₀,C,hη,hηT,hε₀,hε₀half,hC,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ₀ k d A hA m ζ w hm hζ
    J θ hθ hθT hcarrier hregular L hL hzero hgram hlocal t ht M' _ _ _ _ h Φ hΦ hinj hmetric
  apply hrecognize (L.base.metric t) h Φ hΦ hinj hmetric
  simpa only [standardCapMetric_eq_metric] using
    hclose w hm hζ J θ hθ hθT hcarrier hregular L hL hzero hgram hlocal t ht


end DifferentialGeometry.PDE.RicciFlow.StandardCap
