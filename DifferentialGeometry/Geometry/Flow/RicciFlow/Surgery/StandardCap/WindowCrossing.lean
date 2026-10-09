import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowFlowDistance
import DifferentialGeometry.Geometry.Curvature.LocalPullbackRicci
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowFlowComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardRadialSectional
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCutScaleProtection

set_option autoImplicit false
noncomputable section
open Set Filter Function Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (standardCapWindow D).isOpen)


theorem exists_cutoff_cap_survivor_partialDiffeomorph_or_discarded_of_standard_metric_close
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ ∀ b : ℝ, R ≤ b →
      ∃ η : ℝ, 0 < η ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
        (parameters : CutoffParameters) (record : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, record.delta j ≤ η) → ∀ (r D : ℝ), R ≤ r → r ≤ b → b < D →
      ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 θ →
      ∀ (Ψ : standardCapWindow D → (H.event i).incoming.terminalRegularOpen)
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ), Injective Ψ →
      ∀ (q : ℝ) (hq : 0 < q),
      (∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ j ≤ 2,
        metricDerivNorm j (localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Ψ hΨ)
          ((S.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ ε) →
      let K := Ψ '' {x : standardCapWindow D | ‖x.val‖ ≤ b}
      (∃ F : PartialDiffeomorph ThreeModel ThreeModel
          (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
        K ⊆ F.source ∧
        (∀ y ∈ F.source, (H.event i).RegularCrossing y.val (F y)) ∧
        (∀ z : (H.event i).old, (H.event i).oldTerminal z ∈ F.source →
          F ((H.event i).oldTerminal z) = (H.event i).oldOutput z) ∧
        ∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
          (H.event i).outputMetric.inner (F y)
            (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) y w) =
              (H.event i).terminal.metric.inner y v w) ∨
      ∀ x ∈ K, ∃ z : (H.event i).transition.trace.tubes.core, z.val = x.val ∧
        ∃ d : (H.event i).discarded.Carrier,
          (H.event i).transition.trace.presentation
            ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d := by
  obtain ⟨R, εrad, hR, hεrad, hboundary⟩ :=
    exists_uniform_standard_radial_image_frontier_tangent_sectional_lower_bound_of_metric_close θ hθ hθ1
  obtain ⟨εscalar, C, hεscalar, hC, hscalar⟩ :=
    StandardCap.exists_uniform_scalar_bound_of_standard_metric_close_on_opens θ hθ hθ1
  have hlt : ENNReal.ofReal θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hθ1
  obtain ⟨Λ, hΛ, heq⟩ := uniformStandardLifetime_metricComparison θ hθ hlt
  let L := Λ + 1
  have hL : 0 < L := by dsimp only [L]; linarith
  let ε := min εrad (min εscalar 1)
  have hε : 0 < ε := lt_min hεrad (lt_min hεscalar zero_lt_one)
  refine ⟨R, ε, hR, hε, ?_⟩
  intro b hb
  have hbpos : 0 < b := hR.trans_le hb
  obtain ⟨η, hη, hcut⟩ :=
    exists_cutoff_cap_survivor_partialDiffeomorph_or_discarded_tolerance_of_sectional_lower_bound
      hC (show 0 ≤ 2 * L * b by positivity) (show (0 : ℝ) < 1 / 128 by norm_num)
  refine ⟨η, hη, ?_⟩
  intro H i parameters record hold hdelta r D hr hrb hbD S t ht Ψ hΨ hinj q hq hclose
  let U := standardCapWindow D
  let g := (H.event i).terminal.metric
  let P := localPullMetric (scaleMetric q hq g) Ψ hΨ
  have hrpos : 0 < r := hR.trans_le hr
  have hball (a : ℝ) (ha : a ≤ b) : Metric.closedBall (0 : E3) a ⊆ U := by
    intro x hx
    have hn : ‖x‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change ‖x‖ < D + 1
    linarith
  obtain ⟨f, hf, _, hΨf, hfront, hsec⟩ := hboundary S t ht r hr U (hball r hrb)
    g Ψ hΨ hinj q hq (by
      intro x hx j hj
      have hn : ‖x.val‖ ≤ r := by
        have hh := Metric.isClosed_closedBall.frontier_subset hx
        simpa only [Metric.mem_closedBall, dist_zero_right] using hh
      exact (hclose x (hn.trans_lt (hrb.trans_lt hbD)) j hj).trans (min_le_left _ _))
  let K := Ψ '' {x : standardCapWindow D | ‖x.val‖ ≤ b}
  let A := Ψ '' {x : standardCapWindow D | ‖x.val‖ ≤ r}
  have hAK : A ⊆ K := image_mono fun _ hx => hx.trans hrb
  have hcompact : IsCompact A := by
    have hc : IsCompact {x : U | ‖x.val‖ ≤ r} := by
      have hcr : IsCompact {x : E3 | ‖x‖ ≤ r} := by
        simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : E3) r
      exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcr (by
        intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        apply hball r hrb
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx)
    exact hc.image hΨ.contMDiff.continuous
  have hconnected : IsPreconnected K := by
    have hc : IsPreconnected ((Subtype.val : U → E3) ⁻¹' Metric.closedBall 0 b) :=
      (convex_closedBall (0 : E3) b).isPreconnected.preimage_of_isOpenMap
        Subtype.val_injective U.isOpenEmbedding'.isOpenMap
        (fun x hx => ⟨⟨x, hball b le_rfl hx⟩, rfl⟩)
    have he : ((Subtype.val : U → E3) ⁻¹' Metric.closedBall 0 b) =
        {x : U | ‖x.val‖ ≤ b} := by ext x; simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq]
    rw [he] at hc
    exact hc.image Ψ hΨ.contMDiff.continuous.continuousOn
  have hinterior : (interior A).Nonempty := by
    let x : U := ⟨0, by change ‖(0 : E3)‖ < D + 1; simp only [norm_zero]; linarith⟩
    refine ⟨Ψ x, mem_interior.mpr ?_⟩
    refine ⟨Ψ '' {y : U | ‖y.val‖ < r}, image_mono (fun _ hy => le_of_lt (show ‖_‖ < r from hy)), ?_, ?_⟩
    · exact hΨ.isOpenMap _ (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)
    · exact mem_image_of_mem Ψ (by change ‖(0 : E3)‖ < r; simpa only [norm_zero] using hrpos)
  have hfront' : frontier A = range (Ψ ∘ f) := by
    simpa only [A, Metric.mem_closedBall, dist_zero_right] using hfront
  have hscalar' : ∀ x ∈ K, metricScalarAt g x ≤ C * q := by
    rintro _ ⟨x, hx, rfl⟩
    have hxD : ‖x.val‖ < D := (show ‖x.val‖ ≤ b from hx).trans_lt hbD
    have hh := hscalar U P S t ht x
      (fun j hj => (hclose x hxD j hj).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [metricScalarAt_localPull, metricScalarAt_scaleMetric] at hh
    have hlo := (le_abs_self _).trans hh
    rw [← div_eq_inv_mul, div_le_iff₀ hq] at hlo
    exact hlo
  have hupper : ∀ x : U, ‖x.val‖ < D → ∀ v : TangentSpace ThreeModel x,
      (scaleMetric q hq g).inner (Ψ x) (mfderiv ThreeModel ThreeModel Ψ x v)
        (mfderiv ThreeModel ThreeModel Ψ x v) ≤ L ^ 2 * StandardCap.metric.inner x.val v v := by
    intro x hx v
    have hm := metricDifference_abs_le P ((S.val.metric t).restrictOpen U)
      (StandardCap.metric.restrictOpen U) x v v
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at hm
    have hm' := hm.trans (mul_le_mul_of_nonneg_right
      ((hclose x hx 0 (by norm_num)).trans ((min_le_right _ _).trans (min_le_right _ _)))
      (metric_inner_self_nonneg _ _ _))
    have hs := (heq S t ht).2 x.val v |>.2
    have hLsq : Λ + 1 ≤ L ^ 2 := by dsimp only [L]; nlinarith
    have hnn := metric_inner_self_nonneg StandardCap.metric x.val v
    have hh := mul_le_mul_of_nonneg_right hLsq hnn
    change (scaleMetric q hq g).inner (Ψ x) (mfderiv ThreeModel ThreeModel Ψ x v)
      (mfderiv ThreeModel ThreeModel Ψ x v) ≤ _
    have hpoint : P.inner x v v ≤ (Λ + 1) * StandardCap.metric.inner x.val v v := by
      change |P.inner x v v - (S.val.metric t).inner x.val v v| ≤
        1 * StandardCap.metric.inner x.val v v at hm'
      linarith [(abs_le.mp hm').2]
    exact hpoint.trans hh
  have hdiam : ∀ x ∈ K, ∀ y ∈ K,
      riemannianEDistOf (scaleMetric q hq g) x y ≤ ENNReal.ofReal (2 * L * b) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hh := StandardCap.window_edist_map_le_of_metric_upper
      (scaleMetric q hq g) hL Ψ hΨ hinj hupper x y
      ((show ‖x.val‖ ≤ b from hx).trans_lt hbD) ((show ‖y.val‖ ≤ b from hy).trans_lt hbD)
    have hn : ‖x.val‖ + ‖y.val‖ ≤ 2 * b := by
      change ‖x.val‖ ≤ b at hx
      change ‖y.val‖ ≤ b at hy
      linarith
    exact hh.trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hn hL.le]))
  apply hcut H i parameters record hold hdelta (Ψ ∘ f) hΨf A K hAK hcompact hconnected
    hinterior hfront' q hq hscalar' hdiam
  intro z u v
  have heq : (1 / 128 : ℝ) * q = q / 128 := by ring
  rw [heq]
  exact hsec z u v


theorem exists_cutoff_cap_survivor_partialDiffeomorph_of_standard_metric_close
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ ∀ b : ℝ, R ≤ b →
      ∃ η : ℝ, 0 < η ∧ ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
        (parameters : CutoffParameters) (record : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, record.delta j ≤ η) → ∀ (r D : ℝ), R ≤ r → r ≤ b → b < D →
      ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 θ →
      ∀ (Ψ : standardCapWindow D → (H.event i).incoming.terminalRegularOpen)
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ), Injective Ψ →
      ∀ (q : ℝ) (hq : 0 < q),
      (∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ j ≤ 2,
        metricDerivNorm j (localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Ψ hΨ)
          ((S.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ ε) →
      ∀ (x : standardCapWindow D), ‖x.val‖ ≤ b → ∀ y : (H.stage i.succ).Carrier,
      (H.event i).RegularCrossing (Ψ x).val y →
      let K := Ψ '' {x : standardCapWindow D | ‖x.val‖ ≤ b}
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel
          (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
        K ⊆ F.source ∧
        (∀ y ∈ F.source, (H.event i).RegularCrossing y.val (F y)) ∧
        (∀ z : (H.event i).old, (H.event i).oldTerminal z ∈ F.source →
          F ((H.event i).oldTerminal z) = (H.event i).oldOutput z) ∧
        (∀ y ∈ F.source, ∀ v w : TangentSpace ThreeModel y,
          (H.event i).outputMetric.inner (F y)
            (mfderiv ThreeModel ThreeModel (F : _ → _) y v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) y w) =
              (H.event i).terminal.metric.inner y v w) ∧ F (Ψ x) = y := by
  obtain ⟨R, ε, hR, hε, hcrossing⟩ :=
    exists_cutoff_cap_survivor_partialDiffeomorph_or_discarded_of_standard_metric_close θ hθ hθ1
  refine ⟨R, ε, hR, hε, ?_⟩
  intro b hb
  obtain ⟨η, hη, hcrossing⟩ := hcrossing b hb
  refine ⟨η, hη, ?_⟩
  intro H i parameters record hold hdelta r D hr hrb hbD S t ht Ψ hΨ hinj q hq hclose x hx y hxy
  rcases hcrossing H i parameters record hold hdelta r D hr hrb hbD S t ht Ψ hΨ hinj
    q hq hclose with hsurvive | hdiscard
  · obtain ⟨F, hsource, hcross, holdF, hmetric⟩ := hsurvive
    refine ⟨F, hsource, hcross, holdF, hmetric, ?_⟩
    exact (H.event i).regularCrossing_right_unique
      (hcross (Ψ x) (hsource (mem_image_of_mem Ψ hx))) hxy
  · obtain ⟨z, hz, d, hpres⟩ := hdiscard (Ψ x) (mem_image_of_mem Ψ hx)
    obtain ⟨w, _, hw, _⟩ := hxy
    have heq : z = w.val := Subtype.ext (hz.trans hw.symm)
    rw [heq, (H.event i).oldOutput_eq] at hpres
    cases hpres


theorem exists_cutoff_cap_survivor_partialDiffeomorph_of_window_flow_curvature_bound
    {E H₀ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
    (θ K : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ b : ℝ, R ≤ b →
      ∃ D₀ ε₀ η : ℝ, b + 2 < D₀ ∧ 0 < ε₀ ∧ 0 < η ∧ ∃ m₀ : ℕ,
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : Geometry.Neck.normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      D₀ ≤ D → m₀ ≤ m → ζ ≤ ε₀ →
      ∀ (T : ℝ) (hT : 0 < T), T ≤ θ →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0 T hT.le),
      IsSolutionOn S → S.base.metric 0 = w.windowMetric →
      (∀ (y : standardCapWindow D) (j l : Fin (Module.finrank ℝ ThreeSpace)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
          (fun z : ℝ × standardCapWindow D =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) y z.2 j l)
          (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) →
      (∀ t ∈ Icc 0 T, ∀ y : standardCapWindow D, nablaKRm04NormSqIntrinsic S 0 t y ≤ K) →
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (record : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, record.delta j ≤ η) →
      ∀ (Ψ : standardCapWindow D → (H.event i).incoming.terminalRegularOpen)
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ), Injective Ψ →
      ∀ (q : ℝ) (hq : 0 < q),
      S.base.metric T = localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Ψ hΨ →
      ∀ (x : standardCapWindow D), ‖x.val‖ ≤ b → ∀ y : (H.stage i.succ).Carrier,
      (H.event i).RegularCrossing (Ψ x).val y →
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel
          (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
        Ψ '' {x : standardCapWindow D | ‖x.val‖ ≤ b} ⊆ F.source ∧
        (∀ z ∈ F.source, (H.event i).RegularCrossing z.val (F z)) ∧
        (∀ z : (H.event i).old, (H.event i).oldTerminal z ∈ F.source →
          F ((H.event i).oldTerminal z) = (H.event i).oldOutput z) ∧
        (∀ z ∈ F.source, ∀ v w : TangentSpace ThreeModel z,
          (H.event i).outputMetric.inner (F z)
            (mfderiv ThreeModel ThreeModel (F : _ → _) z v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) z w) =
              (H.event i).terminal.metric.inner z v w) ∧ F (Ψ x) = y := by
  obtain ⟨R, ε, hR, hε, hcross⟩ :=
    exists_cutoff_cap_survivor_partialDiffeomorph_of_standard_metric_close θ hθ.le hθ1
  refine ⟨R, hR, ?_⟩
  intro b hb
  obtain ⟨η, hη, hcross⟩ := hcross b hb
  obtain ⟨D₀, _, hDb, m₀, ε₀, hε₀, hcompare⟩ :=
    StandardCap.exists_uniform_standard_cap_comparison_on_bounded_intervals_of_curvature_bound
      (I := I) θ K (b + 2) ε hθ hθ1 hε 2
  refine ⟨D₀, ε₀, η, hDb, hε₀, hη, m₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA D m ζ w hD hm hζ T hT hTθ S hS hzero hgram hcurv
    H i parameters record hold hdelta Ψ hΨ hinj q hq hterminal x hx y hxy
  obtain ⟨Q, _, hclose⟩ := hcompare w hD hm hζ T hT hTθ S hS hzero hgram hcurv
  have hsmall : b + 1 ≤ D := by linarith
  let hsub : standardCapWindow (b + 1) ≤ standardCapWindow D :=
    fun z hz => hz.trans_le (add_le_add hsmall (le_refl 1))
  let inc : standardCapWindow (b + 1) → standardCapWindow D := Opens.inclusion hsub
  have hinc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc := fun z =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : standardCapWindow (b + 1) => hsub z.property)
      (isLocalDiffeomorph_subtype_val (standardCapWindow (b + 1)) z)
  let Φ := Ψ ∘ inc
  have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ := isLocalDiffeomorph_comp hΨ hinc
  have hΦinj : Injective Φ := hinj.comp (fun _ _ h => Subtype.ext (congrArg (fun z : standardCapWindow D => z.val) h))
  have hlocal : localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Φ hΦ =
      (S.base.metric T).restrictOpenOfSubset hsub := by
    rw [hterminal]
    exact (localPullMetric_restrictOpenOfSubset_eq _ hsub Ψ hΨ Φ hΦ rfl).symm
  have hcompact : IsCompact {y : standardCapWindow D | ‖y.val‖ ≤ b + 2} := by
    have hc : IsCompact {y : ThreeSpace | ‖y‖ ≤ b + 2} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) (b + 2)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro z hz
      refine ⟨⟨z, ?_⟩, rfl⟩
      change ‖z‖ < D + 1
      change ‖z‖ ≤ b + 2 at hz
      linarith)
  have hcp : ∀ z : standardCapWindow (b + 1), ‖z.val‖ < b + 1 → ∀ j ≤ 2,
      metricDerivNorm j (localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Φ hΦ)
        ((Q.val.metric T).restrictOpen (standardCapWindow (b + 1)))
        (StandardCap.metric.restrictOpen (standardCapWindow (b + 1))) z ≤ ε := by
    intro z hz j hj
    rw [hlocal, ← SmoothRiemannianMetric.restrictOpen_flat _ hsub,
      ← SmoothRiemannianMetric.restrictOpen_flat _ hsub, metricDerivNorm_flat]
    have hn : ‖(inc z).val‖ ≤ b + 2 := by change ‖z.val‖ ≤ b + 2; linarith
    exact (derivNorm_le_sup hcompact hj _ _ _ hn).trans (hclose T ⟨hT.le, le_rfl⟩).le
  let z : standardCapWindow (b + 1) := ⟨x.val, by change ‖x.val‖ < b + 1 + 1; linarith⟩
  have heq : inc z = x := Subtype.ext rfl
  obtain ⟨F, hsource, hcrossF, holdF, hmetric, hpoint⟩ := hcross H i parameters record hold hdelta
    R (b + 1) le_rfl hb (by linarith) Q T ⟨hT.le, hTθ⟩ Φ hΦ hΦinj q hq hcp
    z hx y (by simpa only [Φ, Function.comp_apply, heq] using hxy)
  refine ⟨F, ?_, hcrossF, holdF, hmetric, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    let v' : standardCapWindow (b + 1) := ⟨v.val, by change ‖v.val‖ < b + 1 + 1; change ‖v.val‖ ≤ b at hv; linarith⟩
    exact hsource ⟨v', hv, congrArg Ψ (Subtype.ext rfl)⟩
  · simpa only [Φ, Function.comp_apply, heq] using hpoint



open DifferentialGeometry.Tensor0SBundle in
theorem exists_cutoff_cap_survivor_partialDiffeomorph_of_window_flow_tip_ricci_lower_bound
    (T K κ : ℝ) (hκ : 0 < κ) :
    ∀ D : ℝ, 0 < D + 1 → ∃ η : ℝ, 0 < η ∧
      ∀ (J : RealTimeInterval) (θ : ℝ), θ ≤ T →
      Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
      ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
      IsSolutionOn S →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        (S.base.metric 0).inner x v v ≤ (3 / 2 : ℝ) * StandardCap.metric.inner x.val v v) →
      (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      ∀ τ ∈ Icc 0 θ,
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
        (record : GeometricCutoffRecord H i parameters),
      (H.event i).old = (H.event i).transition.trace.retainedCore →
      (∀ j, record.delta j ≤ η) →
      ∀ (Ψ : standardCapWindow D → (H.event i).incoming.terminalRegularOpen)
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ),
      ∀ (q : ℝ) (hq : 0 < q),
      S.base.metric τ = localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Ψ hΨ →
      ∀ z : standardCapWindow D,
      (∀ v : TangentSpace ThreeModel z,
        κ * (S.base.metric τ).inner z v v ≤ ricciTensor (S.base.metric τ) z v v) →
      ∀ x : standardCapWindow D, ∀ y : (H.stage i.succ).Carrier,
      (H.event i).RegularCrossing (Ψ x).val y →
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel
          (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
        range Ψ ⊆ F.source ∧
        (∀ w ∈ F.source, (H.event i).RegularCrossing w.val (F w)) ∧
        (∀ w : (H.event i).old, (H.event i).oldTerminal w ∈ F.source →
          F ((H.event i).oldTerminal w) = (H.event i).oldOutput w) ∧
        (∀ w ∈ F.source, ∀ v z : TangentSpace ThreeModel w,
          (H.event i).outputMetric.inner (F w)
            (mfderiv ThreeModel ThreeModel (F : _ → _) w v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) w z) =
              (H.event i).terminal.metric.inner w v z) ∧ F (Ψ x) = y := by
  obtain ⟨L, hL, hdist⟩ := StandardCap.exists_uniform_window_flow_edist_bound_on_bounded_horizon T K
  let C := 9 * Real.sqrt K + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  intro D hD
  obtain ⟨η, hη, hprotect⟩ := exists_cutoff_protection_tolerance_of_ricci_lower_bound
    hC (show 0 ≤ 2 * L * (D + 1) by positivity) hκ
  refine ⟨η, hη, ?_⟩
  intro J θ hθ hcarrier hregular S hS hinit hcurv τ hτ H i parameters record hold hdelta
    Ψ hΨ q hq hmetric z hRic x y hcross
  let g := (H.event i).terminal.metric
  let h := scaleMetric q hq g
  have hscalar : ∀ w ∈ range Ψ, metricScalarAt g w ≤ C * q := by
    rintro _ ⟨w, rfl⟩
    have hb := scalar_abs_le_rm (S.base.metric τ) w
    have hn : Real.sqrt (normSq0S (S.base.metric τ) w 4 (metricRm04At (S.base.metric τ) w)) ≤
        Real.sqrt K := by
      apply Real.sqrt_le_sqrt
      exact hcurv τ hτ w
    have hdim : Module.finrank ℝ (TangentSpace ThreeModel w) = 3 := by
      change Module.finrank ℝ ThreeSpace = 3
      simp [ThreeSpace]
    rw [hdim] at hb
    norm_num only [Nat.cast_ofNat, show (3 : ℝ)^2=9 by norm_num] at hb
    have hb' : metricScalarAt (S.base.metric τ) w ≤ C := by
      dsimp only [C]
      have hh := (le_abs_self _).trans hb
      nlinarith
    rw [hmetric, metricScalarAt_localPull, metricScalarAt_scaleMetric, ← div_eq_inv_mul,
      div_le_iff₀ hq] at hb'
    exact hb'
  have hdiam : ∀ v ∈ range Ψ, ∀ w ∈ range Ψ,
      riemannianEDistOf h v w ≤ ENNReal.ofReal (2 * L * (D + 1)) := by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    have hp := edistOf_le_of_quad_of_localDiffeomorph (S.base.metric τ) h Ψ hΨ
      (by norm_num : (0 : ℝ) < 1) (by
        intro a z
        rw [hmetric, localPullMetric_inner]
        simp only [one_mul]
        rfl) v w
    have hh := hdist D J θ hθ hcarrier hregular S hS hinit hcurv τ hτ v w
    simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hp
    have hv : ‖v.val‖ < D + 1 := v.property
    have hw : ‖w.val‖ < D + 1 := w.property
    exact hp.trans (hh.trans (ENNReal.ofReal_le_ofReal (by nlinarith)))
  have hric : ∀ v : TangentSpace ThreeModel (Ψ z),
      κ * q * g.inner (Ψ z) v v ≤ ricciTensor g (Ψ z) v v := by
    intro v
    obtain ⟨w, hw⟩ := (hΨ.mfderivToContinuousLinearEquiv (by simp) z).surjective v
    have hh := hRic w
    rw [hmetric, localPullMetric_inner, ricciTensor_localPull, ricciTensor_scaleMetric,
      scaleMetric_inner] at hh
    change κ * (q * g.inner (Ψ z) (mfderiv ThreeModel ThreeModel Ψ z w)
      (mfderiv ThreeModel ThreeModel Ψ z w)) ≤
      ricciTensor g (Ψ z) (mfderiv ThreeModel ThreeModel Ψ z w)
        (mfderiv ThreeModel ThreeModel Ψ z w) at hh
    rw [show mfderiv ThreeModel ThreeModel Ψ z w = v from hw] at hh
    simpa only [mul_assoc] using hh
  have hconn : IsPreconnected (range Ψ) := by
    let : PreconnectedSpace (standardCapWindow D) := by
      apply isPreconnected_iff_preconnectedSpace.mp
      change IsPreconnected {x : ThreeSpace | ‖x‖ < D + 1}
      simpa only [Metric.ball, dist_zero_right] using (convex_ball (0 : ThreeSpace) (D + 1)).isPreconnected
    exact isPreconnected_range hΨ.contMDiff.continuous
  have hOld := hprotect H i parameters record hold hdelta (range Ψ) hconn q hq
    hscalar hdiam (Ψ z) (mem_range_self z) hric (Ψ x) (mem_range_self x) y hcross
  let W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨{w | w.val ∈ interior (Subtype.val '' (H.event i).old)},
      isOpen_interior.preimage continuous_subtype_val⟩
  obtain ⟨F, hsource, hFcross, hFold, hFmetric⟩ :=
    (H.event i).exists_survivor_partialDiffeomorph W ⟨Ψ x, hOld (Ψ x) (mem_range_self x)⟩ (fun _ hw => hw)
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    exact hOld
  · intro w hw
    apply hFcross
    rwa [hsource] at hw
  · intro w hw
    apply hFold
    rwa [hsource] at hw
  · intro w hw
    apply hFmetric
    rwa [hsource] at hw
  · apply (H.event i).regularCrossing_right_unique _ hcross
    apply hFcross
    exact hOld (Ψ x) (mem_range_self x)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
