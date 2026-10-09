import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalInitialSpatialCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RicciRayleigh
import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullbackCurvature
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

theorem exists_uniform_initial_tip_ricci_lower_bound_of_local_curvature
    (T K : ℝ) (hT : 0 < T) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η ≤ T ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      65 ≤ D → 4 ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 64 →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ t ∈ Icc 0 (min η θ), ∀ (x : standardCapWindow D), x.val = 0 →
          ∀ v : TangentSpace ThreeModel x,
            (1 / 2 : ℝ) * (L.base.metric t).inner x v v ≤ ricciTensor (L.base.metric t) x v v := by
  obtain ⟨η, ε₀, hη, hηT, hε₀, hεhalf, hclose⟩ :=
    exists_uniform_initial_metric_closeness_of_local_curvature 65 1 T K (1 / 1444)
      (by norm_num) (by norm_num) hT (by norm_num) 2
  refine ⟨η, ε₀, hη, hηT, hε₀, hεhalf, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hD hm hζ
    J θ hθ hθT hcarrier hregular L hL hzero hgram hcurv t ht x hx v
  let hsub : standardCapWindow 65 ≤ standardCapWindow D :=
    fun y hy => hy.trans_le (add_le_add hD (le_refl 1))
  let inc : standardCapWindow 65 → standardCapWindow D := Opens.inclusion hsub
  have hi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      inc (contMDiff_inclusion hsub) (fun y => by
        change Function.Injective (mfderiv ThreeModel ThreeModel (Opens.inclusion hsub) y)
        rw [mfderiv_opens_incl]
        exact Function.injective_id) rfl
  let S := L.localPullback inc hi
  have heq (s : ℝ) : S.base.metric s = (L.base.metric s).restrictOpenOfSubset hsub := by
    apply SmoothRiemannianMetric.ext_inner
    intro y a b
    change (localPullMetric (L.base.metric s) inc hi).inner y a b = _
    rw [localPullMetric_inner]
    simp only [inc, mfderiv_opens_incl]
    rfl
  have hSzero : S.base.metric 0 = (w.restrictWindow (by norm_num : (0 : ℝ) < 65) hD).windowMetric := by
    rw [heq, hzero, CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
  have hSgram := L.localPullback_chartGramMatrix_joint_contMDiffOn inc hi (Icc 0 θ) hgram
  have hScurv : ∀ s ∈ Icc 0 θ, ∀ y : standardCapWindow 65, ‖y.val‖ ≤ 64 * 1 →
      nablaKRm04NormSqIntrinsic S 0 s y ≤ K := by
    intro s hs y hy
    have he : nablaKRm04NormSqIntrinsic S 0 s y = nablaKRm04NormSqIntrinsic L 0 s (inc y) := by
      simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
      exact normSq0S_metricRm04At_localPullMetric (L.base.metric s) inc hi y
    rw [he]
    exact hcurv s hs (inc y) (by simpa using hy)
  have hnear := hclose (w.restrictWindow (by norm_num : (0 : ℝ) < 65) hD)
    hm hζ J θ hθ hθT hcarrier hregular S (hL.localPullback inc hi) hSzero hSgram hScurv t ht
  let y : standardCapWindow 65 := ⟨0, by change ‖(0 : ThreeSpace)‖ < 65 + 1; norm_num⟩
  have hyx : inc y = x := Subtype.ext hx.symm
  cases hyx
  have hjets (j : ℕ) (hj : j ≤ 2) :
      metricDerivNorm j (S.base.metric t) (metric.restrictOpen (standardCapWindow 65))
        (metric.restrictOpen (standardCapWindow 65)) y ≤ 1 / 1444 := by
    rw [standardCapMetric_eq_metric] at hnear
    exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hnear hj (by change ‖(0 : ThreeSpace)‖ ≤ 1; norm_num)).le
  have hRic (a : TangentSpace ThreeModel y) :
      1 * (metric.restrictOpen (standardCapWindow 65)).inner y a a ≤
        ricciTensor (metric.restrictOpen (standardCapWindow 65)) y a a := by
    rw [DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen, mfderiv_subtype_val_apply,
      SmoothRiemannianMetric.restrictOpen_inner]
    change 1 * metric.inner 0 a a ≤ ricciTensor metric 0 a a
    exact (one_mul _).le.trans (ricciTensor_zero (show ThreeSpace from a) (show ThreeSpace from a)).symm.le
  let vy : TangentSpace ThreeModel y := v
  have hlow := ricciTensor_lower_bound_of_small_metric_derivatives
    (S.base.metric t) (metric.restrictOpen (standardCapWindow 65)) y
    (by norm_num : (1 / 1444 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hjets hRic (by norm_num [ThreeSpace]) vy
  change (1 / 2 : ℝ) * (localPullMetric (L.base.metric t) inc hi).inner y vy vy ≤
    ricciTensor (localPullMetric (L.base.metric t) inc hi) y vy vy at hlow
  rw [localPullMetric_inner, ricciTensor_localPull] at hlow
  have hd : mfderiv ThreeModel ThreeModel inc y vy = v := by
    change mfderiv ThreeModel ThreeModel (Opens.inclusion hsub) y vy = v
    rw [mfderiv_opens_incl]
    rfl
  rw [hd] at hlow
  exact hlow

end DifferentialGeometry.PDE.RicciFlow.StandardCap
