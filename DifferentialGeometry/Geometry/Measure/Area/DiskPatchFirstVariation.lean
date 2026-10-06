import DifferentialGeometry.Geometry.Measure.Area.CompactDomainMetricDerivative
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import DifferentialGeometry.Geometry.Metric.Family.Stationary
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskReflectionDifferential
import DifferentialGeometry.Analysis.Integration.Measure.ComplexNullLines

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem density_comp_conj (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    riemannianAreaDensity g (U ∘ conj) z = riemannianAreaDensity g U (conj z) := by
  change tangentTwoJacobian g (diskMapPartial (U ∘ conj) z 1)
    (diskMapPartial (U ∘ conj) z Complex.I) =
      tangentTwoJacobian g (diskMapPartial U (conj z) 1)
        (diskMapPartial U (conj z) Complex.I)
  rw [diskMapPartial_comp_conj_one, diskMapPartial_comp_conj_I]
  simp only [tangentTwoJacobian, map_neg, _root_.neg_apply, neg_neg, neg_sq,
    Function.comp_apply]

variable [FiniteDimensional ℝ E] [T3Space M]

/-- Differentiate the actual full folded patch, with its lower half represented
by the literal reflection of the same disk extension. Both quotients are
integrable before the two integrals are added. Neither seam differentiability,
normality, minimality, nor an area-derivative identity is an input. -/
theorem hasDerivAt_riemannianArea_isotopy_of_halfDisk_immersion
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦzero : ∀ x, Φ 0 x = x) (p r : ℝ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hi : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hir : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) z)) :
    let U := diskExtension u
    let S := Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}
    let G := fun t => Diffeomorph.pullbackMetric g (Φ t)
    IntegrableOn (diskMapGramMetricVariationDensity G 0 U) S ∧
      IntegrableOn (diskMapGramMetricVariationDensity G 0 (U ∘ conj)) S ∧
      HasDerivAt (fun t => riemannianArea g ((Φ t) ∘ U) (Metric.closedBall (p : ℂ) r))
        ((∫ z in S, diskMapGramMetricVariationDensity G 0 U z) +
          ∫ z in S, diskMapGramMetricVariationDensity G 0 (U ∘ conj) z) 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let U : ℂ → M := diskExtension u
  let S : Set ℂ := Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}
  let T : Set ℂ := Metric.ball (p : ℂ) r ∩ {z : ℂ | z.im < 0}
  let K : Set ℂ := Metric.closedBall (p : ℂ) r
  let G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M :=
    fun t => Diffeomorph.pullbackMetric g (Φ t)
  let D := RealTimeInterval.univ 0
  have hS : IsOpen S := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hT : IsOpen T := Metric.isOpen_ball.inter
    (isOpen_lt Complex.continuous_im continuous_const)
  have hSK : S ⊆ K := inter_subset_left.trans Metric.ball_subset_closedBall
  have hTK : T ⊆ K := inter_subset_left.trans Metric.ball_subset_closedBall
  have hconjdist (z : ℂ) : dist (conj z) (p : ℂ) = dist z (p : ℂ) := by
    simpa using Complex.dist_conj_conj z (p : ℂ)
  have hpre : (conj : ℂ → ℂ) ⁻¹' T = S := by
    ext z
    simp only [T, S, mem_preimage, mem_inter_iff, Metric.mem_ball, mem_ofPred_eq,
      hconjdist, Complex.conj_im, neg_lt_zero]
  have hconjT {z : ℂ} (hz : z ∈ T) : conj z ∈ S := by
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, hconjdist] using hz.1
    · change 0 < (conj z).im
      simpa only [Complex.conj_im] using neg_pos.mpr (show z.im < 0 from hz.2)
  have hinvolution : (U ∘ conj) ∘ conj = U := by
    funext z
    simp only [Function.comp_apply, starRingEnd_self_apply]
  have hiT {z : ℂ} (hz : z ∈ T) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    have heq := mfderiv_comp_planeLinearEquiv (E := E) (U ∘ conj) Complex.conjCLE z
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ((U ∘ conj) ∘ conj) z = _ at heq
    rw [hinvolution] at heq
    rw [heq]
    exact (hir (conj z) (hconjT hz)).comp Complex.conjCLE.injective
  have hdT {z : ℂ} (hz : z ∈ T) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z := by
    have hd := ((hUr (conj z) (hconjT hz)).contMDiffAt
      (hS.mem_nhds (hconjT hz))).mdifferentiableAt (by norm_num)
    have hc := hd.comp z Complex.conjCLE.differentiableAt.mdifferentiableAt
    change MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ((U ∘ conj) ∘ conj) z at hc
    rwa [hinvolution] at hc
  have hnosphere : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (p : ℂ) r := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (p : ℂ) r using 1
    congr 1
    ext z
    simp
  have hcover : K =ᵐ[volume] S ∪ T := by
    filter_upwards [hnosphere, ae_complex_im_ne 0] with z hz hzi
    apply propext
    change dist z (p : ℂ) ≤ r ↔
      (dist z (p : ℂ) < r ∧ 0 < z.im) ∨ (dist z (p : ℂ) < r ∧ z.im < 0)
    constructor
    · intro hk
      have hb : dist z (p : ℂ) < r := lt_of_le_of_ne hk hz
      rcases lt_or_gt_of_ne hzi with hm | hp
      · exact Or.inr ⟨hb, hm⟩
      · exact Or.inl ⟨hb, hp⟩
    · rintro (⟨hb, _⟩ | ⟨hb, _⟩) <;> exact le_of_lt hb
  have hgood : ∀ᵐ z ∂volume.restrict K, z ∈ S ∨ z ∈ T := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_restrict_of_ae hcover] with z hz heq
    change z ∈ S ∪ T
    simpa only [← heq] using hz
  have hiAE : ∀ᵐ z ∂volume.restrict K,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
    hgood.mono (fun z hz => hz.elim (hi z) (fun ht => hiT ht))
  have hdAE : ∀ᵐ z ∂volume.restrict K, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z := by
    apply hgood.mono
    intro z hz
    rcases hz with hz | hz
    · exact ((hU z hz).contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by norm_num)
    · exact hdT hz
  have hG : MetricFamilySmoothOn D G :=
    metricFamilySmoothOn_parameterPullback (metricFamilySmoothOn_stationary g D)
      isOpen_univ hΦ.contMDiffOn D rfl (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have ht₀ : D.regular ∈ 𝓝 (0 : ℝ) := Filter.univ_mem
  have hΦ₀ : Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞ := by
    ext x
    exact hΦzero x
  have hG₀ : G 0 = g := by
    dsimp only [G]
    rw [hΦ₀, Diffeomorph.pullbackMetric_refl]
  have hcont : Continuous U := u.continuous.comp diskRetraction_lipschitz.continuous
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (p : ℂ) r).measure_lt_top.ne
  have hJ : IntegrableOn (riemannianAreaDensity (G 0) U) K := by
    rw [hG₀]
    exact integrableOn_riemannianAreaDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g huLip) K
  obtain ⟨hQ, hd⟩ := hasDerivAt_riemannianArea_metric_of_ae_immersion hG ht₀
    hcont measurableSet_closedBall (isCompact_closedBall (p : ℂ) r) Subset.rfl hJ hiAE
  have harea (t : ℝ) : riemannianArea (G t) U K = riemannianArea g ((Φ t) ∘ U) K := by
    apply integral_congr_ae
    exact hdAE.mono (fun z hz => riemannianAreaDensity_pullback g (Φ t) hz)
  have hQconj {z : ℂ} (hz : z ∈ S) :
      diskMapGramMetricVariationDensity G 0 (U ∘ conj) z =
        diskMapGramMetricVariationDensity G 0 U (conj z) := by
    have hzt : conj z ∈ T := by
      change z ∈ (conj : ℂ → ℂ) ⁻¹' T
      rwa [hpre]
    have hd₁ := hasDerivAt_diskMapAreaDensity_metric_of_immersion hG ht₀ (hiT hzt)
    have hd₂ := hasDerivAt_diskMapAreaDensity_metric_of_immersion hG ht₀ (hir z hz)
    exact hd₂.unique (hd₁.congr_of_eventuallyEq
      (Eventually.of_forall (fun t => density_comp_conj (G t) U z)))
  have hQS : IntegrableOn (diskMapGramMetricVariationDensity G 0 U) S := hQ.mono_set hSK
  have hQT : IntegrableOn (diskMapGramMetricVariationDensity G 0 U) T := hQ.mono_set hTK
  have hQr : IntegrableOn (diskMapGramMetricVariationDensity G 0 (U ∘ conj)) S := by
    have hc := (Complex.conjLIE.measurePreserving.integrableOn_comp_preimage
      Complex.conjLIE.toMeasurableEquiv.measurableEmbedding).mpr hQT
    change IntegrableOn (fun z => diskMapGramMetricVariationDensity G 0 U (conj z))
      ((conj : ℂ → ℂ) ⁻¹' T) at hc
    rw [hpre] at hc
    exact hc.congr_fun (fun z hz => (hQconj hz).symm) hS.measurableSet
  have hreflect : (∫ z in S, diskMapGramMetricVariationDensity G 0 (U ∘ conj) z) =
      ∫ z in T, diskMapGramMetricVariationDensity G 0 U z := by
    calc
      _ = ∫ z in S, diskMapGramMetricVariationDensity G 0 U (conj z) :=
        setIntegral_congr_fun hS.measurableSet (fun _ hz => hQconj hz)
      _ = _ := by
        have he := Complex.conjLIE.measurePreserving.setIntegral_preimage_emb
          Complex.conjLIE.toMeasurableEquiv.measurableEmbedding
          (diskMapGramMetricVariationDensity G 0 U) T
        change (∫ z in (conj : ℂ → ℂ) ⁻¹' T,
          diskMapGramMetricVariationDensity G 0 U (conj z)) = _ at he
        simpa only [hpre] using he
  have hdisj : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz ht
    have hp : 0 < z.im := hz.2
    have hm : z.im < 0 := ht.2
    exact lt_asymm hp hm
  have hsplit : (∫ z in K, diskMapGramMetricVariationDensity G 0 U z) =
      (∫ z in S, diskMapGramMetricVariationDensity G 0 U z) +
        ∫ z in S, diskMapGramMetricVariationDensity G 0 (U ∘ conj) z := by
    calc
      _ = ∫ z in S ∪ T, diskMapGramMetricVariationDensity G 0 U z :=
        setIntegral_congr_set hcover
      _ = (∫ z in S, diskMapGramMetricVariationDensity G 0 U z) +
          ∫ z in T, diskMapGramMetricVariationDensity G 0 U z :=
        setIntegral_union hdisj hT.measurableSet hQS hQT
      _ = _ := by rw [hreflect]
  rw [hsplit] at hd
  refine ⟨hQS, hQr, ?_⟩
  exact hd.congr_of_eventuallyEq (Eventually.of_forall (fun t => (harea t).symm))

end DifferentialGeometry.Geometry
