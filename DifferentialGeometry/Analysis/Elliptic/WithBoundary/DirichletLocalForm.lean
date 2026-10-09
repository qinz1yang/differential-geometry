import DifferentialGeometry.Analysis.Integration.Lp.BilinearForm
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSobolev
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

open Bundle Manifold Set
open scoped ContDiff Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric I_hs M} :
    SeminormedAddCommGroup
      (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

omit [T2Space M] [CompactSpace M] in
theorem weightedInvGramOnEuclid_div_density_ratio
    (q h : SmoothRiemannianMetric I_hs M) (α : M)
    (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd)
    (hz : z ∈ chartTargetEuclid (I := I_hs) α) :
    weightedInvGramOnEuclid h α i j z / (densityOnEuclid h α z / densityOnEuclid q α z) =
      densityOnEuclid q α z * invGramOnEuclid h α i j z := by
  have hρ : densityOnEuclid h α z ≠ 0 := (densityOnEuclid_pos h α hz).ne'
  have hσ : densityOnEuclid q α z ≠ 0 := (densityOnEuclid_pos q α hz).ne'
  unfold weightedInvGramOnEuclid
  field_simp

theorem exists_local_dirichlet_bilinear_form_family
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    let Dp := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    ∃ F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ,
      (∀ t u v, F t u v = ∑ i, ∑ j, ∫ z in Ω,
        Dp i u z * (densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z) * Dp j v z) ∧
      (∀ u v, AEStronglyMeasurable (fun t => F t u v) (volume.restrict J)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ t ∂volume.restrict J, ‖F t‖ ≤ C := by
  intro Dp
  let c := fun t i j z => densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z
  have htarget : closure Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  have hcstat (t i j) : ContinuousOn (c t i j) (closure Ω) :=
    ((densityOnEuclid_contDiffOn q α).continuousOn.mono htarget).mul
      ((invGramOnEuclid_contDiffOn (G.metric t) α i j).continuousOn.mono htarget)
  have hcmem (t i j) : MemLp (c t i j) ∞ (volume.restrict Ω) :=
    (hcstat t i j).memLp_top_of_subset_isCompact hΩc hΩ.measurableSet subset_closure
  have hcjoint (i j) : ContinuousOn (fun p : ℝ × EuStd => c p.1 i j p.2) (J ×ˢ closure Ω) :=
    (((densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => htarget hp.2)).mul
        (invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
  have hcmeas (i j) : AEStronglyMeasurable (fun p : ℝ × EuStd => c p.1 i j p.2)
      ((volume.restrict J).prod (volume.restrict Ω)) := by
    have h := (hcjoint i j).memLp_top_of_subset_isCompact (hJc.prod hΩc)
      (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.aestronglyMeasurable
  have hcp : ContinuousOn
      (fun p : ℝ × EuStd => fun i j : Fin (Module.finrank ℝ EuN) => c p.1 i j p.2)
      (J ×ˢ closure Ω) := continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hcjoint i j
  obtain ⟨C, hCb⟩ := (hJc.prod hΩc).exists_bound_of_continuousOn hcp
  have hbound : ∀ᵐ t ∂volume.restrict J, ∀ i j, ∀ᵐ z ∂volume.restrict Ω,
      ‖c t i j z‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem hJc.measurableSet] with t ht
    intro i j
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
    exact ((norm_le_pi_norm (fun j => c t i j z) j).trans
      ((norm_le_pi_norm (fun i j => c t i j z) i).trans
        (hCb (t, z) ⟨ht, subset_closure hz⟩))).trans (le_max_left _ _)
  let : IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  obtain ⟨F, hF, hFm, hFb⟩ := MeasureTheory.exists_bilinear_integral_weight_mul_family
    Dp c hcmem hcmeas (le_max_right C 0) hbound
  refine ⟨F, hF, hFm, ∑ i, ∑ j, max C 0 * ‖Dp i‖ * ‖Dp j‖, ?_, hFb⟩
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

omit [T2Space M] [CompactSpace M] in
private theorem exists_uniform_density_inv_gram_sum_lower_bound
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {K : Set EuStd} (hKc : IsCompact K)
    (hKs : K ⊆ chartTargetEuclid (I := I_hs) α) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ z ∈ K,
      ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
        c * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
          ξ i * (densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z) * ξ j := by
  let A := fun p : ℝ × EuStd => Matrix.of (fun i j : Fin (Module.finrank ℝ EuN) =>
    densityOnEuclid q α p.2 * invGramOnEuclid (G.metric p.1) α i j p.2)
  have hAcont (i j) : ContinuousOn (fun p => A p i j) (J ×ˢ K) := by
    exact (((densityOnEuclid_contDiffOn q α).continuousOn.comp
      continuous_snd.continuousOn (fun p hp => hKs hp.2)).mul
      ((invGramOnEuclid_family_continuousOn hG hJ α i j).mono
        (prod_mono Subset.rfl hKs)))
  have hApos (p : ℝ × EuStd) (hp : p ∈ J ×ˢ K) : (A p).PosDef :=
    (invGramOnEuclid_posDef (G.metric p.1) α (hKs hp.2)).smul
      (densityOnEuclid_pos q α (hKs hp.2))
  obtain ⟨c, hc, hb⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound
    (hJc.prod hKc) A hAcont hApos
  refine ⟨c, hc, ?_⟩
  intro t ht z hz ξ
  have h := hb (t, z) ⟨ht, hz⟩ (WithLp.toLp 2 ξ)
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply,
    Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum,
    A, Matrix.of_apply, mul_assoc] using h


private theorem integral_bilinear_weight_lower_bound
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z}
    (f : ι → Lp ℝ 2 μ) (a : ι → ι → Z → ℝ)
    (ha : ∀ i j, MemLp (a i j) ∞ μ) {c : ℝ}
    (hbound : ∀ᵐ z ∂μ, ∀ ξ : ι → ℝ,
      c * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, ξ i * a i j z * ξ j) :
    c * ∑ i, ‖f i‖ ^ 2 ≤ ∑ i, ∑ j, ∫ z, f i z * a i j z * f j z ∂μ := by
  have hs (i) : Integrable (fun z => (f i z) ^ 2) μ := by
    have h := (Lp.memLp (f i)).integrable_mul (Lp.memLp (f i))
    change Integrable (fun z => f i z * f i z) μ at h
    simpa only [sq] using h
  have hp (i j) : Integrable (fun z => f i z * a i j z * f j z) μ :=
    integrable_weight_mul_lp (a i j) (ha i j) (f i) (f j)
  have hi := integral_mono_ae
    ((integrable_finsetSum Finset.univ (fun i _ => hs i)).const_mul c)
    (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j)))
    (hbound.mono fun z hz => hz (fun i => f i z))
  have hnorm (i) : ∫ z, (f i z) ^ 2 ∂μ = ‖f i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [Real.inner_apply, sq]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hs i)] at hi
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hp i j))] at hi
  simp_rw [integral_finsetSum _ (fun j _ => hp _ j), hnorm] at hi
  exact hi

theorem exists_local_dirichlet_integral_lower_bound
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    let Dp := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ v : H1ComplDirichlet q,
      c * ∑ i, ‖Dp i v‖ ^ 2 ≤ ∑ i, ∑ j, ∫ z in Ω,
        Dp i v z * (densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z) * Dp j v z := by
  intro Dp
  have htarget : closure Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  obtain ⟨c, hc, hb⟩ := exists_uniform_density_inv_gram_sum_lower_bound
    q hG hJc hJ α hΩc htarget
  refine ⟨c, hc, ?_⟩
  intro t ht v
  have hcmem (i j) : MemLp
      (fun z => densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z)
      ∞ (volume.restrict Ω) :=
    (((densityOnEuclid_contDiffOn q α).continuousOn.mono htarget).mul
      ((invGramOnEuclid_contDiffOn (G.metric t) α i j).continuousOn.mono htarget)).memLp_top_of_subset_isCompact
        hΩc hΩ.measurableSet subset_closure
  apply integral_bilinear_weight_lower_bound (fun i => Dp i v) _ hcmem
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
  exact hb t ht z (subset_closure hz)

theorem exists_local_dirichlet_bilinear_form_lower_bound
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :
    let Dp := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (∀ t v, F t v v = ∑ i, ∑ j, ∫ z in Ω,
      Dp i v z * (densityOnEuclid q α z * invGramOnEuclid (G.metric t) α i j z) * Dp j v z) →
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ v, c * ∑ i, ‖Dp i v‖ ^ 2 ≤ F t v v := by
  intro Dp hF
  obtain ⟨c, hc, hb⟩ := exists_local_dirichlet_integral_lower_bound q hG hJc hJ α hΩ hΩc hΩs
  exact ⟨c, hc, fun t ht v => (hb t ht v).trans_eq (hF t v).symm⟩


end DifferentialGeometry.Analysis.Parabolic.Dirichlet
