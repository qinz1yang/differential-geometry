import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientTimeEquation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ForcedTimeH1Energy

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

private theorem ae_eq_add_of_ae_ae_eq_sub
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite ν]
    (P : Lp ℝ 2 (μ.prod ν)) {Q E R : A × B → ℝ}
    (hQ : MemLp Q 2 (μ.prod ν)) (hE : MemLp E 2 (μ.prod ν))
    (hP : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, P (t, x) = R (t, x))
    (hR : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, Q (t, x) = R (t, x) - E (t, x)) :
    P =ᵐ[μ.prod ν] fun p => Q p + E p := by
  let Q' := hQ.toLp Q
  let E' := hE.toLp E
  have hmeas : MeasurableSet {p | P p = Q' p + E' p} :=
    (Lp.stronglyMeasurable P).measurableSet_eq_fun
      ((Lp.stronglyMeasurable Q').add (Lp.stronglyMeasurable E'))
  have heq : P =ᵐ[μ.prod ν] fun p => Q' p + E' p := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [hP, hR, Measure.ae_ae_of_ae_prod hQ.coeFn_toLp,
      Measure.ae_ae_of_ae_prod hE.coeFn_toLp] with t hPt hRt hQt hEt
    filter_upwards [hPt, hRt, hQt, hEt] with x hPx hRx hQx hEx
    change P (t, x) = hQ.toLp Q (t, x) + hE.toLp E (t, x)
    rw [hQx, hEx, hRx]
    linarith
  filter_upwards [heq, hQ.coeFn_toLp, hE.coeFn_toLp] with p hp hQp hEp
  change P p = hQ.toLp Q p + hE.toLp E p at hp
  rwa [hQp, hEp] at hp

section

variable {A B X ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite ν]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

private theorem integral_dual_add_eq_source_add
    (D : ι → X →L[ℝ] Lp ℝ 2 ν) {Q Mx Ex : ι → A × B → ℝ}
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod ν))
    (hE : ∀ j, MemLp (Ex j) 2 (μ.prod ν))
    (hME : ∀ j, Mx j =ᵐ[μ.prod ν] fun p => Q j p + Ex j p)
    (ℓ Lm : Lp (X →L[ℝ] ℝ) 2 μ) (S : Lp ℝ 2 μ → X → ℝ)
    (hℓ : ∀ (τ : Lp ℝ 2 μ) (v : X), (∫ t, τ t * ℓ t v ∂μ) = S τ v -
      ∑ j, ∫ p, τ p.1 * Q j p * D j v p.2 ∂μ.prod ν)
    (hLm : ∀ (τ : Lp ℝ 2 μ) (v : X), (∫ t, τ t * Lm t v ∂μ) =
      ∑ j, ∫ p, τ p.1 * Mx j p * D j v p.2 ∂μ.prod ν)
    (τ : Lp ℝ 2 μ) (v : X) :
    (∫ t, τ t * (ℓ + Lm) t v ∂μ) = S τ v +
      ∑ j, ∫ p, τ p.1 * Ex j p * D j v p.2 ∂μ.prod ν := by
  have h1 : Integrable (fun t => τ t * ℓ t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp ℓ)
  have h2 : Integrable (fun t => τ t * Lm t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Lm)
  have hparts (j) : (∫ p, τ p.1 * Mx j p * D j v p.2 ∂μ.prod ν) =
      (∫ p, τ p.1 * Q j p * D j v p.2 ∂μ.prod ν) +
      ∫ p, τ p.1 * Ex j p * D j v p.2 ∂μ.prod ν := by
    rw [← integral_add (MemLp.integrable_mul_tensor (hQ j) τ (D j v))
      (MemLp.integrable_mul_tensor (hE j) τ (D j v))]
    apply integral_congr_ae
    filter_upwards [hME j] with p hp
    rw [hp]
    ring
  have hadd : (∫ t, τ t * (ℓ + Lm) t v ∂μ) =
      (∫ t, τ t * ℓ t v ∂μ) + ∫ t, τ t * Lm t v ∂μ := by
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add ℓ Lm] with t ht
    rw [ht]
    change τ t * (ℓ t v + Lm t v) = _
    ring
  rw [hadd, hℓ, hLm]
  simp_rw [hparts, Finset.sum_add_distrib]
  ring

end

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem integral_mul_sum_norm_sq_le_of_timeH1_mass_dual
    {X Y Z ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype ι]
    {a b : ℝ} (hab : a ≤ b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) μ)
    {CF : ℝ} (hCF : ∀ᵐ t ∂μ, ‖F t‖ ≤ CF)
    (J : X →L[ℝ] Y) (D : ι → X →L[ℝ] Z)
    (c : ℝ) (hc : ∀ t ∈ Icc a b, ∀ x, c * ∑ i, ‖D i x‖ ^ 2 ≤ F t x x)
    (v : Lp X 2 μ) (ℓ β : Lp (X →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (hmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = inner ℝ (J (v (a + s))) (J z))
    (hderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp X 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, F t (v t) (z t) ∂μ)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζb : ζ (b - a) = 0) :
    c * (∫ s, ζ s * ∑ i, ‖D i (v (a + s))‖ ^ 2 ∂timeMeasure (b - a)) ≤
      (3 * (K : ℝ) / 2) * ∫ s, ‖J (v (a + s))‖ ^ 2 ∂timeMeasure (b - a) +
        ∫ s, ζ s * β (a + s) (v (a + s)) ∂timeMeasure (b - a) := by
  let B : X →L[ℝ] X →L[ℝ] ℝ := (innerSL ℝ).bilinearComp J J
  have hB (x y : X) : B x y = inner ℝ (J x) (J y) := rfl
  have hBsymm : B.flip = B := by
    ext x y
    exact real_inner_comm _ _
  have hBpos (x : X) : 0 ≤ B x x := real_inner_self_nonneg
  have hwmass : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (v (a + s)) := by
    filter_upwards [hmass] with s hs
    ext z
    exact hs z
  have henergy := integral_mul_bilinear_le_of_timeH1_mass_dual_integral_on hab μ hμ F hF hCF
    B hBsymm hBpos v ℓ β w hwmass hderiv hpair
    hζsmooth hζ hζpos hζlip hζ0 hζb
  have hmassnorm : (∫ s, B (v (a + s)) (v (a + s)) ∂timeMeasure (b - a)) =
      ∫ s, ‖J (v (a + s))‖ ^ 2 ∂timeMeasure (b - a) := by
    simp only [hB, real_inner_self_eq_norm_sq]
  rw [hmassnorm] at henergy
  have hshift : MeasurePreserving (fun s : ℝ => a + s) (timeMeasure (b - a)) μ := by
    rw [hμ]
    have h := (measurePreserving_add_right volume a).restrict_image_emb
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
    simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm a] using h
  have hv : MemLp (fun s => v (a + s)) 2 (timeMeasure (b - a)) :=
    (Lp.memLp v).comp_measurePreserving hshift
  have hcoerc : ∀ᵐ s ∂timeMeasure (b - a),
      c * ∑ i, ‖D i (v (a + s))‖ ^ 2 ≤ F (a + s) (v (a + s)) (v (a + s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have htime : a + s ∈ Icc a b := by constructor <;> linarith [hs.1, hs.2]
    exact hc (a + s) htime (v (a + s))
  have hle := MeasureTheory.integral_mul_sum_norm_sq_le_bilinear D (fun s => F (a + s))
    (fun x y => (hF x y).comp_quasiMeasurePreserving hshift.quasiMeasurePreserving)
    (hshift.quasiMeasurePreserving.ae hCF) hv hcoerc (hζ.restrict _) (ae_restrict_of_ae hζpos)
  exact hle.trans henergy

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

omit [T2Space M] [CompactSpace M] in
private theorem memLp_cutoff_gradient_flux_error
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} (hμ : μ ≤ volume.restrict J)
    {V : ℝ × EuStd → ℝ} (hV : MemLp V 2 (μ.prod (volume.restrict Ω)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∀ j, MemLp (fun p : ℝ × EuStd => ∑ i,
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p) 2 (μ.prod (volume.restrict Ω)) := by
  have htarget : closure Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  have hcjoint (i j) : ContinuousOn (fun p : ℝ × EuStd =>
      MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2)
        (J ×ˢ closure Ω) :=
    (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => htarget hp.2)).mul
        (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
  have hcoeff (i j) : MemLp (fun p : ℝ × EuStd =>
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1)) ∞ (μ.prod (volume.restrict Ω)) := by
    have hdiff : Continuous (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_snd
    have h := ((hcjoint i j).mul hdiff.continuousOn).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  intro j
  exact memLp_finsetSum Finset.univ fun i _ => hV.mul (r := 2) (hcoeff i j)

private theorem ae_cutoff_gradient_flux_eq_fixed_density
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (G : MetricConnectionFamilyOn (I := I_hs) (M := M) D)
    (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) {T : ℝ} {μ : Measure ℝ} (hμ : μ ≤ timeMeasure T)
    (u : timeL2 (H1ComplDirichlet q) T) (v : Lp (H1ComplDirichlet q) 2 μ)
    (k : Fin (Module.finrank ℝ EuN))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω₀)))
    {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => H i (t, z))
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t)) Ω₀)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) => MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    let c := fun i j (p : ℝ × EuStd) => σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
    let V := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u
    ∀ j, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω₀,
      (∑ i, (η z / r (t, z)) * A i j (t, z) * H i (t, z)) =
        (∑ i, c i j (t, z) * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) z) -
          ∑ i, c i j (t, z) * fderiv ℝ η z (EuclideanSpace.single i 1) * V (t, z) := by
  intro ρ σ r A c V j
  have h := ae_cutoff_gradient_flux_eq q α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub
    u v k H A r hv hweak hη hηc j
  have hV := (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs
    (timeMeasure T) k u).filter_mono (ae_mono hμ)
  filter_upwards [h, hV] with t ht hVt
  have hVt₀ := hVt.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [ht, hVt₀, ae_restrict_mem hΩ₀.measurableSet] with z hz hVz hzm
  have hcoeff (i) : A i j (t, z) / r (t, z) = c i j (t, z) :=
    weightedInvGramOnEuclid_div_density_ratio q (G.metric t) α i j z
      (hΩ₀s.trans (image_mono interior_subset) (subset_closure hzm))
  simpa only [hcoeff, ← hVz] using hz

private theorem exists_local_dirichlet_main_flux_dual
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hF : ∀ t u v, F t u v = ∑ i, ∑ j, ∫ x,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u x *
        (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v x ∂volume.restrict Ω)
    {μ : Measure ℝ} [SFinite μ] (hμ : μ ≤ volume.restrict J)
    (v : Lp (H1ComplDirichlet q) 2 μ) :
    ∃ P : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ j, ∀ᵐ t ∂μ, (fun x => P j (t, x)) =ᵐ[volume.restrict Ω]
        fun x => ∑ i, (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) ∧
      (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * ℓ t z ∂μ) =
          ∑ j, ∫ p, τ p.1 * P j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : Lp (H1ComplDirichlet q) 2 μ,
        Integrable (fun t => F t (v t) (z t)) μ ∧
        (∫ t, ℓ t (z t) ∂μ) = ∫ t, F t (v t) (z t) ∂μ := by
  let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
    MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
  have hc (i j) : MemLp (c i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have hcont : ContinuousOn (c i j) (J ×ˢ closure Ω) :=
      (((MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => (hΩs.trans (image_mono interior_subset)) hp.2)).mul
        (MetricExtension.invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)).continuousOn
    have h := hcont.memLp_top_of_subset_isCompact (hJc.prod hΩc)
      (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  obtain ⟨P, hP, hp⟩ := MeasureTheory.exists_lp_flux_of_bilinear_integral
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs) c hc F hF v
  obtain ⟨ℓ, hℓ, _, hℓv⟩ := exists_lp_chart_divergence_dual_integral_integral α hΩ hΩc hΩs P
  exact ⟨P, ℓ, hP, hℓ, fun z => ⟨(hp z).1, (hℓv z).trans (hp z).2.symm⟩⟩

private theorem exists_cutoff_gradient_forcing
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [SFinite μ] (hμ : μ ≤ volume.restrict J)
    (V : ℝ × EuStd → ℝ) (hV : MemLp V 2 (μ.prod (volume.restrict Ω)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (v : Lp (H1ComplDirichlet q) 2 μ)
    (ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hF : ∀ t u z, F t u z = ∑ i, ∑ j, ∫ x in Ω,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u x *
        (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z x)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod (volume.restrict Ω)))
    (hℓ : ∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
      MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
    let E := fun j (p : ℝ × EuStd) => ∑ i, c i j p * fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
    (∀ j, ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω,
      Q j (t, x) = (∑ i, c i j (t, x) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) - E j (t, x)) →
    ∃ Lm : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * (ℓ + Lm) t z ∂μ) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
              ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, Lm t (z t) ∂μ) = ∫ t, F t (v t) (z t) ∂μ := by
  intro c E hflux
  have hE : ∀ j, MemLp (E j) 2 (μ.prod (volume.restrict Ω)) :=
    memLp_cutoff_gradient_flux_error q hG hJc hJ α hΩ hΩc hΩs hμ hV hη
  obtain ⟨P, Lm, hP, hLm, hpair⟩ := exists_local_dirichlet_main_flux_dual q hG hJc hJ α hΩ hΩc hΩs F hF hμ v
  have hPE (j) : P j =ᵐ[μ.prod (volume.restrict Ω)] fun p => Q j p + E j p :=
    ae_eq_add_of_ae_ae_eq_sub (μ := μ) (ν := volume.restrict Ω) (P j)
      (Q := Q j) (E := E j)
      (R := fun p => ∑ i, c i j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v p.1) p.2)
      (hQ j) (hE j) (hP j) (hflux j)
  exact ⟨Lm, integral_dual_add_eq_source_add
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs) hQ hE hPE ℓ Lm _ hℓ hLm,
    fun z => (hpair z).2⟩

private theorem exists_cutoff_gradient_energy_of_timeH1
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁)
    (μ : Measure ℝ) [SFinite μ] (hμ : μ = volume.restrict (Icc t₀ t₁))
    (hreg : Icc t₀ t₁ ⊆ D.regular)
    (α : M) {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : timeL2 (H1ComplDirichlet q) T) (k : Fin (Module.finrank ℝ EuN))
    (V : ℝ × EuStd → ℝ) (hV : MemLp V 2 (μ.prod (volume.restrict Ω₀)))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (form : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hform : ∀ t x z, form t x z = ∑ i, ∑ j, ∫ y in Ω₀,
      dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i x y *
        (MetricExtension.densityOnEuclid q α y * MetricExtension.invGramOnEuclid (G.metric t) α i j y) *
          dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j z y)
    (hformm : ∀ x y, AEStronglyMeasurable (fun t => form t x y) μ)
    {CF : ℝ} (hCF : ∀ᵐ t ∂μ, ‖form t‖ ≤ CF)
    (c : ℝ) (hcoerc : ∀ t ∈ Icc t₀ t₁, ∀ x,
      c * ∑ i, ‖dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i x‖ ^ 2 ≤ form t x x)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod (volume.restrict Ω₀))) :
    let ν := μ.prod (volume.restrict Ω₀)
    let E := fun j p => ∑ i,
      (MetricExtension.densityOnEuclid q α p.2 * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
        fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
    (∀ v : Lp (H1ComplDirichlet q) 2 μ, (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z)) →
      ∀ j, ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω₀,
        Q j (t, x) = (∑ i,
          (MetricExtension.densityOnEuclid q α x * MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
            dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) x) - E j (t, x)) →
    (∃ v : Lp (H1ComplDirichlet q) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z)) ∧
        (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z)) ∧
        (w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s)) ∧
        (∀ ζ : timeH1 (H1ComplDirichlet q) (t₁ - t₀),
          ζ.toFun 0 = 0 → ζ.toFun (t₁ - t₀) = 0 →
          (∫ s, inner ℝ (H1ComplDirichletToLp q (v (t₀ + s)))
            (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (t₁ - t₀)) +
            (∫ s, ℓ (t₀ + s) (ζ.toFun s) ∂timeMeasure (t₁ - t₀)) = 0) ∧
        (∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t z ∂μ) =
            (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q j p *
              dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j z p.2 ∂ν)) →
    ∃ v : Lp (H1ComplDirichlet q) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z)) ∧
        (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z)) ∧
        (w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s)) ∧
        (∀ ζ : timeH1 (H1ComplDirichlet q) (t₁ - t₀),
          ζ.toFun 0 = 0 → ζ.toFun (t₁ - t₀) = 0 →
          (∫ s, inner ℝ (H1ComplDirichletToLp q (v (t₀ + s)))
            (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (t₁ - t₀)) +
            (∫ s, ℓ (t₀ + s) (ζ.toFun s) ∂timeMeasure (t₁ - t₀)) = 0) ∧
        (∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t z ∂μ) =
            (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q j p *
              dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j z p.2 ∂ν) ∧
        ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
            (∫ t, τ t * β t z ∂μ) =
              (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
                ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) +
              ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j z p.2 ∂ν) ∧
          (∀ z : Lp (H1ComplDirichlet q) 2 μ,
            (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
              ∫ t, (∑ i, ∑ j, ∫ y in Ω₀,
                dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) y *
                  (MetricExtension.densityOnEuclid q α y *
                    MetricExtension.invGramOnEuclid (G.metric t) α i j y) *
                  dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j (z t) y) ∂μ) ∧
          ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
            (∀ᵐ s ∂volume, 0 ≤ ζ s) → LipschitzWith K ζ → ζ 0 = 0 → ζ (t₁ - t₀) = 0 →
            c * (∫ s, ζ s * ∑ i, ‖dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v (t₀ + s))‖ ^ 2 ∂timeMeasure (t₁ - t₀)) ≤
              (3 * (K : ℝ) / 2) * ∫ s, ‖H1ComplDirichletToLp q (v (t₀ + s))‖ ^ 2 ∂timeMeasure (t₁ - t₀) +
                ∫ s, ζ s * β (t₀ + s) (v (t₀ + s)) ∂timeMeasure (t₁ - t₀) := by
  intro ν E hflux hpacket
  obtain ⟨v, w, ℓ, hv, hw, hd, htest, hℓ⟩ := hpacket
  obtain ⟨Lm, hβ, hLm⟩ := exists_cutoff_gradient_forcing q hG isCompact_Icc hreg
    α hΩ₀ hΩ₀c hΩ₀s hμ.le V hV hη v ℓ form hform Q B hQ hℓ (hflux v hv)
  have hpair (z : Lp (H1ComplDirichlet q) 2 μ) :
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, (ℓ + Lm) t (z t) ∂μ) -
        ∫ t, form t (v t) (z t) ∂μ := by
    have hint (L : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ) :
        Integrable (fun t => L t (z t)) μ :=
      MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable
        (fun _ => ContinuousLinearMap.id ℝ (H1ComplDirichlet q →L[ℝ] ℝ))
        (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
        (Lp.memLp L) (Lp.memLp z)
    have heq : (∫ t, (ℓ + Lm) t (z t) ∂μ) =
        (∫ t, ℓ t (z t) ∂μ) + ∫ t, Lm t (z t) ∂μ := by
      rw [← integral_add (hint ℓ) (hint Lm)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add ℓ Lm] with t ht
      exact congrArg (fun L : H1ComplDirichlet q →L[ℝ] ℝ => L (z t)) ht
    rw [heq, hLm]
    exact (add_sub_cancel_right _ _).symm
  refine ⟨v, w, ℓ, hv, hw, hd, htest, hℓ, ℓ + Lm, hβ, ?_, ?_⟩
  · intro z
    simpa only [hform] using hpair z
  intro ζ K hζsmooth hζ hζpos hζlip hζ0 hζ1
  exact integral_mul_sum_norm_sq_le_of_timeH1_mass_dual ht₀₁ μ hμ form hformm hCF
    (H1ComplDirichletToLp q) (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s)
    c hcoerc v ℓ (ℓ + Lm) w hw hd hpair hζsmooth hζ hζpos hζlip hζ0 hζ1

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_gradient_energy
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ < t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, σ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * V k p)) * φ p ∂ν) ∧
      let C := fun k p => (r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * V k p)
      let Q := fun k j p => ∑ i, (η p.2 / r p) * A i j p * H k i p
      let B := fun k p => η p.2 * C k p -
        ∑ i, ∑ j, A i j p * H k i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      let E := fun k j p => ∑ i,
        (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V k p
      (∀ k j, MemLp (Q k j) 2 ν) ∧ (∀ k, MemLp (B k) 2 ν) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ k, ∃ v : Lp (H1ComplDirichlet q) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u t) z)) ∧
        (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z)) ∧
        (w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s)) ∧
        (∀ ζ : timeH1 (H1ComplDirichlet q) (t₁ - t₀),
          ζ.toFun 0 = 0 → ζ.toFun (t₁ - t₀) = 0 →
          (∫ s, inner ℝ (H1ComplDirichletToLp q (v (t₀ + s)))
            (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (t₁ - t₀)) +
            (∫ s, ℓ (t₀ + s) (ζ.toFun s) ∂timeMeasure (t₁ - t₀)) = 0) ∧
        (∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t z ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν) ∧
        ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
            (∫ t, τ t * β t z ∂μ) =
              (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q z
                ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) +
              ∑ j, ∫ p, τ p.1 * E k j p * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν) ∧
          (∀ z : Lp (H1ComplDirichlet q) 2 μ,
            (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
              ∫ t, (∑ i, ∑ j, ∫ y in Ω₀,
                dirichletLocalWeakPartialLp q α hΩ₀
                  (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                  (hΩ₀Ω.trans (subset_closure.trans hΩs)) i (v t) y *
                  (MetricExtension.densityOnEuclid q α y *
                    MetricExtension.invGramOnEuclid (G.metric t) α i j y) *
                  dirichletLocalWeakPartialLp q α hΩ₀
                    (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                    (hΩ₀Ω.trans (subset_closure.trans hΩs)) j (z t) y) ∂μ) ∧
          ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
            (∀ᵐ s ∂volume, 0 ≤ ζ s) → LipschitzWith K ζ → ζ 0 = 0 → ζ (t₁ - t₀) = 0 →
            c * (∫ s, ζ s * ∑ i, ‖dirichletLocalWeakPartialLp q α hΩ₀
              (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
              (hΩ₀Ω.trans (subset_closure.trans hΩs)) i (v (t₀ + s))‖ ^ 2 ∂timeMeasure (t₁ - t₀)) ≤
              (3 * (K : ℝ) / 2) * ∫ s, ‖H1ComplDirichletToLp q (v (t₀ + s))‖ ^ 2 ∂timeMeasure (t₁ - t₀) +
                ∫ s, ζ s * β (t₀ + s) (v (t₀ + s)) ∂timeMeasure (t₁ - t₀) := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  have htime : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht₀.le.trans ht.1, ht.2.trans ht₁.le⟩
  have hexForm := exists_local_dirichlet_bilinear_form_family q hG
    isCompact_Icc (htime.trans hreg) α hΩ₀ hΩ₀c hΩ₀s
  let form := Classical.choose hexForm
  have hform := (Classical.choose_spec hexForm).1
  have hformm := (Classical.choose_spec hexForm).2.1
  let CF := Classical.choose (Classical.choose_spec hexForm).2.2
  have hCF := (Classical.choose_spec (Classical.choose_spec hexForm).2.2).2
  have hexCoerc := exists_local_dirichlet_integral_lower_bound q hG
    isCompact_Icc (htime.trans hreg) α hΩ₀ hΩ₀c hΩ₀s
  let c := Classical.choose hexCoerc
  have hc := (Classical.choose_spec hexCoerc).1
  have hcoerc := (Classical.choose_spec hexCoerc).2
  intro μ ν ρ σ r A U V
  classical
  have hex := hu.exists_timeH1_cutoff_gradient_dual_deriv hXcont hacont α hΩ hΩc hΩs hXsmooth
    ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω hη hηc hηs
  let R := hex.choose
  let H := hex.choose_spec.choose
  let F := hex.choose_spec.choose_spec.choose
  have hp := hex.choose_spec.choose_spec.choose_spec
  have hR := hp.1
  have hH := hp.2.1
  have hHsym := hp.2.2.1
  have hF := hp.2.2.2.1
  have hfixed := hp.2.2.2.2.1
  have hsource := hp.2.2.2.2.2
  refine ⟨R, H, F, hR, hH, hHsym, hF, hfixed, ?_⟩
  intro C Q B E
  obtain ⟨hQ, hB, htimeH1⟩ := hsource
  refine ⟨hQ, hB, c, hc, ?_⟩
  intro k
  have hμ : μ = volume.restrict (Icc t₀ t₁) := Measure.restrict_restrict_of_subset htime
  have hμJ : μ ≤ volume.restrict (Icc t₀ t₁) := hμ.le
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hV : MemLp (V k) 2 ν := (Lp.memLp (V k)).mono_measure
    (Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl))
  refine exists_cutoff_gradient_energy_of_timeH1 q hG ht₀₁.le μ hμ (htime.trans hreg)
    α hΩ₀ hΩ₀c hΩ₀s u k (V k) hV hη form hform
    (fun x y => (hformm x y).mono_measure hμJ) (hCF.filter_mono (ae_mono hμJ))
    c (fun t ht x => (hcoerc t ht x).trans_eq (hform t x x).symm) (Q k) (B k) (hQ k) ?_ (htimeH1 k)
  intro v hv
  exact ae_cutoff_gradient_flux_eq_fixed_density q G α hΩ hΩc hΩs
    hΩ₀ hΩ₀c hΩ₀s hsub (μ := μ) Measure.restrict_le_self u v k (H k) hv (hH k) hη hηc

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
