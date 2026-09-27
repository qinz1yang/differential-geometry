import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityTimeDerivative
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffForcing
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffScalarSource
import DifferentialGeometry.Analysis.Integration.Lp.Pairing

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric I_hs M} :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

theorem exists_local_dirichlet_second_weak_derivative_of_weighted_weak_equation
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (((volume.restrict (Icc a b)).restrict (Icc c d)).prod
          (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun x => H i k (t, x))
          (fun x => K i (t, x)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        Sobolev.Euclidean.MemWkp 2 2 (fun x => U (t, x)) Ω₀ := by
  classical
  let q := G.metric a
  let μ := volume.restrict (Icc a b)
  let ν := μ.prod (volume.restrict Ω)
  let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
  let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
  let r := fun p => ρ p / σ p
  let A := fun i j (p : ℝ × EuStd) =>
    MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
  let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hOt)
  have hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun _ hp => hOt hp.2)
  have hσne (p : ℝ × EuStd) (hp : p.2 ∈ O) : σ p ≠ 0 :=
    (MetricExtension.densityOnEuclid_pos q α (hOt hp)).ne'
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ O) : ρ p ≠ 0 :=
    (MetricExtension.densityOnEuclid_pos (G.metric p.1) α (hOt hp)).ne'
  have hr : ContDiffOn ℝ (⊤ : ℕ∞) r (D.regular ×ˢ O) :=
    hρ.div hσ (fun p hp => hσne p hp.2)
  have hrne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ O) : r p ≠ 0 :=
    div_ne_zero (hρne p hp.2) (hσne p hp.2)
  have hA (i j : Fin (Module.finrank ℝ EuN)) : MemLp (A i j) ∞ ν := by
    have hm := (MetricExtension.weightedInvGramOnEuclid_family_contDiffOn
      hG hreg α hΩs i j).continuousOn.memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm
  have hPmem (j) : MemLp (fun p => ∑ i, A i j p * K i p) 2 ν :=
    memLp_finsetSum Finset.univ fun i _ => (Lp.memLp (K i)).mul (r := 2) (hA i j)
  let P := fun j => (hPmem j).toLp (fun p => ∑ i, A i j p * K i p)
  have hP (j) : P j =ᵐ[ν] fun p => ∑ i, A i j p * K i p := (hPmem j).coeFn_toLp
  have hmem : ∀ᵐ p ∂ν, p.2 ∈ Ω :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume.restrict Ω)).ae
      (ae_restrict_mem hΩ.measurableSet)
  have hweak' : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, r p * (σ p * U p) * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, F p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have hl : (∫ p, r p * (σ p * U p) * fderiv ℝ φ p (1, 0) ∂ν) =
        ∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hmem] with p hp
      dsimp only [r]
      field_simp [hσne p (hΩs (subset_closure hp))]
    rw [hl, hweak φ hφ hφc hφs]
    apply congrArg₂ (fun x y : ℝ => x - y) ?_ rfl
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hP j] with p hp
    rw [hp]
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨δ, η, _, _, hη, hηc, _, hηone, hηs⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ hΩ₀Ω
  let C := fun p => (r p)⁻¹ * F p -
    ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)
  let Q := fun j p => (η p.2 / r p) * P j p
  let B := fun p => η p.2 * C p - ∑ j, P j p *
    fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
  obtain ⟨v, hv, hDv, hQ, hB, ℓ, w, hwmass, hwderiv, hℓ, _⟩ :=
    exists_timeH1_cutoff_mass_of_joint_weak_partials q α hΩ hΩc hΩs hη hηc hηs
      hab μ rfl (D.regular_isOpen.prod hO) (Set.prod_mono hreg hΩs)
      hr hrne U F P K hspatial hweak'
  let coeff := fun i j (p : ℝ × EuStd) =>
    σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
  let error := fun j (p : ℝ × EuStd) => ∑ i,
    coeff i j p * fderiv ℝ η p.2 (EuclideanSpace.single i 1) * U p
  have hflux (j) : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω,
      Q j (t, x) = (∑ i, coeff i j (t, x) *
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) - error j (t, x) := by
    filter_upwards [ae_all_iff.mpr hDv, Measure.ae_ae_of_ae_prod (hP j)] with t ht hPt
    filter_upwards [ae_all_iff.mpr ht, hPt, ae_restrict_mem hΩ.measurableSet]
      with x hx hPx hxΩ
    have hcoeff (i) : A i j (t, x) / r (t, x) = coeff i j (t, x) :=
      weightedInvGramOnEuclid_div_density_ratio q (G.metric t) α i j x
        (hOt (hΩs (subset_closure hxΩ)))
    change (η x / r (t, x)) * P j (t, x) = _
    rw [hPx, Finset.mul_sum]
    change _ = (∑ i, coeff i j (t, x) *
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) -
        ∑ i, coeff i j (t, x) * fderiv ℝ η x (EuclideanSpace.single i 1) * U (t, x)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i, ← hcoeff i]
    simp only [div_eq_mul_inv]
    ring
  have hexForm := exists_local_dirichlet_bilinear_form_family q hG
    isCompact_Icc hreg α hΩ hΩc hΩs
  let form := Classical.choose hexForm
  have hform := (Classical.choose_spec hexForm).1
  change ∀ t u z, form t u z = _ at hform
  obtain ⟨Lm, hβ, hLm⟩ := exists_cutoff_forcing_dual q hG isCompact_Icc hreg
    α hΩ hΩc hΩs (μ := μ) le_rfl U (Lp.memLp U) hη v ℓ form hform
    Q B hQ hℓ hflux
  have hspatial' (j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => K j (t, x)) (fun x => (Lp.memLp U).toLp U (t, x)) Ω := by
    simpa only [Lp.toLp_coeFn] using hspatial j
  obtain ⟨f, _, hfsource⟩ := exists_lp_scalar_source_of_cutoff_pairing q hG
    isCompact_Icc hreg α hΩ hΩc hΩs (μ := μ) le_rfl hη hηs hB
    (Lp.memLp U) K hspatial' (ℓ + Lm) hβ
  have hpair (z : Lp (H1ComplDirichlet q) 2 μ) :
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, (ℓ + Lm) t (z t) ∂μ) -
        ∫ t, (∑ i, ∑ j, ∫ x in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x *
            (MetricExtension.densityOnEuclid q α x *
              MetricExtension.invGramOnEuclid (G.metric t) α i j x) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) x) ∂μ := by
    have he := Lp.integral_add_apply ℓ Lm z
    rw [hLm] at he
    simp only [hform] at he
    change _ = _ + _ at he
    exact eq_sub_of_add_eq he.symm
  obtain ⟨H, hH, _⟩ := exists_local_dirichlet_second_weak_derivative_of_timeH1_interior
    hG hab.le hreg q α hΩ hΩc hΩs hac hdb v f ℓ (ℓ + Lm) w
    hwmass hwderiv hpair hfsource hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hηone' (x : EuStd) (hx : x ∈ Ω₀) : η x = 1 :=
    hηone x (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hx))
  have hηderiv (x : EuStd) (hx : x ∈ Ω₀) : fderiv ℝ η x = 0 := by
    have he : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hΩ₀.mem_nhds hx] with y hy
      exact hηone' y hy
    rw [he.fderiv_eq]
    simp
  have hDvK (i) : ∀ᵐ t ∂μ.restrict (Icc c d),
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
        fun x => K i (t, x) := by
    filter_upwards [(hDv i).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
    filter_upwards [ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem hΩ₀.measurableSet] with x hx hxΩ
    simpa only [hηone' x hxΩ, hηderiv x hxΩ, one_mul,
      zero_apply, zero_mul, add_zero] using hx
  have hHK (i k) : ∀ᵐ t ∂μ.restrict (Icc c d),
      DeGiorgi.HasWeakPartialDeriv k (fun x => H i k (t, x)) (fun x => K i (t, x)) Ω₀ := by
    filter_upwards [hH i k, hDvK i] with t ht hKt
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ k hKt ht
  refine ⟨H, hHK, ?_⟩
  have hν : (μ.restrict (Icc c d)).prod (volume.restrict Ω₀) ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  apply Sobolev.Euclidean.ae_memWkp_two_of_hasWeakPartialDeriv
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ₀ ((Lp.memLp U).mono_measure hν)
    (fun i => (Lp.memLp (K i)).mono_measure hν) (fun i k => Lp.memLp (H i k)) ?_ hHK
  intro i
  filter_upwards [(hspatial i).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
  exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
