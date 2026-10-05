import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartMassPairing
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual
import DifferentialGeometry.Analysis.Parabolic.WeakEquationTensor
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure

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

theorem exists_timeH1_cutoff_mass_of_weighted_weak_equation
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    {a b : ℝ} (hab : a < b) (μ : Measure ℝ)
    (hμ : μ = volume.restrict (Icc a b))
    {S : Set (ℝ × EuStd)} (hS : IsOpen S)
    (hSsub : Icc a b ×ˢ closure Ω ⊆ S)
    {r : ℝ × EuStd → ℝ} (hr : ContDiffOn ℝ (⊤ : ℕ∞) r S)
    (hrne : ∀ p ∈ S, r p ≠ 0)
    (U F : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (P : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : Lp (H1ComplDirichlet q) 2 μ)
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun x => η x * U (t, x)))
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, r p * (MetricExtension.densityOnEuclid q α p.2 * U p) *
        fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
          ∫ p, F p * φ p ∂μ.prod (volume.restrict Ω)) :
    let ν := μ.prod (volume.restrict Ω)
    let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
    let C := fun p => (r p)⁻¹ * F p -
      ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)
    let Q := fun j p => (η p.2 / r p) * P j p
    let B := fun p => η p.2 * C p - ∑ j, P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
    (∀ j, MemLp (Q j) 2 ν) ∧ MemLp B 2 ν ∧
      ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
          (∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
            w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s)))
              (H1ComplDirichletToLp q z)) ∧
          (w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s)) ∧
          (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
            (∫ t, τ t * ℓ t z ∂μ) =
              (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
                ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
              ∑ j, ∫ p, τ p.1 * Q j p *
                dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2 ∂ν) ∧
          ∀ ζ : timeH1 (H1ComplDirichlet q) (b - a),
            ζ.toFun 0 = 0 → ζ.toFun (b - a) = 0 →
            (∫ s, inner ℝ (H1ComplDirichletToLp q (v (a + s)))
              (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (b - a)) +
              (∫ s, ℓ (a + s) (ζ.toFun s) ∂timeMeasure (b - a)) = 0 := by
  subst μ
  intro ν σ C Q B
  classical
  let μ := volume.restrict (Icc a b)
  let : IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  have hlift (f : ℝ × EuStd → ℝ) (hf : ContinuousOn f S) : MemLp f ∞ ν := by
    have h := (hf.mono hSsub).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h
  have hσsp : MemLp (MetricExtension.densityOnEuclid q α) ∞ (volume.restrict Ω) :=
    ((MetricExtension.densityOnEuclid_contDiffOn q α).continuousOn.mono
      (hΩs.trans (image_mono interior_subset))).memLp_top_of_subset_isCompact
        hΩc hΩ.measurableSet subset_closure
  have hσ : MemLp σ ∞ ν := hσsp.comp_snd μ
  have hηsp : MemLp η ∞ (volume.restrict Ω) :=
    hη.continuous.memLp_top_of_hasCompactSupport hηc _
  have hηp : MemLp (fun p : ℝ × EuStd => η p.2) ∞ ν := hηsp.comp_snd μ
  have hηS : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × EuStd => η p.2) S :=
    (hη.comp contDiff_snd).contDiffOn
  have hrinv : MemLp (fun p => (r p)⁻¹) ∞ ν := hlift _ (hr.inv hrne).continuousOn
  have hrt : MemLp (fun p => fderiv ℝ r p (1, 0)) ∞ ν :=
    hlift _ (((hr.fderiv_of_isOpen hS (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiffOn_const).continuousOn)
  have hηr : MemLp (fun p => η p.2 / r p) ∞ ν :=
    hlift _ (hηS.div hr hrne).continuousOn
  have hdηr (j : Fin (Module.finrank ℝ EuN)) :
      MemLp (fun p => fderiv ℝ (fun z : ℝ × EuStd => η z.2 / r z) p
        (0, EuclideanSpace.single j 1)) ∞ ν :=
    hlift _ ((((hηS.div hr hrne).fderiv_of_isOpen hS (m := (⊤ : ℕ∞))
      (by simp)).clm_apply contDiffOn_const).continuousOn)
  have hW : MemLp (fun p => σ p * U p) 2 ν := hσ.fun_mul (r := 2) (Lp.memLp U)
  have hC : MemLp C 2 ν :=
    (hrinv.fun_mul (r := 2) (Lp.memLp F)).sub
      ((hrinv.fun_mul (r := ∞) hrt).fun_mul (r := 2) hW)
  have hQ (j : Fin (Module.finrank ℝ EuN)) : MemLp (Q j) 2 ν :=
    hηr.fun_mul (r := 2) (Lp.memLp (P j))
  have hB : MemLp B 2 ν := by
    apply (hηp.fun_mul (r := 2) hC).sub
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp (P j)).fun_mul (r := 2) (hdηr j)
  have hI : Ioo a b ×ˢ Ω ⊆ S :=
    (Set.prod_mono Ioo_subset_Icc_self subset_closure).trans hSsub
  have hfixed : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, (σ p * U p) * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, C p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact DifferentialGeometry.Analysis.Sobolev.integral_fderiv_eq_of_weighted_identity
      (isOpen_Ioo.prod hΩ) (1, 0)
      (hW.integrable (by norm_num)).locallyIntegrable
      ((Lp.memLp F).integrable (by norm_num)).locallyIntegrable
      (hr.mono hI) (fun p hp => hrne p (hI hp))
      (fun ψ => ∑ j, ∫ p, P j p * fderiv ℝ ψ p
        (0, EuclideanSpace.single j 1) ∂ν)
      hweak hφ hφc hφs
  obtain ⟨ℓ, hℓ⟩ := exists_lp_chart_source_sub_divergence_dual
    α hΩ hΩc hΩs hB hQ
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω)) := Lp.SecondCountableTopology
  obtain ⟨Ut, hUt, _⟩ := Lp.exists_curry (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) U
  have hUsection : ∀ᵐ t ∂μ,
      (fun x => U (t, x)) =ᵐ[volume.restrict Ω] (Ut t : EuStd → ℝ) :=
    hUt.mono fun _ ht => ht.symm
  have hvUt : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun x => η x * Ut t x) := by
    filter_upwards [hv, hUsection] with t hvt ht
    apply hvt.trans
    apply chartPullback_ae_eq_of_ae_eq q α
    have hall := (ae_restrict_iff' hΩ.measurableSet).mp ht
    filter_upwards [hall] with x hx
    by_cases hx' : x ∈ tsupport η
    · exact congrArg (fun y => η x * y) (hx (hηs hx'))
    · simp only [image_eq_zero_of_notMem_tsupport hx', zero_mul]
  let mass : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (H1ComplDirichletToLp q) (H1ComplDirichletToLp q)
  have hmass (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q) :
      (∫ t, τ t * mass (v t) z ∂μ) =
        ∫ p, τ p.1 * (η p.2 * (σ p * U p)) * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν := by
    apply (integral_mass_inner_eq_integral_chart_prod q α hΩ hΩc hΩs
      hη hηc hηs τ v Ut U hUsection z hvUt).trans
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [σ]
    ring
  have htensor (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ)
      (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hτc : HasCompactSupport τ)
      (hτs : tsupport τ ⊆ Ioo a b) :
      let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
      (∫ p, deriv τ p.1 * (η p.2 * (σ p * U p)) * ψ p.2 ∂ν) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
          ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
    intro ψ
    let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
    have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
    have hψO : ContDiffOn ℝ (⊤ : ℕ∞) ψ O := by
      apply (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn α z.smooth).comp
        (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
      rintro x ⟨y, hy, rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
    have hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω := hψO.mono (subset_closure.trans hΩs)
    have hψmem : MemLp ψ ∞ (volume.restrict Ω) :=
      (hψO.continuousOn.mono hΩs).memLp_top_of_subset_isCompact
        hΩc hΩ.measurableSet subset_closure
    have hdψmem (j : Fin (Module.finrank ℝ EuN)) :
        MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j 1)) ∞ (volume.restrict Ω) :=
      ((((hψO.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        contDiffOn_const).continuousOn).mono hΩs).memLp_top_of_subset_isCompact
          hΩc hΩ.measurableSet subset_closure
    have hτmem : MemLp τ ∞ μ := hτ.continuous.memLp_top_of_hasCompactSupport hτc _
    have hint (A : ℝ × EuStd → ℝ) (hA : MemLp A 2 ν)
        (χ : EuStd → ℝ) (hχ : MemLp χ ∞ (volume.restrict Ω)) :
        Integrable (fun p => τ p.1 * A p * χ p.2) ν :=
      (((hτmem.comp_fst (volume.restrict Ω)).fun_mul (r := 2) hA).fun_mul
        (r := 2) (hχ.comp_snd μ)).integrable (by norm_num)
    have hmain (j) : Integrable (fun p => τ p.1 * ((η p.2 / r p) * P j p) *
        fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) ν :=
      hint (Q j) (hQ j) _ (hdψmem j)
    have herr (j) : Integrable (fun p => τ p.1 * (P j p *
        fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) * ψ p.2) ν :=
      hint _ ((Lp.memLp (P j)).fun_mul (r := 2) (hdηr j)) ψ hψmem
    have hsource : Integrable (fun p => τ p.1 * (η p.2 * C p) * ψ p.2) ν :=
      hint _ (hηp.fun_mul (r := 2) hC) ψ hψmem
    have hmem : ∀ᵐ p ∂ν, p.1 ∈ Icc a b ∧ p.2 ∈ Ω := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ.measurableSet)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact ⟨ht, hx⟩
    have hgood : ∀ᵐ p ∂ν,
        DifferentiableAt ℝ ψ p.2 ∧ DifferentiableAt ℝ r p ∧ r p ≠ 0 := by
      filter_upwards [hmem] with p hp
      have hpS : p ∈ S := hSsub ⟨hp.1, subset_closure hp.2⟩
      exact ⟨(hψ.contDiffAt (hΩ.mem_nhds hp.2)).differentiableAt (by simp),
        (hr.contDiffAt (hS.mem_nhds hpS)).differentiableAt (by simp), hrne p hpS⟩
    exact integral_fixed_density_tensor_test (fun j => EuclideanSpace.single j 1)
      hΩ hη hηc hηs hψ hgood hfixed hτ hτc hτs hmain herr hsource
  obtain ⟨w, hwmass, hwderiv⟩ := exists_timeH1_dual_of_tensor_integrals_on
    (ν := volume.restrict Ω) (X := H1ComplDirichlet q) (S := SmoothScalarDirichlet q)
    hab μ rfl (smoothToH1ComplDirichlet q) (denseRange_smoothToH1ComplDirichlet q)
    (mass.comp_memLp v) (Lp.memLp ℓ)
    (W := fun p => η p.2 * (σ p * U p)) (B := B) (Q := Q)
    (R := fun z x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q z)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)))
    (D := fun z j => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (smoothToH1ComplDirichlet q z))
    (fun τ z => hmass τ (smoothToH1ComplDirichlet q z))
    (fun τ z => hℓ τ (smoothToH1ComplDirichlet q z))
    (fun z τ hτ hτc hτs => integral_chart_tensor_test_of_smooth q α hΩ hΩc hΩs
      μ z τ (htensor z τ hτ hτc hτs))
  have hw : ∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s)))
        (H1ComplDirichletToLp q z) := by
    filter_upwards [hwmass] with s hs
    intro z
    exact (congrArg (fun L : H1ComplDirichlet q →L[ℝ] ℝ => L z) hs).symm
  refine ⟨hQ, hB, ℓ, w, hw, hwderiv, hℓ, ?_⟩
  intro ζ hζ0 hζ1
  exact integral_timeH1_test_of_mass_dual hab.le mass v w ℓ hw hwderiv ζ hζ0 hζ1

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure

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

theorem exists_timeH1_cutoff_mass_of_joint_weak_partials
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    {a b : ℝ} (hab : a < b) (μ : Measure ℝ)
    (hμ : μ = volume.restrict (Icc a b))
    {S : Set (ℝ × EuStd)} (hS : IsOpen S)
    (hSsub : Icc a b ×ˢ closure Ω ⊆ S)
    {r : ℝ × EuStd → ℝ} (hr : ContDiffOn ℝ (⊤ : ℕ∞) r S)
    (hrne : ∀ p ∈ S, r p ≠ 0)
    (U F : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (P : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, r p * (MetricExtension.densityOnEuclid q α p.2 * U p) *
        fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
          ∫ p, F p * φ p ∂μ.prod (volume.restrict Ω)) :
    let ν := μ.prod (volume.restrict Ω)
    let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
    let C := fun p => (r p)⁻¹ * F p -
      ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)
    let Q := fun j p => (η p.2 / r p) * P j p
    let B := fun p => η p.2 * C p - ∑ j, P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
    ∃ v : Lp (H1ComplDirichlet q) 2 μ,
      (∀ᵐ t ∂μ,
        (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
          chartPullback I_hs α (fun x => η x * U (t, x))) ∧
      (∀ j, ∀ᵐ t ∂μ,
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v t) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
          fun x => η x * K j (t, x) +
            fderiv ℝ η x (EuclideanSpace.single j 1) * U (t, x)) ∧
      (∀ j, MemLp (Q j) 2 ν) ∧ MemLp B 2 ν ∧
      ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
          (∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
            w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s)))
              (H1ComplDirichletToLp q z)) ∧
          (w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s)) ∧
          (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
            (∫ t, τ t * ℓ t z ∂μ) =
              (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
                ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
              ∑ j, ∫ p, τ p.1 * Q j p *
                dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2 ∂ν) ∧
          ∀ ζ : timeH1 (H1ComplDirichlet q) (b - a),
            ζ.toFun 0 = 0 → ζ.toFun (b - a) = 0 →
            (∫ s, inner ℝ (H1ComplDirichletToLp q (v (a + s)))
              (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (b - a)) +
              (∫ s, ℓ (a + s) (ζ.toFun s) ∂timeMeasure (b - a)) = 0 := by
  intro ν σ C Q B
  obtain ⟨v, hv⟩ := exists_lp_h1ComplDirichlet_chartPullback_mul_of_joint_weak_partials
    q α hΩ hΩc hΩs hη hηc hηs U K hspatial
  refine ⟨v, hv, ?_, ?_⟩
  · intro j
    exact ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul
      q α hΩ hΩc hΩs v hv (Lp.memLp U) (Lp.memLp (K j)) j (hspatial j) hη
  · exact exists_timeH1_cutoff_mass_of_weighted_weak_equation
      q α hΩ hΩc hΩs hη hηc hηs hab μ hμ hS hSsub hr hrne U F P v hv hweak

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
