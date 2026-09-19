import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatGradientEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffWeakEquation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_lp_cutoff_gradient_tensor_identity_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let σ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let c := fun p => ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2))
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω₀) →
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ S : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, S k =ᵐ[ν] fun p =>
        (c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
          (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)) +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (A i j) z (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * V i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k p * φ p ∂ν) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, σ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * S k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * V k p)) * φ p ∂ν) ∧
      let C := fun k p => (r p)⁻¹ * S k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * V k p)
      let Q := fun k j p => ∑ i, (η p.2 / r p) * A i j p * H k i p
      let B := fun k p => η p.2 * C k p -
        ∑ i, ∑ j, A i j p * H k i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      (∀ k j, MemLp (Q k j) 2 ν) ∧ (∀ k, MemLp (B k) 2 ν) ∧
      (∀ k, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∀ τ : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t v ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j v p.2 ∂ν) ∧
      ∀ k (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo a b →
        let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (∫ p, deriv τ p.1 * (η p.2 * (σ p * V k p)) * ψ p.2 ∂ν) =
          (∑ j, ∫ p, τ p.1 * Q k j p *
            fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
          ∫ p, τ p.1 * B k p * ψ p.2 ∂ν := by
  intro μ ν x ρ σ r A U V F c Df hDf
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨R, H, S, hR, hH, hHsym, hSformula, hS, hfixed⟩ :=
    exists_lp_weak_gradient_equation_fixed_density_of_heat_timeH1 hG hT hreg q hCg hequiv Cv hCv0
      hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv Df hDf
  refine ⟨R, H, S, hR, hH, hHsym, hSformula, hS, hfixed, ?_⟩
  intro C Q B
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (k) : MemLp (V k) 2 ν := (Lp.memLp (V k)).mono_measure hmeasure
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hchart)
  have hσall : ContDiffOn ℝ (⊤ : ℕ∞) σ (D.regular ×ˢ Ω) :=
    (densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => hchart hp.2)
  have hσne (p : ℝ × EuStd) (hp : p.2 ∈ Ω) : σ p ≠ 0 :=
    (densityOnEuclid_pos q α (hchart hp)).ne'
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ Ω) : ρ p ≠ 0 :=
    (densityOnEuclid_pos (g p.1) α (hchart hp)).ne'
  have hrall : ContDiffOn ℝ (⊤ : ℕ∞) r (D.regular ×ˢ Ω) :=
    hρall.div hσall (fun p hp => hσne p hp.2)
  have hrne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ Ω) : r p ≠ 0 :=
    div_ne_zero (hρne p hp.2) (hσne p hp.2)
  have hAall (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ Ω) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α
      (subset_closure.trans hΩs) i j
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : MemLp f ∞ ν := by
    have hb := (hc.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hrinv : MemLp (fun p => (r p)⁻¹) ∞ ν := hlift _ (hrall.inv hrne).continuousOn
  have hrt : MemLp (fun p => fderiv ℝ r p (1, 0)) ∞ ν :=
    hlift _ ((hrall.fderiv_of_isOpen (m := (⊤ : ℕ∞)) (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hσmem : MemLp σ ∞ ν := hlift _ hσall.continuousOn
  have hAmem (i j) : MemLp (A i j) ∞ ν := hlift _ (hAall i j).continuousOn
  have hC (k) : MemLp (C k) 2 ν :=
    ((Lp.memLp (S k)).mul (r := 2) hrinv).sub (((hV k).mul (r := 2) hσmem).mul (r := 2) (hrt.mul (r := ∞) hrinv))
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let P := fun k j p => ∑ i, A i j p * H k i p
  have hP (k j) : MemLp (P k j) 2 ν := by
    apply memLp_finsetSum
    intro i _
    exact (Lp.memLp (H k i)).mul (r := 2) (hAmem i j)
  have hSsub : Ioo a b ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg ⟨ha.le.trans hp.1.1.le, hp.1.2.le.trans hb.le⟩, hsub hp.2⟩
  have hr := hrall.mono hSsub
  have hw (k) : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, (σ p * V k p) * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P k j p * fderiv ℝ (fun z => ψ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, C k p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hψrs : tsupport (fun z => ψ z / r z) ⊆ Ioo a b ×ˢ Ω₀ := by
      simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun z => (r z)⁻¹)).trans hψs
    have hψr : ContDiff ℝ (⊤ : ℕ∞) (fun z => ψ z / r z) :=
      (hψ.contDiffOn.div hr (fun p hp => hrne p (hSsub hp))).contDiff_of_tsupport_subset
        (isOpen_Ioo.prod hΩ₀) hψrs
    have hψrc : HasCompactSupport (fun z => ψ z / r z) := by
      exact hψc.isCompact.of_isClosed_subset (isClosed_tsupport _) (by
        simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun z => (r z)⁻¹)))
    have hdψ (j) : MemLp (fun p => fderiv ℝ (fun z => ψ z / r z) p (0, EuclideanSpace.single j 1)) ∞ ν :=
      ((hψr.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hψrc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
    have hin (i j) : Integrable (fun p => A i j p * H k i p *
        fderiv ℝ (fun z => ψ z / r z) p (0, EuclideanSpace.single j 1)) ν :=
      (((hdψ j).mul (r := 2) ((Lp.memLp (H k i)).mul (r := 2) (hAmem i j))).integrable (by norm_num))
    have heach (j) : (∫ p, P k j p * fderiv ℝ (fun z => ψ z / r z) p
        (0, EuclideanSpace.single j 1) ∂ν) =
        ∑ i, ∫ p, A i j p * H k i p * fderiv ℝ (fun z => ψ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν := by
      simp only [P, Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => hin i j)
    simp_rw [heach]
    rw [Finset.sum_comm]
    exact hfixed k ψ hψ hψc hψs
  have hKO : Icc a b ×ˢ closure Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg ⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩, hΩ₀Ω hp.2⟩
  have hcore (k) := exists_lp_dual_of_fixed_density_cutoff_equation
    (q := q) α hΩ₀ hΩ₀c hΩ₀s (D.regular_isOpen.prod hΩ) hKO hrall hrne
    (hC k) (hP k) (hw k) hη hηc hηs
  have hQeq (k j) (p : ℝ × EuStd) : (η p.2 / r p) * P k j p = Q k j p := by
    simp only [P, Q, Finset.mul_sum, mul_assoc]
  have hBeq (k) (p : ℝ × EuStd) : (η p.2 * C k p - ∑ j, P k j p * fderiv ℝ
      (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) = B k p := by
    simp only [P, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k j
    simpa only [hQeq] using (hcore k).1 j
  · intro k
    simpa only [hBeq] using (hcore k).2.1
  · intro k
    simpa only [hQeq, hBeq] using (hcore k).2.2.1
  · intro k v τ hτ hτc hτs
    simpa only [hQeq, hBeq] using (hcore k).2.2.2 v τ hτ hτc hτs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
