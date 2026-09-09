import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientEnergy
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

section Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_lp_scalar_source_of_weak_gradient
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω)
    (B V : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    {A : Fin d → Fin d → ℝ × E → ℝ}
    (hA : ∀ i j, MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i j, MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i j, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω)
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => V (t, x)) Ω) :
    ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (A i j p * H j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
        (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
          (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, (∑ i, A i j p * V p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  obtain ⟨D, hD, hDtest⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ (fun _ => V) (fun _ => H)
      hA hDA hAsmooth (fun _ => hweak)
  refine ⟨B - D, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub B D, hD] with p hp hDp
    simpa only [Pi.sub_apply, hDp] using hp
  · intro φ hφ hφc hφs
    have hBint : Integrable (fun p => B p * φ p) (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp B).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hDint : Integrable (fun p => D p * φ p) (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp D).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have heq : (∫ p, (B - D) p * φ p ∂μ.prod (volume.restrict Ω)) =
        (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) -
          ∫ p, D p * φ p ∂μ.prod (volume.restrict Ω) := by
      rw [← integral_sub hBint hDint]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub B D] with p hp
      simp only [hp, Pi.sub_apply, sub_mul]
    rw [heq, hDtest φ hφ hφc hφs, sub_neg_eq_add]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [Finset.sum_mul]
    symm
    apply integral_finsetSum
    intro i _
    have hflux : MemLp (fun p => A i j p * V p) 2 (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp V).mul (hA i j)
    exact (hflux.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1))

end Euclidean

open Bundle Manifold
open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

omit [T2Space M] [CompactSpace M] in
private theorem exists_lp_scalar_source_of_cutoff_gradient
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (hμ : μ ≤ volume.restrict J)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (B V : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => V (t, x)) Ω) :
    let A := fun i j (p : ℝ × EuStd) =>
      (MetricExtension.densityOnEuclid q α p.2 *
        MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
    ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (A i j p * H j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
        (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
          (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, (∑ i, A i j p * V p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  intro A
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hUt : U ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ U) := by
    have hden : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2)
        (D.regular ×ˢ U) :=
      (MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => hUt hp.2)
    have hηd : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      (hη.contDiff_fderiv_apply (by simp)).comp (contDiff_snd.prodMk contDiff_const)
    exact (hden.mul (MetricExtension.invGramOnEuclid_family_contDiffOn
      hG Subset.rfl α (show U ⊆ U from Subset.rfl) i j)).mul hηd.contDiffOn
  have hAmem (i j) : MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have h := ((hA i j).continuousOn.mono (prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)) := by
    have hc := (spatialFDeriv_contDiffOn (G := fun t x => A i j (t, x))
      D.regular_isOpen.uniqueDiffOn hU (hA i j)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single j 1))
    have h := (hc.continuousOn.mono (prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hAsmooth (i j) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω := by
    filter_upwards [(ae_restrict_mem hJc.measurableSet).filter_mono (ae_mono hμ)] with t ht
    exact (hA i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hJ ht, hΩs (subset_closure hx)⟩)
  exact exists_lp_scalar_source_of_weak_gradient hΩ B V H
    hAmem hDA hAsmooth hweak

private theorem exists_lp_scalar_source_of_cutoff_gradient_pairing
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (hμ : μ ≤ volume.restrict J)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    {B V : ℝ × EuStd → ℝ}
    (hB : MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hV : MemLp V 2 (μ.prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => hV.toLp V (t, x)) Ω)
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ :
      let E := fun j p => ∑ i,
        (MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
            fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
      ∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * β t z ∂μ) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
            ∂μ.prod (volume.restrict Ω)) +
          ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      let P := fun i j (p : ℝ × EuStd) =>
        (MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
            fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (P i j p * H j p +
          fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ z : Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, β t (z t) ∂μ) =
          ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  let ν := μ.prod (volume.restrict Ω)
  let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2
  let E := fun j p => ∑ i,
    (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
      fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
  let W : Lp ℝ 2 ν := hV.toLp V
  have hW : W =ᵐ[ν] V := hV.coeFn_toLp
  let BW : Lp ℝ 2 ν := hB.toLp B
  have hBWeq : BW =ᵐ[ν] B := hB.coeFn_toLp
  obtain ⟨f, hf, hftest⟩ := exists_lp_scalar_source_of_cutoff_gradient q hG hJc hJ
    α hΩ hΩc hΩs (μ := μ) hμ hη BW W H hweak
  refine ⟨f, ?_⟩
  classical
  intro P
  have hfeq : f =ᵐ[ν] fun p => B p - ∑ i, ∑ j,
      (P i j p * H j p +
        fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p) := by
    filter_upwards [hf, hW, hBWeq] with p hp hWp hBp
    simpa only [hWp, hBp] using hp
  have htest (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω) :
      (∫ p, f p * φ p ∂ν) = (∫ p, B p * φ p ∂ν) +
        ∑ j, ∫ p, E j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
    rw [hftest φ hφ hφc hφs]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · apply integral_congr_ae
      filter_upwards [hBWeq] with p hp
      rw [hp]
    · apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [hW] with p hp
      rw [hp]
  have hPs (t : ℝ) (i j) : tsupport (fun x => P i j (t, x)) ⊆ tsupport η :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
  have hPzero (p : ℝ × EuStd) (hp : p.2 ∉ tsupport η) (i j) : P i j p = 0 := by
    exact image_eq_zero_of_notMem_tsupport (f := fun x => P i j (p.1, x))
      (fun hx => hp (hPs p.1 i j hx))
  have hDPzero (p : ℝ × EuStd) (hp : p.2 ∉ tsupport η) (i j) :
      fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun hx => hp (hPs p.1 i j hx))]
    rfl
  have hS : ∀ᵐ p ∂ν, p.2 ∉ tsupport η → f p - B p = 0 := by
    filter_upwards [hfeq] with p hp hout
    simp only [hp, hPzero p hout, hDPzero p hout, zero_mul, add_zero,
      Finset.sum_const_zero, sub_zero, sub_self]
  have hE : ∀ j, ∀ᵐ p ∂ν, p.2 ∉ tsupport η → E j p = 0 := by
    intro j
    exact Filter.Eventually.of_forall fun p hp => by
      change (∑ i, P i j p * V p) = 0
      simp only [hPzero p hp, zero_mul, Finset.sum_const_zero]
  refine ⟨hfeq, ?_⟩
  exact integral_chart_source_dual_eq_of_compact_flux_pairing α hΩ hΩc hΩs
    hηc.isCompact hηs f hB hS hE htest β hβ

private theorem exists_source_of_time_packet
    {A B C D E : Type*} {P : A → Prop} {Q : A → B → Prop} {R : B → C → Prop}
    {S : A → C → Prop} {T : C → Prop} {U : D → Prop} {V : A → C → D → Prop} {Y : A → D → Prop} {W : D → E → Prop}
    (h : ∃ a b c, P a ∧ Q a b ∧ R b c ∧ S a c ∧ T c ∧ ∃ d, U d ∧ V a c d ∧ Y a d)
    (hsource : ∀ d, U d → ∃ e, W d e) :
    ∃ a b c d e, P a ∧ Q a b ∧ R b c ∧ T c ∧ U d ∧ V a c d ∧ W d e := by
  obtain ⟨a, b, c, hp, hq, hr, _, ht, d, hu, hv, _⟩ := h
  obtain ⟨e, he⟩ := hsource d hu
  exact ⟨a, b, c, d, e, hp, hq, hr, ht, hu, hv, he⟩

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_gradient_scalar_source
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
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      ∃ B : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ,
      let Q := fun k j p => ∑ i, (η p.2 / r p) * A i j p * H k i p
      let E := fun k j p => ∑ i,
        (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V k p
      let P := fun i j (p : ℝ × EuStd) =>
        (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      (∀ k j, MemLp (Q k j) 2 ν) ∧ (∀ k, MemLp (B k) 2 ν) ∧
      ∀ k, ∃ v : Lp (H1ComplDirichlet q) 2 μ,
        ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∃ f : Lp ℝ 2 ν,
        (∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u t) z)) ∧
        (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z)) ∧
        (w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s)) ∧
        (∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t z ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν) ∧
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
        (f =ᵐ[ν] fun p => B k p - ∑ i, ∑ j,
          (P i j p * H k j p +
            fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V k p)) ∧
        (∀ z : Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, β t (z t) ∂μ) =
            ∫ t, (∫ x in Ω₀, f (t, x) * H1ComplDirichletToLp q (z t)
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ) := by
  intro μ ν ρ σ r A V
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hF, hfixed, hsource⟩ :=
    hu.exists_timeH1_cutoff_gradient_energy hXcont hacont α hΩ hΩc hΩs hXsmooth
      ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω hη hηc hηs
  let C := fun k p => (r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * V k p)
  let B := fun k p => η p.2 * C k p -
    ∑ i, ∑ j, A i j p * H k i p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
  refine ⟨H, hH, hHsym, B, ?_⟩
  intro Q E P
  obtain ⟨hQ, hB, c, hc, hpacket⟩ := hsource
  refine ⟨hQ, hB, ?_⟩
  intro k
  apply exists_source_of_time_packet (hpacket k)
  intro β hβ
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hν : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV : MemLp (V k) 2 ν := (Lp.memLp (V k)).mono_measure hν
  let W : Lp ℝ 2 ν := hV.toLp (V k)
  have hW : W =ᵐ[ν] V k := hV.coeFn_toLp
  have hweak (j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H k j (t, x)) (fun x => W (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [hH k j, Measure.ae_ae_of_ae_prod hW, hc] with t ht hwt hct
    have he : (fun x => W (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  obtain ⟨f, hpair⟩ := exists_lp_scalar_source_of_cutoff_gradient_pairing
    q hG isCompact_Icc hreg α hΩ₀ hΩ₀c hΩ₀s (μ := μ) Measure.restrict_le_self
    hη hηc hηs (hB k) hV (H k) hweak β hβ
  exact ⟨f, hpair⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
