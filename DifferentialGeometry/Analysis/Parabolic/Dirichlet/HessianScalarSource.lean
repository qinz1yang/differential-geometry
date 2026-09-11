import DifferentialGeometry.Analysis.Integration.Lp.Pairing
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HessianTimeEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffForcing
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffScalarSource

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
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

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric I_hs M} :
    SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

private theorem exists_cutoff_scalar_source
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} (hμ : μ ≤ volume.restrict J)
    (H : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : Lp (H1ComplDirichlet q) 2 μ)
    (ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => K j (t, z)) (fun z => H (t, z)) Ω)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod (volume.restrict Ω)))
    (hB : MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hℓ : ∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
      MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
    let P := fun i j (p : ℝ × EuStd) => c i j p * fderiv ℝ η p.2 (EuclideanSpace.single i 1)
    let E := fun j p => ∑ i, P i j p * H p
    (∀ j, ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω,
      Q j (t, x) = (∑ i, c i j (t, x) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) - E j (t, x)) →
    ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
        (∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
          (∫ t, τ t * β t z ∂μ) =
            (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) +
              ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
                ∂μ.prod (volume.restrict Ω)) ∧
        (∀ z : Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
            ∫ t, (∑ i, ∑ j, ∫ y in Ω,
              dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
                c i j (t, y) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y) ∂μ) ∧
        (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
          (P i j p * K j p +
            fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * H p)) ∧
        ∀ z : Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, β t (z t) ∂μ) =
            ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  let : IsLocallyFiniteMeasure μ := Measure.isLocallyFiniteMeasure_of_le hμ
  intro c P E hflux
  have hexForm := exists_local_dirichlet_bilinear_form_family q hG
    hJc hJ α hΩ hΩc hΩs
  let form := Classical.choose hexForm
  have hform := (Classical.choose_spec hexForm).1
  change ∀ t u z, form t u z = _ at hform
  obtain ⟨Lm, hβ, hLm⟩ := exists_cutoff_forcing_dual q hG hJc hJ
    α hΩ hΩc hΩs hμ (fun p => H p) (Lp.memLp H) hη v ℓ form hform
    Q B hQ hℓ hflux
  have hweak' (j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => K j (t, x))
      (fun x => (Lp.memLp H).toLp H (t, x)) Ω := by
    simpa only [Lp.toLp_coeFn] using hweak j
  obtain ⟨f, hf, hfsource⟩ := exists_lp_scalar_source_of_cutoff_pairing q hG
    hJc hJ α hΩ hΩc hΩs hμ hη hηs hB (Lp.memLp H) K hweak' (ℓ + Lm) hβ
  refine ⟨ℓ + Lm, f, hβ, ?_, hf, hfsource⟩
  intro z
  have he := Lp.integral_add_apply ℓ Lm z
  rw [hLm] at he
  simp only [hform] at he
  change _ = _ + _ at he
  exact eq_sub_of_add_eq he.symm

private theorem ae_cutoff_flux_eq
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} (G : MetricConnectionFamilyOn (I := I_hs) (M := M) D)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} (H : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : ℝ → H1ComplDirichlet q) {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * H (t, z)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => H (t, z)) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) => MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    let c := fun i j (p : ℝ × EuStd) => σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2
    ∀ j, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω,
      (∑ i, (η z / r (t, z)) * A i j (t, z) * K i (t, z)) =
        (∑ i, c i j (t, z) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) z) -
          ∑ i, c i j (t, z) * fderiv ℝ η z (EuclideanSpace.single i 1) * H (t, z) := by
  intro ρ σ r A c j
  classical
  have hpartial (i) : ∀ᵐ t ∂μ,
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
        (fun z => η z * K i (t, z) + fderiv ℝ η z (EuclideanSpace.single i 1) * H (t, z)) :=
    ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul q α hΩ hΩc hΩs v hv
      (Lp.memLp H) (Lp.memLp (K i)) i (hweak i) hη
  filter_upwards [ae_all_iff.mpr hpartial] with t ht
  filter_upwards [ae_all_iff.mpr ht, ae_restrict_mem hΩ.measurableSet] with z hz hzm
  have hcoeff (i) : A i j (t, z) / r (t, z) = c i j (t, z) :=
    weightedInvGramOnEuclid_div_density_ratio q (G.metric t) α i j z
      (hΩs.trans (image_mono interior_subset) (subset_closure hzm))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i, ← hcoeff i]
  simp only [div_eq_mul_inv]
  ring

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_hessian_scalar_source
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
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ S : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i j, H i j = H j i) ∧
      (∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
        (fun z => K i j l (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
      (∀ k i l, K k i l = K k l i) ∧
      (∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k l p * φ p ∂ν) ∧
      let C := fun k l p => (r p)⁻¹ * S k l p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * H k l p)
      let B := fun k l p => η p.2 * C k l p -
        ∑ i, ∑ j, A i j p * K k l i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      let P := fun i j (p : ℝ × EuStd) =>
        (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      ∃ v : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp (H1ComplDirichlet q) 2 μ,
        (∀ k l, ∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v k l t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            chartPullback I_hs α (fun z => η z * H k l (t, z))) ∧
        ∀ k l, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
          ∃ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          ∃ f : Lp ℝ 2 ν,
            (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
              w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v k l (t₀ + s)))
                (H1ComplDirichletToLp q z)) ∧
            w.deriv =ᵐ[timeMeasure (t₁ - t₀)] (fun s => ℓ (t₀ + s)) ∧
            (∀ z : Lp (H1ComplDirichlet q) 2 μ,
              (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
                ∫ t, (∑ i, ∑ j, ∫ y in Ω₀,
                  dirichletLocalWeakPartialLp q α hΩ₀
                    (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                    (hΩ₀Ω.trans (subset_closure.trans hΩs)) i (v k l t) y *
                    (MetricExtension.densityOnEuclid q α y *
                      MetricExtension.invGramOnEuclid (G.metric t) α i j y) *
                    dirichletLocalWeakPartialLp q α hΩ₀
                      (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                      (hΩ₀Ω.trans (subset_closure.trans hΩs)) j (z t) y) ∂μ) ∧
            (f =ᵐ[ν] fun p => B k l p - ∑ i, ∑ j,
              (P i j p * K k l j p +
                fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * H k l p)) ∧
            (∀ z : Lp (H1ComplDirichlet q) 2 μ,
              (∫ t, β t (z t) ∂μ) =
                ∫ t, (∫ x in Ω₀, f (t, x) * H1ComplDirichletToLp q (z t)
                  ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ) := by
  intro μ ν ρ σ r A
  classical
  have hex := hu.exists_timeH1_cutoff_hessian_dual_deriv hXcont hacont α hΩ hΩc hΩs hXsmooth
    ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω hη hηs
  let H := hex.choose
  let K := hex.choose_spec.choose
  let S := hex.choose_spec.choose_spec.choose
  have hp := hex.choose_spec.choose_spec.choose_spec
  have hH := hp.1
  have hHsym := hp.2.1
  have hK := hp.2.2.1
  have hKsym := hp.2.2.2.1
  have hS := hp.2.2.2.2.1
  have hsource := hp.2.2.2.2.2.2
  refine ⟨H, K, S, hH, hHsym, hK, hKsym, hS, ?_⟩
  intro C B P
  let Q := fun k l j p => ∑ i, (η p.2 / r p) * A i j p * K k l i p
  have hQ := hsource.1
  have hB := hsource.2.1
  let v := hsource.2.2.choose
  have hv := hsource.2.2.choose_spec.1
  have htime := hsource.2.2.choose_spec.2
  refine ⟨v, hv, ?_⟩
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  intro k l
  let ℓ := (htime k l).choose
  let w := (htime k l).choose_spec.choose
  have htime' := (htime k l).choose_spec.choose_spec
  have hℓ := htime'.1
  have hw := htime'.2.1
  have hd := htime'.2.2.1
  have hflux := ae_cutoff_flux_eq q G α hΩ₀ hΩ₀c hΩ₀s (H k l) (K k l)
    (fun t => v k l t) (hv k l) (hK k l) hη
  obtain ⟨β, f, _, hpair, hf, hfsource⟩ := exists_cutoff_scalar_source q hG
    isCompact_Icc hreg α hΩ₀ hΩ₀c hΩ₀s (μ := μ) Measure.restrict_le_self
    (H k l) (K k l) (v k l) ℓ hη hηs (hK k l) (Q k l) (B k l)
    (hQ k l) (hB k l) hℓ hflux
  exact ⟨ℓ, w, β, f, hw, hd, hpair, hf, hfsource⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
