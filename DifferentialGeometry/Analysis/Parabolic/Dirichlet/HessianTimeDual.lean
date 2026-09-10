import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HessianH1
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakSpatialDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict

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

theorem IsWeakEvolutionSolution.exists_timeH1_weighted_hessian_dual
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
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcs : tsupport c ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ i j, ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        ∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ v : H1ComplDirichlet q,
          w.toFun s v = ∫ z in Ω₀, H i j (t₀ + s, z) * c z *
            H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  intro μ H hH i j
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  obtain ⟨z, hz⟩ := hu.exists_timeH1_localWeakPartial hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω i
  have hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht₀.le.trans ht.1, ht.2.trans ht₁.le⟩
  have hshift : MeasurePreserving (fun s : ℝ => t₀ + s)
      (timeMeasure (t₁ - t₀)) μ := measurePreserving_add_right_timeMeasure_restrict hI
  have hweak : ∀ᵐ s ∂timeMeasure (t₁ - t₀), DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t₀ + s, x)) (z.toFun s) Ω₀ := by
    filter_upwards [hz, hshift.quasiMeasurePreserving.ae (hH i j)] with s hzs hHs
    intro φ hφ hφc hφs
    refine (integral_congr_ae ?_).trans (hHs φ hφ hφc hφs)
    filter_upwards [hzs] with x hx
    exact congrArg (· * fderiv ℝ φ x (EuclideanSpace.single j 1)) hx
  obtain ⟨w, hw, _⟩ := exists_timeH1_weighted_weak_partial_dual q α hΩ₀ hΩ₀c hΩ₀s
    hc hcs j z (fun p => H i j (t₀ + p.1, p.2))
    (hshift.quasiMeasurePreserving.ae ((Lp.memLp (H i j)).prodMk_left (by norm_num))) hweak
  exact ⟨w, hw⟩

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_hessian_mass_dual
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
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∃ v : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp (H1ComplDirichlet q) 2 μ,
        (∀ i j, ∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v i j t) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I_hs) (M := M) q]
            chartPullback I_hs α (fun z => η z * H i j (t, z))) ∧
        ∀ i j, ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
          ∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
            w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v i j (t₀ + s)))
              (H1ComplDirichletToLp q z) := by
  intro μ H hH
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let c : EuStd → ℝ := fun z => MetricExtension.densityOnEuclid q α z * η z
  have hcs : tsupport c ⊆ Ω₀ := tsupport_mul_subset_right.trans hηs
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (((MetricExtension.densityOnEuclid_contDiffOn q α).mono
      (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset)))).mul
        hη.contDiffOn).contDiff_of_tsupport_subset hΩ₀ hcs
  obtain ⟨_, _, v, hv, _⟩ := hu.exists_lp_h1_hessian_chartPullback_mul
    hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁.le hΩ₀ hΩ₀Ω hη hηs H hH
  refine ⟨v, hv, ?_⟩
  intro i j
  obtain ⟨w, hw⟩ := hu.exists_timeH1_weighted_hessian_dual hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω hc hcs H hH i j
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω₀)) := Lp.SecondCountableTopology
  obtain ⟨P, hP, _⟩ := Lp.exists_curry (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (H i j)
  have hvP : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v i j t) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * P t z) := by
    filter_upwards [hv i j, hP] with t hvt hPt
    apply hvt.trans
    apply chartPullback_ae_eq_of_ae_eq q α
    have hall := (ae_restrict_iff' hΩ₀.measurableSet).mp hPt
    filter_upwards [hall] with x hx
    by_cases hxs : x ∈ tsupport η
    · exact congrArg (η x * ·) (hx (hηs hxs)).symm
    · simp only [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  have hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht₀.le.trans ht.1, ht.2.trans ht₁.le⟩
  have hshift : MeasurePreserving (fun s : ℝ => t₀ + s)
      (timeMeasure (t₁ - t₀)) μ := measurePreserving_add_right_timeMeasure_restrict hI
  refine ⟨w, ?_⟩
  filter_upwards [hw, hshift.quasiMeasurePreserving.ae hvP,
    hshift.quasiMeasurePreserving.ae hP] with s hws hvs hPs
  intro z
  rw [hws z, inner_eq_integral_chartPullback_mul q α hΩ₀s hη hηs
    (P (t₀ + s)) (v i j (t₀ + s)) z hvs]
  apply integral_congr_ae
  filter_upwards [hPs] with x hx
  change H i j (t₀ + s, x) * c x * _ = P (t₀ + s) x * c x * _
  rw [hx]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
