import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientH1
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakPartialDual
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

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

theorem IsWeakEvolutionSolution.exists_timeH1_weighted_gradient_dual
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
    (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ Ω₀) (k : Fin (Module.finrank ℝ EuN)) :
    ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
      ∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ v : H1ComplDirichlet q,
        w.toFun s v = ∫ z in Ω₀,
          dirichletLocalWeakPartialLp q α hΩ₀
            (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
            (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u (t₀ + s)) z * c z *
            H1ComplDirichletToLp q v ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let R : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω₀) :=
    (chartRestrictionLp q α hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) 2).comp
      (H1ComplDirichletToLp q)
  let D : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω₀) :=
    dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k
  obtain ⟨L, _, hL⟩ := exists_lp_dual_weak_partial q α hΩ₀ hΩ₀c hΩ₀s hc hcc hcs k
  obtain ⟨z, hz⟩ := hu.exists_timeH1_chartInverse hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω
  obtain ⟨w, _, hw, _⟩ := exists_timeH1_comp_clm
    (X := Lp ℝ 2 (volume.restrict Ω₀)) (Y := H1ComplDirichlet q →L[ℝ] ℝ) L z
  refine ⟨w, ?_⟩
  filter_upwards [hz, ae_restrict_mem measurableSet_Icc] with s hs hsI
  intro v
  have hRz : z.toFun s = R (u (t₀ + s)) := by
    apply Lp.ext
    exact hs.trans (chartRestrictionLp_coeFn q α hΩ₀.measurableSet hΩ₀c
      (hΩ₀s.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q (u (t₀ + s)))).symm
  have hleft : w.toFun s v = L (R (u (t₀ + s))) v :=
    congrArg (fun F : H1ComplDirichlet q →L[ℝ] ℝ => F v)
      ((hw s hsI).trans (congrArg L hRz))
  apply hleft.trans
  apply (hL (u (t₀ + s)) v).trans
  apply integral_congr_ae
  filter_upwards [chartRestrictionLp_coeFn q α hΩ₀.measurableSet hΩ₀c
    (hΩ₀s.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q v)] with x hx
  change _ * (R v : EuStd → ℝ) x = _
  exact congrArg (fun y : ℝ => D (u (t₀ + s)) x * c x * y) hx

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_gradient_mass_dual
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
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω₀) (k : Fin (Module.finrank ℝ EuN)) :
    ∃ v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc t₀ t₁)),
      ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
        (∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁),
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u t) z)) ∧
        ∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z) := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let c : EuStd → ℝ := fun x => MetricExtension.densityOnEuclid q α x * η x
  have hcs : tsupport c ⊆ Ω₀ := tsupport_mul_subset_right.trans hηs
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (((MetricExtension.densityOnEuclid_contDiffOn q α).mono
      (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset)))).mul hη.contDiffOn).contDiff_of_tsupport_subset hΩ₀ hcs
  have hcc : HasCompactSupport c := hηc.mul_left
  obtain ⟨w, hw⟩ := hu.exists_timeH1_weighted_gradient_dual hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁
    hΩ₀ hΩ₀Ω hc hcc hcs k
  obtain ⟨v, hv⟩ := hu.exists_lp_h1_gradient_chartPullback_mul hXcont hacont α hΩ₀ hΩ₀c hΩ₀s hXsmooth
    ht₀ ht₁ hη hηc hηs k
  refine ⟨v, w, hv, ?_⟩
  have hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht₀.le.trans ht.1, ht.2.trans ht₁.le⟩
  have hshift : MeasurePreserving (fun s : ℝ => t₀ + s) (timeMeasure (t₁ - t₀))
      ((timeMeasure T).restrict (Icc t₀ t₁)) := by
    exact measurePreserving_add_right_timeMeasure_restrict hI
  filter_upwards [hw, hshift.quasiMeasurePreserving.ae hv] with t ht hvt
  intro z
  exact (ht z).trans (inner_eq_integral_chartPullback_mul q α hΩ₀s hη hηs
    (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u (t₀ + t))) (v (t₀ + t)) z hvt).symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
