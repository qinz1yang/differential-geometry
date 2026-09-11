import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorRegularity
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff

noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology
namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Chart
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
private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem IsWeakEvolutionSolution.exists_lp_h1_gradient_chartPullback_mul
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
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuN)) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuN) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt EuN (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (k : Fin (Module.finrank ℝ EuN)) :
    ∃ v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc t₀ t₁)), ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁),
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) z) := by
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  have hμle : μ ≤ timeMeasure T := Measure.restrict_le_self
  obtain ⟨Ω₀, hΩ₀, hKΩ₀, hΩ₀Ω, hΩ₀c⟩ :=
    exists_open_between_and_isCompact_closure hηc.isCompact hΩ hηs
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let uμ : Lp (H1ComplDirichlet q) 2 μ := ((Lp.memLp u).mono_measure hμle).toLp u
  let A := dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k
  let P : Lp (Lp ℝ 2 (volume.restrict Ω₀)) 2 μ := A.compLpL 2 μ uμ
  choose dv hdv using hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  let W : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω₀)) := fun i => dv k i
  have hPae : ∀ᵐ t ∂μ, (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      (A (u t) : EuStd → ℝ) := by
    filter_upwards [A.coeFn_compLpL uμ, MemLp.coeFn_toLp ((Lp.memLp u).mono_measure hμle)] with t ht hu_t
    rw [show P t = A (uμ t) from ht, hu_t]
  have hgrad (t : ℝ) :
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) := by
    have ho := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t))
    have hi := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t)
    have hLo := ((Lp.memLp (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t))).mono_measure
      (Measure.restrict_mono hsub le_rfl)).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hLi := (Lp.memLp (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t))).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀ ho hi hLo hLi
  have hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => W i (t,z)) (P t) Ω₀ := by
    intro i
    filter_upwards [hdv k i, hPae] with t ht hp
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      hΩ₀ i ((hgrad t).trans hp.symm) ht
  obtain ⟨v, hv⟩ := exists_lp_h1ComplDirichlet_chartPullback_mul_of_weak_partials
    q α hΩ₀ hΩ₀c hΩ₀s hη hηc hKΩ₀ P W hweak
  refine ⟨v, ?_⟩
  filter_upwards [hv, hPae] with t ht hp
  have hfg : (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) := hp.trans (hgrad t).symm
  have hall := (ae_restrict_iff' hΩ₀.measurableSet).mp hfg
  apply ht.trans
  apply DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_ae_eq_of_ae_eq q α
  filter_upwards [hall] with z hz
  by_cases hz' : z ∈ tsupport η
  · exact congrArg (fun r => η z * r) (hz (hKΩ₀ hz'))
  · have he : η z = 0 := image_eq_zero_of_notMem_tsupport hz'
    simp [he]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
