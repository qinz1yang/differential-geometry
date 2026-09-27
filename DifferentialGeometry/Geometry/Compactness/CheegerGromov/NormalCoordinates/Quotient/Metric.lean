import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Smooth
import DifferentialGeometry.Topology.Manifold.OpenTransitionDerivative
import DifferentialGeometry.Geometry.Metric.Construction.OpenCoefficients
import DifferentialGeometry.Geometry.Metric.ChartGluing

section

section

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


theorem IntrinsicBallChart.exists_mfderiv_eq_comp_transition_of_buffered_inclusion_eq
    (hdiff : ∀ a, DifferentiableOn ℝ (J a) (Metric.ball (0 : E) (ρ / 2))) :
    let U : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (i j : ι) (z w : U), D.toGlueData.ι i z = D.toGlueData.ι j w →
      ∃ h : near i j = true, J ⟨(i, j), h⟩ z = w ∧
        mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
          (fun z : U => D.toGlueData.ι i z) z =
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
          (fun z : U => D.toGlueData.ι j z) w).comp (fderiv ℝ (J ⟨(i, j), h⟩) z) := by
  intro U D C hchart i j z w hzw
  let := C
  have hrel : ∀ (i j : ι) (z w : U),
      D.Rel ⟨i, z⟩ ⟨j, w⟩ ↔ ∃ h : near i j = true, J ⟨(i, j), h⟩ z = w := by
    intro i j z w
    dsimp only [D, IntrinsicBallChart.bufferedTransitionGlueData]
    exact TopCat.GlueData.rel_iff_graph _ _ _ _ _ _ _ _ _ _ i j z w
  have hgraph : ∀ (i j : ι) (z w : U),
      D.toGlueData.ι i z = D.toGlueData.ι j w ↔
      ∃ h : near i j = true, J ⟨(i, j), h⟩ z = w := by
    intro i j z w
    exact (D.ι_eq_iff_rel i j z w).trans (hrel i j z w)
  obtain ⟨hnear, hJzw⟩ := (hgraph i j z w).mp hzw
  refine ⟨hnear, hJzw, ?_⟩
  exact Topology.Manifold.mfderiv_eq_comp_fderiv_of_open_transition U
    (fun z : U => D.toGlueData.ι i z) (fun z : U => D.toGlueData.ι j z)
    (J ⟨(i, j), hnear⟩)
    ((hdiff ⟨(i, j), hnear⟩).mono (Metric.ball_subset_ball (by linarith)))
    ((hchart j).contMDiff.mdifferentiable (by simp)) (fun u v huv => (hgraph i j u v).mpr ⟨hnear, huv⟩) z w hJzw

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

end

section

section

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


theorem IntrinsicBallChart.exists_smoothMetric_bufferedTransitionGlueData
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball (0 : E) ρ))
    (hsymm : ∀ i z, z ∈ Metric.ball (0 : E) ρ → ∀ v w, B i z v w = B i z w v)
    (hpos : ∀ i z, z ∈ Metric.ball (0 : E) ρ → ∀ v, v ≠ 0 → 0 < B i z v v)
    (hdiff : ∀ a, DifferentiableOn ℝ (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hmetric : ∀ a z, z ∈ Metric.ball (0 : E) (ρ / 2) →
      J a z ∈ Metric.ball (0 : E) ρ →
      B a.1.1 z = CheegerGromovCompactness.pullbackForm
        (B a.1.2 (J a z), fderiv ℝ (J a) z)) :
    let U : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      ∀ (_ : IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued),
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∃ gQ : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) D.toGlueData.glued,
        ∀ (i : ι) (z : U) (v w : E),
          gQ.inner (D.toGlueData.ι i z)
            (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
              (fun z : U => D.toGlueData.ι i z) z v)
            (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
              (fun z : U => D.toGlueData.ι i z) z w) = B i z v w := by
  dsimp only
  intro C hman hchart
  let U : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
  let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
  let := C
  let := hman
  let : T2Space D.toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space g hEnorm x hρ c near hclass J hcont hconv
  have hUρ : (U : Set E) ⊆ Metric.ball (0 : E) ρ := Metric.ball_subset_ball (by linarith)
  have hlocal (i : ι) : ∃ gi : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) U,
      ∀ z v w, gi.inner z v w = B i z v w :=
    Geometry.exists_smoothMetric_of_contDiffOn_bilinearField U (B i)
      (fun z hz => hsymm i z (hUρ hz))
      (fun z hz => hpos i z (hUρ hz)) ((hB i).mono hUρ)
  choose gi hgi using hlocal
  have hinj : ∀ i : ι, Function.Injective (fun z : U => D.toGlueData.ι i z) :=
    fun i => D.ι_injective i
  have hcover : ∀ q : D.toGlueData.glued, ∃ i : ι, ∃ z : U, D.toGlueData.ι i z = q :=
    D.ι_jointly_surjective
  have hcompat : ∀ (i j : ι) (z w : U) (hzw : D.toGlueData.ι i z = D.toGlueData.ι j w),
      hzw ▸ localPushInner (gi i) (fun z : U => D.toGlueData.ι i z) (hchart i) z =
        localPushInner (gi j) (fun z : U => D.toGlueData.ι j z) (hchart j) w := by
    intro i j z w hzw
    obtain ⟨hnear, hJzw, hd⟩ :=
      IntrinsicBallChart.exists_mfderiv_eq_comp_transition_of_buffered_inclusion_eq
        g hEnorm x hρ c near hclass J hcont hconv hdiff C hchart i j z w hzw
    apply localPushInner_eq_of_derivative_factorization (gi i) (gi j)
      (fun z : U => D.toGlueData.ι i z) (fun z : U => D.toGlueData.ι j z)
      (hchart i) (hchart j) z w hzw (fderiv ℝ (J ⟨(i, j), hnear⟩) (z : E)) hd
    intro v₁ v₂
    have hzhalf : (z : E) ∈ Metric.ball (0 : E) (ρ / 2) :=
      Metric.ball_subset_ball (by linarith) z.property
    have hwρ : J ⟨(i, j), hnear⟩ z ∈ Metric.ball (0 : E) ρ := by
      rw [hJzw]
      exact hUρ w.property
    have hb := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v₁ v₂)
      (hmetric ⟨(i, j), hnear⟩ z hzhalf hwρ)
    change B i z v₁ v₂ = B j (J ⟨(i, j), hnear⟩ z)
      ((fderiv ℝ (J ⟨(i, j), hnear⟩) z) v₁)
      ((fderiv ℝ (J ⟨(i, j), hnear⟩) z) v₂) at hb
    rw [hJzw] at hb
    exact (hgi i z v₁ v₂).trans (hb.trans (hgi j w _ _).symm)
  obtain ⟨gQ, hgQ, _⟩ := Geometry.Metric.exists_unique_metric_of_localDiffeomorph_cover
    (fun i (z : U) => D.toGlueData.ι i z) hchart hinj hcover gi hcompat
  refine ⟨gQ, ?_⟩
  intro i z v w
  have he := congrArg (fun g : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) U =>
    g.inner z v w) (hgQ i)
  exact he.trans (hgi i z v w)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

end
