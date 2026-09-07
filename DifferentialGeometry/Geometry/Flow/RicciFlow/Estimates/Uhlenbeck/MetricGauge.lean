import DifferentialGeometry.Geometry.Metric.Family.Uhlenbeck
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricGaugeVelocityWithin_eq_ricciSharp_of_hasDerivWithinAt
    [BoundarylessManifold I M] (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} {t : ℝ} (hJ : UniqueDiffWithinAt ℝ J t) (x : M)
    (hg : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)) (t, x))
    (hflow : ∀ v w : TangentSpace I x, HasDerivWithinAt (fun s => (g s).inner x v w)
      (-2 * ricciTensor (I := I) (g t) x v w) J t) :
    metricGaugeVelocityWithin g J t x = ricciSharp (I := I) (g t) x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hgtime := ContMDiffWithinAt.fiberwise_time_contDiffWithinAt
    (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (V := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (f := fun s y => (g s).inner y) (u := univ) (s := J) hg (mem_univ x)
  have hgderiv := (hgtime.differentiableWithinAt (by simp)).hasDerivWithinAt
  ext v
  apply (DifferentialGeometry.Geometry.Operator.metricFlatMap (I := I) (g t) x).injective
  ext w
  change (g t).inner x (metricGaugeVelocityWithin g J t x v) w =
    (g t).inner x (ricciSharp (I := I) (g t) x v) w
  rw [inner_metricGaugeVelocityWithin, inner_ricciSharp]
  have heval := (hgderiv.clm_apply (hasDerivWithinAt_const t J v)).clm_apply
    (hasDerivWithinAt_const t J w)
  simp only [map_zero, add_zero] at heval
  have heq := (heval.derivWithin hJ).symm.trans ((hflow v w).derivWithin hJ)
  rw [heq]
  ring

theorem metricGaugeVelocityWithin_eq_ricciSharp [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {J : Set ℝ} {t : ℝ}
    (ht : t ∈ D.regular) (hJ : UniqueDiffWithinAt ℝ J t) (x : M) :
    metricGaugeVelocityWithin S.family.metric J t x =
      ricciSharp (I := I) (S.family.metric t) x := by
  apply metricGaugeVelocityWithin_eq_ricciSharp_of_hasDerivWithinAt S.family.metric hJ x
    (((hS.smoothMetric.metricCLMSmoothAt
      (x := x) (D.regular_isOpen.mem_nhds ht)).contMDiffWithinAt).of_le (by simp))
  intro v w
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
    (metricDerivAt S hS ⟨t, ht⟩ x v w).hasDerivWithinAt (s := J)

theorem metricGaugeVelocity_eq_ricciSharp [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t : ℝ} (ht : t ∈ D.regular) (x : M) :
    metricGaugeVelocity S.family.metric t x =
      ricciSharp (I := I) (S.family.metric t) x := by
  have h := metricGaugeVelocityWithin_eq_ricciSharp S hS ht
    (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := t)) x
  rw [metricGaugeVelocityWithin_eq_metricGaugeVelocity _ (by simp) _] at h
  exact h

theorem exists_uhlenbeck_isometry_on_interval_of_hasDerivWithinAt [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)))
    (hflow : ∀ t ∈ J, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) J t)
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (J ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (g t) x (ι t x v)) J t) ∧
      ∀ t ∈ J, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w := by
  obtain ⟨ι, hinit, hsmooth, hinvsmooth, hderiv, hmetric⟩ :=
    exists_metric_freezing_isometry_on_interval hJ ht₀ g hg h ι₀ hι₀ h₀
  refine ⟨ι, hinit, hsmooth, hinvsmooth, ?_, hmetric⟩
  intro x v t ht
  rcases J.subsingleton_or_nontrivial with hs | hn
  · exact HasFDerivWithinAt.of_subsingleton hs
  have hdiff := uniqueDiffOn_convex hJ.convex
    (hJ.convex.nontrivial_iff_nonempty_interior.mp hn)
  have hvelocity := metricGaugeVelocityWithin_eq_ricciSharp_of_hasDerivWithinAt g (hdiff t ht) x
    ((hg (t, x) ⟨ht, mem_univ x⟩).of_le (by simp)) (hflow t ht x)
  simpa only [hvelocity] using hderiv x v t ht

theorem exists_uhlenbeck_isometry_on_interval [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hJD : J ⊆ D.regular)
    (h : RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (J ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (J ×ˢ (univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) ∧
      ∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = h.inner x v w := by
  have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set M)) := fun p hp =>
    (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hJD hp.1))).contMDiffWithinAt
  apply exists_uhlenbeck_isometry_on_interval_of_hasDerivWithinAt hJ ht₀ S.family.metric hg
    (h := h) (ι₀ := ι₀) (hι₀ := hι₀) (h₀ := h₀)
  intro t ht x v w
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
    (metricDerivAt S hS ⟨t, hJD ht⟩ x v w).hasDerivWithinAt (s := J)

end DifferentialGeometry.PDE.RicciFlow
