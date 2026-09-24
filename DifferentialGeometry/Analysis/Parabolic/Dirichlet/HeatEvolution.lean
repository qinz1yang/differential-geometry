import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakFormIntegration
import DifferentialGeometry.Geometry.Metric.Family.UniformEquivalence
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.CompactVolumeEquivalence
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CometricEvolution
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Gradient
import DifferentialGeometry.Geometry.Operator.Divergence
import DifferentialGeometry.Geometry.Operator.DivergenceMetricChange

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian (smoothMulLp)
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem integral_dirichlet_heat_adjoint
    (q h : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hY : (Y : ∀ x, TangentSpace (I_half n) x) =
      gradientFun h (fun x => Real.log (riemannianVolumeDensity q h x)))
    (a : C^∞⟮I_half n, M; ℝ⟯) (U : DirichletHs q 0) (φ : SmoothScalarDirichlet q) :
    (∫ x, dirichletHsZeroEquivL2 q U x *
      WithBoundary.ΔGWithBoundary q φ.smooth φ.interior_support x
      ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) +
    (∫ x, dirichletHsZeroEquivL2 q U x *
      divergence (leviCivitaConnectionOfMetric q)
        (WithBoundary.gradGWithBoundarySection h φ.smooth φ.interior_support -
          WithBoundary.gradGWithBoundarySection q φ.smooth φ.interior_support) x
      ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) -
    (∫ x, dirichletHsZeroEquivL2 q U x *
      (tangentSectionAction Y φ.toFun x +
        (divergence (leviCivitaConnectionOfMetric q) Y x + a x) * φ.toFun x)
      ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) =
    ∫ x, dirichletHsZeroEquivL2 q U x *
      (riemannianVolumeDensity q h x * laplacian (leviCivitaConnectionOfMetric h) h
        (fun y => φ.toFun y / riemannianVolumeDensity q h y) x - a x * φ.toFun x)
      ∂riemannianVolumeMeasure (I := I_half n) (M := M) q := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) q
  let V := dirichletHsZeroEquivL2 q U
  let Δφ := WithBoundary.ΔGWithBoundary q φ.smooth φ.interior_support
  let Z := WithBoundary.gradGWithBoundarySection h φ.smooth φ.interior_support -
    WithBoundary.gradGWithBoundarySection q φ.smooth φ.interior_support
  let b := divergence (leviCivitaConnectionOfMetric q) Z
  let c := fun x => tangentSectionAction Y φ.toFun x +
    (divergence (leviCivitaConnectionOfMetric q) Y x + a x) * φ.toFun x
  have hi (w : M → ℝ) (hw : Continuous w) : Integrable (fun x => V x * w x) μ :=
    (Lp.memLp V).integrable_mul
      (hw.memLp_of_hasCompactSupport (p := 2) (HasCompactSupport.of_compactSpace _))
  have hiΔ := hi Δφ (WithBoundary.Δ_g_with_boundary_continuous q φ.smooth φ.interior_support)
  have hib := hi b (leviCivita_divergence_contMDiff q Z).continuous
  have hic := hi c
    ((DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_contMDiff
      Y φ.smooth).continuous.add
      (((leviCivita_divergence_contMDiff q Y).continuous.add a.contMDiff.continuous).mul
        φ.smooth.continuous))
  change (∫ x, V x * Δφ x ∂μ) + (∫ x, V x * b x ∂μ) -
    (∫ x, V x * c x ∂μ) = _
  have hisum : Integrable (fun x => V x * Δφ x + V x * b x) μ := hiΔ.add hib
  rw [← integral_add hiΔ hib, ← integral_sub hisum hic]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    have hbase : Δφ x = divergence (leviCivitaConnectionOfMetric q)
        (gradientFun q φ.toFun) x := by
      dsimp only [Δφ]
      rw [WithBoundary.Δ_g_with_boundary_def,
        DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_metricCov]
      rfl
    have hb : b x = divergence (leviCivitaConnectionOfMetric q)
        (gradientFun h φ.toFun) x -
        divergence (leviCivitaConnectionOfMetric q) (gradientFun q φ.toFun) x := by
      exact divergence_sub _
        ((gradientFun_smooth h φ.smooth).mdifferentiable (by simp) x)
        ((gradientFun_smooth q φ.smooth).mdifferentiable (by simp) x)
    rw [riemannianVolumeDensity_mul_laplacian_div q h φ.smooth x]
    change V x * Δφ x + V x * b x - V x * c x = _
    rw [hbase, hb]
    change V x * _ + V x * (_ - _) - V x *
      (mvfderiv (I := I_half n) φ.toFun x (Y x) +
        (divergence (leviCivitaConnectionOfMetric q) Y x + a x) * φ.toFun x) = _
    rw [hY]
    ring

theorem exists_local_dirichlet_heat_weak_solution
    {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric (I_half n) M}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D g)
    (h0reg : (0 : ℝ) ∈ D.regular)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯)
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M))) :
    let q := g 0
    ∃ T : ℝ, 0 < T ∧ Icc (0 : ℝ) T ⊆ D.regular ∧
      ∀ (u₀ : DirichletHs q 0) (f₀ : timeL2 (DirichletHs q (-1)) T),
        ∃ (u : timeH1 (DirichletHs q (-1)) T)
          (U₂ : timeL2 (DirichletHs q 1) T) (U₀ : ℝ → DirichletHs q 0),
          ContinuousOn U₀ (Icc (0 : ℝ) T) ∧ U₀ 0 = u₀ ∧
          (fun t => dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (U₂ t))
            =ᵐ[timeMeasure T] U₀ ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U₀ t) = u.toFun t) ∧
          ∀ᵐ t ∂timeMeasure T, ∀ φ : SmoothScalarDirichlet q,
            dirichletHsNegOneEquivH1Dual q (u.deriv t) (smoothToH1ComplDirichlet q φ) =
              (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
                (riemannianVolumeDensity q (g t) x *
                  laplacian (leviCivitaConnectionOfMetric (g t)) (g t)
                    (fun y => φ.toFun y / riemannianVolumeDensity q (g t) y) x -
                  a t x * φ.toFun x)
                ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) +
              dirichletHsNegOneEquivH1Dual q (f₀ t) (smoothToH1ComplDirichlet q φ) := by
  intro q
  let G : MetricConnectionFamilyOn (I := I_half n) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hlog (t : ℝ) : ContMDiff (I_half n) 𝓘(ℝ) ∞
      (fun x => Real.log (riemannianVolumeDensity q (g t) x)) := by
    intro x
    exact (Real.contDiffAt_log.mpr
      (ne_of_gt (riemannianVolumeDensity_pos q (g t) x))).contMDiffAt.comp x
      (riemannianVolumeDensity_contMDiff q (g t) x)
  let Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯ := fun t =>
    ⟨gradientFun (g t) (fun x => Real.log (riemannianVolumeDensity q (g t) x)),
      gradientFun_smooth (g t) (hlog t)⟩
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn (G := G) hG q
  have hlogJoint : ContMDiffOn (𝓘(ℝ).prod (I_half n)) 𝓘(ℝ) ∞
      (fun p : ℝ × M => Real.log (riemannianVolumeDensity q (g p.1) p.2))
      (D.regular ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact (Real.contDiffAt_log.mpr
      (ne_of_gt (riemannianVolumeDensity_pos q (g p.1) p.2))).comp_contMDiffWithinAt
      (f := fun r : ℝ × M => riemannianVolumeDensity q (g r.1) r.2) (hρ p hp)
  have hgradJoint := hG.gradient_joint_contMDiffOn hlogJoint
  have hY : ContMDiffOn (𝓘(ℝ).prod (I_half n)) ((I_half n).tangent) ∞
      (fun p : ℝ × M => (⟨p.2, Y p.1 p.2⟩ : TangentBundle (I_half n) M))
      (D.regular ×ˢ (Set.univ : Set M)) := by
    simpa only [Y, ContMDiffSection.coeFn_mk] using hgradJoint
  have hdiv : ContMDiffOn (𝓘(ℝ).prod (I_half n)) 𝓘(ℝ) ∞
      (fun p : ℝ × M => divergence (leviCivitaConnectionOfMetric q) (Y p.1) p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hYAt := hY.contMDiffAt (x := p)
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds hp)
    exact (divergence_contMDiffAt_partial (I := I_half n) (IP := 𝓘(ℝ))
      (X := fun t x => Y t x) (p := p) (m := ⊤) (n := ∞)
      (leviCivitaConnectionOfMetric q)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative q)
      hYAt (by simp)).contMDiffWithinAt
  obtain ⟨T, hT, hreg, hsol⟩ := exists_local_dirichlet_cometric_weak_solution (G := G)
    hG h0reg Y a hY.continuousOn hdiv.continuousOn ha
  refine ⟨T, hT, hreg, fun u₀ f₀ => ?_⟩
  obtain ⟨u, U₂, U₀, hcont, hinit, hfield, hpoint, heq⟩ := hsol u₀ f₀
  refine ⟨u, U₂, U₀, hcont, hinit, hfield, hpoint, ?_⟩
  filter_upwards [heq] with t ht
  intro φ
  rw [ht φ]
  congr 1
  exact integral_dirichlet_heat_adjoint q (g t) (Y t) rfl (a t) (U₀ t) φ

theorem exists_local_dirichlet_heat_variational_solution
    {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric (I_half n) M}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D g)
    (h0reg : (0 : ℝ) ∈ D.regular)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯)
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M))) :
    let q := g 0
    ∃ T : ℝ, 0 < T ∧ Icc (0 : ℝ) T ⊆ D.regular ∧
      ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞, ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
          (g t).inner x w w ≤ Cg * q.inner x w w,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
          Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q,
      ∀ (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
        (f₀ : timeL2 (H1ComplDirichlet q →L[ℝ] ℝ) T),
        ∃ (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
          (V : timeL2 (H1ComplDirichlet q) T)
          (U : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)),
          ContinuousOn U (Icc (0 : ℝ) T) ∧ U 0 = u₀ ∧
          (fun t => H1ComplDirichletToLp q (V t)) =ᵐ[timeMeasure T] U ∧
          (∀ t ∈ Icc (0 : ℝ) T, ∀ v : H1ComplDirichlet q,
            w.toFun t v = inner ℝ (U t) (H1ComplDirichletToLp q v)) ∧
          ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ v : H1ComplDirichlet q,
            w.deriv t v =
              dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
                hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (V t)
                (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) v) -
              inner ℝ (smoothMulLp q (a t) (U t)) (H1ComplDirichletToLp q v) + f₀ t v := by
  intro q
  obtain ⟨T, hT, hreg, hsol⟩ := exists_local_dirichlet_heat_weak_solution hG h0reg a ha
  obtain ⟨Cg, hCg, hequiv⟩ :=
    exists_metric_equivalence_bound_on_icc_of_metricFamilySmoothOn
      g hG (fun _ ht => D.regular_subset (hreg ht)) q
  let G : MetricConnectionFamilyOn (I := I_half n) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨Cv, hCv0, hCvtop, hvolBoth⟩ := volume_uniform_equiv
    (I := I_half n) (M := M) q g isCompact_Icc
    (fun x₀ i j => MetricFamilySmoothOn.chartGramMatrix_continuousOn (G := G) hG hreg x₀ i j)
  let hvol := fun t ht => (hvolBoth t ht).1
  refine ⟨T, hT, hreg, Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, fun u₀ f₀ => ?_⟩
  let J := (dirichletHsNegOneEquivH1Dual q).symm.toContinuousLinearMap
  let fHs := J.compLpL 2 (timeMeasure T) f₀
  obtain ⟨u, U₂, U₀, hcont, hinit, hfield, hpoint, heq⟩ :=
    hsol ((dirichletHsZeroEquivL2 q).symm u₀) fHs
  obtain ⟨w, _, hw, hwd⟩ :=
    exists_timeH1_comp_clm (dirichletHsNegOneEquivH1Dual q).toContinuousLinearMap u
  simp only [ContinuousLinearEquiv.coe_coe] at hw hwd
  let K := (dirichletHsOneEquivH1Compl q).toContinuousLinearEquiv.toContinuousLinearMap
  let V := K.compLpL 2 (timeMeasure T) U₂
  let U := fun t => dirichletHsZeroEquivL2 q (U₀ t)
  have hV : V =ᵐ[timeMeasure T] fun t => dirichletHsOneEquivH1Compl q (U₂ t) :=
    K.coeFn_compLpL U₂
  have hf : fHs =ᵐ[timeMeasure T] fun t => (dirichletHsNegOneEquivH1Dual q).symm (f₀ t) :=
    J.coeFn_compLpL f₀
  refine ⟨w, V, U, (dirichletHsZeroEquivL2 q).continuous.comp_continuousOn hcont,
    ?_, ?_, ?_, ?_⟩
  · change dirichletHsZeroEquivL2 q (U₀ 0) = u₀
    rw [hinit, LinearIsometryEquiv.apply_symm_apply]
  · filter_upwards [hV, hfield] with t hVt hfieldt
    rw [hVt, H1ComplDirichletToLp_dirichletHsOneEquivH1Compl, hfieldt]
  · intro t ht v
    rw [hw t ht, ← hpoint t ht]
    exact dirichletHsNegOneEquivH1Dual_inclusion_zero_apply q (U₀ t) v
  · filter_upwards [heq, hfield, hV, hf, hwd] with t heqt hfieldt hVt hft hwdt
    intro ht v
    have hU : H1ComplDirichletToLp q (dirichletHsOneEquivH1Compl q (U₂ t)) = U t := by
      rw [H1ComplDirichletToLp_dirichletHsOneEquivH1Compl, hfieldt]
    have h := eq_dirichletWeakFormCompl_of_heat_adjoint (g t) hCg (hequiv t ht)
      Cv hCv0 hCvtop (hvol t ht) (a t) (dirichletHsOneEquivH1Compl q (U₂ t))
      (dirichletHsNegOneEquivH1Dual q (u.deriv t))
      (dirichletHsNegOneEquivH1Dual q (fHs t))
      (by intro φ; rw [hU]; exact heqt φ) v
    rw [hU, hft, ContinuousLinearEquiv.apply_symm_apply] at h
    rw [hwdt, hVt]
    exact h

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
