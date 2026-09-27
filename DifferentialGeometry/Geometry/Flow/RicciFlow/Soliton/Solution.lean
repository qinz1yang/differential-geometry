import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Tensor.Coordinates

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private theorem canonical_time_domain_open (sigma : Real) :
    IsOpen (canonicalTimeDomain sigma) :=
  isOpen_lt continuous_const
    (continuous_const.sub (continuous_const.mul continuous_id))

omit [FiniteDimensional Real E] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem spatial_lift_contMDiffOn
    (Y : (x : M) → TangentSpace I x) {u : Set M} (K : Set Real)
    (hY : ContMDiffOn I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) u) :
    ContMDiffOn (𝓘(Real, Real).prod I)
      ((𝓘(Real, Real).prod I).prod 𝓘(Real, Real × E)) ∞
      (fun q : Real × M =>
        (⟨q, ((0 : Real), Y q.2)⟩ : TangentBundle (𝓘(Real, Real).prod I) (Real × M)))
      (K ×ˢ u) := by
  have hzero : ContMDiffOn (𝓘(Real, Real).prod I)
      (𝓘(Real, Real).prod 𝓘(Real, Real)) ∞
      (fun q : Real × M => (⟨q.1, (0 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
      (K ×ˢ u) :=
    ((contMDiff_zeroSection Real
      (TangentSpace 𝓘(Real, Real) : Real → Type _)).comp contMDiff_fst).contMDiffOn
  have hv := hY.comp
    (contMDiffOn_snd (I := 𝓘(Real, Real)) (s := K ×ˢ u))
    (fun q hq => hq.2)
  exact (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(Real, Real)) (I' := I) (M := Real) (M' := M)
    (n := (∞ : WithTop ℕ∞))).comp_contMDiffOn (hzero.prodMk hv)

omit [FiniteDimensional Real E] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem spatial_pushforward_contMDiffOn
    (Phi : Real × M → M) (U : Set Real) (hU : IsOpen U)
    (hPhi : ContMDiffOn (𝓘(Real, Real).prod I) I ∞ Phi (U ×ˢ Set.univ))
    (Y : (x : M) → TangentSpace I x) {u : Set M}
    (hY : ContMDiffOn I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) u) :
    ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E)) ∞
      (fun q : Real × M => TotalSpace.mk' E (Phi q)
        (mfderiv I I (fun x => Phi (q.1, x)) q.2 (Y q.2))) (U ×ˢ u) := by
  have hOpen := hU.prod (isOpen_univ : IsOpen (Set.univ : Set M))
  have htan := hPhi.contMDiffOn_tangentMapWithin (m := (∞ : WithTop ℕ∞))
    (by simp) hOpen.uniqueMDiffOn
  have hinput := spatial_lift_contMDiffOn (I := I) Y U hY
  have hcomp := htan.comp hinput (fun q hq => ⟨hq.1, mem_univ q.2⟩)
  refine hcomp.congr ?_
  intro q hq
  have hPhiAt : MDifferentiableAt (𝓘(Real, Real).prod I) I Phi q :=
    ((hPhi q ⟨hq.1, mem_univ q.2⟩).contMDiffAt
      (hOpen.mem_nhds ⟨hq.1, mem_univ q.2⟩)).mdifferentiableAt (by simp)
  change TotalSpace.mk' E (Phi q)
      (mfderiv I I (fun x => Phi (q.1, x)) q.2 (Y q.2)) =
    tangentMapWithin (𝓘(Real, Real).prod I) I Phi (U ×ˢ Set.univ)
      (⟨q, (0, Y q.2)⟩ : TangentBundle (𝓘(Real, Real).prod I) (Real × M))
  have hwithin := tangentMapWithin_eq_tangentMap
    (I := 𝓘(Real, Real).prod I) (I' := I) (f := Phi)
    (p := (⟨q, (0, Y q.2)⟩ : TangentBundle (𝓘(Real, Real).prod I) (Real × M)))
    (hOpen.uniqueMDiffOn q ⟨hq.1, mem_univ q.2⟩) hPhiAt
  have heq : mfderiv (𝓘(Real, Real).prod I) I Phi q (0, Y q.2) =
      mfderiv I I (fun x => Phi (q.1, x)) q.2 (Y q.2) := by
    have hsplit := mfderiv_prod_eq_add_apply
      (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
      (f := Phi) (p := q) (v := (0, Y q.2)) hPhiAt
    have hz := (mfderiv 𝓘(Real, Real) I (fun z => Phi (z, q.2)) q.1).map_zero
    exact hsplit.trans ((congrArg
      (fun a : TangentSpace I (Phi q) =>
        a + mfderiv I I (fun x => Phi (q.1, x)) q.2 (Y q.2)) hz).trans (zero_add _))
  exact (congrArg (TotalSpace.mk' E (Phi q)) heq.symm).trans hwithin.symm

private theorem canonical_pushforward_contMDiffOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (Y : (x : M) → TangentSpace I x) {u : Set M}
    (hY : ContMDiffOn I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) u) :
    ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E)) ∞
      (fun q : Real × M => TotalSpace.mk' E
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma q.1) q.2)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma q.1) : M → M) q.2 (Y q.2)))
      (canonicalTimeDomain sigma ×ˢ u) := by
  apply spatial_pushforward_contMDiffOn
    (I := I) _ _ (canonical_time_domain_open sigma) _ Y hY
  intro q hq
  have h := canonicalFlowMap_contMDiffAt (I := I) g f sigma hcomplete hsol hq.1 q.2
  simpa only [canonicalFlowDiffeomorph_apply] using
    h.contMDiffWithinAt (s := canonicalTimeDomain sigma ×ˢ Set.univ)

private theorem canonical_metric_frame_contMDiffOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (Y Z : (x : M) → TangentSpace I x) {u : Set M}
    (hY : ContMDiffOn I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) u)
    (hZ : ContMDiffOn I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Z x)) u) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M =>
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol q.1).inner
          q.2 (Y q.2) (Z q.2))
      (canonicalTimeDomain sigma ×ˢ u) := by
  let Phi : Real × M → M := fun q =>
    canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma q.1) q.2
  have hPhi : ContMDiffOn (𝓘(Real, Real).prod I) I ∞ Phi
      (canonicalTimeDomain sigma ×ˢ u) := by
    intro q hq
    have h := canonicalFlowMap_contMDiffAt
      (I := I) g f sigma hcomplete hsol hq.1 q.2
    simpa only [Phi, canonicalFlowDiffeomorph_apply] using
      h.contMDiffWithinAt (s := canonicalTimeDomain sigma ×ˢ u)
  have hg := g.contMDiff.comp_contMDiffOn hPhi
  have hpushY := canonical_pushforward_contMDiffOn
    (I := I) g f sigma hcomplete hsol Y hY
  have hpushZ := canonical_pushforward_contMDiffOn
    (I := I) g f sigma hcomplete hsol Z hZ
  have happ := ContMDiffOn.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := Real)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M Real)
    (b := Phi) hg hpushY hpushZ
  have hscalar : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => g.inner (Phi q)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma q.1) : M → M) q.2 (Y q.2))
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma q.1) : M → M) q.2 (Z q.2)))
      (canonicalTimeDomain sigma ×ˢ u) := by
    intro q hq
    have h := happ q hq
    rw [contMDiffWithinAt_totalSpace] at h
    exact h.2
  have hscale : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => 1 - sigma * q.1)
      (canonicalTimeDomain sigma ×ˢ u) :=
    contMDiffOn_const.sub (contMDiffOn_const.mul contMDiffOn_fst)
  refine (hscale.mul hscalar).congr ?_
  intro q hq
  rw [canonicalMetricFamily_eq (I := I) g f sigma hcomplete hsol hq.1,
    canonicalMetric, Diffeomorph.pullbackMetric_inner, scaleMetric_inner]
  rfl

private theorem canonical_metric_chartGram_contMDiffOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (x : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => chartGramMatrix (I := I)
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol q.1) x q.2 i j)
      (canonicalTimeDomain sigma ×ˢ (trivializationAt E (TangentSpace I) x).baseSet) := by
  exact canonical_metric_frame_contMDiffOn (I := I) g f sigma hcomplete hsol
    (chartBasisVecFiber (I := I) x i) (chartBasisVecFiber (I := I) x j)
    (chartBasisVec_contMDiffOn (I := I) x i)
    (chartBasisVec_contMDiffOn (I := I) x j)

private theorem canonical_metric_coeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (x : M) (v w : TangentSpace I x) :
    ContDiffOn Real ∞
      (fun t : Real =>
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol t).inner x v w)
      (canonicalTimeDomain sigma) := by
  have hframe := canonical_metric_frame_contMDiffOn
    (I := I) (u := Set.univ) g f sigma hcomplete hsol
    (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w)
    (smoothExtensionTangent_contMDiff (I := I) x v).contMDiffOn
    (smoothExtensionTangent_contMDiff (I := I) x w).contMDiffOn
  have hcurve : ContMDiffOn 𝓘(Real, Real) (𝓘(Real, Real).prod I) ∞
      (fun t : Real => (t, x)) (canonicalTimeDomain sigma) :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have h := hframe.comp hcurve (fun t ht => ⟨ht, mem_univ x⟩)
  simpa only [Function.comp_def, smoothExtensionTangent_eq] using h.contDiffOn

private theorem canonical_metricFamilySmoothOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) (hD : D.carrier ⊆ canonicalTimeDomain sigma) :
    MetricFamilySmoothOn (I := I) D
      (canonicalMetricFamily (I := I) g f sigma hcomplete hsol) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x v w
    exact (canonical_metric_coeff_contDiffOn (I := I) g f sigma hcomplete hsol x v w).mono
      (D.regular_subset.trans hD)
  · intro x v w
    have h := canonical_metric_coeff_contDiffOn (I := I) g f sigma hcomplete hsol x v w
    exact h.continuousOn.mono hD
  · apply metricTensorCont_of_chartGram
    intro x i j
    have h := (canonical_metric_chartGram_contMDiffOn
      (I := I) g f sigma hcomplete hsol x i j).continuousOn
    have hincl : ContinuousOn
        (fun q : {t : Real // t ∈ D.carrier} × M => ((q.1 : Real), q.2))
        {q : {t : Real // t ∈ D.carrier} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x).baseSet} :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    have hc := h.comp hincl (fun q hq => ⟨hD q.1.2, hq⟩)
    simpa only [Function.comp_def] using hc
  · intro Idx _ frame u hframe i j
    exact (canonical_metric_frame_contMDiffOn (I := I) g f sigma hcomplete hsol
      (frame i) (frame j) (hframe.contMDiffOn i) (hframe.contMDiffOn j)).mono
      (prod_mono_left (D.regular_subset.trans hD))

def canonicalSolutionOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) : SolutionOn (I := I) (M := M) D where
  base := { metric := canonicalMetricFamily (I := I) g f sigma hcomplete hsol }

@[simp] theorem canonicalSolutionOn_metric
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) (t : Real) :
    (canonicalSolutionOn (I := I) g f sigma hcomplete hsol D).base.metric t =
      canonicalMetricFamily (I := I) g f sigma hcomplete hsol t := rfl

theorem canonicalSolutionOn_metric_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) :
    (canonicalSolutionOn (I := I) g f sigma hcomplete hsol D).base.metric 0 = g :=
  canonicalMetricFamily_zero (I := I) g f sigma hcomplete hsol

theorem canonicalSolutionOn_complete
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) (hD : D.carrier ⊆ canonicalTimeDomain sigma)
    {t : Real} (ht : t ∈ D.carrier) :
    RiemannianMetricComplete (I := I)
      ((canonicalSolutionOn (I := I) g f sigma hcomplete hsol D).base.metric t) :=
  canonicalMetricFamily_complete (I := I) g f sigma hcomplete hsol (hD ht)

theorem canonicalSolutionOn_isSolutionOn
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) (hD : D.carrier ⊆ canonicalTimeDomain sigma) :
    IsSolutionOn (I := I)
      (canonicalSolutionOn (I := I) g f sigma hcomplete hsol D) := by
  let G := canonicalMetricFamily (I := I) g f sigma hcomplete hsol
  have hU : UniqueDiffOn Real (canonicalTimeDomain sigma) :=
    (canonical_time_domain_open sigma).uniqueDiffOn
  have hgram := canonical_metric_chartGram_contMDiffOn
    (I := I) g f sigma hcomplete hsol
  apply isSolutionOn_of_reg (I := I) G
  · exact canonical_metricFamilySmoothOn (I := I) g f sigma hcomplete hsol D hD
  · intro t ht x v w
    exact canonicalMetricFamily_ricciFlow (I := I) g f sigma hcomplete hsol
      (hD (D.regular_subset ht)) x v w
  · exact (scalarCont_of_joint (I := I) G (canonicalTimeDomain sigma) hU hgram).mono
      (prod_mono_left hD)
  · intro t ht x
    exact (scalarTime_of_joint (I := I) G (canonicalTimeDomain sigma) hU hgram
      t (hD ht) x).mono hD
  · exact (ricciCont_of_joint (I := I) G (canonicalTimeDomain sigma) hU hgram).mono hD
  · exact (rm04Cont_of_joint (I := I) G (canonicalTimeDomain sigma) hU hgram).mono hD

end DifferentialGeometry.PDE.RicciFlow.Soliton
