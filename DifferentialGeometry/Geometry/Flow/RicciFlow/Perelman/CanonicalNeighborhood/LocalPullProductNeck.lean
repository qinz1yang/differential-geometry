import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProductChart
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation

set_option autoImplicit false
noncomputable section
open Set Manifold Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open TopologicalSpace (Opens)

universe u

variable {M Y : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M] [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
  [IsManifold I3 ∞ Y] [T2Space Y]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [ConnectedSpace N] [SigmaCompactSpace N]

omit [IsManifold I3 ∞ Y] [T2Space Y] in
private def diffeomorphOfOpensEq {U₁ U₂ : Opens Y} (h : U₁ = U₂) : U₁ ≃ₘ⟮I3, I3⟯ U₂ :=
  h ▸ Diffeomorph.refl I3 U₁ ∞

omit [IsManifold I3 ∞ Y] [T2Space Y] in
private theorem diffeomorphOfOpensEq_val {U₁ U₂ : Opens Y} (h : U₁ = U₂) (x : U₁) :
    ((diffeomorphOfOpensEq h x : U₂) : Y) = x := by
  subst h
  rfl

omit [IsManifold I3 ∞ Y] [T2Space Y] in
private theorem mfderiv_diffeomorphOfOpensEq {U₁ U₂ : Opens Y} (h : U₁ = U₂) (x : U₁)
    (v : TangentSpace I3 x) : mfderiv I3 I3 (diffeomorphOfOpensEq h) x v = v := by
  subst h
  change mfderiv I3 I3 (Diffeomorph.refl I3 U₁ ∞) x v = v
  rw [Diffeomorph.coe_refl, mfderiv_id]
  rfl

theorem SpatialCanonicalWitness.exists_localNeck_of_localPull_product_close
    (g : SmoothRiemannianMetric I3 M) (gY : SmoothRiemannianMetric I3 Y)
    {V : Opens Y} {Fm : V → M} (hFm : IsLocalDiffeomorph I3 I3 ∞ Fm) (hinj : Injective Fm)
    (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (e : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ Y)
    (hemetric : Diffeomorph.pullbackMetricCross gY e = h.prod (euclideanMetric (E := ℝ)))
    (z : V) {r η : ℝ} (hr : 0 < r) (hη : η ≤ 1 / 8)
    (hcpt : IsCompact (riemannianClosedBallOf gY z.val r))
    (hsub : riemannianClosedBallOf gY z.val r ⊆ V)
    (hclose : ∀ w : V, w.val ∈ riemannianClosedBallOf gY z.val r → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (localPullMetric g Fm hFm) (gY.restrictOpen V) (gY.restrictOpen V) w ≤ η)
    {epsc eps C1 C2 : ℝ} (W : SpatialCanonicalWitness g epsc C1 C2 (Fm z))
    (hW : W.capTubeHasNeckChart eps) (heps : eps ≤ 1 / 1000)
    (hsmall : 720 * η < C2⁻¹ * metricScalarAt g (Fm z) / 16)
    (hrad : 2 * Real.sqrt 2 * (C1 / Real.sqrt (metricScalarAt g (Fm z))) < r) :
    ∃ neck : SpatialLocalNeck g epsc (Fm z) W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hlower : ∀ w : V, w.val ∈ riemannianClosedBallOf gY z.val r → ∀ u : TangentSpace I3 w,
      gY.inner w.val u u ≤ Real.sqrt 2 ^ 2 *
        g.inner (Fm w) (mfderiv I3 I3 Fm w u) (mfderiv I3 I3 Fm w u) := by
    intro w hw u
    have hb := Geometry.Metric.inner_bounds_of_metricDerivNorm_le (gY.restrictOpen V)
      (localPullMetric g Fm hFm) w (hclose w hw 0 (Nat.zero_le _)) u
    rw [SmoothRiemannianMetric.restrictOpen_inner, localPullMetric_inner] at hb
    have hnn : 0 ≤ gY.inner w.val u u := metric_inner_self_nonneg gY w.val u
    have hnn' : 0 ≤ g.inner (Fm w) (mfderiv I3 I3 Fm w u) (mfderiv I3 I3 Fm w u) :=
      metric_inner_self_nonneg g _ _
    rw [Real.sq_sqrt (by norm_num)]
    nlinarith [hb.1]
  have himg := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens g gY V Fm hFm hinj z
    hr hsq2 hcpt hsub hlower
  have hQ := W.Q_pos
  have hdom : W.domain.carrier ⊆ riemannianBallOf g (Fm z) (r / Real.sqrt 2) := by
    intro w hw
    refine (W.inside_ball hw).trans_le (ENNReal.ofReal_le_ofReal ?_)
    have h2 : 2 * W.radius ≤ 2 * (C1 / Real.sqrt (metricScalarAt g (Fm z))) := by
      linarith [W.radius_upper]
    have h3 : 2 * (C1 / Real.sqrt (metricScalarAt g (Fm z))) ≤ r / Real.sqrt 2 := by
      rw [le_div_iff₀ hsq2]
      nlinarith [hrad, Real.sqrt_nonneg 2]
    linarith
  let O : Opens (N × ℝ) := ⟨e ⁻¹' (V : Set Y), V.isOpen.preimage e.continuous⟩
  have hOsrc : (O : Set (N × ℝ)) ⊆ e.toPartialDiffeomorph.source := Set.subset_univ _
  let d₁ := PartialDiffeomorph.toOpensDiffeo e.toPartialDiffeomorph hOsrc
  have himgO : (⟨(e.toPartialDiffeomorph : N × ℝ → Y) '' (O : Set (N × ℝ)),
      image_opens_isOpen e.toPartialDiffeomorph hOsrc⟩ : Opens Y) = V := by
    apply Opens.ext
    change (e : N × ℝ → Y) '' (e ⁻¹' (V : Set Y)) = V
    exact Set.image_preimage_eq _ e.surjective
  let ι : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V := d₁.trans (diffeomorphOfOpensEq himgO)
  have hιval : ∀ o : O, ((ι o : V) : Y) = e o.val := by
    intro o
    change ((diffeomorphOfOpensEq himgO (d₁ o) : V) : Y) = e o.val
    rw [diffeomorphOfOpensEq_val]
    rfl
  have hιmfd : ∀ (o : O) (v : TangentSpace (J.prod 𝓘(ℝ)) o),
      mfderiv (J.prod 𝓘(ℝ)) I3 ι o v = mfderiv (J.prod 𝓘(ℝ)) I3 e o.val v := by
    intro o v
    have hcomp : mfderiv (J.prod 𝓘(ℝ)) I3 ι o v =
        mfderiv I3 I3 (diffeomorphOfOpensEq himgO) (d₁ o) (mfderiv (J.prod 𝓘(ℝ)) I3 d₁ o v) := by
      have h1 := mfderiv_comp o ((diffeomorphOfOpensEq himgO).mdifferentiable (by decide) (d₁ o))
        (d₁.mdifferentiable (by decide) o)
      rw [show ((diffeomorphOfOpensEq himgO) ∘ d₁ : O → V) = ι from
        (Diffeomorph.coe_trans d₁ (diffeomorphOfOpensEq himgO)).symm] at h1
      exact DFunLike.congr_fun h1 v
    rw [hcomp, mfderiv_diffeomorphOfOpensEq, PartialDiffeomorph.mfderiv_toOpensDiffeo]
    rfl
  let q : O → M := fun o => Fm (ι o)
  have hq : IsLocalDiffeomorph (J.prod 𝓘(ℝ)) I3 ∞ q :=
    isLocalDiffeomorph_comp hFm ι.isLocalDiffeomorph
  have hqinj : Injective q := hinj.comp ι.injective
  have hfdim : Module.finrank ℝ (F × ℝ) = Module.finrank ℝ ThreeSpace := by
    simp only [Module.finrank_prod, hdim, Module.finrank_self]
    simp [ThreeSpace]
  have hqemb := KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hq hqinj
  obtain ⟨V', Φ, hV', hΦ, hΦsymm, hmetric⟩ :=
    Geometry.Metric.exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric g
      hqemb.isImmersion hqinj
      hfdim
  have hpre : ∀ w ∈ W.domain.carrier, ∃ x : V, x.val ∈ riemannianClosedBallOf gY z.val r ∧
      Fm x = w := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := himg (hdom hw)
    exact ⟨x, hx, hxw⟩
  have hcapV : W.domain.carrier ⊆ V' := by
    intro w hw
    rw [hV']
    obtain ⟨x, -, hxw⟩ := hpre w hw
    exact ⟨ι.symm x, by change Fm (ι (ι.symm x)) = w; rw [ι.apply_symm_apply]; exact hxw⟩
  have hpull : Diffeomorph.pullbackMetricCross (g.restrictOpen V') Φ =
      Diffeomorph.pullbackMetricCross (localPullMetric g Fm hFm) ι := by
    rw [hmetric]
    apply SmoothRiemannianMetric.ext_inner
    intro o v w
    rw [Diffeomorph.pullbackMetricCross_inner, localPullMetric_inner]
    change g.inner (q o) (mfderiv (J.prod 𝓘(ℝ)) I3 q o v) (mfderiv (J.prod 𝓘(ℝ)) I3 q o w) = _
    have hd : ∀ u : TangentSpace (J.prod 𝓘(ℝ)) o, mfderiv (J.prod 𝓘(ℝ)) I3 q o u =
        mfderiv I3 I3 Fm (ι o) (mfderiv (J.prod 𝓘(ℝ)) I3 ι o u) := by
      intro u
      have h1 := mfderiv_comp o (hFm.contMDiff.mdifferentiableAt (by decide) (x := ι o))
        (ι.mdifferentiable (by decide) o)
      exact DFunLike.congr_fun h1 u
    rw [hd v, hd w]
  have hprodO : (h.prod (euclideanMetric (E := ℝ))).restrictOpen O =
      Diffeomorph.pullbackMetricCross (gY.restrictOpen V) ι := by
    apply SmoothRiemannianMetric.ext_inner
    intro o v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, ← hemetric,
      Diffeomorph.pullbackMetricCross_inner (gY.restrictOpen V) ι,
      SmoothRiemannianMetric.restrictOpen_inner, hιmfd, hιmfd]
    refine (Diffeomorph.pullbackMetricCross_inner gY e o.val v w).trans ?_
    exact congrArg (fun p => gY.inner p (mfderiv (J.prod 𝓘(ℝ)) I3 e o.val v)
      (mfderiv (J.prod 𝓘(ℝ)) I3 e o.val w)) (hιval o).symm
  let _ : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (J.prod 𝓘(ℝ)) O.isOpen)
  let _ : IsManifold (J.prod 𝓘(ℝ)) 1 O := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold (J.prod 𝓘(ℝ)) 2 O := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold (J.prod 𝓘(ℝ)) ((∞ : WithTop ℕ∞) + 1) O := by
    simpa using (inferInstance : IsManifold (J.prod 𝓘(ℝ)) ∞ O)
  let _ : IsManifold I3 1 V := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I3 2 V := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I3 ((∞ : WithTop ℕ∞) + 1) V := by
    simpa using (inferInstance : IsManifold I3 ∞ V)
  refine W.exists_localNeck_of_product_chart hW heps h hdim O V' Φ hcapV (by linarith) hsmall ?_
  intro w hw m hm
  rw [hpull, hprodO, metricDerivNorm_pullbackCross]
  obtain ⟨x, hx, hxw⟩ := hpre w.val hw
  have hxι : ι (Φ.symm w) = x := by
    apply hinj
    change q (Φ.symm w) = Fm x
    rw [hΦsymm w, hxw]
  rw [hxι]
  exact hclose x hx m hm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
