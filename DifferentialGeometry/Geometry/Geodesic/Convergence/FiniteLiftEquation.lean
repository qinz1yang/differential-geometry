import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.PullbackGeodesics
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartPullback
import DifferentialGeometry.Geometry.Metric.Pullback.CoefficientConvergence
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Analysis.FiniteDimensional.BilinearPositivity
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing

/-!
# LC50′, lift step: the chart equation of an inverse-lifted geodesic

Finite-order twin of X84's `intrinsicGeodesic_inverse_isGeodesicAt` (BufferedGeodesicEquation),
in chart form. Let `g` be a smooth metric on `M`, `j : N → M` a partial diffeomorphism of finite
order `K ≥ 2`, and `V = g.geodesicFlow p` CM-P's geodesic flow of `g`. While `V` stays over
`j.target`, the inverse lift
`Γ s = ⟨j⁻¹ (V s).proj, d(j⁻¹) (V s).snd⟩ ∈ TN`
solves, in every tangent chart of `N` at `q`, the metric-spray equation of the ACTUAL pulled-back
coefficients `pullbackMetricCoefficients g (j ∘ (extChartAt I q.proj)⁻¹)`. No metric on `N` and no
flow on `N` is used.

Route: the `M`-chart equation of `V` (CM-P `hasDerivAt_geodesicFlow_chart`, `g` smooth, `r := ⊤`);
the coordinate change `τ = φ_N ∘ j⁻¹ ∘ ψ_M⁻¹`, a partial diffeomorphism `E → E` of order `K`
(Mathlib `PartialDiffeomorph.trans`); the chain rule `c = τ^* b` for the coefficients
(`pullbackMetricCoefficients_comp_eq_pullbackForm`); CM-L's chart naturality
`hasDerivWithinAt_pushforward_geodesic`; and the identification of the tangent-chart reading of
`Γ` with `(τ ∘ X, Dτ X')`.

* `hasDerivAt_chart_inverseLift`: the chart equation at every time of the flow domain over
  `j.target`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.MetricKoszul
open DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

private local instance liftEquationDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Reading of a tangent-bundle chart (the tree's `extChartAt_tangent_apply_eq`, here without a
metric on the manifold). -/
theorem extChartAt_tangent_apply_eq_mfderiv (a p : TangentBundle I N)
    (hp : p.proj ∈ (chartAt H a.proj).source) :
    extChartAt I.tangent a p =
      (extChartAt I a.proj p.proj, mfderiv I 𝓘(ℝ, E) (extChartAt I a.proj) p.proj p.snd) := by
  apply Prod.ext
  · exact TangentBundle.extChartAt_tangent_apply_fst a
  · rw [TangentBundle.extChartAt_tangent_apply_snd a hp,
      TangentBundle.continuousLinearMapAt_trivializationAt hp]
    rfl

/-- **Chart equation of the inverse lift.** For a smooth metric `g` on `M`, a partial
diffeomorphism `j : N → M` of order `K ≥ 2`, and a time `t` of the flow domain of `p` with
`(g.geodesicFlow p t).proj ∈ j.target`, the curve
`s ↦ ⟨j⁻¹ (V s).proj, d(j⁻¹) (V s).snd⟩` read in the tangent chart of `N` at `q` (whose base chart
contains the lifted point) has derivative at `t` the metric spray of the pulled-back coefficients
`pullbackMetricCoefficients g (j ∘ (extChartAt I q.proj).symm)`. -/
theorem hasDerivAt_chart_inverseLift (g : SmoothRiemannianMetric I M) {K : ℕ} (hK : 2 ≤ K)
    (j : PartialDiffeomorph I I N M K) {p : TangentBundle I M} {t : ℝ}
    (ht : (p, t) ∈ g.geodesicFlowDomain) (htarget : (g.geodesicFlow p t).proj ∈ j.target)
    (q : TangentBundle I N)
    (hq : j.symm (g.geodesicFlow p t).proj ∈ (chartAt H q.proj).source) :
    HasDerivAt (fun s => extChartAt I.tangent q
        (⟨j.symm (g.geodesicFlow p s).proj, mfderiv I I (j.symm : M → N)
          (g.geodesicFlow p s).proj (g.geodesicFlow p s).snd⟩ : TangentBundle I N))
      (metricSpray (pullbackMetricCoefficients g ((j : N → M) ∘ (extChartAt I q.proj).symm))
        (extChartAt I.tangent q (⟨j.symm (g.geodesicFlow p t).proj, mfderiv I I (j.symm : M → N)
          (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd⟩ : TangentBundle I N))) t := by
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hK2 : (2 : ℕ∞ω) ≤ ((K : ℕ) : ℕ∞ω) := by exact_mod_cast hK
  have : IsManifold I (K : ℕ∞ω) M := IsManifold.of_le hKle
  have : IsManifold I (K : ℕ∞ω) N := IsManifold.of_le hKle
  set V := g.geodesicFlow p with hVdef
  set a : M := (V t).proj with ha
  set x₀ : N := q.proj with hx₀
  set ψ := extChartAt I a with hψ
  set φ := extChartAt I x₀ with hφ
  -- the coordinate change and the pulled-back parametrization, as partial diffeomorphisms
  let Pψ := DifferentialGeometry.PartialDiffeomorph.extChartAt I (K : ℕ∞ω) a
  let Pφ := DifferentialGeometry.PartialDiffeomorph.extChartAt I (K : ℕ∞ω) x₀
  let T : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E K := Pψ.symm.trans (j.symm.trans Pφ)
  let F : PartialDiffeomorph 𝓘(ℝ, E) I E M K := Pφ.symm.trans j
  have hTapp (x : E) : T x = φ (j.symm (ψ.symm x)) := rfl
  have hFapp (x : E) : F x = j (φ.symm x) := rfl
  have hTsource (x : E) :
      x ∈ T.source ↔ x ∈ ψ.target ∧ ψ.symm x ∈ j.target ∧ j.symm (ψ.symm x) ∈ φ.source := by
    change x ∈ ψ.target ∩ ψ.symm ⁻¹' (j.target ∩ j.symm ⁻¹' φ.source) ↔ _
    rfl
  have hFsource (x : E) : x ∈ F.source ↔ x ∈ φ.target ∧ φ.symm x ∈ j.source := by
    change x ∈ φ.target ∩ φ.symm ⁻¹' j.source ↔ _
    rfl
  let b : E → E →L[ℝ] E →L[ℝ] ℝ := pullbackMetricCoefficients g (F : E → M)
  have hbdef : b = pullbackMetricCoefficients g ((j : N → M) ∘ (extChartAt I q.proj).symm) := rfl
  -- the open time interval where everything is in the charts
  have hVcont : ContinuousAt V t :=
    ((g.isMIntegralCurveOn_geodesicFlow (r := ⊤) le_top p t ht).hasMFDerivAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds ht)).continuousAt
  have hprojcont : ContinuousAt (fun s => (V s).proj) t :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hVcont
  have hdomOpen : IsOpen {s : ℝ | (p, s) ∈ g.geodesicFlowDomain} :=
    (g.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage (Continuous.prodMk_right p)
  have hjsymm : ContinuousAt (j.symm : M → N) a :=
    j.symm.contMDiffOn.continuousOn.continuousAt (j.open_target.mem_nhds htarget)
  have hev : ∀ᶠ s in 𝓝 t, (p, s) ∈ g.geodesicFlowDomain ∧ (V s).proj ∈ ψ.source ∧
      (V s).proj ∈ j.target ∧ j.symm (V s).proj ∈ φ.source := by
    refine (show ∀ᶠ s in 𝓝 t, (p, s) ∈ g.geodesicFlowDomain from hdomOpen.mem_nhds ht).and ?_
    refine (hprojcont.eventually ((isOpen_extChartAt_source a).mem_nhds
      (mem_extChartAt_source a))).and ?_
    refine (hprojcont.eventually (j.open_target.mem_nhds htarget)).and ?_
    exact hprojcont.eventually (hjsymm.preimage_mem_nhds
      ((isOpen_extChartAt_source x₀).mem_nhds (by rw [extChartAt_source]; exact hq)))
  obtain ⟨O, hOP, hOo, htO⟩ := eventually_nhds_iff.1 hev
  -- the `M`-chart equation of the flow
  let X : ℝ → E := fun s => ψ (V s).proj
  let X' : ℝ → E := fun s => mfderiv I 𝓘(ℝ, E) ψ (V s).proj (V s).snd
  let c : E → E →L[ℝ] E →L[ℝ] ℝ := chartCoeff g a
  have hread (s : ℝ) (hs : s ∈ O) : extChartAt I.tangent (V t) (V s) = (X s, X' s) := by
    have hmem : (V s).proj ∈ (chartAt H (V t).proj).source := by
      rw [← extChartAt_source (I := I)]; exact (hOP s hs).2.1
    exact extChartAt_tangent_apply_eq_mfderiv (V t) (V s) hmem
  have hpair (s : ℝ) (hs : s ∈ O) :
      HasDerivAt (fun u => (X u, X' u)) (metricSpray c (X s, X' s)) s := by
    have hmem : (V s).proj ∈ (chartAt H (V t).proj).source := by
      rw [← extChartAt_source (I := I)]; exact (hOP s hs).2.1
    have h : HasDerivAt (fun u => extChartAt I.tangent (V t) (V u))
        (metricSpray c (extChartAt I.tangent (V t) (V s))) s :=
      Bundle.ContMDiffRiemannianMetric.hasDerivAt_geodesicFlow_chart (r := ⊤) g le_top
        (hOP s hs).1 (V t) hmem
    rw [hread s hs] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hOo.mem_nhds hs] with u hu
    exact (hread u hu).symm
  have hx : ∀ s ∈ O, HasDerivWithinAt X (X' s) O s := by
    intro s hs
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := (X s, X' s))).comp_hasDerivAt s
      (hpair s hs)
    exact h.hasDerivWithinAt
  have hx' := fun s (hs : s ∈ O) =>
    ((hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := (X s, X' s))).comp_hasDerivAt s
      (hpair s hs)).hasDerivWithinAt (s := O)
  -- the coordinate change `T`
  have hXT : ∀ s ∈ O, X s ∈ T.source := by
    intro s hs
    obtain ⟨-, hsψ, hsj, hsφ⟩ := hOP s hs
    refine (hTsource _).2 ⟨ψ.map_source hsψ, ?_, ?_⟩
    · change ψ.symm (ψ (V s).proj) ∈ j.target
      rw [ψ.left_inv hsψ]; exact hsj
    · change j.symm (ψ.symm (ψ (V s).proj)) ∈ φ.source
      rw [ψ.left_inv hsψ]; exact hsφ
  have hTmaps : MapsTo T T.source F.source := by
    intro x hx
    obtain ⟨-, hxj, hxφ⟩ := (hTsource x).1 hx
    refine (hFsource _).2 ⟨φ.map_source hxφ, ?_⟩
    change φ.symm (φ (j.symm (ψ.symm x))) ∈ j.source
    rw [φ.left_inv hxφ]
    exact j.map_target hxj
  have hTsmooth : ContDiffOn ℝ 2 T T.source :=
    (contMDiffOn_iff_contDiffOn.mp T.contMDiffOn).of_le hK2
  have hTinv : ∀ x ∈ T.source, (fderiv ℝ T x).IsInvertible := by
    intro x hx
    have h := (T.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (K : ℕ∞ω) hx).isInvertible_mfderiv hK0
    rwa [mfderiv_eq_fderiv] at h
  have hFT : ∀ x ∈ T.source, (F : E → M) ∘ (T : E → E) =ᶠ[𝓝 x] (ψ.symm : E → M) := by
    intro x hx
    filter_upwards [T.open_source.mem_nhds hx] with y hy
    obtain ⟨-, hyj, hyφ⟩ := (hTsource y).1 hy
    change j (φ.symm (φ (j.symm (ψ.symm y)))) = ψ.symm y
    rw [φ.left_inv hyφ]
    exact j.toPartialEquiv.right_inv hyj
  -- the coefficient fields
  have hb : ContDiffOn ℝ 1 b F.source :=
    Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner g (r := 1) (s := (K : ℕ∞ω))
      (by exact_mod_cast le_top) (by exact_mod_cast hK) F.open_source F.contMDiffOn
  have hbsymm : ∀ y ∈ F.source, ∀ u v : E, b y u v = b y v u := fun y _ u v => by
    simp only [b, pullbackMetricCoefficients_apply]
    exact g.symm _ _ _
  have hbco : ∀ y ∈ F.source, IsCoercive (b y) := by
    intro y hy
    obtain ⟨e, he⟩ := (F.isLocalDiffeomorphAt 𝓘(ℝ, E) I (K : ℕ∞ω) hy).isInvertible_mfderiv hK0
    refine DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal _ fun v hv => ?_
    have hne : mfderiv 𝓘(ℝ, E) I (F : E → M) y v ≠ 0 := by
      rw [← he]
      exact e.map_ne_zero_iff.mpr hv
    simp only [b, pullbackMetricCoefficients_apply]
    exact g.pos _ _ hne
  have hpull : ∀ x ∈ T.source, ∀ u v : E,
      c x u v = b (T x) (fderiv ℝ T x u) (fderiv ℝ T x v) := by
    intro x hx u v
    have hFx : MDifferentiableAt 𝓘(ℝ, E) I (F : E → M) (T x) :=
      F.mdifferentiableAt hK0 (hTmaps hx)
    have hTx : DifferentiableAt ℝ T x :=
      mdifferentiableAt_iff_differentiableAt.mp (T.mdifferentiableAt hK0 hx)
    have hcomp := pullbackMetricCoefficients_comp_eq_pullbackForm g hFx hTx
    rw [pullbackMetricCoefficients_eq_of_eventuallyEq g (hFT x hx)] at hcomp
    have h := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B u v) hcomp
    simp only [pullbackForm_apply] at h
    exact h
  -- CM-L's chart naturality along the coordinate change
  have hpush := DifferentialGeometry.Analysis.ODE.GeodesicLimits.hasDerivWithinAt_pushforward_geodesic
    F.open_source T.open_source hb hbsymm hbco hTsmooth hTmaps hTinv hpull hXT hx hx' t htO
  have hd1 : HasDerivAt (fun s => T (X s)) (fderiv ℝ T (X t) (X' t)) t :=
    hpush.1.hasDerivAt (hOo.mem_nhds htO)
  have hd2 := hpush.2.hasDerivAt (hOo.mem_nhds htO)
  -- the tangent-chart reading of the lift
  have hident : ∀ s ∈ O, extChartAt I.tangent q
      (⟨j.symm (V s).proj, mfderiv I I (j.symm : M → N) (V s).proj (V s).snd⟩ :
        TangentBundle I N) = (T (X s), fderiv ℝ T (X s) (X' s)) := by
    intro s hs
    obtain ⟨-, hsψ, hsj, hsφ⟩ := hOP s hs
    set y := (V s).proj with hy
    have hchart : j.symm y ∈ (chartAt H q.proj).source := by
      rw [← extChartAt_source (I := I)]; exact hsφ
    refine (extChartAt_tangent_apply_eq_mfderiv q _ hchart).trans ?_
    have hTψ : (T : E → E) ∘ (ψ : M → E) =ᶠ[𝓝 y] (φ : N → E) ∘ (j.symm : M → N) := by
      filter_upwards [(isOpen_extChartAt_source a).mem_nhds hsψ] with w hw
      change φ (j.symm (ψ.symm (ψ w))) = φ (j.symm w)
      rw [ψ.left_inv hw]
    have hψd : MDifferentiableAt I 𝓘(ℝ, E) (ψ : M → E) y :=
      mdifferentiableAt_extChartAt (by rw [← extChartAt_source (I := I)]; exact hsψ)
    have hTd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (T : E → E) (ψ y) :=
      T.mdifferentiableAt hK0 (hXT s hs)
    have hφd : MDifferentiableAt I 𝓘(ℝ, E) (φ : N → E) (j.symm y) :=
      mdifferentiableAt_extChartAt hchart
    have hjd : MDifferentiableAt I I (j.symm : M → N) y := j.symm.mdifferentiableAt hK0 hsj
    have h1 := mfderiv_comp y hTd hψd
    have h2 := mfderiv_comp y hφd hjd
    rw [hTψ.mfderiv_eq, h2, mfderiv_eq_fderiv] at h1
    have h3 := DFunLike.congr_fun h1 (V s).snd
    refine Prod.ext ?_ ?_
    · change φ (j.symm y) = φ (j.symm (ψ.symm (ψ y)))
      rw [ψ.left_inv hsψ]
    · exact h3
  have hfinal : HasDerivAt (fun s => (T (X s), fderiv ℝ T (X s) (X' s)))
      (metricSpray b (T (X t), fderiv ℝ T (X t) (X' t))) t := hd1.prodMk hd2
  rw [← hident t htO] at hfinal
  refine hfinal.congr_of_eventuallyEq ?_
  filter_upwards [hOo.mem_nhds htO] with s hs
  exact hident s hs

end DifferentialGeometry.Geometry.Riemannian.Geodesic
