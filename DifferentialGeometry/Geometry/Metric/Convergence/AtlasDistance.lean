import DifferentialGeometry.Geometry.Metric.Convergence.FiniteCoefficientDistance
import DifferentialGeometry.Geometry.Metric.Isometry.LocalDistance
import DifferentialGeometry.Geometry.Metric.LocalDistanceCompatibility
import DifferentialGeometry.Geometry.Metric.FiniteCoefficients
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.OpenSubtype








set_option autoImplicit false
noncomputable section
open Bundle Manifold Set IsManifold Filter TopologicalSpace
open scoped ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.Geometry.Metric
section
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) 1 X]

private def chartDiffeomorph (e : OpenPartialHomeomorph X E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) 1 X) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X E 1 where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

private def chartToOpen (e : OpenPartialHomeomorph X E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) 1 X) (U : TopologicalSpace.Opens E) (hU : Nonempty U) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X U 1 :=
  (chartDiffeomorph e he).trans
    (DifferentialGeometry.PartialDiffeomorph.ofLE
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, E)) U hU)
      (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).symm

omit [IsManifold 𝓘(ℝ, E) 1 X] in
private theorem chartToOpen_source (e : OpenPartialHomeomorph X E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) 1 X) (U : TopologicalSpace.Opens E) (hU : Nonempty U) :
    (chartToOpen e he U hU).source = e.source ∩ e ⁻¹' (U : Set E) := by
  change e.source ∩ e ⁻¹' (U.openPartialHomeomorphSubtypeCoe hU).target = _
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

omit [IsManifold 𝓘(ℝ, E) 1 X] in
private theorem chartToOpen_val (e : OpenPartialHomeomorph X E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) 1 X) (U : TopologicalSpace.Opens E) (hU : Nonempty U)
    {x : X} (hx : x ∈ (chartToOpen e he U hU).source) :
    ((chartToOpen e he U hU x : U) : E) = e x := by
  exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv hx.2

omit [IsManifold 𝓘(ℝ, E) 1 X] in
private theorem chartToOpen_derivative (e : OpenPartialHomeomorph X E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) 1 X) (U : TopologicalSpace.Opens E) (hU : Nonempty U)
    {x : X} (hx : x ∈ (chartToOpen e he U hU).source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartToOpen e he U hU) x =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x := by
  let Φ := chartToOpen e he U hU
  have hEq : (fun x : X => ((Φ x : U) : E)) =ᶠ[𝓝 x] e := by
    filter_upwards [Φ.open_source.mem_nhds hx] with y hy
    exact chartToOpen_val e he U hU hy
  have hD := hEq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val ∘ Φ) x =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x at hD
  rw [mfderiv_comp x (contMDiff_subtype_val.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
    (Φ.mdifferentiableAt one_ne_zero hx), DifferentialGeometry.mfderiv_subtype_val] at hD
  exact hD

variable [RegularSpace X]
private theorem local_chart_edist {k l : ℕ∞ω}
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) k E (TangentSpace 𝓘(ℝ, E) : X → Type _))
    (e : OpenPartialHomeomorph X E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) 1 X)
    (U : TopologicalSpace.Opens E)
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) l E (TangentSpace 𝓘(ℝ, E) : U → Type _))
    (b : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ x ∈ e.source, ∀ v w : E, g.inner x v w = b (e x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x w))
    (hh : ∀ u : U, ∀ v w : E, h.inner u v w = b u v w)
    {p : X} (hp : p ∈ e.source) (hpU : e p ∈ U) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨h.toRiemannianMetric⟩
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧
      ∃ hsub : V ⊆ e.source ∩ e ⁻¹' (U : Set E),
        ∀ x, ∀ hx : x ∈ V, ∀ y, ∀ hy : y ∈ V,
          riemannianEDist 𝓘(ℝ, E) (⟨e x, (hsub hx).2⟩ : U)
            (⟨e y, (hsub hy).2⟩ : U) = riemannianEDist 𝓘(ℝ, E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨h.toRiemannianMetric⟩
  let hU : Nonempty U := ⟨⟨e p, hpU⟩⟩
  let Φ := chartToOpen e he U hU
  have hinner : ∀ x ∈ Φ.source, ∀ v w : TangentSpace 𝓘(ℝ, E) x,
      h.inner (Φ x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ x w) = g.inner x v w := by
    intro x hx v w
    erw [hh]
    rw [chartToOpen_derivative e he U hU hx, chartToOpen_val e he U hU hx, hg x hx.1 v w]
    rfl
  obtain ⟨V, hV, hpV, hsub, hVeq⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_intrinsic_edist_eq_nhds_of_inner_eq g h Φ.toOpenPartialHomeomorph
      Φ.contMDiffOn_toFun Φ.contMDiffOn_invFun hinner
      (show p ∈ Φ.source from by rw [chartToOpen_source]; exact ⟨hp, hpU⟩)
  have hsub' : V ⊆ e.source ∩ e ⁻¹' (U : Set E) := by
    change V ⊆ (chartToOpen e he U hU).source at hsub
    simpa only [chartToOpen_source] using hsub
  refine ⟨V, hV, hpV, hsub', ?_⟩
  intro x hx y hy
  have hxPhi : Φ x = (⟨e x, (hsub' hx).2⟩ : U) := Subtype.ext (chartToOpen_val e he U hU (hsub hx))
  have hyPhi : Φ y = (⟨e y, (hsub' hy).2⟩ : U) := Subtype.ext (chartToOpen_val e he U hU (hsub hy))
  have hxy := hVeq x hx y hy
  change riemannianEDist 𝓘(ℝ, E) (Φ x) (Φ y) = riemannianEDist 𝓘(ℝ, E) x y at hxy
  simpa only [hxPhi, hyPhi] using hxy
end
section
open DifferentialGeometry Geometry
variable {α ι E F H X : Type*} {l : Filter ι} [l.NeBot]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : ι → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [MetricSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) 1 X]

private abbrev atlasDistanceBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private abbrev atlasDistanceBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
attribute [local instance] atlasDistanceBilinearGroup atlasDistanceBilinearSpace












theorem isRiemannianManifold_of_atlas_metric_limits
    (hX : ∀ x y : X, Metric.intrinsicEDist x y = edist x y) (k : ℕ∞ω)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) k E (TangentSpace 𝓘(ℝ, E) : X → Type _))
    (e : α → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ a, x ∈ (e a).source)
    (he : ∀ a, e a ∈ maximalAtlas 𝓘(ℝ, E) 1 X)
    (R : α → ℝ) (hR : ∀ a, 0 < R a)
    (htarget : ∀ a, (e a).target ⊆ Metric.ball 0 (R a / 8))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hg : ∀ i, letI : RiemannianBundle (TangentSpace I : M i → Type _) :=
      ⟨(g i).toRiemannianMetric⟩; IsRiemannianManifold I (M i))
    (Φ : α → ∀ i, OpenPartialHomeomorph E (M i))
    (hΦ : ∀ a, ∀ᶠ i in l, ContMDiffOn 𝓘(ℝ, E) I 1 (Φ a i) (Φ a i).source)
    (hΦinv : ∀ a, ∀ᶠ i in l, ContMDiffOn I 𝓘(ℝ, E) 1 (Φ a i).symm (Φ a i).target)
    (hsource : ∀ a, ∀ᶠ i in l, Metric.ball (0 : E) (R a) ⊆ (Φ a i).source)
    (himage : ∀ a, ∀ᶠ i in l, (Φ a i : E → M i) '' Metric.ball 0 (R a) =
      Metric.ball (Φ a i 0) (R a))
    (hrad : ∀ a, ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 (R a), dist (Φ a i x) (Φ a i 0) = ‖x‖)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ k (b a) (Metric.ball 0 (R a)))
    (hconv : ∀ a, TendstoUniformlyOn
      (fun i => pullbackMetricCoefficients (g i) (Φ a i)) (b a) l (Metric.ball 0 (R a)))
    (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hlower : ∀ a, ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 (R a), ∀ v : E,
      c a * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ a i) x v v)
    (hG : ∀ a x, x ∈ (e a).source → ∀ v w : E,
      G.inner x v w = b a (e a x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e a) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e a) x w))
    (o : ∀ i, M i) (p : X) {r ε : ι → ℝ}
    (A : ∀ i, GC.MetricGeometry.PointedBallApprox (o i) p (r i) (ε i))
    (hε : Tendsto ε l (𝓝 0)) (L : α → E → X)
    (hdom : ∀ a, ∀ᶠ i in l, ∀ w ∈ Metric.closedBall (0 : E) (R a / 4),
      Φ a i w ∈ Metric.closedBall (o i) (r i))
    (hmap : ∀ a, TendstoUniformlyOn (fun i w => (A i).extendToWholeSpace (Φ a i w)) (L a) l
      (Metric.closedBall 0 (R a / 4)))
    (hchart : ∀ a, EqOn (e a).symm (L a) (e a).target) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
    IsRiemannianManifold 𝓘(ℝ, E) X := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
    ⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩
  apply Manifold.isRiemannianManifold_of_local_edist_eq hX
  intro x₀
  obtain ⟨a, ha⟩ := hcover x₀
  let U := Opens.mk (Metric.ball (0 : E) (R a)) Metric.isOpen_ball
  have hsymm : ∀ x ∈ U, ∀ v w : E, b a x v w = b a x w v := by
    intro x hx v w
    have he (v w : E) : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w) := by
      fun_prop
    apply tendsto_nhds_unique ((he v w).tendsto _ |>.comp ((hconv a).tendsto_at hx))
    have hs := (he w v).tendsto _ |>.comp ((hconv a).tendsto_at hx)
    exact hs.congr (fun i => (g i).symm (Φ a i x) _ _)
  have hpos : ∀ x, x ∈ U → ∀ v : E, v ≠ 0 → 0 < b a x v v := by
    intro x hx v hv
    have he : Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v v) := by fun_prop
    have hl := ge_of_tendsto ((he.tendsto _).comp ((hconv a).tendsto_at hx))
      ((hlower a).mono (fun i hi => hi x hx v))
    exact (mul_pos (hc a) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le hl
  obtain ⟨h, hh⟩ := exists_contMDiffMetric_of_contDiffOn_bilinearField U k (b a)
    hsymm hpos (hb a)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨h.toRiemannianMetric⟩
  have hd := edist_eq_of_uniform_pullbackMetricCoefficients (R a) (hR a) g hg
    (Φ a) (hΦ a) (hΦinv a) (hsource a) (himage a) (hrad a) k (b a) h hh (hconv a)
    (c a) (hc a) (hlower a) o p A hε (L a) (hdom a) (hmap a)
  have hmem (x : X) (hx : x ∈ (e a).source) : e a x ∈ U := by
    have ht := htarget a ((e a).map_source hx)
    have hsmall : R a / 8 < R a := by linarith [hR a]
    exact (Metric.ball_subset_ball hsmall.le) ht
  obtain ⟨V, hV, hx₀V, hsub, hlocal⟩ := local_chart_edist G (e a) (he a) U h (b a)
    (hG a) hh ha (hmem x₀ ha)
  refine ⟨V, hV.mem_nhds hx₀V, ?_⟩
  intro x hx y hy
  have hxt := (e a).map_source (hsub hx).1
  have hyt := (e a).map_source (hsub hy).1
  have hnx : ‖e a x‖ ≤ R a / 8 := by
    have hh := htarget a hxt
    exact (show ‖e a x‖ < R a / 8 from by simpa only [Metric.mem_ball, dist_zero_right] using hh).le
  have hny : ‖e a y‖ ≤ R a / 8 := by
    have hh := htarget a hyt
    exact (show ‖e a y‖ < R a / 8 from by simpa only [Metric.mem_ball, dist_zero_right] using hh).le
  let u : U := ⟨e a x, (hsub hx).2⟩
  let v : U := ⟨e a y, (hsub hy).2⟩
  have hLx : L a (e a x) = x := (hchart a hxt).symm.trans ((e a).left_inv (hsub hx).1)
  have hLy : L a (e a y) = y := (hchart a hyt).symm.trans ((e a).left_inv (hsub hy).1)
  calc
    riemannianEDist 𝓘(ℝ, E) x y = riemannianEDist 𝓘(ℝ, E) u v := (hlocal x hx y hy).symm
    _ = edist (L a (e a x)) (L a (e a y)) := (hd u v hnx hny).symm
    _ = edist x y := by rw [hLx, hLy]
end
end DifferentialGeometry.Geometry.Metric
