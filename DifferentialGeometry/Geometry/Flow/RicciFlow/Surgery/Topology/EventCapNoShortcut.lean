import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCanonicalWindowData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereShortConnector
import DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction
import DifferentialGeometry.Topology.FirstExit
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

/-!
# S-CH11-FIX8 patched-at-path astra `EventCapNoShortcut`

来源：donor `EventCapNoShortcut.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（2 个 error + 1 个未知标识符）。本文件只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `hlen` 里 `simpa only [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) …)] using …`
  的 `by norm_num` 目标是未定元（`0 ≤ ?m`）：改为先 `ENNReal.ofReal_mul`（显式给出
  `0 ≤ 2 * Real.sqrt S.neck.scale`，`positivity`）改写 `ofReal_le_ofReal (hspeed t)` 再 `exact`；
* 末行 `mul_le_mul_left' hdist _` 在本树 Mathlib 里已不存在：改为 `mul_le_mul' le_rfl hdist`。

本文件在原路径（patched-at-path）：下游 `EventWindowEndpointPair` / `NonnegativeEventWindowEndpointPair`
有 `open private … from …EventCapNoShortcut`，所以不用 shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold TopologicalSpace Bundle MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

section WindowQuadraticBound

open StandardCap DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}


private theorem canonical_window_inner_bounds
    (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε) (heps : ε ≤ 1 / 2)
    {x : standardCapWindow D} (hx : ‖x.val‖ < D) (v : TangentSpace ThreeModel x) :
    (1 / 2 : ℝ) * (standardCapMetric.restrictOpen (standardCapWindow D)).inner x v v ≤
      w.windowMetric.inner x v v ∧
    w.windowMetric.inner x v v ≤
      (3 / 2 : ℝ) * (standardCapMetric.restrictOpen (standardCapWindow D)).inner x v v := by
  have hclose := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at hclose
  simp only [distance_zero] at hclose
  have hb := inner_bounds_of_metricDerivENormSupOn_lt
    (metric.restrictOpen (standardCapWindow D)) w.windowMetric hclose hx v
  rw [standardCapMetric_eq_metric]
  have hn := metric_inner_self_nonneg (metric.restrictOpen (standardCapWindow D)) x v
  constructor <;> nlinarith [hb.1, hb.2]

end WindowQuadraticBound

private theorem exceptional_mem_cap
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    {q : Q.Carrier} (hq : q ∉ interior (range E.oldOutput)) :
    ∃ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
      q = (S b).inclusion ((S b).witness.cap z) := by
  let T := E.transition.trace
  let K : Set Q.Carrier := ⋃ b : T.tubes.Boundary,
    Sum.inl ⁻¹' (T.presentation '' range (T.capping.cap b))
  have hK : IsClosed K := isClosed_iUnion_of_finite fun b =>
    ((isCompact_range (T.capping.cap b).continuous).image
      T.presentation.continuous).isClosed.preimage continuous_inl
  have hcompl : Kᶜ ⊆ range E.oldOutput := by
    intro q' hq'
    have hn : T.presentation.symm (Sum.inl q') ∈
        range T.capping.coreInclusion ∪ ⋃ b, range (T.capping.cap b) := by
      rw [T.capping.exhaustive]
      exact mem_univ _
    rcases hn with ⟨x, hx⟩ | hn
    · have hxq : T.presentation (T.capping.coreInclusion x) = Sum.inl q' := by
        rw [hx, Homeomorph.apply_symm_apply]
      have hxold : x ∈ E.old := by
        rw [hOld]
        exact ⟨q', hxq⟩
      refine ⟨⟨x, hxold⟩, ?_⟩
      have h := E.oldOutput_eq ⟨x, hxold⟩
      rw [hxq] at h
      exact (Sum.inl_injective h).symm
    · obtain ⟨b, z, hz⟩ := mem_iUnion.mp hn
      have hmem : q' ∈ K := mem_iUnion.mpr ⟨b, T.capping.cap b z, ⟨z, rfl⟩, by
        rw [hz, Homeomorph.apply_symm_apply]⟩
      exact absurd hmem hq'
  have hqK : q ∈ K := by
    by_contra hn
    exact hq (mem_interior.mpr ⟨Kᶜ, hcompl, hK.isOpen_compl, hn⟩)
  obtain ⟨b, hb⟩ := mem_iUnion.mp hqK
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hb
  let b' : E.RetainedBoundaryIndex :=
    ⟨b, E.retainedBoundary_of_presentation_cap_eq_inl hz⟩
  exact ⟨b', z, Sum.inl_injective (hz.symm.trans ((S b').cap_eq z))⟩

private theorem exceptional_mem_inner_window
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow)
    {q : Q.Carrier} (hq : q ∉ interior (range E.oldOutput)) :
    ∃ (b : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      ‖x.val‖ ≤ StandardCap.transitionEnd ∧ (S b).window x = q := by
  obtain ⟨b, z, hz⟩ := exceptional_mem_cap E S hOld hq
  obtain ⟨_, _, _, _, _, _, _, hcap⟩ := hcanonical b
  obtain ⟨x, hx, hpoint⟩ := hcap z
  exact ⟨b, x, hx, hpoint.trans hz.symm⟩

private theorem actual_window_quad_bounds
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b)
    (hcanonical : S.hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (x : standardCapWindow D) (hx : ‖x.val‖ < D)
    (v : TangentSpace ThreeModel x) :
    (1 / 2 : ℝ) * StandardCap.metric.inner x.val v v ≤
        S.neck.scale * E.outputMetric.inner (S.window x)
          (mfderiv ThreeModel ThreeModel S.window x v)
          (mfderiv ThreeModel ThreeModel S.window x v) ∧
      S.neck.scale * E.outputMetric.inner (S.window x)
          (mfderiv ThreeModel ThreeModel S.window x v)
          (mfderiv ThreeModel ThreeModel S.window x v) ≤
        (3 / 2 : ℝ) * StandardCap.metric.inner x.val v v := by
  obtain ⟨_, _, _, _, w, _, hmetric, _⟩ := hcanonical
  have h := canonical_window_inner_bounds w hε hx v
  rw [standardCapMetric_eq_metric, SmoothRiemannianMetric.restrictOpen_inner,
    hmetric x v v] at h
  exact h

private theorem exists_isometric_old_inverse
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) :
    let V : Opens Q.Carrier := ⟨interior (range E.oldOutput), isOpen_interior⟩
    ∃ F : V → E.incoming.terminalRegularOpen,
      ContMDiff ThreeModel ThreeModel ∞ F ∧
      (∀ y : V, ∃ x : E.old, F y = E.oldTerminal x ∧ E.oldOutput x = y.val) ∧
      ∀ (y : V) (v w : TangentSpace ThreeModel y),
        E.terminal.metric.inner (F y) (mfderiv ThreeModel ThreeModel F y v)
          (mfderiv ThreeModel ThreeModel F y w) =
          E.outputMetric.inner y.val v w := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.transition.trace.tubes.core := E.transition.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.transition.trace.tubes.core := E.transition.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  let V : Opens Q.Carrier := ⟨interior (range E.oldOutput), isOpen_interior⟩
  let i : V → Q.Carrier ⊕ E.discarded.Carrier := fun y => Sum.inl y.val
  have hi : IsSmoothEmbedding ThreeModel ThreeModel ∞ i :=
    (IsSmoothEmbedding.sumInl (I := ThreeModel) (M := Q.Carrier)
      (M' := E.discarded.Carrier)).comp_of_boundarylessManifold_middle
        (IsSmoothEmbedding.of_opens V) (by simp)
  let z : V → E.capped.Carrier := E.transition.presentation.symm ∘ i
  have hz : IsSmoothEmbedding ThreeModel ThreeModel ∞ z :=
    hi.diffeomorph_comp E.transition.presentation.symm
  have hsub : range z ⊆ range E.transition.trace.capping.coreInclusion := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := interior_subset y.property
    refine ⟨x.val, ?_⟩
    apply E.transition.presentation.injective
    change E.transition.presentation (E.transition.trace.capping.coreInclusion x.val) =
      E.transition.presentation (E.transition.presentation.symm (i y))
    rw [E.transition.presentation.apply_symm_apply]
    exact (congrFun E.transition.presentation_eq (E.transition.trace.capping.coreInclusion x.val)).trans
      ((E.oldOutput_eq x).trans (congrArg Sum.inl hx))
  let k : V → E.transition.trace.tubes.core :=
    E.transition.core_inclusion_smooth.lift z hsub
  have hk : ContMDiff ThreeModel (𝓡∂ 3) ∞ k :=
    E.transition.core_inclusion_smooth.contMDiff_lift hz.contMDiff hsub
  let f : V → P.Carrier := Subtype.val ∘ k
  have hf : ContMDiff ThreeModel ThreeModel ∞ f := E.transition.core_induced.contMDiff.comp hk
  have hmem (y : V) : ∃ x : E.old, f y = x.val.val ∧ E.oldOutput x = y.val := by
    obtain ⟨x, hx⟩ := interior_subset y.property
    have hkx : k y = x.val := by
      apply E.transition.core_inclusion_smooth.isEmbedding.injective
      rw [E.transition.core_inclusion_smooth.comp_lift hsub y]
      apply E.transition.presentation.injective
      change E.transition.presentation (E.transition.presentation.symm (i y)) = _
      rw [E.transition.presentation.apply_symm_apply]
      exact ((congrFun E.transition.presentation_eq
        (E.transition.trace.capping.coreInclusion x.val)).trans
          ((E.oldOutput_eq x).trans (congrArg Sum.inl hx))).symm
    exact ⟨x, congrArg Subtype.val hkx, hx⟩
  have hregular (y : V) : f y ∈ E.incoming.terminalRegularOpen := by
    obtain ⟨x, hx, _⟩ := hmem y
    rw [hx, ← E.oldTerminal_eq x]
    exact (E.oldTerminal x).property
  let F : V → E.incoming.terminalRegularOpen := fun y => ⟨f y, hregular y⟩
  have hF : ContMDiff ThreeModel ThreeModel ∞ F := by
    intro y
    exact (ContMDiffAt.subtypeVal_comp_iff E.incoming.terminalRegularOpen F y).mp
      hf.contMDiffAt
  have hFmem (y : V) : ∃ x : E.old, F y = E.oldTerminal x ∧ E.oldOutput x = y.val := by
    obtain ⟨x, hx, hy⟩ := hmem y
    exact ⟨x, Subtype.ext (hx.trans (E.oldTerminal_eq x).symm), hy⟩
  have hsubF : range F ⊆ range E.oldTerminal := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx, _⟩ := hFmem y
    exact ⟨x, hx.symm⟩
  let σ : V → E.old := E.oldTerminal_isSmoothEmbedding.lift F hsubF
  have hσ : ContMDiff ThreeModel (𝓡∂ 3) ∞ σ :=
    E.oldTerminal_isSmoothEmbedding.contMDiff_lift hF hsubF
  have hσterm : E.oldTerminal ∘ σ = F :=
    funext (E.oldTerminal_isSmoothEmbedding.comp_lift hsubF)
  have hσout : E.oldOutput ∘ σ = Subtype.val := by
    funext y
    obtain ⟨x, hx, hy⟩ := hFmem y
    have hσx : σ y = x := E.oldTerminal_isSmoothEmbedding.isEmbedding.injective
      ((congrFun hσterm y).trans hx)
    exact (congrArg E.oldOutput hσx).trans hy
  refine ⟨F, hF, hFmem, ?_⟩
  intro y v w
  have hT := mfderiv_comp y
    (E.oldTerminal_isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp))
  have hO := mfderiv_comp y (E.contMDiff_oldOutput.mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp))
  rw [hσterm] at hT
  rw [hσout, DifferentialGeometry.mfderiv_subtype_val] at hO
  have hv : mfderiv (𝓡∂ 3) ThreeModel E.oldOutput (σ y)
      (mfderiv ThreeModel (𝓡∂ 3) σ y v) = v :=
    (congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A v) hO).symm
  have hw : mfderiv (𝓡∂ 3) ThreeModel E.oldOutput (σ y)
      (mfderiv ThreeModel (𝓡∂ 3) σ y w) = w :=
    (congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A w) hO).symm
  rw [hT]
  change E.terminal.metric.inner (F y)
    (mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal (σ y) (mfderiv ThreeModel (𝓡∂ 3) σ y v))
    (mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal (σ y) (mfderiv ThreeModel (𝓡∂ 3) σ y w)) = _
  have hmetric := E.old_metric_eq (σ y)
    (mfderiv ThreeModel (𝓡∂ 3) σ y v) (mfderiv ThreeModel (𝓡∂ 3) σ y w)
  have hterminal := congrArg (fun p : E.incoming.terminalRegularOpen =>
    E.terminal.metric.inner p
      (mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal (σ y) (mfderiv ThreeModel (𝓡∂ 3) σ y v))
      (mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal (σ y) (mfderiv ThreeModel (𝓡∂ 3) σ y w)))
    (congrFun hσterm y)
  have houtput := congrArg (fun p : Q.Carrier => E.outputMetric.inner p v w)
    (congrFun hσout y)
  exact hterminal.symm.trans (hmetric.trans ((congrArg₂
    (fun v w : ThreeSpace => E.outputMetric.inner (E.oldOutput (σ y)) v w) hv hw).trans houtput))

private theorem exists_window_exit
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b)
    {R T : ℝ} (hR : R < D + 1) (hT : 0 < T)
    (γ : ℝ → Q.Carrier) (hγ : ContinuousOn γ (Icc 0 T))
    (x : standardCapWindow D) (hx : ‖x.val‖ < R) (hstart : γ 0 = S.window x)
    (hend : γ T ∉ S.window '' {y : standardCapWindow D | ‖y.val‖ ≤ R}) :
    ∃ τ ∈ Ioc 0 T,
      (∀ t ∈ Icc 0 τ,
        γ t ∈ S.window '' {y : standardCapWindow D | ‖y.val‖ ≤ R}) ∧
      ∃ y : standardCapWindow D, ‖y.val‖ = R ∧ S.window y = γ τ := by
  let K : Set Q.Carrier := S.window '' {y : standardCapWindow D | ‖y.val‖ ≤ R}
  let U : Set (standardCapWindow D) := {y | ‖y.val‖ < R}
  have hK : IsClosed K :=
    ((StandardCap.isCompact_window_norm_le hR).image S.window.continuous).isClosed
  have hU : IsOpen U := isOpen_lt continuous_subtype_val.norm continuous_const
  have hJ := DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
    S.window S.window_smooth.contMDiff S.window_smooth.isEmbedding.injective
    (fun y => (S.window_smooth.isImmersion.isImmersionAt y).mfderiv_injective (by simp)) rfl
  have hUK : S.window '' U ⊆ K := image_mono fun y hy =>
    show ‖y.val‖ ≤ R from (show ‖y.val‖ < R from hy).le
  have hstartK : γ 0 ∈ interior K := by
    rw [hstart]
    exact mem_interior.mpr ⟨S.window '' U, hUK, hJ.isOpenMap U hU,
      mem_image_of_mem S.window hx⟩
  obtain ⟨τ, hτ, hstay, hfront⟩ :=
    DifferentialGeometry.exists_first_exit_frontier hK hT hγ hstartK hend
  obtain ⟨y, hy, hyτ⟩ := hK.closure_eq ▸ frontier_subset_closure hfront
  have hyR : ‖y.val‖ = R := by
    apply le_antisymm hy
    apply le_of_not_gt
    intro hlt
    apply hfront.2
    rw [← hyτ]
    exact mem_interior.mpr ⟨S.window '' U, hUK, hJ.isOpenMap U hU,
      mem_image_of_mem S.window hlt⟩
  exact ⟨τ, hτ, hstay, y, hyR, hyτ⟩

private theorem exists_window_smooth_lift
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b)
    (γ : ℝ → Q.Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ)
    (x : standardCapWindow D) :
    ∃ η : ℝ → standardCapWindow D,
      ∀ t : ℝ, γ t ∈ range S.window →
        ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel ∞ η t ∧ S.window (η t) = γ t := by
  classical
  let U : Set ℝ := γ ⁻¹' range S.window
  have hJ := DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
    S.window S.window_smooth.contMDiff S.window_smooth.isEmbedding.injective
    (fun y => (S.window_smooth.isImmersion.isImmersionAt y).mfderiv_injective (by simp)) rfl
  have hU : IsOpen U := hJ.isOpen_range.preimage hγ.continuous
  let η : ℝ → standardCapWindow D := fun t =>
    if ht : γ t ∈ range S.window then
      S.window_smooth.isEmbedding.toHomeomorph.symm ⟨γ t, ht⟩ else x
  have hcomp (t : ℝ) (ht : t ∈ U) : S.window (η t) = γ t := by
    dsimp only [η]
    change γ t ∈ range S.window at ht
    rw [dite_eq_left ht]
    exact congrArg Subtype.val
      (S.window_smooth.isEmbedding.toHomeomorph.apply_symm_apply ⟨γ t, ht⟩)
  have hcont : ContinuousOn η U :=
    S.window_smooth.isEmbedding.continuousOn_iff.mpr
      (hγ.continuous.continuousOn.congr hcomp)
  refine ⟨η, ?_⟩
  intro t ht
  have hcompNear : S.window ∘ η =ᶠ[𝓝 t] γ := by
    filter_upwards [hU.mem_nhds ht] with r hr
    exact hcomp r hr
  refine ⟨?_, hcomp t ht⟩
  rw [ContMDiffAt.iff_comp_isImmersionAt (S.window_smooth.isImmersion.isImmersionAt (η t))]
  exact ⟨hcont.continuousAt (hU.mem_nhds ht),
    hγ.contMDiffAt.congr_of_eventuallyEq hcompNear⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edist_le_elength
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X]
    (g : SmoothRiemannianMetric ThreeModel X) {γ : ℝ → X} {l r : ℝ}
    (hlr : l ≤ r) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc l r)) :
    riemannianEDistOf g (γ l) (γ r) ≤ riemannianCurveELength g γ l r := by
  let : RiemannianBundle (TangentSpace ThreeModel : X → Type _) := ⟨g.toRiemannianMetric⟩
  rw [riemannianCurveELength_eq_pathELength]
  exact riemannianEDist_le_pathELength hγ rfl rfl hlr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem window_radial_change_le_length
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b)
    (hcanonical : S.hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (γ : ℝ → Q.Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ)
    {l r : ℝ} (hlr : l ≤ r)
    (hmap : MapsTo γ (Icc l r)
      (S.window '' {y : standardCapWindow D | ‖y.val‖ < D}))
    (x y : standardCapWindow D) (hx : S.window x = γ l) (hy : S.window y = γ r) :
    ENNReal.ofReal |‖y.val‖ - ‖x.val‖| ≤
      ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
        riemannianCurveELength E.outputMetric γ l r := by
  obtain ⟨η, hη⟩ := exists_window_smooth_lift S γ hγ x
  have hrange (t : ℝ) (ht : t ∈ Icc l r) : γ t ∈ range S.window := by
    obtain ⟨z, _, hz⟩ := hmap ht
    exact ⟨z, hz⟩
  have hηC (t : ℝ) (ht : t ∈ Icc l r) := (hη t (hrange t ht)).1
  have hpoint (t : ℝ) (ht : t ∈ Icc l r) := (hη t (hrange t ht)).2
  have hηnorm (t : ℝ) (ht : t ∈ Icc l r) : ‖(η t).val‖ < D := by
    obtain ⟨z, hz, hzγ⟩ := hmap ht
    have heq : η t = z := S.window_smooth.isEmbedding.injective
      ((hpoint t ht).trans hzγ.symm)
    exact heq.symm ▸ hz
  have hηl : η l = x := S.window_smooth.isEmbedding.injective
    ((hpoint l ⟨le_rfl, hlr⟩).trans hx.symm)
  have hηr : η r = y := S.window_smooth.isEmbedding.injective
    ((hpoint r ⟨hlr, le_rfl⟩).trans hy.symm)
  let δ : ℝ → ThreeSpace := Subtype.val ∘ η
  have hδ (t : ℝ) (ht : t ∈ Icc l r) : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel ∞ δ t :=
    (contMDiff_subtype_val (U := standardCapWindow D)).contMDiffAt.comp t (hηC t ht)
  have hδ1 : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 δ (Icc l r) :=
    fun t ht => ((hδ t ht).of_le (by simp)).contMDiffWithinAt
  have hlower : ENNReal.ofReal |‖y.val‖ - ‖x.val‖| ≤
      riemannianCurveELength StandardCap.metric δ l r := by
    have hdist : riemannianEDistOf StandardCap.metric x.val y.val ≤
        riemannianCurveELength StandardCap.metric δ l r := by
      simpa only [δ, Function.comp_apply, hηl, hηr] using
        (edist_le_elength StandardCap.metric hlr hδ1)
    exact (StandardCap.radial_difference_le_edist x.val y.val).trans hdist
  have hlength : riemannianCurveELength StandardCap.metric δ l r ≤
      ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
        riemannianCurveELength E.outputMetric γ l r := by
    unfold riemannianCurveELength
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht' : t ∈ Icc l r := Ioo_subset_Icc_self ht
    have hnear : S.window ∘ η =ᶠ[𝓝 t] γ := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
      exact hpoint v (Ioo_subset_Icc_self hv)
    have hD := (hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)).symm
    rw [mfderiv_comp t (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
      ((hηC t ht').mdifferentiableAt (by simp))] at hD
    have hvalD := mfderiv_comp t
      ((contMDiff_subtype_val (U := standardCapWindow D) (n := ∞)).mdifferentiableAt (by simp))
      ((hηC t ht').mdifferentiableAt (by simp))
    rw [DifferentialGeometry.mfderiv_subtype_val] at hvalD
    let v : ThreeSpace := mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1
    have hδD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel δ t 1 : ThreeSpace) = v := by
      exact congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) hvalD
    have hγD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ t 1 : ThreeSpace) =
        mfderiv ThreeModel ThreeModel S.window (η t) v := by
      exact congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) hD
    have hquad := (actual_window_quad_bounds S hcanonical hε (η t) (hηnorm t ht') v).1
    let X := StandardCap.metric.inner (η t).val v v
    let Y := E.outputMetric.inner (S.window (η t))
      (mfderiv ThreeModel ThreeModel S.window (η t) v)
      (mfderiv ThreeModel ThreeModel S.window (η t) v)
    have hY : 0 ≤ Y := metric_inner_self_nonneg E.outputMetric _ _
    have hfour : X ≤ 4 * S.neck.scale * Y := by
      have hqY : 0 ≤ S.neck.scale * Y := mul_nonneg S.neck.scale_pos.le hY
      change (1 / 2 : ℝ) * X ≤ S.neck.scale * Y at hquad
      nlinarith
    have hsqrt : Real.sqrt X ≤ (2 * Real.sqrt S.neck.scale) * Real.sqrt Y := by
      calc
        Real.sqrt X ≤ Real.sqrt (4 * S.neck.scale * Y) := Real.sqrt_le_sqrt hfour
        _ = (2 * Real.sqrt S.neck.scale) * Real.sqrt Y := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) S.neck.scale_pos.le),
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    have hs : riemannianCurveSpeed StandardCap.metric δ t ≤
        (2 * Real.sqrt S.neck.scale) * riemannianCurveSpeed E.outputMetric γ t := by
      have hδspeed : riemannianCurveSpeed StandardCap.metric δ t = Real.sqrt X :=
        congrArg Real.sqrt (congrArg
          (fun v : ThreeSpace => StandardCap.metric.inner (η t).val v v) hδD)
      have hγspeed : riemannianCurveSpeed E.outputMetric γ t = Real.sqrt Y :=
        congrArg Real.sqrt (congrArg₂
          (fun (p : Q.Carrier) (v : ThreeSpace) => E.outputMetric.inner p v v)
          (hpoint t ht').symm hγD)
      calc
        _ = Real.sqrt X := hδspeed
        _ ≤ (2 * Real.sqrt S.neck.scale) * Real.sqrt Y := hsqrt
        _ = _ := congrArg (fun z : ℝ => (2 * Real.sqrt S.neck.scale) * z) hγspeed.symm
    exact (ENNReal.ofReal_le_ofReal hs).trans_eq
      (ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Real.sqrt_nonneg S.neck.scale)))
  exact hlower.trans hlength

private local instance sphereDimension : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem window_sphere_distance_bound
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b)
    (hcanonical : S.hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    {R : ℝ} (hRL : StandardCap.transitionEnd ≤ R) (hRD : R < D)
    (x y : standardCapWindow D) (hx : ‖x.val‖ = R) (hy : ‖y.val‖ = R) :
    ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
        riemannianEDistOf E.outputMetric (S.window x) (S.window y) ≤
      ENNReal.ofReal (4 * Real.pi) := by
  have hR : 0 < R := StandardCap.transitionEnd_pos.trans_le hRL
  let p : Sphere 2 := ⟨R⁻¹ • x.val, by
    apply (show (R⁻¹ • x.val ∈ Metric.sphere (0 : ThreeSpace) 1) ↔
      ‖R⁻¹ • x.val‖ = 1 by simp only [Metric.mem_sphere, dist_zero_right]).mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hx,
      inv_mul_cancel₀ hR.ne']⟩
  let q : Sphere 2 := ⟨R⁻¹ • y.val, by
    apply (show (R⁻¹ • y.val ∈ Metric.sphere (0 : ThreeSpace) 1) ↔
      ‖R⁻¹ • y.val‖ = 1 by simp only [Metric.mem_sphere, dist_zero_right]).mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hy,
      inv_mul_cancel₀ hR.ne']⟩
  obtain ⟨L, σ, hL, hσ, hσ0, hσ1, hσspeed⟩ :=
    Perelman.KappaSolutions.sphere2_exists_short_constant_speed_curve p q
  have hσnorm (t : ℝ) : ‖(σ t : ThreeSpace)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using (σ t).property
  let ψ : ℝ → ThreeSpace := fun t => R • (σ t : ThreeSpace)
  have hψ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ ψ :=
    (contMDiff_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (c := R)).smul
      ((contMDiff_coe_sphere (n := 2)).comp hσ)
  have hψnorm (t : ℝ) : ‖ψ t‖ = R := by
    simp only [ψ, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hσnorm, mul_one]
  let β : ℝ → standardCapWindow D := fun t => ⟨ψ t, by
    change ‖ψ t‖ < D + 1
    rw [hψnorm]
    linarith⟩
  have hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β := by
    intro t
    exact (ContMDiffAt.subtypeVal_comp_iff (standardCapWindow D) β t).mp
      hψ.contMDiffAt
  have hβ0 : β 0 = x := by
    apply Subtype.ext
    change R • (σ 0 : ThreeSpace) = x.val
    rw [hσ0]
    change R • (R⁻¹ • x.val) = x.val
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hβ1 : β 1 = y := by
    apply Subtype.ext
    change R • (σ 1 : ThreeSpace) = y.val
    rw [hσ1]
    change R • (R⁻¹ • y.val) = y.val
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hβD (t : ℝ) : (mfderiv 𝓘(ℝ, ℝ) ThreeModel β t 1 : ThreeSpace) =
      R • dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1) := by
    have hval := mfderiv_comp t
      ((contMDiff_subtype_val (U := standardCapWindow D) (n := ∞)).mdifferentiableAt (by simp))
      (hβ.mdifferentiableAt (by simp))
    rw [DifferentialGeometry.mfderiv_subtype_val] at hval
    have hscale := const_smul_mfderiv
      (((contMDiff_coe_sphere (n := 2)).comp hσ).mdifferentiableAt (by simp) (x := t)) R
    have hincl := mfderiv_comp t
      ((contMDiff_coe_sphere (m := ∞) (n := 2)).mdifferentiableAt (by simp))
      (hσ.mdifferentiableAt (by simp))
    have hD : mfderiv 𝓘(ℝ, ℝ) ThreeModel ψ t =
        R • (dIncl (n := 2) (σ t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) := by
      exact hscale.trans (congrArg (fun A => R • A) hincl)
    have heq : mfderiv 𝓘(ℝ, ℝ) ThreeModel β t =
        R • (dIncl (n := 2) (σ t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t) :=
      hval.symm.trans hD
    exact congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) heq
  have hmodel (t : ℝ) : StandardCap.metric.inner (β t).val
      (mfderiv 𝓘(ℝ, ℝ) ThreeModel β t 1)
      (mfderiv 𝓘(ℝ, ℝ) ThreeModel β t 1) = 2 * L ^ 2 := by
    refine (congrArg (fun v : ThreeSpace => StandardCap.metric.inner (β t).val v v)
      (hβD t)).trans ?_
    change StandardCap.metric.inner (R • (σ t : ThreeSpace))
      (R • dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1))
      (R • dIncl (n := 2) (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1)) = _
    have h := StandardCap.metric_inner_polar (hσnorm t)
      (dIncl_orth (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1))
      (dIncl_orth (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) σ t 1)) hR 0 0
    simpa only [zero_smul, zero_add, zero_mul,
      StandardCap.warpingFunction_eq_sqrt_two hRL, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      ← roundMetric_inner, hσspeed] using h
  let δ : ℝ → Q.Carrier := S.window ∘ β
  have hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ δ := S.window_smooth.contMDiff.comp hβ
  have hspeed (t : ℝ) :
      (2 * Real.sqrt S.neck.scale) * riemannianCurveSpeed E.outputMetric δ t ≤ 4 * L := by
    have hD := mfderiv_comp t (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
      (hβ.mdifferentiableAt (by simp))
    let v : ThreeSpace := mfderiv 𝓘(ℝ, ℝ) ThreeModel β t 1
    let Y := E.outputMetric.inner (S.window (β t))
      (mfderiv ThreeModel ThreeModel S.window (β t) v)
      (mfderiv ThreeModel ThreeModel S.window (β t) v)
    have hq := (actual_window_quad_bounds S hcanonical hε (β t)
      (by change ‖ψ t‖ < D; rw [hψnorm]; exact hRD) v).2
    rw [show StandardCap.metric.inner (β t).val v v = 2 * L ^ 2 from hmodel t] at hq
    have hq4 : S.neck.scale * Y ≤ 4 * L ^ 2 := by
      change S.neck.scale * Y ≤ (3 / 2 : ℝ) * (2 * L ^ 2) at hq
      nlinarith [sq_nonneg L]
    have hs : Real.sqrt S.neck.scale * Real.sqrt Y ≤ 2 * L := by
      calc
        Real.sqrt S.neck.scale * Real.sqrt Y = Real.sqrt (S.neck.scale * Y) :=
          (Real.sqrt_mul S.neck.scale_pos.le Y).symm
        _ ≤ Real.sqrt (4 * L ^ 2) := Real.sqrt_le_sqrt hq4
        _ = 2 * L := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq hL.1]; norm_num
    unfold riemannianCurveSpeed
    rw [hD]
    change (2 * Real.sqrt S.neck.scale) * Real.sqrt Y ≤ 4 * L
    nlinarith
  have hlen : ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
      riemannianCurveELength E.outputMetric δ 0 1 ≤ ENNReal.ofReal (4 * L) := by
    unfold riemannianCurveELength
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (4 * L) := by
        apply lintegral_mono_ae
        filter_upwards [] with t
        have h1 := ENNReal.ofReal_le_ofReal (hspeed t)
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt S.neck.scale)] at h1
        exact h1
      _ = ENNReal.ofReal (4 * L) := by rw [setLIntegral_const, Real.volume_Icc]; norm_num
  have hdist := edist_le_elength E.outputMetric zero_le_one
    (hδ.of_le (by simp)).contMDiffOn
  have hend : δ 0 = S.window x ∧ δ 1 = S.window y :=
    ⟨congrArg S.window hβ0, congrArg S.window hβ1⟩
  rw [hend.1, hend.2] at hdist
  exact ((mul_le_mul' le_rfl hdist).trans hlen).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hL.2 (by norm_num)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_post_minimizing_curve
    (Q : OrientedThreeStage.{u}) (g : SmoothRiemannianMetric ThreeModel Q.Carrier)
    (p q : Q.Carrier) (hfin : riemannianEDistOf g p q ≠ ⊤) :
    ∃ (γ : ℝ → Q.Carrier) (c : ℝ), 0 ≤ c ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧ γ 0 = p ∧ γ 1 = q ∧
      (∀ l r : ℝ, l ≤ r → riemannianCurveELength g γ l r = ENNReal.ofReal (c * (r - l))) ∧
      (∀ l r : ℝ, 0 ≤ l → l ≤ r → r ≤ 1 →
        riemannianEDistOf g (γ l) (γ r) = ENNReal.ofReal (c * (r - l))) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let : IsManifold ThreeModel 1 Q.Carrier :=
    IsManifold.of_le (I := ThreeModel) (M := Q.Carrier) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : MetrizableSpace Q.Carrier := Manifold.metrizableSpace ThreeModel Q.Carrier
  let : T3Space Q.Carrier := inferInstance
  let : RiemannianBundle (fun x : Q.Carrier => TangentSpace ThreeModel x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : Q.Carrier => TangentSpace ThreeModel x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Q.Carrier := EMetricSpace.ofRiemannianMetric ThreeModel Q.Carrier
  let : PseudoEMetricSpace Q.Carrier :=
    (EMetricSpace.ofRiemannianMetric ThreeModel Q.Carrier).toPseudoEMetricSpace
  let : CompleteSpace Q.Carrier := (RiemannianMetricComplete.of_compact g).complete
  have hEnorm : Riemannian.IsMetricNorm (I := ThreeModel) (M := Q.Carrier) g := by
    intro x v
    exact Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := ThreeModel) g x v
  obtain ⟨v, hv, hnorm⟩ :=
    Riemannian.Exponential.hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      g hEnorm p q hfin
  let γ : ℝ → Q.Carrier := Riemannian.Exponential.intrinsicGeodesic g hEnorm p v
  let c : ℝ := Real.sqrt (g.inner p v v)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ :=
    Riemannian.Exponential.intrinsicGeodesic_contMDiff g hEnorm p v
  have hγ0 : γ 0 = p := Riemannian.Exponential.intrinsicGeodesic_zero g hEnorm p v
  have hγ1 : γ 1 = q := hv
  have hspeed (t : ℝ) : riemannianCurveSpeed g γ t = c := by
    exact congrArg Real.sqrt
      (Riemannian.Exponential.intrinsicGeodesic_speedSq_eq g hEnorm p v t)
  have hlen (l r : ℝ) (_hlr : l ≤ r) :
      riemannianCurveELength g γ l r = ENNReal.ofReal (c * (r - l)) := by
    unfold riemannianCurveELength
    simp_rw [hspeed]
    rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hc]
  have hupper (l r : ℝ) (hlr : l ≤ r) :
      riemannianEDistOf g (γ l) (γ r) ≤ ENNReal.ofReal (c * (r - l)) := by
    exact (edist_le_elength g hlr (hγ.of_le (by simp)).contMDiffOn).trans_eq (hlen l r hlr)
  have hfinite (l r : ℝ) (hlr : l ≤ r) : riemannianEDistOf g (γ l) (γ r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper l r hlr)
  have hupperReal (l r : ℝ) (hlr : l ≤ r) :
      (riemannianEDistOf g (γ l) (γ r)).toReal ≤ c * (r - l) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper l r hlr)
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hc (sub_nonneg.mpr hlr))] using h
  have h01 : (riemannianEDistOf g (γ 0) (γ 1)).toReal = c := by
    rw [hγ0, hγ1]
    exact hnorm.symm
  refine ⟨γ, c, hc, hγ, hγ0, hγ1, hlen, ?_⟩
  intro l r hl hlr hr
  apply (ENNReal.toReal_eq_toReal_iff' (hfinite l r hlr) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (mul_nonneg hc (sub_nonneg.mpr hlr))]
  refine le_antisymm (hupperReal l r hlr) ?_
  have htri1 := riemannianEDistOf_toReal_triangle g (γ 0) (γ r) (γ 1)
    (hfinite 0 r (hl.trans hlr)) (hfinite r 1 hr)
  have htri2 := riemannianEDistOf_toReal_triangle g (γ 0) (γ l) (γ r)
    (hfinite 0 l hl) (hfinite l r hlr)
  rw [h01] at htri1
  have ha := hupperReal 0 l hl
  have hb := hupperReal r 1 hr
  nlinarith

private theorem minimizing_curve_avoids_inner_window
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b)
    (hcanonical : S.hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (γ : ℝ → Q.Carrier) (c : ℝ) (hc : 0 ≤ c)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ)
    (hlen : ∀ l r : ℝ, l ≤ r →
      riemannianCurveELength E.outputMetric γ l r = ENNReal.ofReal (c * (r - l)))
    (hsegment : ∀ l r : ℝ, 0 ≤ l → l ≤ r → r ≤ 1 →
      riemannianEDistOf E.outputMetric (γ l) (γ r) = ENNReal.ofReal (c * (r - l)))
    (hzero : γ 0 ∉ S.window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hone : γ 1 ∉ S.window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10}) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ S.window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd} := by
  intro t ht hhit
  obtain ⟨x, hx, hxt⟩ := hhit
  change ‖x.val‖ ≤ StandardCap.transitionEnd at hx
  let R : ℝ := StandardCap.transitionEnd + 10
  have hxR : ‖x.val‖ < R := by dsimp [R]; linarith
  have ht0 : 0 < t := by
    by_contra hnot
    have htEq : t = 0 := le_antisymm (not_lt.mp hnot) ht.1
    apply hzero
    exact ⟨x, hxR.le, hxt.trans (congrArg γ htEq)⟩
  have ht1 : t < 1 := by
    by_contra hnot
    have htEq : t = 1 := le_antisymm ht.2 (not_lt.mp hnot)
    apply hone
    exact ⟨x, hxR.le, hxt.trans (congrArg γ htEq)⟩
  let γminus : ℝ → Q.Carrier := fun v => γ (t - v)
  let γplus : ℝ → Q.Carrier := fun v => γ (t + v)
  obtain ⟨τminus, hτminus, hstayminus, yminus, hyminus, hymγ⟩ :=
    exists_window_exit S (by dsimp [R]; linarith) ht0 γminus
      (hγ.continuous.comp (continuous_const.sub continuous_id)).continuousOn x hxR
      (by simpa only [γminus, sub_zero] using hxt.symm)
      (by simpa only [γminus, sub_self] using hzero)
  obtain ⟨τplus, hτplus, hstayplus, yplus, hyplus, hypγ⟩ :=
    exists_window_exit S (by dsimp [R]; linarith) (sub_pos.mpr ht1) γplus
      (hγ.continuous.comp (continuous_const.add continuous_id)).continuousOn x hxR
      (by simpa only [γplus, add_zero] using hxt.symm)
      (by simpa only [γplus, show t + (1 - t) = 1 by ring] using hone)
  let l : ℝ := t - τminus
  let r : ℝ := t + τplus
  have hl0 : 0 ≤ l := sub_nonneg.mpr hτminus.2
  have hlt : l ≤ t := by dsimp [l]; linarith [hτminus.1]
  have htr : t ≤ r := by dsimp [r]; linarith [hτplus.1]
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [hτplus.2]
  have hm (v : ℝ) (hv : v ∈ Icc l t) :
      γ v ∈ S.window '' {y : standardCapWindow D | ‖y.val‖ < D} := by
    have hv' : t - v ∈ Icc (0 : ℝ) τminus := by
      dsimp [l] at hv
      constructor <;> linarith [hv.1, hv.2]
    obtain ⟨y, hy, hyγ⟩ := hstayminus (t - v) hv'
    refine ⟨y, hy.trans_lt hD, ?_⟩
    simpa only [γminus, sub_sub_cancel] using hyγ
  have hp (v : ℝ) (hv : v ∈ Icc t r) :
      γ v ∈ S.window '' {y : standardCapWindow D | ‖y.val‖ < D} := by
    have hv' : v - t ∈ Icc (0 : ℝ) τplus := by
      dsimp [r] at hv
      constructor <;> linarith [hv.1, hv.2]
    obtain ⟨y, hy, hyγ⟩ := hstayplus (v - t) hv'
    refine ⟨y, hy.trans_lt hD, ?_⟩
    simpa only [γplus, show t + (v - t) = v by ring] using hyγ
  have hradialMinus := window_radial_change_le_length S hcanonical hε γ hγ hlt
    (fun _ hv => hm _ hv) yminus x hymγ hxt
  have hradialPlus := window_radial_change_le_length S hcanonical hε γ hγ htr
    (fun _ hv => hp _ hv) x yplus hxt hypγ
  have htenMinus : (10 : ℝ) ≤ |‖x.val‖ - ‖yminus.val‖| := by
    rw [hyminus, abs_of_nonpos (by dsimp [R]; linarith)]
    dsimp [R]
    linarith
  have htenPlus : (10 : ℝ) ≤ |‖yplus.val‖ - ‖x.val‖| := by
    rw [hyplus, abs_of_nonneg (by dsimp [R]; linarith)]
    dsimp [R]
    linarith
  have hminus := (ENNReal.ofReal_le_ofReal htenMinus).trans hradialMinus
  have hplus := (ENNReal.ofReal_le_ofReal htenPlus).trans hradialPlus
  have hsum : riemannianCurveELength E.outputMetric γ l t +
      riemannianCurveELength E.outputMetric γ t r =
      riemannianEDistOf E.outputMetric (γ l) (γ r) := by
    rw [hlen l t hlt, hlen t r htr, hsegment l r hl0 (hlt.trans htr) hr1,
      ← ENNReal.ofReal_add (mul_nonneg hc (sub_nonneg.mpr hlt))
        (mul_nonneg hc (sub_nonneg.mpr htr))]
    congr 1
    ring
  have hshort := window_sphere_distance_bound S hcanonical hε
    (show StandardCap.transitionEnd ≤ R by dsimp [R]; linarith) hD
    yminus yplus hyminus hyplus
  change ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
    riemannianEDistOf E.outputMetric (S.window yminus) (S.window yplus) ≤ _ at hshort
  rw [hymγ, hypγ] at hshort
  have hbad : ENNReal.ofReal (20 : ℝ) ≤ ENNReal.ofReal (4 * Real.pi) := by
    calc
      _ = ENNReal.ofReal (10 : ℝ) + ENNReal.ofReal (10 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
          riemannianCurveELength E.outputMetric γ l t +
          ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
          riemannianCurveELength E.outputMetric γ t r := add_le_add hminus hplus
      _ = ENNReal.ofReal (2 * Real.sqrt S.neck.scale) *
          riemannianEDistOf E.outputMetric (γ l) (γ r) := by rw [← mul_add, hsum]
      _ ≤ _ := hshort
  have hbadReal : (20 : ℝ) ≤ 4 * Real.pi :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 4 * Real.pi)).mp hbad
  nlinarith [Real.pi_lt_four]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem terminal_distance_le_of_interior_curve
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (u z : E.old)
    (γ : ℝ → Q.Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ)
    (hγ0 : γ 0 = E.oldOutput u) (hγ1 : γ 1 = E.oldOutput z)
    (hmap : MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput))) :
    riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal z) ≤
      riemannianCurveELength E.outputMetric γ 0 1 := by
  classical
  let V : Opens Q.Carrier := ⟨interior (range E.oldOutput), isOpen_interior⟩
  obtain ⟨F, hF, hFmem, hmetric⟩ := exists_isometric_old_inverse E
  let δ : ℝ → V := fun t => if ht : γ t ∈ V then ⟨γ t, ht⟩ else ⟨γ 0, hmap (by simp)⟩
  have hpoint (t : ℝ) (ht : γ t ∈ V) : (δ t).val = γ t := by
    dsimp only [δ]
    rw [dite_eq_left ht]
  have hnear (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Subtype.val ∘ δ =ᶠ[𝓝 t] γ := by
    filter_upwards [(hγ.continuous.isOpen_preimage _ V.isOpen).mem_nhds (hmap ht)] with r hr
    exact hpoint r hr
  have hδ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel ∞ δ t := by
    apply (ContMDiffAt.subtypeVal_comp_iff V δ t).mp
    exact hγ.contMDiffAt.congr_of_eventuallyEq (hnear t ht)
  let η : ℝ → E.incoming.terminalRegularOpen := F ∘ δ
  have hη (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel ∞ η t := hF.contMDiffAt.comp t (hδ t ht)
  have hη0 : η 0 = E.oldTerminal u := by
    obtain ⟨x, hx, hxout⟩ := hFmem (δ 0)
    have hxu : x = u := E.oldOutput_injective
      (hxout.trans ((hpoint 0 (hmap (by simp))).trans hγ0))
    exact hx.trans (congrArg E.oldTerminal hxu)
  have hη1 : η 1 = E.oldTerminal z := by
    obtain ⟨x, hx, hxout⟩ := hFmem (δ 1)
    have hxz : x = z := E.oldOutput_injective
      (hxout.trans ((hpoint 1 (hmap (by simp))).trans hγ1))
    exact hx.trans (congrArg E.oldTerminal hxz)
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      riemannianCurveSpeed E.terminal.metric η t = riemannianCurveSpeed E.outputMetric γ t := by
    have hD := mfderiv_comp t (hF.mdifferentiableAt (by simp))
      ((hδ t ht).mdifferentiableAt (by simp))
    have hDval := mfderiv_comp t
      ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiableAt (by simp))
      ((hδ t ht).mdifferentiableAt (by simp))
    rw [DifferentialGeometry.mfderiv_subtype_val] at hDval
    have hDγ := (hnear t ht).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    have hδγ : mfderiv 𝓘(ℝ, ℝ) ThreeModel δ t = mfderiv 𝓘(ℝ, ℝ) ThreeModel γ t :=
      hDval.symm.trans hDγ
    have hηD : (mfderiv 𝓘(ℝ, ℝ) ThreeModel η t 1 : ThreeSpace) =
        mfderiv ThreeModel ThreeModel F (δ t) (mfderiv 𝓘(ℝ, ℝ) ThreeModel δ t 1) :=
      congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) hD
    have hδγv : (mfderiv 𝓘(ℝ, ℝ) ThreeModel δ t 1 : ThreeSpace) =
        mfderiv 𝓘(ℝ, ℝ) ThreeModel γ t 1 :=
      congrArg (fun A : ℝ →L[ℝ] ThreeSpace => A 1) hδγ
    have hleft := congrArg
      (fun v : ThreeSpace => E.terminal.metric.inner (F (δ t)) v v) hηD
    have hmiddle := hmetric (δ t) (mfderiv 𝓘(ℝ, ℝ) ThreeModel δ t 1)
      (mfderiv 𝓘(ℝ, ℝ) ThreeModel δ t 1)
    have hright := congrArg₂
      (fun (p : Q.Carrier) (v : ThreeSpace) => E.outputMetric.inner p v v)
      (hpoint t (hmap ht)) hδγv
    exact congrArg Real.sqrt (hleft.trans (hmiddle.trans hright))
  have hlen : riemannianCurveELength E.terminal.metric η 0 1 =
      riemannianCurveELength E.outputMetric γ 0 1 := by
    unfold riemannianCurveELength
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hspeed t ht]
  have hdist := edist_le_elength E.terminal.metric zero_le_one
    (fun t ht => ((hη t ht).of_le (by simp)).contMDiffWithinAt)
  rw [hη0, hη1, hlen] at hdist
  exact hdist

theorem MetricCutCapEvent.oldTerminal_edist_le_of_outside_canonical_cap_windows
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow)
    (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (u z : E.old)
    (hu : ∀ b, E.oldOutput u ∉ (S b).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ b, E.oldOutput z ∉ (S b).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10}) :
    riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal z) ≤
      riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput z) := by
  classical
  by_cases htop : riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput z) = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨γ, c, hc, hγ, hγ0, hγ1, hlen, hsegment⟩ :=
    exists_post_minimizing_curve Q E.outputMetric (E.oldOutput u) (E.oldOutput z) htop
  have hinside : MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) := by
    intro t ht
    by_contra hnot
    obtain ⟨b, x, hx, hxt⟩ := exceptional_mem_inner_window E S hOld hcanonical hnot
    have havoid := minimizing_curve_avoids_inner_window (S b) (hcanonical b) hε hD
      γ c hc hγ hlen hsegment
      (by simpa only [hγ0] using hu b) (by simpa only [hγ1] using hz b)
    exact havoid t ht ⟨x, hx, hxt⟩
  have hbound := terminal_distance_le_of_interior_curve E u z γ hγ hγ0 hγ1 hinside
  have htotal : riemannianCurveELength E.outputMetric γ 0 1 =
      riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput z) := by
    rw [hlen 0 1 zero_le_one, ← hsegment 0 1 le_rfl zero_le_one le_rfl, hγ0, hγ1]
  exact hbound.trans_eq htotal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
