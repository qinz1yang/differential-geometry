import DifferentialGeometry.Topology.Manifold.LinearRechart
import DifferentialGeometry.Topology.Manifold.TransportedCarrier
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Metric
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularityProof

/-!
# LFR49 noncompact branch, item (a): the soul carrier re-charted over the model of the sources

Frozen blueprint master207A, LFR49 (A:29096), noncompact branch: "apply LFR45–LFR47 … The zero
carrier now has metric order `K-5 ≥ 5`, its actual soul-flow and normal bundle are smooth, and all
distances and the supplied cone remain unchanged." LFR47's carrier
(`DifferentialGeometry.Topology.TransportedCarrier`) carries the charts of the total space `X`,
modelled on `EB × F`; the convergence statements (LFR48, T4) need the model `E` of the sources.

`CarrierRechart e Λ` is a one-field wrapper of the points of `N`, with the topology of `N`, whose
charts are those of `X` pushed along `e⁻¹` and followed by a linear equivalence
`Λ : EB × F ≃L E` (`DifferentialGeometry.Topology.linearRechart`). Named instances `*_LFR49A`:
topology, `T2`, connected, charted space over `E`, smooth manifold over `𝓘(ℝ, E)`, and for a
metric space `N` the SAME distance (isometric to `N` through the points), complete, proper.

* `CarrierRechart.diffeomorph e Λ : X ≃ₘ⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ CarrierRechart e Λ`, the
  SMOOTH carrier map, pointwise `e`;
* `CarrierRechart.identity Λ e`: for a `C^s` diffeomorphism `e`, the identity of the points is a
  `C^s` diffeomorphism onto `N`; `CarrierRechart.isometryEquiv`: it is an isometry;
* `CarrierRechart.ofTransported`: the smooth identification with LFR47's `TransportedCarrier e`;
* `CarrierRechart.metric Λ e G hmn hms`: the unchanged metric `G` of `N` read on the carrier
  (`finitePullbackMetric` along `identity`), `C^m` for `m ≤ n`, `m + 1 ≤ s`;
* `CarrierRechart.isRiemannianManifold`: with the transported metric as its Riemannian bundle, the
  carrier is a Riemannian manifold whenever `N` is (`riemannianEDist` is preserved by the `C¹`
  identity, which is norm-preserving on tangent vectors);
* `pushField`: the push-forward of a field along a smooth diffeomorphism, smooth, with the chain
  rules for maps and for real functions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology (TransportedCarrier linearRechart linearRechartDiffeomorph)

universe uX uN

variable {EB F E : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The points of `N`, with the smooth structure of `X` (model `EB × F`) transported along
`e : X ≃ₜ N` and re-read over the model `E` through the linear equivalence `Λ`. -/
structure CarrierRechart {X : Type uX} {N : Type uN} [TopologicalSpace X] [TopologicalSpace N]
    (e : X ≃ₜ N) (Λ : (EB × F) ≃L[ℝ] E) : Type uN where
  /-- The underlying point of `N`. -/
  point : N

namespace CarrierRechart

section Topology

variable {X : Type uX} {N : Type uN} [TopologicalSpace X] [TopologicalSpace N]
  (e : X ≃ₜ N) (Λ : (EB × F) ≃L[ℝ] E)

/-- The tautological bijection with the points of `N`. -/
def equivPoint : CarrierRechart e Λ ≃ N where
  toFun := point
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The topology of `N`. -/
instance instTopologicalSpace_LFR49A : TopologicalSpace (CarrierRechart e Λ) :=
  TopologicalSpace.induced point ‹TopologicalSpace N›

/-- The identity on points, a homeomorphism onto `N`. -/
def homeomorphPoint : CarrierRechart e Λ ≃ₜ N :=
  (equivPoint e Λ).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] theorem homeomorphPoint_apply (y : CarrierRechart e Λ) :
    homeomorphPoint e Λ y = y.point := rfl

@[simp] theorem homeomorphPoint_symm_apply (y : N) :
    (homeomorphPoint e Λ).symm y = ⟨y⟩ := rfl

/-- The identification with `X`: `y ↦ e⁻¹ y`. -/
def toSource : CarrierRechart e Λ ≃ₜ X :=
  (homeomorphPoint e Λ).trans e.symm

@[simp] theorem toSource_apply (y : CarrierRechart e Λ) : toSource e Λ y = e.symm y.point := rfl

@[simp] theorem toSource_symm_apply (x : X) : (toSource e Λ).symm x = ⟨e x⟩ := rfl

instance instT2Space_LFR49A [T2Space N] : T2Space (CarrierRechart e Λ) :=
  (homeomorphPoint e Λ).isEmbedding.t2Space

instance instConnectedSpace_LFR49A [ConnectedSpace N] : ConnectedSpace (CarrierRechart e Λ) :=
  (homeomorphPoint e Λ).symm.surjective.connectedSpace (homeomorphPoint e Λ).symm.continuous

end Topology

section Charts

variable {X : Type uX} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]

variable (X) in
/-- The charts of `X` (model `EB × F`) followed by `Λ` (model `E`). -/
@[reducible] def modelCharts (Λ : (EB × F) ≃L[ℝ] E) : ChartedSpace E X :=
  @linearRechart (EB × F) E _ _ _ _ X _ (inferInstanceAs (ChartedSpace (ModelProd EB F) X)) Λ

variable (Λ : (EB × F) ≃L[ℝ] E) [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]

/-- The re-charted `X` is a smooth manifold over `𝓘(ℝ, E)`. -/
theorem modelCharts_isManifold : @IsManifold ℝ _ E _ _ E _ 𝓘(ℝ, E) ∞ X _ (modelCharts X Λ) := by
  let _ : ChartedSpace (EB × F) X := inferInstanceAs (ChartedSpace (ModelProd EB F) X)
  have h : IsManifold 𝓘(ℝ, EB × F) ∞ X := by
    rw [modelWithCornersSelf_prod]
    exact ‹IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X›
  exact DifferentialGeometry.Topology.linearRechart_isManifold (M := X) Λ ∞

omit [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X] in
/-- The re-chart of `X` is smooth from the product model to `𝓘(ℝ, E)`. -/
theorem contMDiff_modelCharts :
    @ContMDiff ℝ _ (EB × F) _ _ (ModelProd EB F) _ (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) X _ _ E _ _ E _
      𝓘(ℝ, E) X _ (modelCharts X Λ) ∞ id := by
  let _ : ChartedSpace (EB × F) X := inferInstanceAs (ChartedSpace (ModelProd EB F) X)
  let _ : ChartedSpace E X := modelCharts X Λ
  have h : ContMDiff 𝓘(ℝ, EB × F) 𝓘(ℝ, E) ∞ (id : X → X) :=
    (@linearRechartDiffeomorph (EB × F) E _ _ _ _ X _ _ Λ ∞).contMDiff
  rw [modelWithCornersSelf_prod] at h
  exact h

omit [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X] in
/-- The re-chart of `X` is smooth from `𝓘(ℝ, E)` back to the product model. -/
theorem contMDiff_modelCharts_symm :
    @ContMDiff ℝ _ E _ _ E _ 𝓘(ℝ, E) X _ (modelCharts X Λ) (EB × F) _ _ (ModelProd EB F) _
      (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) X _ _ ∞ id := by
  let _ : ChartedSpace (EB × F) X := inferInstanceAs (ChartedSpace (ModelProd EB F) X)
  let _ : ChartedSpace E X := modelCharts X Λ
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EB × F) ∞ (id : X → X) :=
    (@linearRechartDiffeomorph (EB × F) E _ _ _ _ X _ _ Λ ∞).symm.contMDiff
  rw [modelWithCornersSelf_prod] at h
  exact h

end Charts

section Carrier

variable {X : Type uX} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]
  {N : Type uN} [TopologicalSpace N] (e : X ≃ₜ N) (Λ : (EB × F) ≃L[ℝ] E)

/-- The charts of `X` pushed along `e⁻¹`, followed by `Λ`. -/
instance instChartedSpace_LFR49A : ChartedSpace E (CarrierRechart e Λ) :=
  @DifferentialGeometry.Topology.Handle.chartedSpaceOfHomeomorph E _ X _ (CarrierRechart e Λ) _
    (toSource e Λ) (modelCharts X Λ)

variable [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]

instance instIsManifold_LFR49A : IsManifold 𝓘(ℝ, E) ∞ (CarrierRechart e Λ) :=
  @DifferentialGeometry.Topology.Handle.isManifoldOfHomeomorph ℝ _ E E _ _ _ 𝓘(ℝ, E) X _
    (modelCharts X Λ) ∞ (CarrierRechart e Λ) _ (toSource e Λ) (modelCharts_isManifold Λ)

/-- **The smooth carrier map** `X ≃ CarrierRechart e Λ`, pointwise `e`. -/
def diffeomorph : X ≃ₘ⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ CarrierRechart e Λ where
  toFun x := ⟨e x⟩
  invFun y := e.symm y.point
  left_inv x := e.symm_apply_apply x
  right_inv y := by
    change (⟨e (e.symm y.point)⟩ : CarrierRechart e Λ) = y
    rw [e.apply_symm_apply]
  contMDiff_toFun := by
    let _ : ChartedSpace E X := modelCharts X Λ
    have _ : IsManifold 𝓘(ℝ, E) ∞ X := modelCharts_isManifold Λ
    have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (toSource e Λ).symm :=
      DifferentialGeometry.Topology.Handle.contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (toSource e Λ) 𝓘(ℝ, E) ∞
    exact h.comp (contMDiff_modelCharts Λ)
  contMDiff_invFun := by
    let _ : ChartedSpace E X := modelCharts X Λ
    have _ : IsManifold 𝓘(ℝ, E) ∞ X := modelCharts_isManifold Λ
    have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (toSource e Λ) :=
      DifferentialGeometry.Topology.Handle.contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (toSource e Λ) 𝓘(ℝ, E) ∞
    exact (contMDiff_modelCharts_symm Λ).comp h

@[simp] theorem diffeomorph_apply (x : X) : diffeomorph e Λ x = ⟨e x⟩ := rfl

@[simp] theorem diffeomorph_symm_apply (y : CarrierRechart e Λ) :
    (diffeomorph e Λ).symm y = e.symm y.point := rfl

/-- **The smooth identification with LFR47's carrier** `TransportedCarrier e` (same points). -/
def ofTransported :
    TransportedCarrier e ≃ₘ⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ CarrierRechart e Λ where
  toFun y := ⟨y.point⟩
  invFun y := ⟨y.point⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine ((diffeomorph e Λ).contMDiff.comp
      (TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)) e).symm.contMDiff).congr
      fun y => ?_
    change (⟨y.point⟩ : CarrierRechart e Λ) = ⟨e (e.symm y.point)⟩
    rw [e.apply_symm_apply]
  contMDiff_invFun := by
    refine ((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)) e).contMDiff.comp
      (diffeomorph e Λ).symm.contMDiff).congr fun y => ?_
    change (⟨y.point⟩ : TransportedCarrier e) = ⟨e (e.symm y.point)⟩
    rw [e.apply_symm_apply]

@[simp] theorem ofTransported_apply (y : TransportedCarrier e) :
    ofTransported e Λ y = ⟨y.point⟩ := rfl

@[simp] theorem ofTransported_symm_apply (y : CarrierRechart e Λ) :
    (ofTransported e Λ).symm y = ⟨y.point⟩ := rfl

end Carrier

section Identity

variable {X : Type uX} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace E N] (Λ : (EB × F) ≃L[ℝ] E)
  [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X] {s : ℕ∞}

/-- **The identity of the points**, a `C^s` diffeomorphism onto `N` when `e` is `C^s`. -/
def identity (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) :
    CarrierRechart e.toHomeomorph Λ ≃ₘ^s⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N where
  toEquiv := equivPoint e.toHomeomorph Λ
  contMDiff_toFun := by
    refine (e.contMDiff.comp
      ((diffeomorph e.toHomeomorph Λ).symm.contMDiff.of_le (mod_cast le_top))).congr fun y => ?_
    change y.point = e (e.symm y.point)
    exact (e.apply_symm_apply y.point).symm
  contMDiff_invFun := by
    refine (((diffeomorph e.toHomeomorph Λ).contMDiff.of_le (mod_cast le_top)).comp
      e.symm.contMDiff).congr fun y => ?_
    change (⟨y⟩ : CarrierRechart e.toHomeomorph Λ) = ⟨e (e.symm y)⟩
    rw [e.apply_symm_apply]

@[simp] theorem identity_apply (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N)
    (y : CarrierRechart e.toHomeomorph Λ) : identity Λ e y = y.point := rfl

@[simp] theorem identity_symm_apply (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N)
    (y : N) : (identity Λ e).symm y = ⟨y⟩ := rfl

/-- The smooth carrier map followed by the identity of the points is `e`. -/
theorem identity_diffeomorph_apply (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) (x : X) :
    identity Λ e (diffeomorph e.toHomeomorph Λ x) = e x := rfl

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ N]

/-- **The unchanged metric `G` of `N` read on the re-charted carrier**: the pullback along the
`C^s` identity of the points, of class `C^m` for `m ≤ n`, `m + 1 ≤ s`. -/
def metric (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) {m n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) :
    ContMDiffRiemannianMetric 𝓘(ℝ, E) m E
      (TangentSpace 𝓘(ℝ, E) : CarrierRechart e.toHomeomorph Λ → Type _) :=
  finitePullbackMetric G (identity Λ e) hmn hms

/-- The inner products of the carrier metric are those of `G` through the identity. -/
@[simp] theorem metric_inner (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) {m n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) (y : CarrierRechart e.toHomeomorph Λ)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    (metric Λ e G hmn hms).inner y v w =
      G.inner y.point (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (identity Λ e) y v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (identity Λ e) y w) :=
  rfl

end Identity

section Distance

variable {X : Type uX} [TopologicalSpace X] {N : Type uN} [MetricSpace N] (e : X ≃ₜ N)
  (Λ : (EB × F) ≃L[ℝ] E)

/-- The distance of `N`: the re-chart does not touch distances. -/
instance instMetricSpace_LFR49A : MetricSpace (CarrierRechart e Λ) :=
  (MetricSpace.induced point (equivPoint e Λ).injective ‹MetricSpace N›).replaceTopology rfl

@[simp] theorem dist_eq (y z : CarrierRechart e Λ) : dist y z = dist y.point z.point := rfl

/-- The identity on points is an isometry onto `N`. -/
def isometryEquiv : CarrierRechart e Λ ≃ᵢ N where
  toEquiv := equivPoint e Λ
  isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl

@[simp] theorem isometryEquiv_apply (y : CarrierRechart e Λ) : isometryEquiv e Λ y = y.point :=
  rfl

@[simp] theorem isometryEquiv_symm_apply (y : N) : (isometryEquiv e Λ).symm y = ⟨y⟩ := rfl

instance instCompleteSpace_LFR49A [CompleteSpace N] : CompleteSpace (CarrierRechart e Λ) :=
  (isometryEquiv e Λ).completeSpace

instance instProperSpace_LFR49A [ProperSpace N] : ProperSpace (CarrierRechart e Λ) := by
  refine ⟨fun y r => ?_⟩
  have h : closedBall y r = isometryEquiv e Λ ⁻¹' closedBall y.point r :=
    ((isometryEquiv e Λ).preimage_closedBall y.point r).symm
  rw [h]
  exact (isometryEquiv e Λ).toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)

end Distance

section Riemannian

variable [FiniteDimensional ℝ E] {X : Type uX} [TopologicalSpace X]
  [ChartedSpace (ModelProd EB F) X] [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]
  {N : Type uN} [MetricSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  (Λ : (EB × F) ≃L[ℝ] E) {s : ℕ∞}

/-- The tangent norm of the carrier metric is its `√G'`. -/
theorem enorm_eq (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) {m n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) :
    letI : RiemannianBundle (fun y : CarrierRechart e.toHomeomorph Λ => TangentSpace 𝓘(ℝ, E) y) :=
      ⟨(metric Λ e G hmn hms).toRiemannianMetric⟩
    ∀ (y : CarrierRechart e.toHomeomorph Λ) (w : TangentSpace 𝓘(ℝ, E) y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((metric Λ e G hmn hms).inner y w w)) :=
  fun y w => DifferentialGeometry.Topology.Manifold.enorm_tangent_eq_sqrt_inner
    (metric Λ e G hmn hms) y w

/-- **The re-charted carrier is a Riemannian manifold** for the transported metric, whenever `N`
is one for `G`: the `C¹` identity of the points preserves tangent norms, hence Riemannian
distances, and it is an isometry of the given distances. -/
theorem isRiemannianManifold (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) {m n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : m ≤ n) (hms : m + 1 ≤ s)
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x)] [IsRiemannianManifold 𝓘(ℝ, E) N]
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w))) :
    letI : RiemannianBundle (fun y : CarrierRechart e.toHomeomorph Λ => TangentSpace 𝓘(ℝ, E) y) :=
      ⟨(metric Λ e G hmn hms).toRiemannianMetric⟩
    IsRiemannianManifold 𝓘(ℝ, E) (CarrierRechart e.toHomeomorph Λ) := by
  let _ : RiemannianBundle (fun y : CarrierRechart e.toHomeomorph Λ => TangentSpace 𝓘(ℝ, E) y) :=
    ⟨(metric Λ e G hmn hms).toRiemannianMetric⟩
  set κ := identity Λ e with hκdef
  have h1 : (1 : ℕ∞ω) ≤ (s : ℕ∞ω) := le_trans le_add_self hms
  have hκ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 κ := κ.contMDiff.of_le h1
  have hκ' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 κ.symm := κ.symm.contMDiff.of_le h1
  have hiso : ∀ (y : CarrierRechart e.toHomeomorph Λ) (v : TangentSpace 𝓘(ℝ, E) y),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ y v‖ₑ = ‖v‖ₑ := by
    intro y v
    rw [hGnorm, enorm_eq Λ e G hmn hms y v]
    rfl
  have hiso' : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E) x),
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ.symm x w‖ₑ = ‖w‖ₑ := by
    intro x w
    have hd := mfderiv_comp x ((hκ (κ.symm x)).mdifferentiableAt one_ne_zero)
      ((hκ' x).mdifferentiableAt one_ne_zero)
    have hid : (κ ∘ κ.symm) = id := funext κ.apply_symm_apply
    rw [hid, mfderiv_id] at hd
    have hw : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ (κ.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ.symm x w) = w :=
      (congrArg (fun T => T w) hd).symm
    calc ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ.symm x w‖ₑ
        = ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ (κ.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) κ.symm x w)‖ₑ :=
          (hiso _ _).symm
      _ = ‖w‖ₑ := by rw [hw]; rfl
  refine ⟨fun y z => ?_⟩
  have hle : Manifold.riemannianEDist 𝓘(ℝ, E) (κ y) (κ z) ≤ Manifold.riemannianEDist 𝓘(ℝ, E) y z :=
    DifferentialGeometry.Topology.Manifold.riemannianEDist_comp_le κ hκ hiso y z
  have hge : Manifold.riemannianEDist 𝓘(ℝ, E) (κ.symm (κ y)) (κ.symm (κ z)) ≤
      Manifold.riemannianEDist 𝓘(ℝ, E) (κ y) (κ z) :=
    DifferentialGeometry.Topology.Manifold.riemannianEDist_comp_le κ.symm hκ' hiso' (κ y) (κ z)
  rw [κ.symm_apply_apply, κ.symm_apply_apply] at hge
  have hN : edist (κ y) (κ z) = Manifold.riemannianEDist 𝓘(ℝ, E) (κ y) (κ z) :=
    IsRiemannianManifold.out (κ y) (κ z)
  have hed : edist y z = edist (κ y) (κ z) := by
    rw [edist_dist, edist_dist]
    rfl
  rw [hed, hN]
  exact le_antisymm hle hge

end Riemannian

end CarrierRechart

section PushField

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- The push-forward of a field `W` on `P` along a diffeomorphism `Ψ : P ≃ Q`. -/
def pushField {k : ℕ∞ω} (Ψ : P ≃ₘ^k⟮IP, IQ⟯ Q) (W : (z : P) → TangentSpace IP z) (y : Q) :
    TangentSpace IQ y :=
  mfderiv IP IQ Ψ (Ψ.symm y) (W (Ψ.symm y))

variable [IsManifold IP ∞ P] [IsManifold IQ ∞ Q]

/-- The push-forward of a smooth field along a smooth diffeomorphism is smooth. -/
theorem contMDiff_pushField (Ψ : P ≃ₘ⟮IP, IQ⟯ Q) {W : (z : P) → TangentSpace IP z}
    (hW : ContMDiff IP IP.tangent ∞ (fun z => (⟨z, W z⟩ : TangentBundle IP P))) :
    ContMDiff IQ IQ.tangent ∞ (fun y => (⟨y, pushField Ψ W y⟩ : TangentBundle IQ Q)) := by
  have h := ((Ψ.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hW).comp
    Ψ.symm.contMDiff
  refine h.congr fun y => ?_
  change (⟨y, pushField Ψ W y⟩ : TangentBundle IQ Q) = ⟨Ψ (Ψ.symm y), pushField Ψ W y⟩
  exact congrArg (fun b => (⟨b, pushField Ψ W y⟩ : TangentBundle IQ Q))
    (Ψ.apply_symm_apply y).symm

variable {ER : Type*} [NormedAddCommGroup ER] [NormedSpace ℝ ER]
  {HR : Type*} [TopologicalSpace HR] {IR : ModelWithCorners ℝ ER HR}
  {R : Type*} [TopologicalSpace R] [ChartedSpace HR R]

omit [IsManifold IP ∞ P] [IsManifold IQ ∞ Q] in
/-- **Chain rule for the push-forward**: `df (Ψ_* W) = d(f ∘ Ψ) W`. -/
theorem mfderiv_pushField {k : ℕ∞ω} (hk : k ≠ 0) (Ψ : P ≃ₘ^k⟮IP, IQ⟯ Q)
    (W : (z : P) → TangentSpace IP z) (f : Q → R) (z : P)
    (hf : MDifferentiableAt IQ IR f (Ψ z)) :
    mfderiv IQ IR f (Ψ z) (pushField Ψ W (Ψ z)) = mfderiv IP IR (f ∘ Ψ) z (W z) := by
  rw [mfderiv_comp z hf (Ψ.mdifferentiable hk z), ContinuousLinearMap.comp_apply]
  unfold pushField
  rw [Ψ.symm_apply_apply]

omit [IsManifold IP ∞ P] [IsManifold IQ ∞ Q] in
/-- **Chain rule for the push-forward, real functions**: `du (Ψ_* W) = d(u ∘ Ψ) W`. -/
theorem mvfderiv_pushField {k : ℕ∞ω} (hk : k ≠ 0) (Ψ : P ≃ₘ^k⟮IP, IQ⟯ Q)
    (W : (z : P) → TangentSpace IP z) (u : Q → ℝ) (z : P)
    (hu : MDifferentiableAt IQ 𝓘(ℝ, ℝ) u (Ψ z)) :
    mvfderiv IQ u (Ψ z) (pushField Ψ W (Ψ z)) = mvfderiv IP (u ∘ Ψ) z (W z) := by
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  rw [mfderiv_pushField hk Ψ W u z hu]
  rfl

end PushField

end DifferentialGeometry.Geometry.Collapse
