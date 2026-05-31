import RicciFlower.Coordinates.Normal.Frontier.SmoothEndpoint

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smooth geodesic normal-coordinate frontier

This file contains the future smooth normal-coordinate chart layer.  It is kept
out of the default `RicciFlower.Coordinates.Normal` umbrella because the smooth
exponential local-diffeomorphism theorem is not needed by the current C1
endpoint, injectivity-radius, and textbook-local-coordinate work.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open Set Function
open scoped Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-- Smooth local-diffeomorphism data for the exponential endpoint map.

This is the geometric/ODE frontier behind smooth normal coordinates: the
selected endpoint map must be a genuine smooth local diffeomorphism near
`0 : T_xM`, and it must realize the relation-valued endpoint API on its source.
The normal chart is the local inverse of `expLD`, not the construction chart
`extChartAt I x`. -/
structure NormalExpLocalDiffeomorphData
    (g : SmoothRiemannianMetric I M) (x : M) where
  expLD :
    PartialDiffeomorph
      (modelWithCornersSelf Real (TangentSpace I x)) I
      (TangentSpace I x) M (∞ : WithTop ℕ∞)
  zero_mem_source : (0 : TangentSpace I x) ∈ expLD.source
  map_zero : expLD 0 = x
  expAt_realizes :
    ∀ v : TangentSpace I x, v ∈ expLD.source -> expAt (I := I) g x v (expLD v)

namespace NormalExpLocalDiffeomorphData

/-- The smooth normal partial diffeomorphism `normalCoord ∘ Exp_x^{-1}`.

This is the smooth object underlying the normal chart.  Its inverse is the
exponential local diffeomorphism followed by `normalHCoord⁻¹`. -/
def normalPartialDiffeomorph [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    PartialDiffeomorph I I M H (∞ : WithTop ℕ∞) :=
  PartialDiffeomorph.transDiffeomorph (I := I) D.expLD.symm
    (normalHCoordDiffeomorph (I := I) x)

/-- The normal coordinate chart induced by a smooth local exponential
diffeomorphism.  Its inverse is `D.expLD`; its forward map sends a nearby point
to the normal coordinate of the unique tangent vector that exponentiates to it.
-/
def normalChart [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    OpenPartialHomeomorph M H :=
  (D.normalPartialDiffeomorph (I := I)).toOpenPartialHomeomorph

@[simp]
theorem normalPartialDiffeomorph_toOpenPartialHomeomorph [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    (D.normalPartialDiffeomorph (I := I)).toOpenPartialHomeomorph =
      D.expLD.symm.toOpenPartialHomeomorph.transHomeomorph
        (normalHCoordHomeomorph (I := I) x) := by
  simp [normalPartialDiffeomorph]

@[simp]
theorem normalChart_eq [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    D.normalChart (I := I) =
      D.expLD.symm.toOpenPartialHomeomorph.transHomeomorph
        (normalHCoordHomeomorph (I := I) x) := by
  simp [normalChart]

/-- Forget smooth local-diffeomorphism exponential data to the older
relation-valued endpoint package by shrinking the source to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : D.expLD.source ∈ 𝓝 (0 : TangentSpace I x) :=
    D.expLD.open_source.mem_nhds D.zero_mem_source
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ D.expLD.source :=
    (Classical.choose_spec hnhds).2
  let expHomeomorph := D.expLD.toOpenPartialHomeomorph
  refine {
    radius := r
    radius_pos := hr
    exp := D.expLD
    exp_zero := D.map_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (D.expLD v)).1 (D.expAt_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    exact expHomeomorph.injOn (hrsub hv) (hrsub hw) h_eq
  · exact expHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hrsub

end NormalExpLocalDiffeomorphData

/-- Smooth normal-coordinate chart data before registering the tangent-bundle
trivialization.

This is the correct smooth local-diffeomorphism layer: it records a genuine
normal chart in the maximal atlas and the endpoint/inverse formulas, but does
not yet claim that the chart has been converted to a `LocalChartAt`. -/
structure NormalChartCoreData
    (g : SmoothRiemannianMetric I M) (x : M) where
  domain : Set (TangentSpace I x)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : TangentSpace I x) ∈ domain
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  chart : OpenPartialHomeomorph M H
  mem_source : x ∈ chart.source
  mem_max : chart ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M
  exp_realizes :
    ∀ v : TangentSpace I x, v ∈ domain -> expAt (I := I) g x v (exp v)
  source_eq : exp '' domain = chart.source
  exp_open_image :
    ∀ s : Set (TangentSpace I x), IsOpen s -> s ⊆ domain -> IsOpen (exp '' s)
  ext_exp_eq :
    ∀ v : TangentSpace I x, v ∈ domain -> chart.extend I (exp v) = normalCoord (I := I) x v
  symm_normalCoord_eq :
    ∀ v : TangentSpace I x, v ∈ domain -> chart.symm (normalHCoord (I := I) x v) = exp v

namespace NormalChartCoreData

/-- Forget smooth normal-chart core data to the older relation-valued endpoint
package by shrinking the open tangent-domain to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalChartCoreData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : N.domain ∈ 𝓝 (0 : TangentSpace I x) :=
    N.domain_open.mem_nhds N.zero_mem_domain
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ N.domain :=
    (Classical.choose_spec hnhds).2
  refine {
    radius := r
    radius_pos := hr
    exp := N.exp
    exp_zero := N.exp_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (N.exp v)).1 (N.exp_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    apply normalCoord_injective (I := I) x
    calc
      normalCoord (I := I) x v = N.chart.extend I (N.exp v) := (N.ext_exp_eq v (hrsub hv)).symm
      _ = N.chart.extend I (N.exp w) := congrArg (fun y : M => N.chart.extend I y) h_eq
      _ = normalCoord (I := I) x w := N.ext_exp_eq w (hrsub hw)
  · exact N.exp_open_image (Metric.ball (0 : TangentSpace I x) r)
      Metric.isOpen_ball hrsub

end NormalChartCoreData

namespace NormalExpLocalDiffeomorphData

/-- A smooth local exponential diffeomorphism gives the smooth chart-core
package: the normal chart is the inverse exponential map followed by the
linear normal-coordinate homeomorphism. -/
def toNormalChartCoreData [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    NormalChartCoreData (I := I) g x := by
  classical
  let e : OpenPartialHomeomorph (TangentSpace I x) M :=
    D.expLD.toOpenPartialHomeomorph
  refine {
    domain := D.expLD.source
    domain_open := D.expLD.open_source
    zero_mem_domain := D.zero_mem_source
    exp := D.expLD
    exp_zero := D.map_zero
    chart := D.normalChart (I := I)
    mem_source := ?_
    mem_max := ?_
    exp_realizes := ?_
    source_eq := ?_
    exp_open_image := ?_
    ext_exp_eq := ?_
    symm_normalCoord_eq := ?_
  }
  · have hx_target : x ∈ D.expLD.target := by
      have h0 : D.expLD 0 ∈ D.expLD.target := by
        simpa [e] using
          (e.map_source (x := (0 : TangentSpace I x)) D.zero_mem_source)
      simpa [D.map_zero] using h0
    simpa [normalChart, e] using hx_target
  · exact PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas
      (I := I) (D.normalPartialDiffeomorph (I := I))
  · intro v hv
    exact (expAt_iff (I := I) g x v (D.expLD v)).1 (D.expAt_realizes v hv)
  · simpa [normalChart, e] using e.image_source_eq_target
  · intro s hs hsub
    exact e.isOpen_image_of_subset_source hs hsub
  · intro v hv
    have hv_target : D.expLD v ∈ D.expLD.target := by
      exact e.map_source hv
    have hsymm : D.expLD.symm (D.expLD v) = v := by
      simpa [e] using e.left_inv hv
    have hchart :
        D.normalChart (I := I) (D.expLD v) = normalHCoord (I := I) x v := by
      change normalHCoord (I := I) x (D.expLD.symm (D.expLD v)) =
        normalHCoord (I := I) x v
      rw [hsymm]
    calc
      (D.normalChart (I := I)).extend I (D.expLD v)
          = I (D.normalChart (I := I) (D.expLD v)) := rfl
      _ = I (normalHCoord (I := I) x v) := congrArg I hchart
      _ = normalCoord (I := I) x v := model_normalHCoord (I := I) x v
  · intro v hv
    have hv_target : D.expLD v ∈ D.expLD.target := by
      exact e.map_source hv
    have hnormal_target :
        normalHCoord (I := I) x v ∈ (D.normalChart (I := I)).target := by
      have hpre :
          (normalHCoordHomeomorph (I := I) x).symm
              (normalHCoord (I := I) x v) = v := by
        rw [← normalHCoordHomeomorph_apply (I := I) x v]
        exact (normalHCoordHomeomorph (I := I) x).left_inv v
      simpa [normalChart, e, hpre] using hv
    have hright :
        (D.normalChart (I := I)) ((D.normalChart (I := I)).symm
            (normalHCoord (I := I) x v)) =
          normalHCoord (I := I) x v := by
      exact (D.normalChart (I := I)).right_inv hnormal_target
    have hchart :
        D.normalChart (I := I) (D.expLD v) = normalHCoord (I := I) x v := by
      have hsymm : D.expLD.symm (D.expLD v) = v := by
        simpa [e] using e.left_inv hv
      change normalHCoord (I := I) x (D.expLD.symm (D.expLD v)) =
        normalHCoord (I := I) x v
      rw [hsymm]
    exact (D.normalChart (I := I)).injOn
      ((D.normalChart (I := I)).map_target hnormal_target)
      (by simpa [normalChart, e] using hv_target)
      (hright.trans hchart.symm)

end NormalExpLocalDiffeomorphData

/-- Transport a smooth fixed-chart endpoint local diffeomorphism through the
construction chart to a manifold-valued exponential local diffeomorphism. -/
private theorem expData_of_chartLD
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {R τ : Real}
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (hzero :
      manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
        (0 : TangentSpace I x) = x)
    (hreal : ∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
      expAt (I := I) g x v
        (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v))
    (hchart : ∀ v ∈ Metric.ball (0 : TangentSpace I x) R,
      extChartAt I x
        (manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) =
          chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v)
    (chartLD :
      PartialDiffeomorph
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (TangentSpace I x) (TangentSpace I x) (∞ : WithTop ℕ∞))
    (hzero_src : (0 : TangentSpace I x) ∈ chartLD.source)
    (hsrc_ball : chartLD.source ⊆ Metric.ball (0 : TangentSpace I x) R)
    (hchartLD : ∀ v : TangentSpace I x, v ∈ chartLD.source ->
      chartLD v = chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x v) :
    Nonempty (NormalExpLocalDiffeomorphData (I := I) g x) := by
  classical
  let exp : TangentSpace I x -> M :=
    manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  have hexp_mem_source :
      ∀ v : TangentSpace I x, v ∈ chartLD.source -> exp v ∈ (extChartAt I x).source := by
    intro v hv
    have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
      expAt_mem_source (I := I) (hreal v (hsrc_ball hv))
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source, exp] using hcoord
  have hchartLD_ext :
      ∀ v : TangentSpace I x, v ∈ chartLD.source ->
        chartLD v = extChartAt I x (exp v) := by
    intro v hv
    rw [hchartLD v hv]
    exact (hchart v (hsrc_ball hv)).symm
  let target : Set M :=
    (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' chartLD.target
  let inv : M -> TangentSpace I x :=
    fun y => chartLD.symm (extChartAt I x y)
  let expLD :
      PartialDiffeomorph
        (modelWithCornersSelf Real (TangentSpace I x)) I
        (TangentSpace I x) M (∞ : WithTop ℕ∞) := {
    toFun := exp
    invFun := inv
    source := chartLD.source
    target := target
    map_source' := by
      intro v hv
      refine ⟨hexp_mem_source v hv, ?_⟩
      change extChartAt I x (exp v) ∈ chartLD.target
      rw [← hchartLD_ext v hv]
      exact chartLD.map_source hv
    map_target' := by
      intro y hy
      exact chartLD.map_target hy.2
    left_inv' := by
      intro v hv
      change chartLD.symm (extChartAt I x (exp v)) = v
      rw [← hchartLD_ext v hv]
      exact chartLD.left_inv hv
    right_inv' := by
      intro y hy
      have hinv_src : inv y ∈ chartLD.source := chartLD.map_target hy.2
      apply (extChartAt I x).injOn (hexp_mem_source (inv y) hinv_src) hy.1
      have hright : chartLD (inv y) = extChartAt I x y := by
        exact chartLD.right_inv hy.2
      rw [← hchartLD_ext (inv y) hinv_src]
      exact hright
    open_source := chartLD.open_source
    open_target := by
      simpa [target] using
        isOpen_extChartAt_preimage' (I := I) (x := x) chartLD.open_target
    contMDiffOn_toFun := by
      let extTarget : Set (TangentSpace I x) := (extChartAt I x).target
      let symmT : TangentSpace I x -> M := fun w => (extChartAt I x).symm w
      let candidate : TangentSpace I x -> M :=
        fun v => symmT (chartLD v)
      have hchart_maps :
          ∀ v, v ∈ chartLD.source -> chartLD v ∈ extTarget := by
        intro v hv
        rw [hchartLD_ext v hv]
        exact (extChartAt I x).map_source (hexp_mem_source v hv)
      have hsymmT : ContMDiffOn
          (modelWithCornersSelf Real (TangentSpace I x)) I
          (∞ : WithTop ℕ∞) symmT extTarget := by
        change ContMDiffOn (modelWithCornersSelf Real E) I
          (∞ : WithTop ℕ∞) (extChartAt I x).symm (extChartAt I x).target
        exact contMDiffOn_extChartAt_symm (I := I) (x := x) (n := (∞ : WithTop ℕ∞))
      have hcand : ContMDiffOn
          (modelWithCornersSelf Real (TangentSpace I x)) I
          (∞ : WithTop ℕ∞) candidate chartLD.source := by
        exact hsymmT.comp chartLD.contMDiffOn_toFun hchart_maps
      exact hcand.congr (by
        intro v hv
        change exp v = (extChartAt I x).symm (chartLD v)
        rw [hchartLD_ext v hv]
        exact ((extChartAt I x).left_inv (hexp_mem_source v hv)).symm)
    contMDiffOn_invFun := by
      let extT : M -> TangentSpace I x := fun y => extChartAt I x y
      have hext : ContMDiffOn I
          (modelWithCornersSelf Real (TangentSpace I x))
          (∞ : WithTop ℕ∞) extT target := by
        change ContMDiffOn I (modelWithCornersSelf Real E)
          (∞ : WithTop ℕ∞) (extChartAt I x) target
        exact (contMDiffOn_extChartAt (I := I) (x := x) (n := (∞ : WithTop ℕ∞))).mono
          (by
            intro y hy
            simpa [extChartAt_source] using hy.1)
      have hmaps : ∀ y, y ∈ target -> extT y ∈ chartLD.target := by
        intro y hy
        exact hy.2
      exact chartLD.contMDiffOn_invFun.comp hext hmaps
  }
  refine ⟨{
    expLD := expLD
    zero_mem_source := ?_
    map_zero := ?_
    expAt_realizes := ?_
  }⟩
  · simpa [expLD] using hzero_src
  · simpa [expLD, exp] using hzero
  · intro v hv
    simpa [expLD, exp] using hreal v (hsrc_ball hv)

/-- The real smooth exponential-map frontier.

This now consumes the precise smooth endpoint frontier
`exists_varFlow_smooth_endpoint` and transports it through the construction
chart. -/
theorem expAt_localDiffeomorph
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalExpLocalDiffeomorphData (I := I) g x) := by
  obtain ⟨R, _hR, τ, _hτ, Ψ, hzero, hreal, hchart,
    _hmodelData, chartLD, hzero_src, hsrc_ball, hchartLD⟩ :=
    exists_varFlow_smooth_endpoint (I := I) g x
  exact expData_of_chartLD (I := I) g x Ψ hzero hreal hchart
    chartLD hzero_src hsrc_ball hchartLD

/-- Smooth normal-chart core data follows from the smooth local exponential
diffeomorphism frontier. -/
theorem expAt_smoothChartCore
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalChartCoreData (I := I) g x) := by
  obtain ⟨D⟩ := expAt_localDiffeomorph (I := I) g x
  exact ⟨D.toNormalChartCoreData (I := I)⟩

/-- Normal coordinates as an actual selected local chart.

The chart is part of the data, not reconstructed from the default `extChartAt`.
This is the package downstream normal-coordinate frames should consume.  The
older `NormalCoordinateData` is only the relation-valued compatibility view
obtained by forgetting this chart structure. -/
structure NormalChartData
    (g : SmoothRiemannianMetric I M) (x : M) where
  radius : Real
  radius_pos : 0 < radius
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  localChart : LocalChartAt (I := I) x
  exp_realizes :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        expAt (I := I) g x v (exp v)
  source_eq :
    exp '' Metric.ball (0 : TangentSpace I x) radius = localChart.source
  ext_exp_eq :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        localChart.ext (exp v) = normalCoord (I := I) x v
  symm_normalCoord_eq :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        localChart.chart.symm (normalHCoord (I := I) x v) = exp v

namespace NormalChartData

/-- Forget a genuine normal local chart to the older relation-valued endpoint
package. -/
def toNormalCoordinateData [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalChartData (I := I) g x) :
    NormalCoordinateData (I := I) g x where
  radius := N.radius
  radius_pos := N.radius_pos
  exp := N.exp
  exp_zero := N.exp_zero
  exp_realizes := by
    intro v hv
    exact (expAt_iff (I := I) g x v (N.exp v)).1 (N.exp_realizes v hv)
  source_inj := by
    intro v hv w hw h_eq
    apply normalCoord_injective (I := I) x
    calc
      normalCoord (I := I) x v = N.localChart.ext (N.exp v) := (N.ext_exp_eq v hv).symm
      _ = N.localChart.ext (N.exp w) := congrArg N.localChart.ext h_eq
      _ = normalCoord (I := I) x w := N.ext_exp_eq w hw
  target_open := by
    simpa [N.source_eq] using N.localChart.source_open

end NormalChartData

end Coordinates
end RicciFlower
