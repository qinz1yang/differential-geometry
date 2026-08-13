import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.NormalFrame
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

noncomputable def framedExpMap (g : SmoothRiemannianMetric I M) (p : M) :
    E -> M :=
  fun z => expMap (I := I) g p (normalFrame (I := I) g p z)

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] in
@[simp] theorem framedExpMap_apply (g : SmoothRiemannianMetric I M) (p : M)
    (z : E) :
    framedExpMap (I := I) g p z =
      expMap (I := I) g p (normalFrame (I := I) g p z) := by
  rfl

noncomputable def framedExpDiffeo (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 := by
  let Φ := expMapDiffeo (I := I) g p
  let L := normalFrame (I := I) g p
  exact
    { toPartialEquiv :=
        { toFun := fun z => Φ (L z)
          invFun := fun q => L.symm (Φ.symm q)
          source := L ⁻¹' Φ.source
          target := Φ.target
          map_source' := by
            intro z hz
            exact Φ.map_source hz
          map_target' := by
            intro q hq
            change L (L.symm (Φ.symm q)) ∈ Φ.source
            rw [L.apply_symm_apply]
            exact Φ.map_target hq
          left_inv' := by
            intro z hz
            calc
              L.symm (Φ.symm (Φ (L z))) = L.symm (L z) :=
                congrArg L.symm (Φ.left_inv hz)
              _ = z := L.symm_apply_apply z
          right_inv' := by
            intro q hq
            rw [L.apply_symm_apply]
            exact Φ.right_inv hq }
      open_source := Φ.open_source.preimage L.continuous
      open_target := Φ.open_target
      contMDiffOn_toFun :=
        Φ.contMDiffOn_toFun.comp
          L.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ hz => hz)
      contMDiffOn_invFun :=
        L.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
          Φ.contMDiffOn_invFun }

noncomputable def framedChartAt (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph I (modelWithCornersSelf Real E) M E 1 :=
  (framedExpDiffeo (I := I) g p).symm

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_source (g : SmoothRiemannianMetric I M) (p : M) :
    (framedExpDiffeo (I := I) g p).source =
      normalFrame (I := I) g p ⁻¹' (expMapDiffeo (I := I) g p).source := by
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_target (g : SmoothRiemannianMetric I M) (p : M) :
    (framedExpDiffeo (I := I) g p).target =
      (expMapDiffeo (I := I) g p).target := by
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_apply (g : SmoothRiemannianMetric I M) (p : M)
    (z : E) :
    framedExpDiffeo (I := I) g p z =
      expMapDiffeo (I := I) g p (normalFrame (I := I) g p z) := by
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] in
theorem framed_norm_lt_iff (g : SmoothRiemannianMetric I M) (p : M)
    (z : E) (r : Real) :
    Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) < r ↔
      z ∈ Metric.ball (0 : E) r := by
  rw [normalFrame_sqrt, Metric.mem_ball, dist_zero_right]

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedChart_apply (g : SmoothRiemannianMetric I M) (p : M)
    (q : M) :
    framedChartAt (I := I) g p q =
      (normalFrame (I := I) g p).symm (normalChartAt (I := I) g p q) := by
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem zero_mem_framedExp_source (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ (framedExpDiffeo (I := I) g p).source := by
  rw [framedExp_source]
  simpa using zero_mem_expMapDiffeo_source (I := I) g p

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_zero (g : SmoothRiemannianMetric I M) (p : M) :
    framedExpDiffeo (I := I) g p (0 : E) = p := by
  rw [framedExp_apply, map_zero]
  exact expMapDiffeo_zero (I := I) g p

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedChart_centre (g : SmoothRiemannianMetric I M) (p : M) :
    framedChartAt (I := I) g p p = (0 : E) := by
  rw [framedChart_apply, normalChartAt_centre]
  exact map_zero (normalFrame (I := I) g p).symm

noncomputable def framedTransition (g : SmoothRiemannianMetric I M) (p q : M) :
    E -> E :=
  fun z => framedChartAt (I := I) g q (framedExpDiffeo (I := I) g p z)

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedTrans_apply (g : SmoothRiemannianMetric I M) (p q : M)
    (z : E) :
    framedTransition (I := I) g p q z =
      framedChartAt (I := I) g q (framedExpDiffeo (I := I) g p z) := by
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem framedExp_eq_expMap (g : SmoothRiemannianMetric I M) (p : M)
    {z : E} (hz : z ∈ (framedExpDiffeo (I := I) g p).source) :
    framedExpDiffeo (I := I) g p z =
      framedExpMap (I := I) g p z := by
  rw [framedExpMap_apply, framedExp_apply]
  exact expMapDiffeo_apply_eq (I := I) g p (by
    simpa only [framedExp_source] using hz)

omit [NeZero (Module.finrank Real E)] in
theorem mfderiv_framedExp (g : SmoothRiemannianMetric I M) (p : M)
    {z : E} (hz : z ∈ (framedExpDiffeo (I := I) g p).source) :
    mfderiv (modelWithCornersSelf Real E) I
        (fun w : E => framedExpDiffeo (I := I) g p w) z =
      (mfderiv (modelWithCornersSelf Real E) I
        (fun u : E => expMapDiffeo (I := I) g p u)
        (normalFrame (I := I) g p z)).comp
          (normalFrame (I := I) g p).toContinuousLinearMap := by
  let Φ := expMapDiffeo (I := I) g p
  let L := normalFrame (I := I) g p
  let L0 : E →L[Real] E := L.toContinuousLinearMap
  have hzraw : L0 z ∈ Φ.source := by
    simpa only [L0, L, Φ, framedExp_source] using hz
  have hΦ : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun u : E => Φ u) (L0 z) :=
    Φ.mdifferentiableAt one_ne_zero hzraw
  have hL : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun w : E => L0 w) z :=
    L0.contMDiff.mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp (I := modelWithCornersSelf Real E)
    (I' := modelWithCornersSelf Real E) (I'' := I) z hΦ hL
  have hLderiv : mfderiv (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun w : E => L0 w) z = L0 := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  simpa only [Function.comp_apply, framedExp_apply, Φ, L0, L] using hchain

noncomputable def framedMetric (g : SmoothRiemannianMetric I M) (p : M) :
    E -> E →L[Real] E →L[Real] Real :=
  fun z =>
    let D : E →L[Real] TangentSpace I (framedExpDiffeo (I := I) g p z) :=
      mfderiv (modelWithCornersSelf Real E) I
        (fun w : E => framedExpDiffeo (I := I) g p w) z
    (ContinuousLinearMap.precomp Real D).comp
      ((g.inner (framedExpDiffeo (I := I) g p z)).comp D)

omit [NeZero (Module.finrank Real E)] in
theorem framedMetric_apply (g : SmoothRiemannianMetric I M) (p : M)
    (z v w : E) :
    framedMetric (I := I) g p z v w =
      g.inner (framedExpDiffeo (I := I) g p z)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun q : E => framedExpDiffeo (I := I) g p q) z v)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun q : E => framedExpDiffeo (I := I) g p q) z w) := by
  simp only [framedMetric, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedMetric_zero (g : SmoothRiemannianMetric I M) (p : M) :
    framedMetric (I := I) g p 0 =
      (innerSL Real : E →L[Real] E →L[Real] Real) := by
  ext v w
  rw [framedMetric_apply, framedExp_zero,
    mfderiv_framedExp (I := I) g p (zero_mem_framedExp_source (I := I) g p),
    map_zero]
  calc
    g.inner p
        (mfderiv (modelWithCornersSelf Real E) I
          (fun u : E => expMapDiffeo (I := I) g p u) 0
          (normalFrame (I := I) g p v))
        (mfderiv (modelWithCornersSelf Real E) I
          (fun u : E => expMapDiffeo (I := I) g p u) 0
          (normalFrame (I := I) g p w)) =
      g.inner p (normalFrame (I := I) g p v)
        (normalFrame (I := I) g p w) :=
      normalChartAt_metric_pullback_at_origin (I := I) g p
        (normalFrame (I := I) g p v) (normalFrame (I := I) g p w)
    _ = Inner.inner Real v w := normalFrame_inner (I := I) g p v w
    _ = (innerSL Real : E →L[Real] E →L[Real] Real) v w := rfl

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
