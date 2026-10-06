import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.Transported
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# IMS04 / O4a（S-A10-BOUNDARY, suffix `_BD`）：ball 上的 pulled-back 度量 `ĝ_t = t⁻¹ f_t^* g(t)`

`cores.map i t` 只在开集 `domain i t` 上光滑，`f_t^* g(t)` 不是模型 `H.Carrier` 上的整体度量。
`accuracy t < 1` 时（G1 的 `pullback_inner_pos_BD`）`D f_t` 在 `ball = riemannianBallOf h basepoint
(acc t)⁻¹` 上单射，维数相同 ⇒ `f_t|ball` 是 local diffeomorphism；于是在**开子流形** `↥ball` 上有
整体光滑度量

* `h_B := (cores.model i).metric.restrictOpen ball`（参考度量，模型 `h` 的限制）；
* `ĝ_t := scaleMetric t⁻¹ (localPullMetric (postMetric F.observation t) (f_t|ball) _)`
  （被估计度量，`ĝ_t.inner x v w = t⁻¹ · g(t)(D f v, D f w)`）。

`metric_error` 的 `localPullInner` 与这里的 `ĝ_t` 逐点一致（`pulledMetric_inner_BD`）。O-W-CURV 的曲率估计
（O2 模型 horocycle、O3 `metric_error` k=1 ⇒ 联络差）应针对 `↥ball` 上的 `(h_B, ĝ_t)` 陈述；
O4b（`BallNaturality.lean`）把它搬回 stage 上 `γ_t` 的 `κ_{g(t)}`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Hyperbolic TopologicalSpace Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- `metric_error` 所在的 ball，作为开集。 -/
def PersistentHyperbolicCores.ballOpen_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) : Opens (cores.model i).Carrier :=
  ⟨riemannianBallOf (cores.model i).metric (cores.model i).basepoint (cores.accuracy t)⁻¹,
    isOpen_riemannianBallOf _ _ _⟩

/-- `f_t` 限制到 ball。 -/
def PersistentHyperbolicCores.mapBall_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) :
    ↥(cores.ballOpen_BD i t) → (postStage F.observation t).Carrier :=
  fun x => cores.map i t ht x.1

/-- `f_t|ball` 光滑。 -/
theorem PersistentHyperbolicCores.contMDiff_mapBall_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (cores.mapBall_BD i t ht) :=
  (cores.smooth i t ht).comp_contMDiff contMDiff_subtype_val
    (fun x => cores.advertised_ball i t ht x.2)

/-- `D (f_t|ball)` 与 `D f_t` 在 ball 点处一致（`Subtype.val` 的导数是恒等）。 -/
theorem PersistentHyperbolicCores.mfderiv_mapBall_apply_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) (x : ↥(cores.ballOpen_BD i t))
    (y : TangentSpace (𝓡 3) x) :
    (mfderiv (𝓡 3) (𝓡 3) (cores.mapBall_BD i t ht) x) y =
      (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) x.1) y := by
  have hdf : MDifferentiableAt (𝓡 3) (𝓡 3) (cores.map i t ht) x.1 :=
    ((cores.smooth i t ht).mdifferentiableOn (by simp)).mdifferentiableAt
      ((cores.domain i t).isOpen.mem_nhds (cores.advertised_ball i t ht x.2))
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : ↥(cores.ballOpen_BD i t) →
      (cores.model i).Carrier) x := (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) x hdf hval
  change (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht ∘ Subtype.val) x) y = _
  rw [hcomp]
  exact congrArg _ (mfderiv_subtype_val_apply _ x y)

/-- `accuracy t < 1` 时 `f_t|ball` 是 local diffeomorphism（`D f_t` 在 ball 上单射 + 维数相同）。 -/
theorem PersistentHyperbolicCores.isLocalDiffeomorph_mapBall_BD
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ)
    (ht : cores.start ≤ t) (hacc : cores.accuracy t < 1) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (cores.mapBall_BD i t ht) := by
  refine Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (cores.contMDiff_mapBall_BD i t ht) (fun x => ?_) rfl
  intro v w hvw
  by_contra hne
  have hv0 : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos := cores.pullback_inner_pos_BD i t ht hacc x.2 (v - w) hv0
  have h0 : (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) x.1) (v - w) = 0 := by
    rw [← cores.mfderiv_mapBall_apply_BD i t ht x, map_sub, hvw, sub_self]
    rfl
  rw [h0] at hpos
  simp at hpos

/-- **被估计度量** `ĝ_t = t⁻¹ · (f_t|ball)^* g(t)`（`↥ball` 上的整体光滑度量）。 -/
def PersistentHyperbolicCores.pulledMetric_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) (hacc : cores.accuracy t < 1) :
    SmoothRiemannianMetric (𝓡 3) ↥(cores.ballOpen_BD i t) :=
  scaleMetric t⁻¹ (inv_pos.mpr (cores.start_pos.trans_le ht))
    (localPullMetric (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
      (cores.mapBall_BD i t ht) (cores.isLocalDiffeomorph_mapBall_BD i t ht hacc))

/-- `ĝ_t(v, w) = t⁻¹ · g(t)(D f_t v, D f_t w)`（即 `metric_error` 里的 `t⁻¹ • localPullInner`）。 -/
theorem PersistentHyperbolicCores.pulledMetric_inner_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) (hacc : cores.accuracy t < 1)
    (x : ↥(cores.ballOpen_BD i t)) (v w : TangentSpace (𝓡 3) x) :
    (cores.pulledMetric_BD i t ht hacc).inner x v w =
      t⁻¹ * (postMetric F.observation t).inner (cores.map i t ht x.1)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) x.1 v)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) x.1 w) := by
  change t⁻¹ * (localPullMetric (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
    (cores.mapBall_BD i t ht) (cores.isLocalDiffeomorph_mapBall_BD i t ht hacc)).inner x v w = _
  rw [localPullMetric_inner, cores.mfderiv_mapBall_apply_BD, cores.mfderiv_mapBall_apply_BD]
  rfl

/-- 参考度量：模型 `h` 限制到 ball。 -/
abbrev PersistentHyperbolicCores.refMetric_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) : SmoothRiemannianMetric (𝓡 3) ↥(cores.ballOpen_BD i t) :=
  (cores.model i).metric.restrictOpen (cores.ballOpen_BD i t)

/-- G1 搬到 `↥ball`：`(1 - acc) h_B(v,v) ≤ ĝ_t(v,v) ≤ (1 + acc) h_B(v,v)`。 -/
theorem PersistentHyperbolicCores.pulledMetric_comparison_BD (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) (hacc : cores.accuracy t < 1)
    (x : ↥(cores.ballOpen_BD i t)) (v : TangentSpace (𝓡 3) x) :
    (1 - cores.accuracy t) * (cores.refMetric_BD i t).inner x v v ≤
        (cores.pulledMetric_BD i t ht hacc).inner x v v ∧
      (cores.pulledMetric_BD i t ht hacc).inner x v v ≤
        (1 + cores.accuracy t) * (cores.refMetric_BD i t).inner x v v := by
  rw [cores.pulledMetric_inner_BD i t ht hacc x v v]
  exact cores.inner_comparison_of_metric_error_BD i t ht x.2 v

end GC.LongTime
