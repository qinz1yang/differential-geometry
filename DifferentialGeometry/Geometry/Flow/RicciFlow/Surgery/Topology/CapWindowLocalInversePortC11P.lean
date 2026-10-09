import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowEllipticity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapAnnulusCoordinates
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Distance.Neighborhood
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Topology.Manifold.OpenFunctionExtension
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# S-CH11-FIX5 port of astra `CapWindowLocalInverse`（`PortC11P`）

来源：donor `CapWindowLocalInverse.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 5 处 elaboration error（`CapAnnulusCoordinates` 落地后才暴露）；本 port 只做
下面 5 处 elaboration 层面修补（no statement / definition / proof idea altered）：
* `inverse_norm_sq_le`：`heq` 的 `(F.open_target.mem_nhds hy).mono …` 改为
  `Filter.Eventually.mono (F.open_target.mem_nhds hy) …`（`mem_nhds` 的类型被 field notation 展开成
  `(𝓝 y).1 F.target`，`.mono` 找不到）；`rw [hder, F.right_inv' hy] at hb` 之前先
  `have hright : F (F.symm y) = y := F.right_inv' hy`（`rw` 的 pattern 是 `F.symm y`，不是
  `F.invFun y`）；末尾 `exact hb` 之前 `rw [norm_tangentSpace_vectorSpace]`（目标里的 `‖·‖` 是
  `TangentSpace` 上 Riemannian bundle 的范数，`hb` 里是 `ThreeSpace` 的 `PiLp` 范数，二者只差
  Mathlib 的这条引理）。
* `hF₀inv`：`⟨ContinuousLinearEquiv.ofBijective _ hb, rfl⟩` 改为
  `⟨(LinearEquiv.ofBijective (mfderiv … S.window ⟨x, _⟩).toLinearMap hb).toContinuousLinearEquiv,
  by ext; rfl⟩`（本树的 `ContinuousLinearEquiv.ofBijective` 取 `ker = ⊥` 与 `range = ⊤`，且在
  `TangentSpace` 上实例统一超 heartbeat；有限维情形用 `LinearEquiv.ofBijective`，与树内
  `AmbientHypersurfaceOrientation` 同写法）。
* `hlower` 里 `hfinal`：`nlinarith [hscaled, hlarger]` 改为 `rw [mul_assoc]; exact
  hscaled.trans hlarger`（`linarith` 对含 `mfderiv%` 的原子匹配失败；两条已有的不等式正好首尾相接）。
* `hUclosed`：`fun _ hy => hy.le` 改为 `fun y hy => (show riemannianEDistOf … y < … from hy).le`。
原路径 `CapWindowLocalInverse` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Filter Manifold Function
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The pointwise inverse calculation keeps the actual output universe independent
of the Euclidean source universe. -/
private theorem inverse_norm_sq_le {Q : OrientedThreeStage.{u}}
    (g : Q.Metric) (F : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace Q.Carrier
      (∞ : WithTop ℕ∞)) (L : ℝ)
    (hlower : ∀ x ∈ F.source, ∀ v : ThreeSpace,
      ‖v‖ ^ 2 ≤ L ^ 2 * g.inner (F x)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → Q.Carrier) x v)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → Q.Carrier) x v))
    (y : Q.Carrier) (hy : y ∈ F.target) (v : TangentSpace ThreeModel y) :
    ‖mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → ThreeSpace) y v‖ ^ 2 ≤
      L ^ 2 * g.inner y v v := by
  have hF := F.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) (F.map_target' hy)
  have hInv := F.symm.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy
  have heq : (F : ThreeSpace → Q.Carrier) ∘ (F.symm : Q.Carrier → ThreeSpace) =ᶠ[𝓝 y] id :=
    Filter.Eventually.mono (F.open_target.mem_nhds hy) fun _ hz => F.right_inv' hz
  have hder : mfderiv ThreeModel ThreeModel (F : ThreeSpace → Q.Carrier) (F.symm y)
      (mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → ThreeSpace) y v) = v := by
    have hcomp := mfderiv_comp_apply y hF hInv v
    have hmaps := heq.mfderiv_eq (I := ThreeModel) (I' := ThreeModel)
    have hid := DFunLike.congr_fun hmaps v
    rw [mfderiv_id] at hid
    exact hcomp.symm.trans hid
  have hb := hlower (F.symm y) (F.map_target' hy)
    (mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → ThreeSpace) y v)
  have hright : (F : ThreeSpace → Q.Carrier) (F.symm y) = y := F.right_inv' hy
  rw [hder, hright] at hb
  rw [norm_tangentSpace_vectorSpace]
  exact hb

private theorem edistOf_euclidean_eq (x y : ThreeSpace) :
    riemannianEDistOf (I := ThreeModel) (DifferentialGeometry.euclideanMetric (E := ThreeSpace)) x y =
      edist x y := by
  exact (IsRiemannianManifold.out (I := ThreeModel) x y).symm

/-- A uniform inverse-coordinate constant for the SAME actual canonical window.
The center may lie anywhere in the closed cap. The positive coordinate buffer
may shrink independently; the same constant precedes all these choices. -/
theorem exists_uniform_local_window_inverse_on_closed_core :
    ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m ε b),
        S.hasCanonicalWindow → ε ≤ 1 / 2 → standardCapL + 1 ≤ D →
        ∀ x₀ : standardCapWindow D, ‖x₀.val‖ ≤ standardCapL →
        ∀ r : ℝ, 0 < r → r ≤ capSeamWidth →
        ∃ (U : TopologicalSpace.Opens Q.Carrier) (χ : Q.Carrier → ThreeSpace),
          S.window x₀ ∈ U ∧
          (∀ y ∈ U, ∃ x : standardCapWindow D,
            x.val = χ y ∧ S.window x = y ∧
              x.val ∈ Metric.ball x₀.val r) ∧
          (∀ x : standardCapWindow D, S.window x ∈ U → χ (S.window x) = x.val) ∧
          ∀ y ∈ U, ∀ z ∈ U,
            edist (χ y) (χ z) ≤ ENNReal.ofReal (Λ * Real.sqrt S.neck.scale) *
              riemannianEDistOf E.outputMetric y z := by
  obtain ⟨Λ, hΛ, hmetric⟩ := exists_uniform_presented_window_ellipticity.{u} (standardCapL + 1 / 2)
  refine ⟨Λ, hΛ, ?_⟩
  intro P Q a s E fixed D ε m b S hcanonical hε hD x₀ hx₀ r hr hrwidth
  classical
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  let V : Set ThreeSpace := Metric.ball x₀.val r
  have hx₀V : x₀.val ∈ V := Metric.mem_ball_self hr
  have hVwindow : V ⊆ (standardCapWindow D : Set ThreeSpace) := by
    intro x hx
    have hxnorm : ‖x‖ < standardCapL + capSeamWidth := by
      have hd := Metric.mem_ball.mp hx
      have hn := norm_le_norm_add_norm_sub' x x₀.val
      rw [← dist_eq_norm] at hn
      linarith
    change ‖x‖ < D + 1
    have ha := capSeamWidth_le_one
    linarith
  have hVR : ∀ x ∈ V, ‖x‖ ≤ standardCapL + 1 / 2 := by
    intro x hx
    have hd := Metric.mem_ball.mp hx
    have hn := norm_le_norm_add_norm_sub' x x₀.val
    rw [← dist_eq_norm] at hn
    have ha := capSeamWidth_le_one
    linarith
  let F₀ : ThreeSpace → Q.Carrier := Function.extend
    (Subtype.val : standardCapWindow D → ThreeSpace) S.window (fun _ => S.window x₀)
  have hF₀ (x : standardCapWindow D) : F₀ x.val = S.window x :=
    Subtype.val_injective.extend_apply _ _ x
  have hF₀restrict : (fun x : standardCapWindow D => F₀ x.val) = S.window := funext hF₀
  have hF₀der (x : standardCapWindow D) :
      mfderiv ThreeModel ThreeModel F₀ x.val =
        mfderiv ThreeModel ThreeModel S.window x := by
    have h := mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel)
      F₀ (standardCapWindow D) x
    rw [hF₀restrict] at h
    exact h.symm
  have hF₀smooth : ContMDiffOn ThreeModel ThreeModel ∞ F₀ V := by
    have h := contMDiffOn_extend_from_open (standardCapWindow D) S.window
      (fun _ => S.window x₀) isOpen_univ S.window_smooth.contMDiff.contMDiffOn
    apply h.mono
    intro x hx
    exact ⟨⟨x, hVwindow hx⟩, mem_univ _, rfl⟩
  have hF₀inv : ∀ x ∈ V, (mfderiv ThreeModel ThreeModel F₀ x).IsInvertible := by
    intro x hx
    rw [hF₀der ⟨x, hVwindow hx⟩]
    have hb := bijective_mfderiv_of_isImmersionAt ThreeModel ThreeModel S.window
      ⟨x, hVwindow hx⟩ (S.window_smooth.isImmersion.isImmersionAt _) rfl
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv ThreeModel ThreeModel S.window ⟨x, hVwindow hx⟩).toLinearMap hb
      ).toContinuousLinearEquiv, by ext; rfl⟩
  have hF₀local := hF₀smooth.isLocalDiffeomorphOn_of_isInvertible_mfderiv
    Metric.isOpen_ball (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)) hF₀inv
  have hF₀inj : InjOn F₀ V := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (S.window_smooth.isEmbedding.injective
      ((hF₀ ⟨x, hVwindow hx⟩).symm.trans (hxy.trans (hF₀ ⟨y, hVwindow hy⟩))))
  obtain ⟨F, hsource, _, hfun⟩ :=
    hF₀local.exists_partialDiffeomorph_of_injOn Metric.isOpen_ball ⟨x₀.val, hx₀V⟩ hF₀inj
  have hFfun : (F : ThreeSpace → Q.Carrier) = F₀ := hfun
  have hx₀source : x₀.val ∈ F.source := hsource.symm ▸ hx₀V
  have hFcenter : F x₀.val = S.window x₀ := by rw [hFfun]; exact hF₀ x₀
  let L : ℝ := Λ * Real.sqrt S.neck.scale
  have hL : 0 < L := mul_pos hΛpos (Real.sqrt_pos.mpr S.neck.scale_pos)
  have hlower : ∀ x ∈ F.source, ∀ v : ThreeSpace,
      ‖v‖ ^ 2 ≤ L ^ 2 * E.outputMetric.inner (F x)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → Q.Carrier) x v)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → Q.Carrier) x v) := by
    intro x hx v
    have hxV : x ∈ V := hsource ▸ hx
    let xw : standardCapWindow D := ⟨x, hVwindow hxV⟩
    have hb := (hmetric S hcanonical hε (by linarith) xw (hVR x hxV) v).1
    have hgi := metric_inner_self_nonneg E.outputMetric (S.window xw)
      (mfderiv ThreeModel ThreeModel S.window xw v)
    have hscaled := mul_le_mul_of_nonneg_left hb hΛpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hΛpos.ne', one_mul] at hscaled
    have hΛsq : Λ ≤ Λ ^ 2 := by nlinarith
    have hlarger := mul_le_mul_of_nonneg_right hΛsq
      (mul_nonneg S.neck.scale_pos.le hgi)
    have hfinal : ‖v‖ ^ 2 ≤ L ^ 2 * E.outputMetric.inner (S.window xw)
        (mfderiv ThreeModel ThreeModel S.window xw v)
        (mfderiv ThreeModel ThreeModel S.window xw v) := by
      dsimp only [L]
      rw [mul_pow, Real.sq_sqrt S.neck.scale_pos.le]
      rw [mul_assoc]
      exact hscaled.trans hlarger
    rw [hFfun, hF₀der xw, hF₀ xw]
    exact hfinal
  obtain ⟨ρ, hρ, hball⟩ := exists_riemannianBallOf_subset_of_mem_nhds E.outputMetric
    (F x₀.val) (F.open_target.mem_nhds (F.map_source' hx₀source))
  have hclosed : riemannianClosedBallOf E.outputMetric (F x₀.val) (ρ / 2) ⊆ F.target := by
    intro y hy
    apply hball
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith))
  have hupper : ∀ y ∈ riemannianClosedBallOf E.outputMetric (F x₀.val) (ρ / 2),
      ∀ v : TangentSpace ThreeModel y,
      (DifferentialGeometry.euclideanMetric (E := ThreeSpace)).inner (F.symm y)
        (mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → ThreeSpace) y v)
        (mfderiv ThreeModel ThreeModel (F.symm : Q.Carrier → ThreeSpace) y v) ≤
          L ^ 2 * E.outputMetric.inner y v v := by
    intro y hy v
    simpa only [DifferentialGeometry.euclideanMetric_inner, real_inner_self_eq_norm_sq] using
      inverse_norm_sq_le E.outputMetric F L hlower y (hclosed hy) v
  let Uset := riemannianBallOf E.outputMetric (F x₀.val) (ρ / 8)
  have hUopen : IsOpen Uset := by
    let : RiemannianBundle (TangentSpace ThreeModel : Q.Carrier → Type _) :=
      ⟨E.outputMetric.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle ThreeSpace (TangentSpace ThreeModel : Q.Carrier → Type _) :=
      ⟨E.outputMetric.inner, E.outputMetric.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : PseudoEMetricSpace Q.Carrier := .ofRiemannianMetric ThreeModel Q.Carrier
    change IsOpen {y : Q.Carrier | edist (F x₀.val) y < ENNReal.ofReal (ρ / 8)}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let U : TopologicalSpace.Opens Q.Carrier := ⟨Uset, hUopen⟩
  have hUclosed : (U : Set Q.Carrier) ⊆
      riemannianClosedBallOf E.outputMetric (F x₀.val) (ρ / 8) :=
    fun y hy =>
      (show riemannianEDistOf E.outputMetric (F x₀.val) y < ENNReal.ofReal (ρ / 8) from hy).le
  have hUtarget : (U : Set Q.Carrier) ⊆ F.target := by
    intro y hy
    exact hclosed ((hUclosed hy).trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hrepr (y : Q.Carrier) (hy : y ∈ U) : ∃ x : standardCapWindow D,
      x.val = F.symm y ∧ S.window x = y ∧ x.val ∈ Metric.ball x₀.val r := by
    have hxV : F.symm y ∈ V := hsource ▸ F.map_target' (hUtarget hy)
    refine ⟨⟨F.symm y, hVwindow hxV⟩, rfl, ?_, hxV⟩
    rw [← hF₀ ⟨F.symm y, hVwindow hxV⟩, ← hFfun]
    exact F.right_inv' (hUtarget hy)
  refine ⟨U, F.symm, ?_, hrepr, ?_, ?_⟩
  · change riemannianEDistOf E.outputMetric (F x₀.val) (S.window x₀) < ENNReal.ofReal (ρ / 8)
    rw [hFcenter, riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · intro x hx
    obtain ⟨z, hz, hzw, _⟩ := hrepr (S.window x) hx
    exact hz.symm.trans (congrArg Subtype.val (S.window_smooth.isEmbedding.injective hzw))
  · intro y hy z hz
    have h := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      E.outputMetric (DifferentialGeometry.euclideanMetric (E := ThreeSpace)) F.symm
      (F x₀.val) y z (by linarith : 0 ≤ ρ / 8) (by linarith : 3 * (ρ / 8) < ρ / 2)
      hL hclosed hupper (hUclosed hy) (hUclosed hz)
    rw [edistOf_euclidean_eq] at h
    exact h

/-- The original seam-centered API is a projection of the same closed-cap
inverse producer at the full fixed coordinate buffer. -/
theorem exists_uniform_local_window_inverse :
    ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m ε b),
        S.hasCanonicalWindow → ε ≤ 1 / 2 → standardCapL + 1 ≤ D →
        ∀ x₀ : standardCapWindow D, ‖x₀.val‖ = standardCapL →
        ∃ (U : TopologicalSpace.Opens Q.Carrier) (χ : Q.Carrier → ThreeSpace),
          S.window x₀ ∈ U ∧
          (∀ y ∈ U, ∃ x : standardCapWindow D,
            x.val = χ y ∧ S.window x = y ∧
              x.val ∈ Metric.ball x₀.val capSeamWidth) ∧
          (∀ x : standardCapWindow D, S.window x ∈ U → χ (S.window x) = x.val) ∧
          ∀ y ∈ U, ∀ z ∈ U,
            edist (χ y) (χ z) ≤ ENNReal.ofReal (Λ * Real.sqrt S.neck.scale) *
              riemannianEDistOf E.outputMetric y z := by
  obtain ⟨Λ, hΛ, hinverse⟩ := exists_uniform_local_window_inverse_on_closed_core.{u}
  refine ⟨Λ, hΛ, ?_⟩
  intro P Q a s E fixed D ε m b S hcanonical hε hD x₀ hx₀
  exact hinverse S hcanonical hε hD x₀ hx₀.le
    capSeamWidth capSeamWidth_pos le_rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
