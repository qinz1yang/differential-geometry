import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.NormalKernel
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.Convexity
import DifferentialGeometry.Geometry.Connection.OpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

/-!
# IMS04 / O2（O-W-CURV, suffix `_CV`）：模型 horocycle 的加速度 `|D^h β'|_h = ½|β'|²_h`

`β s = τ.cuspMap j (γ s, halfZero)`，`γ` 为 `torusMetric`-geodesic。cusp 度量 `dr² + e^{-r} g_T` 中
`r = 0` 水平面是 horocycle 型的 level set（`K = -1/4`），测地曲率 `½`（不是 `0`）。

slice `halfZero` 恰在 `CuspHalfSpace` 的 boundary 上，cusp 侧的 naturality 要 `Boundaryless`，所以在
ambient `H.Carrier` 中算：
1. Gauss（`inner_acceleration_comp_mfderiv_eq_zero_CV`）：`ι = cuspMap(·, halfZero)` isometric ⇒
   `D β' ⟂ dι(T Torus)`；
2. 法向（`inner_gradFun_acceleration_eq_neg_hessFun_CV`）：`exists_actual_cusp_barrier` 的 two-sided
   collar 上 `ρ = e^{-height} - 1`，slice 上 `Hess ρ = ½ h`（`dheight(β') = 0`）、`|∇ρ| = 1`；
3. 维数（`inner_self_eq_sq_of_normal_CV`）：`2 + 1 = 3` ⇒ `|Dβ'|² = ⟨Dβ', ∇ρ⟩² = (½|β'|²)²`；
4. `restrictOpen` 搬运（`covDerivAlong_restrictOpen`）到 collar 邻域与任意开集 `O ⊇ slice`（如 `↥ball`）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Hyperbolic.CuspConvexity
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
/-- 度量在两个相等的基点处取值相同（切空间都是 `E`）。 -/
theorem inner_congr_point_CV (g : SmoothRiemannianMetric I M) {p q : M} (h : p = q) (v w : E) :
    g.inner p v w = g.inner q v w := by
  subst h
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- 开子集中曲线的速度 = ambient 速度（`Subtype.val` 的导数是恒等）。 -/
theorem mfderiv_subtype_val_comp_CV (O : TopologicalSpace.Opens M) {β : ℝ → O} {s : ℝ}
    (hβ : MDifferentiableAt 𝓘(ℝ, ℝ) I β s) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun r => (β r : M)) s 1 : E) = mfderiv 𝓘(ℝ, ℝ) I β s 1 := by
  have hval : MDifferentiableAt I I (Subtype.val : O → M) (β s) :=
    (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I) s hval hβ
  change (mfderiv 𝓘(ℝ, ℝ) I (Subtype.val ∘ β) s 1 : E) = _
  rw [hc, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]

/-- 开子集上的加速度 = ambient 加速度（作为 `E` 中向量）。 -/
theorem covDerivAlong_velocity_restrictOpen_CV [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (O : TopologicalSpace.Opens M) {β : ℝ → O} (hβ : ContMDiff 𝓘(ℝ, ℝ) I ∞ β) (t : ℝ) :
    (covDerivAlong (g.restrictOpen O) β (fun s => mfderiv 𝓘(ℝ, ℝ) I β s 1) t : E) =
      covDerivAlong g (fun s => (β s : M)) (fun s => mfderiv 𝓘(ℝ, ℝ) I (fun r => (β r : M)) s 1)
        t := by
  rw [covDerivAlong_restrictOpen g O β _ t (hβ t).continuousAt]
  exact covDerivAlong_congr_curve g _ _ (Filter.EventuallyEq.refl _ _)
    (Filter.Eventually.of_forall fun s =>
      (mfderiv_subtype_val_comp_CV O ((hβ s).mdifferentiableAt (by simp))).symm)

end Restrict

section Slice

variable {H : FiniteVolumeHyperbolicModel.{u}} (τ : HyperbolicTruncation H) (j : Fin τ.count)

/-- slice 嵌入 `ι x = cuspMap j (x, halfZero)` 光滑。 -/
theorem slice_contMDiff_CV :
    ContMDiff torusModel (𝓡 3) ∞ (fun x : Torus => τ.cuspMap j (x, halfZero)) :=
  (τ.cuspEmbedding j).contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

/-- `dι u = dψ (u, 0)`（`ψ = cuspMap j`）。 -/
theorem slice_mfderiv_apply_CV (x : Torus) (u : TangentSpace torusModel x) :
    mfderiv torusModel (𝓡 3) (fun x : Torus => τ.cuspMap j (x, halfZero)) x u =
      mfderiv halfCollarModel (𝓡 3) (τ.cuspMap j) (x, halfZero)
        ((u, 0) : TangentSpace halfCollarModel ((x, halfZero) : CuspHalfSpace)) := by
  have hψ : MDifferentiableAt halfCollarModel (𝓡 3) (τ.cuspMap j) (x, halfZero) :=
    ((τ.cuspEmbedding j).contMDiff _).mdifferentiableAt (by simp)
  have hφ : MDifferentiableAt torusModel halfCollarModel
      (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hc := mfderiv_comp (I := torusModel) (I' := halfCollarModel) (I'' := 𝓡 3) x hψ hφ
  have hprod : mfderiv torusModel halfCollarModel
      (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x =
      (mfderiv torusModel torusModel (@id Torus) x).prod
        (mfderiv torusModel (𝓡∂ 1) (fun _ : Torus => (halfZero : EuclideanHalfSpace 1)) x) :=
    mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const
  have h1 : (mfderiv torusModel halfCollarModel
      (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x u).1 = u := by
    have h : (mfderiv torusModel halfCollarModel
        (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x u).1 =
        mfderiv torusModel torusModel (@id Torus) x u := congrArg (fun L => (L u).1) hprod
    rw [h, mfderiv_id]
    rfl
  have h2 : (mfderiv torusModel halfCollarModel
      (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x u).2 = 0 := by
    have h : (mfderiv torusModel halfCollarModel
        (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x u).2 =
        mfderiv torusModel (𝓡∂ 1) (fun _ : Torus => (halfZero : EuclideanHalfSpace 1)) x u :=
      congrArg (fun L => (L u).2) hprod
    rw [h, mfderiv_const]
    rfl
  have hv : mfderiv torusModel halfCollarModel
      (fun x : Torus => ((x, halfZero) : CuspHalfSpace)) x u =
      ((u, 0) : TangentSpace halfCollarModel ((x, halfZero) : CuspHalfSpace)) :=
    Prod.ext h1 h2
  change mfderiv torusModel (𝓡 3) (τ.cuspMap j ∘ fun x : Torus => ((x, halfZero) : CuspHalfSpace))
    x u = _
  rw [hc, ContinuousLinearMap.comp_apply, hv]

/-- slice 嵌入是 isometric：`h(dι u, dι v) = g_T(u, v)`（`r = 0` 处 `e^{-r} = 1`）。 -/
theorem slice_inner_CV (x : Torus) (u v : TangentSpace torusModel x) :
    H.metric.inner (τ.cuspMap j (x, halfZero))
        (mfderiv torusModel (𝓡 3) (fun x : Torus => τ.cuspMap j (x, halfZero)) x u)
        (mfderiv torusModel (𝓡 3) (fun x : Torus => τ.cuspMap j (x, halfZero)) x v) =
      (τ.cusp j).torusMetric.inner x u v := by
  rw [slice_mfderiv_apply_CV, slice_mfderiv_apply_CV]
  refine (τ.cuspIsometry j _ _ _).trans (((τ.cusp j).metric_formula _ _ _).trans ?_)
  have hz : Real.exp (-(halfZero : EuclideanHalfSpace 1).val 0) = 1 := by
    have h0 : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl
    rw [h0, neg_zero, Real.exp_zero]
  simp [hz]

end Slice

section Collar

variable {H : FiniteVolumeHyperbolicModel.{u}} {τ : HyperbolicTruncation H} {j : Fin τ.count}
  (d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => τ.cuspMap j (s, halfZero)))

/-- collar 的零截面 `ι_d x = d (x, 0) : ↥d.neighborhood`。 -/
def collarSlice_CV (x : Torus) : d.neighborhood :=
  d.toDiffeomorph (x, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)

theorem collarSlice_val_CV (x : Torus) :
    (collarSlice_CV d x : H.Carrier) = τ.cuspMap j (x, halfZero) :=
  d.zero_eq x

theorem collarSlice_contMDiff_CV : ContMDiff torusModel (𝓡 3) ∞ (collarSlice_CV d) :=
  d.toDiffeomorph.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

theorem collarHeight_collarSlice_CV (x : Torus) :
    collarHeight H τ j d (collarSlice_CV d x) = 0 := by
  unfold collarHeight collarSlice_CV
  rw [Diffeomorph.symm_apply_apply]

theorem collarRho_collarSlice_CV (x : Torus) :
    collarRho H τ j d (collarSlice_CV d x) = 0 := by
  rw [collarRho, collarHeight_collarSlice_CV, neg_zero, Real.exp_zero, sub_self]

/-- `dι_d u = dι u`（作为 `E` 中向量）。 -/
theorem collarSlice_mfderiv_CV (x : Torus) (u : TangentSpace torusModel x) :
    (mfderiv torusModel (𝓡 3) (collarSlice_CV d) x u : EuclideanSpace ℝ (Fin 3)) =
      mfderiv torusModel (𝓡 3) (fun x : Torus => τ.cuspMap j (x, halfZero)) x u := by
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : d.neighborhood → H.Carrier)
      (collarSlice_CV d x) := (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt torusModel (𝓡 3) (collarSlice_CV d) x :=
    ((collarSlice_contMDiff_CV d) x).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (I := torusModel) (I' := 𝓡 3) (I'' := 𝓡 3) x hval hι
  have h1 : mfderiv torusModel (𝓡 3) (Subtype.val ∘ collarSlice_CV d) x u =
      mfderiv torusModel (𝓡 3) (collarSlice_CV d) x u := by
    rw [hc, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
  have he : (Subtype.val ∘ collarSlice_CV d) = fun x : Torus => τ.cuspMap j (x, halfZero) :=
    funext (collarSlice_val_CV d)
  rw [he] at h1
  exact h1.symm

/-- `ι_d` 对 `(torusMetric, H.metric|_{collar})` isometric。 -/
theorem collarSlice_inner_CV (x : Torus) (u v : TangentSpace torusModel x) :
    (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d x)
        (mfderiv torusModel (𝓡 3) (collarSlice_CV d) x u)
        (mfderiv torusModel (𝓡 3) (collarSlice_CV d) x v) =
      (τ.cusp j).torusMetric.inner x u v := by
  rw [SmoothRiemannianMetric.restrictOpen_inner, collarSlice_mfderiv_CV, collarSlice_mfderiv_CV]
  exact (inner_congr_point_CV H.metric (collarSlice_val_CV d x) _ _).trans
    (slice_inner_CV τ j x u v)

/-- 在 slice 上恒为常值的函数，沿 `dι_d` 的方向导数为 `0`。 -/
theorem mvfderiv_collarSlice_eq_zero_CV {f : d.neighborhood → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) (hconst : ∀ x, f (collarSlice_CV d x) = 0)
    (x : Torus) (u : TangentSpace torusModel x) :
    mvfderiv (𝓡 3) f (collarSlice_CV d x) (mfderiv torusModel (𝓡 3) (collarSlice_CV d) x u) =
      0 := by
  have hfd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (collarSlice_CV d x) :=
    (hf _).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt torusModel (𝓡 3) (collarSlice_CV d) x :=
    ((collarSlice_contMDiff_CV d) x).mdifferentiableAt (by simp)
  rw [← mvfderiv_comp_apply x hfd hι u]
  have he : f ∘ collarSlice_CV d = fun _ => (0 : ℝ) := funext hconst
  rw [he, mvfderiv_const]
  rfl

/-- `mfderiv` 版本：在 slice 上恒为 `0` 的实值函数，沿 `dι_d` 的导数为 `0`。 -/
theorem mfderiv_collarSlice_eq_zero_CV {f : d.neighborhood → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) (hconst : ∀ x, f (collarSlice_CV d x) = 0)
    (x : Torus) (u : TangentSpace torusModel x) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f (collarSlice_CV d x)
      (mfderiv torusModel (𝓡 3) (collarSlice_CV d) x u) = 0 := by
  have hfd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (collarSlice_CV d x) :=
    (hf _).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt torusModel (𝓡 3) (collarSlice_CV d) x :=
    ((collarSlice_contMDiff_CV d) x).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply x hfd hι u]
  have he : f ∘ collarSlice_CV d = fun _ => (0 : ℝ) := funext hconst
  rw [he, mfderiv_const]
  rfl

/-- **collar 上的 horocycle 加速度**：`β_d = ι_d ∘ γ`（`γ` 为 `torusMetric`-geodesic）在
`H.metric|_{collar}` 下 `|D β_d'|² = (½ |β_d'|²)²`。 -/
theorem collar_horocycle_acceleration_CV
    (heq : ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
      d.toFun p = τ.cuspMap j (p.1, halfPoint p.2.val hp))
    {γ : ℝ → Torus} (hγ : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ γ)
    (hgeo : IsGeodesic (τ.cusp j).torusMetric γ) (t : ℝ) :
    (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
        (covDerivAlong (H.metric.restrictOpen d.neighborhood) (fun s => collarSlice_CV d (γ s))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) s 1) t)
        (covDerivAlong (H.metric.restrictOpen d.neighborhood) (fun s => collarSlice_CV d (γ s))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) s 1) t) =
      (1 / 2 * (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1)) ^ 2 := by
  have hιs := collarSlice_contMDiff_CV d
  have hβ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun s => collarSlice_CV d (γ s)) := hιs.comp hγ
  have hρ := collarRho_smooth H τ j d
  have hvel : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1 =
      mfderiv torusModel (𝓡 3) (collarSlice_CV d) (γ t) (mfderiv 𝓘(ℝ, ℝ) torusModel γ t 1) := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (collarSlice_CV d ∘ γ) t 1 = _
    rw [mfderiv_comp t ((hιs _).mdifferentiableAt (by simp)) ((hγ t).mdifferentiableAt (by simp))]
    rfl
  have hGauss := inner_acceleration_comp_mfderiv_eq_zero_CV (τ.cusp j).torusMetric
    (H.metric.restrictOpen d.neighborhood) hιs (collarSlice_inner_CV d) hγ hgeo t
  have hq0 : collarHeight H τ j d (collarSlice_CV d (γ t)) = 0 :=
    collarHeight_collarSlice_CV d (γ t)
  obtain ⟨hHess, hgrad⟩ := actual_cusp_barrier_data H τ j d heq (collarSlice_CV d (γ t)) hq0.ge
  have hnL : ∀ w : TangentSpace torusModel (γ t),
      (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
        (gradFun (H.metric.restrictOpen d.neighborhood) (collarRho H τ j d)
          (collarSlice_CV d (γ t)))
        (mfderiv torusModel (𝓡 3) (collarSlice_CV d) (γ t) w) = 0 := by
    intro w
    rw [inner_gradFun]
    exact mfderiv_collarSlice_eq_zero_CV d hρ (collarRho_collarSlice_CV d) (γ t) w
  have hn : (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
      (gradFun (H.metric.restrictOpen d.neighborhood) (collarRho H τ j d)
        (collarSlice_CV d (γ t)))
      (gradFun (H.metric.restrictOpen d.neighborhood) (collarRho H τ j d)
        (collarSlice_CV d (γ t))) = 1 := by
    rw [hq0, mul_zero, Real.exp_zero] at hgrad
    exact hgrad
  have hN := inner_gradFun_acceleration_eq_neg_hessFun_CV (H.metric.restrictOpen d.neighborhood)
    hρ hβ (fun s => (collarRho_collarSlice_CV d (γ s)).trans
      (collarRho_collarSlice_CV d (γ 0)).symm) t
  have hdh : mvfderiv (𝓡 3) (collarHeight H τ j d) (collarSlice_CV d (γ t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1) = 0 := by
    rw [hvel]
    exact mvfderiv_collarSlice_eq_zero_CV d (collarHeight_smooth H τ j d)
      (collarHeight_collarSlice_CV d) (γ t) _
  have hH := hHess (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1)
  rw [hq0, neg_zero, Real.exp_zero, hdh, mul_zero, add_zero] at hH
  have hL : ∀ a : TangentSpace torusModel (γ t), a ≠ 0 →
      0 < (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
        (mfderiv torusModel (𝓡 3) (collarSlice_CV d) (γ t) a)
        (mfderiv torusModel (𝓡 3) (collarSlice_CV d) (γ t) a) := by
    intro a ha
    rw [collarSlice_inner_CV]
    exact (τ.cusp j).torusMetric.pos _ a ha
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (TangentSpace torusModel (γ t)) + 1 := by
    change _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) + 1
    simp [Module.finrank_prod]
  have hsq := inner_self_eq_sq_of_normal_CV (H.metric.restrictOpen d.neighborhood)
    (collarSlice_CV d (γ t)) (mfderiv torusModel (𝓡 3) (collarSlice_CV d) (γ t)).toLinearMap
    hL hdim _ _ hn hnL hGauss
  rw [hsq, (H.metric.restrictOpen d.neighborhood).symm, hN, hH]
  ring

end Collar

section Main

variable {H : FiniteVolumeHyperbolicModel.{u}} {τ : HyperbolicTruncation H} {j : Fin τ.count}

/-- **O2 主定理（`H.Carrier` 上）**：`β s = cuspMap j (γ s, halfZero)`，`γ` 为 `torusMetric`-geodesic，
则 `|D^h β'|_h = ½ |β'|²_h`（horocycle 的测地曲率 `½`）。 -/
theorem horocycle_acceleration_CV {γ : ℝ → Torus} (hγ : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ γ)
    (hgeo : IsGeodesic (τ.cusp j).torusMetric γ) (t : ℝ) :
    Real.sqrt (H.metric.inner (τ.cuspMap j (γ t, halfZero))
        (covDerivAlong H.metric (fun s => τ.cuspMap j (γ s, halfZero))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) s 1) t)
        (covDerivAlong H.metric (fun s => τ.cuspMap j (γ s, halfZero))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) s 1) t)) =
      1 / 2 * H.metric.inner (τ.cuspMap j (γ t, halfZero))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) t 1) := by
  obtain ⟨d, -, heq, -⟩ := exists_actual_cusp_barrier H τ j 1 one_pos
  have hβd : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun s => collarSlice_CV d (γ s)) :=
    (collarSlice_contMDiff_CV d).comp hγ
  have hcurve : (fun s => (collarSlice_CV d (γ s) : H.Carrier)) =
      fun s => τ.cuspMap j (γ s, halfZero) := funext fun s => collarSlice_val_CV d (γ s)
  have hD := covDerivAlong_velocity_restrictOpen_CV H.metric d.neighborhood hβd t
  rw [hcurve] at hD
  have hv := mfderiv_subtype_val_comp_CV d.neighborhood ((hβd t).mdifferentiableAt (by simp))
  rw [hcurve] at hv
  have hsq := collar_horocycle_acceleration_CV d heq hγ hgeo t
  have hpt := collarSlice_val_CV d (γ t)
  have e1 : H.metric.inner (τ.cuspMap j (γ t, halfZero))
      (covDerivAlong H.metric (fun s => τ.cuspMap j (γ s, halfZero))
        (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) s 1) t)
      (covDerivAlong H.metric (fun s => τ.cuspMap j (γ s, halfZero))
        (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) s 1) t) =
      (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
        (covDerivAlong (H.metric.restrictOpen d.neighborhood) (fun s => collarSlice_CV d (γ s))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) s 1) t)
        (covDerivAlong (H.metric.restrictOpen d.neighborhood) (fun s => collarSlice_CV d (γ s))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) s 1) t) := by
    rw [SmoothRiemannianMetric.restrictOpen_inner, hD]
    exact inner_congr_point_CV H.metric hpt.symm _ _
  have e2 : H.metric.inner (τ.cuspMap j (γ t, halfZero))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (γ s, halfZero)) t 1) =
      (H.metric.restrictOpen d.neighborhood).inner (collarSlice_CV d (γ t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => collarSlice_CV d (γ s)) t 1) := by
    rw [SmoothRiemannianMetric.restrictOpen_inner, ← hv]
    exact inner_congr_point_CV H.metric hpt.symm _ _
  rw [e1, e2, hsq, Real.sqrt_sq (mul_nonneg (by norm_num) (metric_inner_self_nonneg _ _ _))]

/-- **O2（任意开集 `O ⊇ slice` 上，如 `↥ball`）**：`β_O s = ⟨cuspMap j (γ s, halfZero), _⟩ : ↥O`，
`|D^{h|_O} β_O'| = ½ |β_O'|²`。BOUNDARY 的 (I2) 形状：`h_B = h.restrictOpen ball`。 -/
theorem horocycle_acceleration_restrictOpen_CV (O : TopologicalSpace.Opens H.Carrier)
    {γ : ℝ → Torus} (hγ : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ γ)
    (hgeo : IsGeodesic (τ.cusp j).torusMetric γ) (hO : ∀ s, τ.cuspMap j (γ s, halfZero) ∈ O)
    (t : ℝ) :
    Real.sqrt ((H.metric.restrictOpen O).inner (⟨τ.cuspMap j (γ t, halfZero), hO t⟩ : O)
        (covDerivAlong (H.metric.restrictOpen O)
          (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O)) s 1) t)
        (covDerivAlong (H.metric.restrictOpen O)
          (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O))
          (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O)) s 1) t)) =
      1 / 2 * (H.metric.restrictOpen O).inner (⟨τ.cuspMap j (γ t, halfZero), hO t⟩ : O)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O)) t 1) := by
  have hβ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun s => τ.cuspMap j (γ s, halfZero)) :=
    (slice_contMDiff_CV τ j).comp hγ
  have hβO : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun s => (⟨τ.cuspMap j (γ s, halfZero), hO s⟩ : O)) :=
    fun s => codRestr_contMDiffAt hO (hβ s)
  have hD := covDerivAlong_velocity_restrictOpen_CV H.metric O hβO t
  have hv := mfderiv_subtype_val_comp_CV O ((hβO t).mdifferentiableAt (by simp))
  rw [SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner, hD,
    ← hv]
  exact horocycle_acceleration_CV hγ hgeo t

end Main

end GC.LongTime
