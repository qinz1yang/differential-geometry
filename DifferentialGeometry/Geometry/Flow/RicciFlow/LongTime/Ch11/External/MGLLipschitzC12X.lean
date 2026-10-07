import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianDistance
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# MGL 第 4 步：uniformization projection 的 2-Lipschitz 性（O-C12X-MGLA G2，后缀 `_C12X`）

对 `e : Q[Γ] ≃ₜ H.Carrier`、`e ∘ π[Γ]` local diffeomorphism 且度量拉回 = `4 ×` hyperboloid
度量（`hmetric`，逐字 = `Truncation/ProducerHG03.lean:50-56`）：

* `mglA_riemannianEDistOf_le_C12X`：`riemannianEDistOf H.metric (p x) (p y) ≤ ofReal (2 * dist x y)`，
  `p = e ∘ π[Γ]`，`dist` 为 `HUpper 3` 的 hyperboloid 距离。证明：经 `hUpperDiffeomorph 3` 转到
  hyperboloid，沿单位速度测地线 `geodesicLine`（`exists_geodesicLine_through`，长度 = `dist`），
  `p ∘ ψ⁻¹` 的速度恒为 `√4 = 2`，用 `riemannianEDistOf_le_of_curve_speed_bound`。
* `mglA_image_ball_subset_C12X`：`2ρ ≤ 1` ⇒
  `p '' Metric.ball x ρ ⊆ riemannianBallOf H.metric (p x) 1`。

`Γ` 上不需要离散 / free 假设（只用 `he` 的光滑性与 `hmetric`）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal

open DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)

namespace GC.LongTime.Ch11.External

universe u

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

/-- 链式法则（照抄 `LorentzModel/Cusps/Metric.lean` 的 private
`metric_inner_comp_hUpperDiffeomorph_symm`，取 `m + 1 = 3`）：`F ∘ ψ⁻¹` 拉回 `g` 为
`4 ×` hyperboloid 度量。 -/
private theorem mglA_inner_comp_symm {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : SmoothRiemannianMetric (𝓡 3) N) (F : HUpper 3 → N)
    (hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F)
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      g.inner (F p) (mfderiv (𝓡 3) (𝓡 3) F p v) (mfderiv (𝓡 3) (𝓡 3) F p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (x : Hyperboloid (EuclideanSpace ℝ (Fin 3))) (v w : TangentSpace (𝓡 3) x) :
    g.inner ((F ∘ (Hyperboloid.hUpperDiffeomorph 3).symm) x)
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ (Hyperboloid.hUpperDiffeomorph 3).symm) x v)
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ (Hyperboloid.hUpperDiffeomorph 3).symm) x w) =
      4 * Hyperboloid.riemannianMetric.inner x v w := by
  let J := Hyperboloid.hUpperDiffeomorph 3
  have hJ : (J : HUpper 3 → Hyperboloid (EuclideanSpace ℝ (Fin 3))) ∘ J.symm = id := by
    funext y
    exact J.apply_symm_apply y
  change g.inner ((F ∘ J.symm) x) (mfderiv _ _ (F ∘ J.symm) x v)
    (mfderiv _ _ (F ∘ J.symm) x w) = _
  rw [mfderiv_comp_apply x (hF.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (hF.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp))]
  change g.inner (F (J.symm x)) _ _ = _
  rw [hmetric]
  have he : 4 * Hyperboloid.riemannianMetric.inner ((J ∘ J.symm) x)
      (mfderiv (𝓡 3) (𝓡 3) (J ∘ J.symm) x v) (mfderiv (𝓡 3) (𝓡 3) (J ∘ J.symm) x w) =
      4 * Hyperboloid.riemannianMetric.inner x v w := by
    rw [hJ, mfderiv_id]
    rfl
  rw [mfderiv_comp_apply x (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp))] at he
  exact he

/-- **MGL 第 4 步**：`e ∘ π[Γ]` 对 `riemannianEDistOf H.metric` 是 2-Lipschitz
（`HUpper 3` 取 hyperboloid 距离）。 -/
theorem mglA_riemannianEDistOf_le_C12X (H : FiniteVolumeHyperbolicModel.{u})
    (Γ : Subgroup (PO 3 1)) (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
        4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (x y : HUpper 3) :
    riemannianEDistOf H.metric ((e ∘ π[Γ]) x) ((e ∘ π[Γ]) y) ≤
      ENNReal.ofReal (2 * dist x y) := by
  let F : HUpper 3 → H.Carrier := e ∘ π[Γ]
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := he.contMDiff
  let J := Hyperboloid.hUpperDiffeomorph 3
  let f : Hyperboloid (EuclideanSpace ℝ (Fin 3)) → H.Carrier := F ∘ J.symm
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := hF.comp J.symm.contMDiff
  have hfm := mglA_inner_comp_symm H.metric F hF hmetric
  have hfx : ∀ z : HUpper 3, f (J z) = F z := fun z => by
    change F (J.symm (J z)) = F z
    rw [J.symm_apply_apply]
  have hdist : dist (J x) (J y) = dist x y := (Hyperboloid.hUpperIsometryEquiv 3).dist_eq x y
  by_cases hxy : J x = J y
  · have hxy' : x = y := J.injective hxy
    subst hxy'
    change riemannianEDistOf H.metric (F x) (F x) ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  obtain ⟨v, hv, ho, hend⟩ := Hyperboloid.exists_geodesicLine_through hxy
  let c := Hyperboloid.geodesicLine (J x) v hv ho
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ c := Hyperboloid.contMDiff_geodesicLine (J x) v hv ho
  have hfc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ c) (Set.Icc 0 (dist (J x) (J y))) :=
    ((hf.comp hc).of_le (by decide)).contMDiffOn
  have hspeed : ∀ t ∈ Set.Ioo 0 (dist (J x) (J y)),
      Real.sqrt (H.metric.inner ((f ∘ c) t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ c) t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ c) t 1)) ≤ 2 := by
    intro t _
    rw [mfderiv_comp_apply t (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
    change Real.sqrt (H.metric.inner (f (c t)) _ _) ≤ 2
    rw [hfm]
    have h1 := Hyperboloid.geodesicLine_unit_speed (J x) v hv ho t
    change Hyperboloid.riemannianMetric.inner (c t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c t 1) = 1 at h1
    rw [h1, mul_one, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have key := Geometry.riemannianEDistOf_le_of_curve_speed_bound H.metric dist_nonneg hfc hspeed
  have h0 : (f ∘ c) 0 = F x := by
    change f (Hyperboloid.geodesicLine (J x) v hv ho 0) = F x
    rw [Hyperboloid.geodesicLine_zero, hfx]
  have h1 : (f ∘ c) (dist (J x) (J y)) = F y := by
    change f (Hyperboloid.geodesicLine (J x) v hv ho (dist (J x) (J y))) = F y
    rw [hend, hfx]
  rw [h0, h1, sub_zero, hdist, ← ENNReal.ofReal_mul (by norm_num)] at key
  exact key

/-- 推论：`2ρ ≤ 1` 时 `e ∘ π[Γ]` 把 hyperbolic 球 `B(x, ρ)` 映进 `H` 的 Riemannian 单位球。 -/
theorem mglA_image_ball_subset_C12X (H : FiniteVolumeHyperbolicModel.{u})
    (Γ : Subgroup (PO 3 1)) (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
        4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (x : HUpper 3) (ρ : ℝ) (hρ : 2 * ρ ≤ 1) :
    (e ∘ π[Γ]) '' Metric.ball x ρ ⊆ riemannianBallOf H.metric ((e ∘ π[Γ]) x) 1 := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : dist z x < ρ := hz
  have hlt : 2 * dist x z < 1 := by
    rw [dist_comm]
    linarith
  exact (mglA_riemannianEDistOf_le_C12X H Γ e he hmetric x z).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hlt)

end GC.LongTime.Ch11.External
