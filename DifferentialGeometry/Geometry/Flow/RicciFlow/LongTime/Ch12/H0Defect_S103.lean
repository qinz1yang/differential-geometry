import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WBNLevelAux_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Embed_S86
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakStrong_S85
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HopenOpen_S103
import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas
import DifferentialGeometry.Geometry.Hyperbolic.ModelAtlasBridge

set_option autoImplicit false

/-!
# CH12-S103 / G3: the defect half of `h0` (the vector defect at the start time `t`)

* `ricci_hyperbolic_S103` : `Ric(H.metric) = -(1/2) H.metric` (constant sectional curvature `-1/4`).
* `defect_of_ckErr_S103` : if the order `≤ 2` pull-back errors `ckErr_S45 H g' t⁻¹ f j x` are `< δ`
  (`δ ≤ 1/2`, `2882 δ ≤ η`), then `|2 t Ric_{g'}(V,V) + g'(V,V)| ≤ η g'(V,V)` for *every* `V` at `f x`.
  (`ckErr_S45` = `metricDerivNorm` of `(f|_U)^*(t⁻¹ g')` against `h_U`; `Ric(h_U) = -1/2 h_U`; the Ricci
  difference bound `abs_ricci_difference_bound_of_small_metric_derivatives`; Ricci naturality of the
  local isometry `f|_U`.)
* `h0_defect_S103` : the defect half of `h0 : WeakAt (η/2) t` at `actS t = j0` for a map `J : H.Carrier →
  stage j0`, from the order `≤ 2` closeness of `(K.stageMetric j0 t)` to `H` along `J` (the tracked point
  of `x` is `J x`).
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Topology.Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem ricci_hyperbolic_S103 (H : FiniteVolumeHyperbolicModel.{u}) (x : H.Carrier)
    (v w : TangentSpace (𝓡 3) x) :
    ricciTensor H.metric x v w = -(1 / 2) * H.metric.inner x v w := by
  have h := ricci_of_op (I := 𝓡 3) H.metric x (-(1 / 4 : ℝ))
    (fun X Y Z => GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature
      H.curvature.toGC x X Y Z) v w
  rw [h]
  simp only [finrank_euclideanSpace_fin]
  push_cast
  ring

/-- **G3a** (pointwise, all vectors).  Order `≤ 2` closeness `< δ` of `(f|_U)^*(t⁻¹ g')` to the hyperbolic
metric at `x ∈ U` gives the vector defect `|2 t Ric_{g'}(V,V) + g'(V,V)| ≤ η g'(V,V)` at `f x`, for every
`V` (`δ ≤ 1/2`, `2882 δ ≤ η`). -/
theorem defect_of_ckErr_S103 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) {t : ℝ} (ht : 0 < t) (f : H.Carrier → N)
    (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    {δ η : ℝ} (hδ : δ ≤ 1 / 2) (hδη : 2882 * δ ≤ η) {x : H.Carrier} (hx : x ∈ U)
    (hck : ∀ j : ℕ, j ≤ 2 → ckErr_S45 H g' t⁻¹ f j x < δ) (V : TangentSpace (𝓡 3) (f x)) :
    |2 * t * ricciTensor g' (f x) V V + g'.inner (f x) V V| ≤ η * g'.inner (f x) V V := by
  classical
  have htinv : 0 < t⁻¹ := inv_pos.2 ht
  let xU : U := ⟨x, hx⟩
  let m : SmoothRiemannianMetric (𝓡 3) N := scaleMetric t⁻¹ htinv g'
  let u : SmoothRiemannianMetric (𝓡 3) U := pullbackRestrict_S57 H m f U hF hinj
  let h : SmoothRiemannianMetric (𝓡 3) U := H.metric.restrictOpen U
  have hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k u h h xU ≤ δ := by
    intro k hk
    have e := ckErr_S45_eq_metricDerivNorm_S57 H g' t⁻¹ htinv f U hF hinj k xU
    have h1 : ckErr_S45 H g' t⁻¹ f k x < δ := hck k hk
    rw [← e]
    exact h1.le
  have hε0 : 0 ≤ δ := le_trans (Real.sqrt_nonneg _) (hsmall 0 (by norm_num))
  have hloc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun z : U => f z) :=
    isLocalDiffeomorph_of_injective_mfderiv (fun z : U => f z) (contMDiff_restrict_C4 f U hF)
      (immersion_restrict_inj_S57 H f U hF hinj) rfl
  obtain ⟨W, hW⟩ : ∃ W : TangentSpace (𝓡 3) xU,
      mfderiv (𝓡 3) (𝓡 3) f xU W = V := by
    let e := (hloc xU).mfderivToContinuousLinearEquiv (by simp)
    obtain ⟨W, hW⟩ := e.surjective V
    refine ⟨W, ?_⟩
    rw [← mfderiv_comp_val_C4 f U hF xU W]
    exact hW
  obtain ⟨hR, hI⟩ := ricci_pullbackRestrict_S98 H m f U hF hinj xU W
  rw [hW] at hR hI
  have hEh : ricciTensor h xU W W = -(1 / 2) * h.inner xU W W := by
    rw [DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen H.metric U xU W W, ricci_hyperbolic_S103 H xU _ _,
      SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
  have hnn : 0 ≤ h.inner xU W W := metric_inner_self_nonneg h xU W
  have hric := abs_ricci_difference_bound_of_small_metric_derivatives u h xU δ hδ hsmall W W
  have hmet := metricDifference_abs_le u h h xU W W
  have hs : Real.sqrt (h.inner xU W W) * Real.sqrt (h.inner xU W W) = h.inner xU W W :=
    Real.mul_self_sqrt hnn
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [hdim, mul_assoc, hs] at hric
  have hmet' : |u.inner xU W W - h.inner xU W W| ≤ δ * h.inner xU W W := by
    rw [mul_assoc, hs] at hmet
    exact hmet.trans (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) hnn)
  have hu_lo : (1 / 2) * h.inner xU W W ≤ u.inner xU W W := by
    have := (abs_le.mp hmet').1
    nlinarith
  have hkey : 2 * ricciTensor u xU W W + u.inner xU W W =
      2 * (ricciTensor u xU W W - ricciTensor h xU W W) + (u.inner xU W W - h.inner xU W W) := by
    rw [hEh]; ring
  have h1 : |2 * ricciTensor u xU W W + u.inner xU W W| ≤ 1441 * δ * h.inner xU W W := by
    rw [hkey]
    calc |2 * (ricciTensor u xU W W - ricciTensor h xU W W) + (u.inner xU W W - h.inner xU W W)|
        ≤ 2 * |ricciTensor u xU W W - ricciTensor h xU W W| +
          |u.inner xU W W - h.inner xU W W| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_two]
      _ ≤ 2 * (240 * 3 * δ * h.inner xU W W) + δ * h.inner xU W W := by gcongr
      _ = 1441 * δ * h.inner xU W W := by ring
  have hu_nn : 0 ≤ u.inner xU W W := by linarith
  have h2 : |2 * ricciTensor u xU W W + u.inner xU W W| ≤ η * u.inner xU W W := by
    refine h1.trans ?_
    nlinarith [mul_nonneg hε0 hnn, mul_nonneg (sub_nonneg.mpr hδη) hu_nn]
  -- back to `g'`
  have hRm : ricciTensor m (f x) V V = ricciTensor g' (f x) V V := ricciTensor_scaleMetric t⁻¹ htinv g' _ V V
  have hIm : m.inner (f x) V V = t⁻¹ * g'.inner (f x) V V := by
    simp only [m, scaleMetric_inner]
  rw [hR, hRm] at h2
  rw [hI, hIm] at h2
  have hg : 0 ≤ g'.inner (f x) V V := metric_inner_self_nonneg g' _ V
  have hrew : 2 * t * ricciTensor g' (f x) V V + g'.inner (f x) V V =
      t * (2 * ricciTensor g' (f x) V V + t⁻¹ * g'.inner (f x) V V) := by
    field_simp
  rw [hrew, abs_mul, abs_of_pos ht]
  calc t * |2 * ricciTensor g' (f x) V V + t⁻¹ * g'.inner (f x) V V|
      ≤ t * (η * (t⁻¹ * g'.inner (f x) V V)) := mul_le_mul_of_nonneg_left h2 ht.le
    _ = η * g'.inner (f x) V V := by field_simp

/-- **G3b** (K-level): the defect half of `h0 : WeakAt (η/2) t` for `J : H.Carrier → stage j0` an immersion
on `U ⊇ B` when `actS t = j0`: the tracked point of `J x` at time `t` is `J x` itself, and the order `≤ 2`
closeness of `K.stageMetric j0 t` to `H` along `J` (`ckErr_S45 … < δ`, `δ ≤ 1/2`, `2882 δ ≤ η`) gives the
vector defect `≤ η` (use `η/2` for `h0`). -/
theorem h0_defect_S103 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) {t : ℝ} (ht : 0 < t) (hact : actS_S70 K t = j0)
    (J : H.Carrier → (K.stage j0).Carrier) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => J x))
    (B : Set H.Carrier) (hBU : B ⊆ U) {δ η : ℝ} (hδ : δ ≤ 1 / 2) (hδη : 2882 * δ ≤ η)
    (hck : ∀ j : ℕ, j ≤ 2 → ∀ p ∈ B, ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J j p < δ) :
    DefectAllAt_S85 K j0 J B η t := by
  have hinj := injective_mfderiv_of_embedding_S86 J U hF hemb
  refine defectAll_of_stage_S103 K j0 J B hact ?_
  intro hle x hx z hz V
  have hself : TrackedAt_S70 K (le_refl j0) J x (J x) :=
    ⟨⟨J x, K.mem_backwardSurvivorDomain_self j0 (J x)⟩, rfl,
      K.backwardSurvivorMap_last j0 j0 le_rfl ⟨J x, K.mem_backwardSurvivorDomain_self j0 (J x)⟩⟩
  have hz' : z = J x := tracked_unique_S70 K hle J x hz hself
  subst hz'
  exact defect_of_ckErr_S103 H (K.stageMetric j0 t) ht J U hF hinj hδ hδη (hBU hx)
    (fun j hj => hck j hj x hx) V

end GC.LongTime.Ch12
