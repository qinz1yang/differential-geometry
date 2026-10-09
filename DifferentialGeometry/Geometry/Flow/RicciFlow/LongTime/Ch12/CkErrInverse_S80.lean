import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompBridge_S60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThreeMetric_S76

set_option autoImplicit false

/-!
# CH12-S80 / G2a: `ckErr` of a global diffeomorphism from `ckErr` of its inverse

`ckErr_inverse_S80`: if `e` is a global diffeomorphism of `H.Carrier` and `ckErr_S45 H H.metric 1 e.symm`
is `< δ` on `e '' U` (orders `≤ m`), then `ckErr_S45 H H.metric 1 e < ε` on `U` (orders `≤ m`).
Route: the bridge `ckErr_S45 = metricDerivNorm` on `↥U` (S57), naturality of `metricDerivNorm` under the
fixed-domain pull-back by `e`, and the three-metric lemma of S76 with `g₁ = h|_U`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- `e^*(e.symm^* h) = h` on `↥U`, in the fixed-domain form. -/
theorem fixedPullback_inverse_eq_S80 (H : FiniteVolumeHyperbolicModel.{u})
    (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.symm : H.Carrier → H.Carrier)
      (diffImage_S60 H e U))
    (hinj : ∀ y ∈ diffImage_S60 H e U,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) y)) :
    fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
        (pullbackRestrict_S57 H (scaleMetric (I := 𝓡 3) 1 one_pos H.metric)
          (e.symm : H.Carrier → H.Carrier) (diffImage_S60 H e U) hf hinj) =
      H.metric.restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [fixedDomainPullbackMetric_inner]
  have hR := SmoothRiemannianMetric.pullbackOfImmersion_inner (I := 𝓡 3)
    (scaleMetric (I := 𝓡 3) 1 one_pos H.metric)
    (fun z : diffImage_S60 H e U => (e.symm : H.Carrier → H.Carrier) z)
    (contMDiff_restrict_C4 _ _ hf)
    (fun z => immersion_restrict_inj_S57 H _ _ hf hinj z) ⟨e x, x, x.2, rfl⟩
    (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x w)
  have e1 := mfderiv_comp_val_C4 (e.symm : H.Carrier → H.Carrier) (diffImage_S60 H e U) hf
    ⟨e x, x, x.2, rfl⟩ (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v)
  have e2 := mfderiv_comp_val_C4 (e.symm : H.Carrier → H.Carrier) (diffImage_S60 H e U) hf
    ⟨e x, x, x.2, rfl⟩ (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x w)
  refine hR.trans ((congrArg₂ (fun a b => (scaleMetric (I := 𝓡 3) 1 one_pos H.metric).inner
    (e.symm (e x)) a b) e1 e2).trans ?_)
  have hv : mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) (e x)
      (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v) = v := by
    exact Diffeomorph.mfderiv_symm_self e (x : H.Carrier) v
  have hw : mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) (e x)
      (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x w) = w := by
    exact Diffeomorph.mfderiv_symm_self e (x : H.Carrier) w
  rw [scaleMetric_inner, one_mul, SmoothRiemannianMetric.restrictOpen_inner]
  change H.metric.inner (e.symm (e x))
    (mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) (e x)
      (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v))
    (mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) (e x)
      (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x w)) =
    H.metric.inner (x : H.Carrier) v w
  rw [hv, hw, Diffeomorph.symm_apply_apply]

theorem ckErr_inverse_S80 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier,
      (∀ j : ℕ, j ≤ m → ∀ y ∈ e '' (U : Set H.Carrier),
        ckErr_S45 H H.metric 1 (e.symm : H.Carrier → H.Carrier) j y < δ) →
      ∀ j : ℕ, j ≤ m → ∀ x ∈ (U : Set H.Carrier),
        ckErr_S45 H H.metric 1 (e : H.Carrier → H.Carrier) j x < ε := by
  obtain ⟨δ, hδ, h3⟩ := three_metric_closeness_S76 (M := U) m ε hε
  refine ⟨δ, hδ, fun e hF j hj x hx => ?_⟩
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e : H.Carrier → H.Carrier) U :=
    e.contMDiff.contMDiffOn
  have hinje : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) y) :=
    fun y _ => mfderiv_inj_S60 H e y
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.symm : H.Carrier → H.Carrier)
      (diffImage_S60 H e U) := e.symm.contMDiff.contMDiffOn
  have hinjf : ∀ y ∈ diffImage_S60 H e U,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) y) :=
    fun y _ => mfderiv_inj_S60 H e.symm y
  have hid := fixedPullback_inverse_eq_S80 H e U hf hinjf
  have hK := pullbackRestrict_self_eq_fixed_S60 H e U he hinje
  have key := h3 (H.metric.restrictOpen U) (H.metric.restrictOpen U)
    (pullbackRestrict_S57 H (scaleMetric (I := 𝓡 3) 1 one_pos H.metric)
      (e : H.Carrier → H.Carrier) U he hinje)
    (fun y r _ => by
      have h0 : metricDerivNorm (I := 𝓡 3) r (H.metric.restrictOpen U) (H.metric.restrictOpen U)
          (H.metric.restrictOpen U) y = 0 := by
        unfold metricDerivNorm metricDiffCovDerivAt
        rw [sub_self]
        have hz : DifferentialGeometry.Tensor0SBundle.normSq0S (I := 𝓡 3)
            (H.metric.restrictOpen U) y (r + 2) 0 = 0 :=
          ((DifferentialGeometry.Tensor0SBundle.tensor0SMetricData (I := 𝓡 3)
            (H.metric.restrictOpen U) y (r + 2)).inner_self_eq_zero_iff 0).2 rfl
        rw [hz, Real.sqrt_zero]
      rw [h0]; exact hδ)
    (fun y r hr => by
      rw [← hid, hK, metricDerivNorm_fixedDomainPullback e U (diffImage_S60 H e U)
        (subset_diffImage_S60 H e U) _ _ _ r y,
        ← ckErr_S45_eq_metricDerivNorm_S57 H H.metric 1 one_pos (e.symm : H.Carrier → H.Carrier)
          (diffImage_S60 H e U) hf hinjf r ⟨e y, y, y.2, rfl⟩]
      exact hF r hr (e y) ⟨y, y.2, rfl⟩) ⟨x, hx⟩ j hj
  rw [ckErr_S45_eq_metricDerivNorm_S57 H H.metric 1 one_pos (e : H.Carrier → H.Carrier) U he hinje
    j ⟨x, hx⟩]
  exact key

end GC.LongTime.Ch12
