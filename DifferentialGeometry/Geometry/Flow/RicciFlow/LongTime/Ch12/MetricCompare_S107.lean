import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricChain_S107
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverCkErr_S90

set_option autoImplicit false

/-!
# CH12-S107 / G2a: `s⁻¹ g_s` against the hyperbolic model along the survivor lift

`metric_compare_S107` : on the open set `B`, with the survivor lift `φ : H → D` (`ψ_{j0} ∘ φ = J` on `B`),
the Grönwall chain (`metric_chain_S107`, factor `(s/t)^η ≤ 2` for `t ≤ s ≤ 2t`, `η ≤ 1`) and the order-zero
closeness `ckErr_S45 H g_t t⁻¹ J 0 < 1/2` (`pullback_inner_ge_of_ckErr_S90` / `…_le_…_S49`) give, for every
`p ∈ B`, `w ∈ T_p H`:
`(1/4) h(w,w) ≤ s⁻¹ g_s(φ p)(dφ w, dφ w) ≤ 3 h(w,w)`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Hyperbolic GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- `ψ_{j0}(φ p) = J p` on an open set transports the push-forward norm to the `J`-pullback. -/
theorem pushInner_eq_pullback_S107 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 last : Fin (K.eventCount + 1)) (hle : j0 ≤ last) (J : H.Carrier → (K.stage j0).Carrier)
    {B : Set H.Carrier} (hB : IsOpen B) (φ : H.Carrier → K.backwardSurvivorDomain j0 last hle)
    (hφ : ContMDiffOn ThreeModel ThreeModel ∞ φ B)
    (hφJ : ∀ p ∈ B, K.backwardSurvivorMap j0 last hle j0 le_rfl hle (φ p) = J p) (t : ℝ)
    {p : H.Carrier} (hp : p ∈ B) (w : TangentSpace ThreeModel p) :
    pushInner_S107 K j0 last hle j0 le_rfl hle t (φ p) (mfderiv ThreeModel ThreeModel φ p w) =
      (K.stageMetric j0 t).inner (J p) (mfderiv ThreeModel ThreeModel J p w)
        (mfderiv ThreeModel ThreeModel J p w) := by
  set ψ := K.backwardSurvivorMap j0 last hle j0 le_rfl hle with hψdef
  have hψ : MDifferentiableAt ThreeModel ThreeModel ψ (φ p) :=
    ((K.backwardSurvivorMap_isLocalDiffeomorph j0 last hle j0 le_rfl hle).contMDiff.contMDiffAt
      ).mdifferentiableAt (by decide)
  have hφd : MDifferentiableAt ThreeModel ThreeModel φ p :=
    ((hφ.contMDiffAt (hB.mem_nhds hp)).mdifferentiableAt (by decide))
  have hcomp : mfderiv ThreeModel ThreeModel (ψ ∘ φ) p =
      (mfderiv ThreeModel ThreeModel ψ (φ p)).comp (mfderiv ThreeModel ThreeModel φ p) :=
    mfderiv_comp p hψ hφd
  have hev : (ψ ∘ φ) =ᶠ[nhds p] J :=
    Filter.eventually_of_mem (hB.mem_nhds hp) (fun q hq => hφJ q hq)
  have h1 : mfderiv ThreeModel ThreeModel (ψ ∘ φ) p = mfderiv ThreeModel ThreeModel J p :=
    hev.mfderiv_eq
  have h2 : ψ (φ p) = J p := hφJ p hp
  have key : ∀ (y₁ y₂ : (K.stage j0).Carrier), y₁ = y₂ → ∀ u : TangentSpace ThreeModel y₁,
      (K.stageMetric j0 t).inner y₁ u u = (K.stageMetric j0 t).inner y₂ u u := by
    rintro _ _ rfl _
    rfl
  unfold pushInner_S107
  have h3 : mfderiv ThreeModel ThreeModel ψ (φ p) (mfderiv ThreeModel ThreeModel φ p w) =
      mfderiv ThreeModel ThreeModel J p w := by
    rw [← h1, hcomp]
    rfl
  rw [h3]
  exact key _ _ h2 _

theorem metric_compare_S107 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) (J : H.Carrier → (K.stage j0).Carrier) {t s η : ℝ}
    (ht0 : 0 < t) (hts : t ≤ s) (hs2 : s ≤ 2 * t) (hs : s ≤ K.horizon) (hη1 : η ≤ 1)
    (hj0 : actS_S70 K t = j0) {last : Fin (K.eventCount + 1)} (hlast : actS_S70 K s = last)
    (hle : j0 ≤ last) {B : Set H.Carrier} (hB : IsOpen B)
    (hW : ∀ r ∈ Icc t s, DefectAllAt_S85 K j0 J B η r)
    (φ : H.Carrier → K.backwardSurvivorDomain j0 last hle)
    (hφ : ContMDiffOn ThreeModel ThreeModel ∞ φ B)
    (hφJ : ∀ p ∈ B, K.backwardSurvivorMap j0 last hle j0 le_rfl hle (φ p) = J p)
    (hck : ∀ p ∈ B, ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J 0 p < 1 / 2) :
    ∀ p ∈ B, ∀ w : TangentSpace ThreeModel p,
      (1 / 4 : ℝ) * H.metric.inner p w w ≤
          s⁻¹ * (K.stageMetric last s).inner (φ p).val (mfderiv ThreeModel ThreeModel φ p w)
            (mfderiv ThreeModel ThreeModel φ p w) ∧
        s⁻¹ * (K.stageMetric last s).inner (φ p).val (mfderiv ThreeModel ThreeModel φ p w)
            (mfderiv ThreeModel ThreeModel φ p w) ≤ 3 * H.metric.inner p w w := by
  intro p hp w
  have hch := metric_chain_S107 K j0 J B ht0 hts hs hj0 hW hlast hle p hp (φ p) (hφJ p hp)
    (mfderiv ThreeModel ThreeModel φ p w)
  rw [pushInner_eq_pullback_S107 H K j0 last hle J hB φ hφ hφJ t hp w] at hch
  have hlo := pullback_inner_ge_of_ckErr_S90 H (K.stageMetric j0 t) t⁻¹ J p (hck p hp) w
  have hup := pullback_inner_le_of_ckErr_S49 H (K.stageMetric j0 t) t⁻¹ J p (hck p hp) w
  have hν : (s / t) ^ η ≤ 2 := by
    have h1 : 1 ≤ s / t := by rw [le_div_iff₀ ht0]; linarith
    have h2 : s / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith
    calc (s / t) ^ η ≤ (s / t) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hη1
      _ = s / t := Real.rpow_one _
      _ ≤ 2 := h2
  have hνpos : 0 < (s / t) ^ η := Real.rpow_pos_of_pos (div_pos (ht0.trans_le hts) ht0) _
  set a := t⁻¹ * (K.stageMetric j0 t).inner (J p) (mfderiv ThreeModel ThreeModel J p w)
    (mfderiv ThreeModel ThreeModel J p w) with ha
  set b := s⁻¹ * (K.stageMetric last s).inner (φ p).val (mfderiv ThreeModel ThreeModel φ p w)
    (mfderiv ThreeModel ThreeModel φ p w) with hb
  have hch1 : a ≤ (s / t) ^ η * b := by
    simpa only [ha, hb, div_eq_inv_mul] using hch.1
  have hch2 : b ≤ (s / t) ^ η * a := by
    simpa only [ha, hb, div_eq_inv_mul] using hch.2
  have hhh : 0 ≤ H.metric.inner p w w := metric_inner_self_nonneg _ _ _
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg (inv_nonneg.mpr (ht0.trans_le hts).le) (metric_inner_self_nonneg _ _ _)
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg (inv_nonneg.mpr ht0.le) (metric_inner_self_nonneg _ _ _)
  constructor
  · -- `h/4 ≤ a/2 ≤ b`
    have : a ≤ 2 * b := by nlinarith
    nlinarith
  · have : b ≤ 2 * a := by nlinarith
    nlinarith

end GC.LongTime.Ch12
