import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompLocalDiffeo_S71
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricWindow_S49
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage

set_option autoImplicit false

/-! # CH12-S90 G1: order-0 metric closeness ⇒ ball covering

* `pullback_inner_ge_of_ckErr_S90`: `ckErr_S45 H g' c f 0 p < δ` gives the lower half
  `(1 - δ) h ≤ c f^*g'` (the upper half is `pullback_inner_le_of_ckErr_S49`);
* `exists_partialDiffeomorph_of_lower_S90`: smooth + injective on open `U` with `(1-δ) h ≤ f^*G`
  (`δ < 1`) is the underlying map of a `PartialDiffeomorph` with source `U`;
* `ball_cover_of_lower_S90`: if moreover the closed `h`-ball `B̄(base, R)` lies in `U`, then
  `B_G(f q, A) ⊆ f '' B̄(base, R)` whenever `q ∈ B(base, r)` and `A/√(1-δ) + r < R`. -/

noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem pullback_inner_ge_of_ckErr_S90 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier) {δ : ℝ}
    (h0 : ckErr_S45 H g' c f 0 p < δ) (w : TangentSpace (𝓡 3) p) :
    (1 - δ) * H.metric.inner p w w ≤
      c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) := by
  change tensor0SFiberNorm H.metric p 2 (scaledMetricError_S49 H g' c f p) < δ at h0
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := 𝓡 3) H.metric p
  have hb := abs_apply_le_sqrt_normSq0S (I := 𝓡 3) H.metric p 2 basis hON
    (scaledMetricError_S49 H g' c f p) (vec2 w w)
  rw [scaledMetricError_apply_vec2_S49, Fin.prod_univ_two] at hb
  simp only [vec2, Fin.isValue, ↓reduceIte, one_ne_zero] at hb
  rw [Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at hb
  have h1 := (abs_le.mp (hb.trans (mul_le_mul_of_nonneg_right h0.le
    (metric_inner_self_nonneg _ _ _)))).1
  linarith

theorem exists_partialDiffeomorph_of_lower_S90 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] (G : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U : Set H.Carrier))
    (hinj : Set.InjOn f (U : Set H.Carrier)) {δ : ℝ} (hδ : δ < 1)
    (hlow : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 - δ) * H.metric.inner p w w ≤
        G.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w)) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier N (∞ : WithTop ℕ∞),
      Φ.source = (U : Set H.Carrier) ∧ (Φ : H.Carrier → N) = f := by
  have : Nonempty H.Carrier := ⟨H.basepoint⟩
  have hinv : ∀ p ∈ (U : Set H.Carrier), (mfderiv (𝓡 3) (𝓡 3) f p).IsInvertible := by
    intro p hp
    have hinj' : Function.Injective (mfderiv (𝓡 3) (𝓡 3) f p) := by
      intro v w hvw
      by_contra hne
      have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
      have h1 := hlow p hp (v - w)
      have hz : mfderiv (𝓡 3) (𝓡 3) f p (v - w) = 0 := by
        rw [map_sub, hvw, sub_self]
      rw [hz] at h1
      have h2 := H.metric.pos p (v - w) hne'
      have h3 : G.inner (f p) (0 : TangentSpace (𝓡 3) (f p)) (0 : TangentSpace (𝓡 3) (f p)) = 0 := by
        simp
      rw [h3] at h1
      nlinarith
    exact isInvertible_of_injective_S71 _ hinj'
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) (∞ : WithTop ℕ∞) f (U : Set H.Carrier) :=
    fun x => DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      U.isOpen x.2 hf (hinv x x.2)
  obtain ⟨Φ, hs, _, hΦ⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn U.isOpen hloc hinj
  exact ⟨Φ, hs, hΦ⟩

/-- Ball covering for a near-isometric (lower bound only) injective smooth map. -/
theorem ball_cover_of_lower_S90 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T3Space N] (G : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U : Set H.Carrier))
    (hinj : Set.InjOn f (U : Set H.Carrier)) {δ : ℝ} (hδ : δ < 1)
    (hlow : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 - δ) * H.metric.inner p w w ≤
        G.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w))
    {R : ℝ} (hRU : riemannianClosedBallOf H.metric H.basepoint R ⊆ (U : Set H.Carrier))
    {q : H.Carrier} {r A : ℝ} (hq : q ∈ riemannianBallOf H.metric H.basepoint r)
    (hmargin : A / Real.sqrt (1 - δ) + r < R) :
    riemannianBallOf G (f q) A ⊆ f '' riemannianClosedBallOf H.metric H.basepoint R := by
  obtain ⟨Φ, hs, hΦ⟩ := exists_partialDiffeomorph_of_lower_S90 H G f U hf hinj hδ hlow
  have : T2Space H.Carrier := inferInstance
  have : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : RegularSpace H.Carrier := inferInstance
  have hpos : 0 < 1 - δ := by linarith
  have hsq : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr hpos
  have hcpt : IsCompact (riemannianClosedBallOf H.metric H.basepoint R) :=
    isCompact_riemannianClosedBallOf H.complete _ _
  have key := DifferentialGeometry.PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
    H.metric G Φ (O := H.basepoint) (x := q) (r := r) (R := R) (A := A)
    (C := 1 / Real.sqrt (1 - δ)) (by positivity) hcpt (hs ▸ hRU)
    (fun z hz v => by
      have hzU : z ∈ (U : Set H.Carrier) := hRU hz
      have h1 := hlow z hzU v
      rw [hΦ]
      have hsq2 : (1 / Real.sqrt (1 - δ)) ^ 2 = 1 / (1 - δ) := by
        rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
      rw [hsq2]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
      linarith)
    hq (by rw [one_div, ← div_eq_inv_mul]; exact hmargin)
  rw [hΦ] at key
  exact key

end GC.LongTime.Ch12
