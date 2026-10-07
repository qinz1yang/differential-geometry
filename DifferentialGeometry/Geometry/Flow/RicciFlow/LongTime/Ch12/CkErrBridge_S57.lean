import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrNaturalitySource_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DuhamelWindow_S57

set_option autoImplicit false

/-!
# CH12-S57 / G2: `ckErr_S45` as `metricDerivNorm` of the rescaled pull-back family on `↥U`

For `f` smooth and an immersion on an open `U ⊆ H.Carrier` and a metric family `g : ℝ → Met N`,
`ckErr_S45 H (g s) s⁻¹ f j x` equals `metricDerivNorm j (rescaledMetric_S57 P t _ s) h_U h_U x`
where `P r = (g r).pullbackOfImmersion (f|_U)` is a metric family on the manifold `↥U` and
`h_U = H.metric.restrictOpen U`.  This is the consumer shape of `rescaled_metricDerivNorm_window_S57`
(W-B1) on the fixed manifold `↥U` (W-B3, bridge half).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

section Bridge

variable (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

/-- injectivity of the differential of the restricted map `f|_U : ↥U → N`. -/
theorem immersion_restrict_inj_S57 (f : H.Carrier → N) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) (z : U) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun w : U => f w) z) := by
  intro v w hvw
  exact hinj z z.property
    ((mfderiv_comp_val_C4 f U hF z v).symm.trans (hvw.trans (mfderiv_comp_val_C4 f U hF z w)))

/-- the pull-back metric `(f|_U)^* g` on the open subtype `↥U`. -/
def pullbackRestrict_S57 (g : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    SmoothRiemannianMetric (𝓡 3) U :=
  g.pullbackOfImmersion (I := 𝓡 3) (fun z : U => f z) (contMDiff_restrict_C4 f U hF)
    (immersion_restrict_inj_S57 H f U hF hinj)

/-- pull-back commutes with scaling. -/
theorem pullbackRestrict_scale_S57 (g : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c)
    (f : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    pullbackRestrict_S57 H (scaleMetric c hc g) f U hF hinj =
      scaleMetric c hc (pullbackRestrict_S57 H g f U hF hinj) := by
  ext z v w
  simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner,
    scaleMetric_inner]

/-- `ckErr_S45` as a `metricDerivNorm` on the open subtype (via `rawNorm_eq_metricDerivNorm_C4`). -/
theorem ckErr_S45_eq_metricDerivNorm_S57 (g : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ)
    (hc : 0 < c) (f : H.Carrier → N) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) (j : ℕ) (x : U) :
    ckErr_S45 H g c f j x =
      metricDerivNorm j (pullbackRestrict_S57 H (scaleMetric c hc g) f U hF hinj)
        (H.metric.restrictOpen U) (H.metric.restrictOpen U) x := by
  have e1 : ckErr_S45 H g c f j x = ckErr_O19 H g c f j x := rfl
  rw [e1, ckErr_eq_scale_O19 H g c hc, ckErr_one_eq_raw_O19]
  exact rawNorm_eq_metricDerivNorm_C4 (scaleMetric c hc g) H.metric f U hF hinj j x

/-- `ckErr_S45` at time `s ≥ t` against `g s` and constant `s⁻¹` is the order-`j` `metricDerivNorm` of
the rescaled pull-back family `rescaledMetric_S57 P t _ s`. -/
theorem ckErr_S45_eq_rescaled_S57 (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) {t : ℝ} (ht : 0 < t)
    (f : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) {s : ℝ} (hs : t ≤ s)
    (j : ℕ) (x : U) :
    ckErr_S45 H (g s) s⁻¹ f j x =
      metricDerivNorm j
        (rescaledMetric_S57 (fun r => pullbackRestrict_S57 H (g r) f U hF hinj) t ht s)
        (H.metric.restrictOpen U) (H.metric.restrictOpen U) x := by
  have hs0 : 0 < s := lt_of_lt_of_le ht hs
  rw [ckErr_S45_eq_metricDerivNorm_S57 H (g s) s⁻¹ (inv_pos.2 hs0) f U hF hinj j x,
    pullbackRestrict_scale_S57 H (g s) s⁻¹ (inv_pos.2 hs0) f U hF hinj]
  have key : ∀ (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (m : SmoothRiemannianMetric (𝓡 3) U),
      c = c' → scaleMetric c hc m = scaleMetric c' hc' m := by
    intro c c' hc hc' m hcc
    subst hcc
    rfl
  unfold rescaledMetric_S57
  rw [key (max s t)⁻¹ s⁻¹ _ (inv_pos.2 hs0) _ (by rw [max_eq_left hs])]

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature in
/-- **W-B1 + W-B3 (bridge half), assembled.**  On a Ricci flow `S` on `↥U` whose metrics are the
pull-backs `(f|_U)^* g r` on `[t, u] ⊆ [t, 2t]`, a bound `η r` on the order-`N'` defect jet
`∇_h^{N'} (g_r + 2 r Ric g_r)` (`h = H.metric|_U`) gives
`ckErr_S45 H (g s) s⁻¹ f N' x ≤ ckErr_S45 H (g t) t⁻¹ f N' x + η` for `s ∈ [t, u]`, `x ∈ K`. -/
theorem ckErr_window_S57 (g : ℝ → SmoothRiemannianMetric (𝓡 3) N)
    (f : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := U) D) (hS : IsSolutionOn S)
    {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) (hu : u ≤ 2 * t) (hreg : Icc t u ⊆ D.regular)
    (hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x₀ p.2 i j)
        (Icc t u ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet))
    (hmet : ∀ r ∈ Icc t u, S.base.metric r = pullbackRestrict_S57 H (g r) f U hF hinj)
    (N' : ℕ) (K : Set U) {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ x ∈ K, ∀ r ∈ Ioo t u,
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (N' + 2)
        (defectJet_S57 S (H.metric.restrictOpen U) N' r x)) ≤ η * r) :
    ∀ s ∈ Icc t u, ∀ x ∈ K,
      ckErr_S45 H (g s) s⁻¹ f N' x ≤ ckErr_S45 H (g t) t⁻¹ f N' x + η := by
  intro s hs x hx
  have hres : ∀ r ∈ Icc t u, rescaledMetric_S57 S.base.metric t ht r =
      rescaledMetric_S57 (fun r => pullbackRestrict_S57 H (g r) f U hF hinj) t ht r := by
    intro r hr
    unfold rescaledMetric_S57
    rw [hmet r hr]
  have h1 := rescaled_metricDerivNorm_window_S57 S hS (H.metric.restrictOpen U) ht htu hu hreg
    hgram N' K hη hdef s hs x hx
  rw [hres s hs, hres t ⟨le_rfl, htu⟩] at h1
  rw [ckErr_S45_eq_rescaled_S57 H g ht f U hF hinj hs.1 N' x,
    ckErr_S45_eq_rescaled_S57 H g ht f U hF hinj le_rfl N' x]
  exact h1

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature in
/-- **All orders `j ≤ k` at once (the shape of the `hLTF04` ckErr clause).**  If the order-`j` pull-back
error at time `t` is `< δ` and all defect jets of order `≤ k` are bounded by `η r`, with `δ + η ≤ ε`,
then the pull-back error at every `s ∈ [t, u] ⊆ [t, 2t]` is `< ε` in all orders `≤ k` on `K`. -/
theorem ckErr_window_lt_S57 (g : ℝ → SmoothRiemannianMetric (𝓡 3) N)
    (f : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := U) D) (hS : IsSolutionOn S)
    {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) (hu : u ≤ 2 * t) (hreg : Icc t u ⊆ D.regular)
    (hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x₀ p.2 i j)
        (Icc t u ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet))
    (hmet : ∀ r ∈ Icc t u, S.base.metric r = pullbackRestrict_S57 H (g r) f U hF hinj)
    (k : ℕ) (K : Set U) {δ η ε : ℝ} (hη : 0 ≤ η) (hδη : δ + η ≤ ε)
    (h0 : ∀ j ≤ k, ∀ x ∈ K, ckErr_S45 H (g t) t⁻¹ f j x < δ)
    (hdef : ∀ j ≤ k, ∀ x ∈ K, ∀ r ∈ Ioo t u,
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (j + 2)
        (defectJet_S57 S (H.metric.restrictOpen U) j r x)) ≤ η * r) :
    ∀ j ≤ k, ∀ s ∈ Icc t u, ∀ x ∈ K, ckErr_S45 H (g s) s⁻¹ f j x < ε := by
  intro j hj s hs x hx
  have := ckErr_window_S57 H g f U hF hinj S hS ht htu hu hreg hgram hmet j K hη
    (hdef j hj) s hs x hx
  linarith [h0 j hj x hx]

end Bridge

end GC.LongTime.Ch12
