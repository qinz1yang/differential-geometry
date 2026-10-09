import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HStep_S82
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LandauUniform_S82
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57

set_option autoImplicit false

/-!
# CH12-S82 / G2: W-B2 core on a fixed manifold (Duhamel window + Landau chain + hstep)

`wbCore_S82`: on a fixed 3-manifold `N` with a metric family `g`, a smooth immersion `f` on an open `U`,
the transported flow `S'` on `↥U` (hLocalFlow data), the coarse reference jets (`hRef`, S81's output),
the h-collar `hgeo` (K2 body, `K (j+1)` inside `K j`) and the ORDER-0 DEFECT bound `hdef0`
(`√|g_r + 2 r Ric g_r|_h ≤ η₀ r` on `K 0`): if `ckErr(t) < ε/2` in all orders `≤ k` on `K k`, then
`ckErr(s) < ε` on `K k` for all `s ∈ [t, 2t]`, all orders `≤ k`.  The threshold `η₀` is the closed formula
`landauEta_S82 (stepConst_S82 _ k ℓ) B (ε/2) k`, independent of `t, f, U, S'` (as `hWB` requires).
The order-0 defect bound is NOT derivable from the C⁰ metric hypothesis of `hWB`
(see state-CH12-S82.md): it is the explicit binder `hdef0`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.Ch12

instance neZero_finrank_euclidean3_S82 : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by simp⟩

/-- the closed threshold of the W-B2 core (depends only on `k, ℓ, B, ε`). -/
def wbEta_S82 (k : ℕ) (ℓ B ε : ℝ) : ℝ :=
  landauEta_S82 (stepConst_S82 (EuclideanSpace ℝ (Fin 3)) k ℓ) B (ε / 2) k

theorem wbEta_pos_S82 (k : ℕ) {ℓ B ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    0 < wbEta_S82 k ℓ B ε :=
  landauEta_pos_S82 (B := B) (one_le_stepConst_S82 (E := EuclideanSpace ℝ (Fin 3)) k hℓ)
    (half_pos hε) k

theorem wbCore_S82 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    (k : ℕ) (K : ℕ → Set U) (hKm : ∀ j, K (j + 1) ⊆ K j) {ℓ B ε t : ℝ} (hℓ : 0 < ℓ) (hB : 1 ≤ B)
    (hε : 0 < ε) (ht : 0 < t)
    {D : RealTimeInterval} (S' : SolutionOn (I := 𝓡 3) (M := U) D) (hS : IsSolutionOn S')
    (hreg : Icc t (2 * t) ⊆ D.regular)
    (hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S'.base.metric p.1) x₀ p.2 i j)
        (Icc t (2 * t) ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet))
    (hmet : ∀ r ∈ Icc t (2 * t), S'.base.metric r = pullbackRestrict_S57 H (g r) f U hF hinj)
    (hRef : ∀ j ≤ k + 1, ∀ r ∈ Ioo t (2 * t), ∀ x ∈ K 0,
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (j + 2)
        (defectJet_S57 S' (H.metric.restrictOpen U) j r x)) ≤ B * r)
    (hgeo : ∀ j < k, ∀ x ∈ K (j + 1),
      ∀ e : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → TangentSpace (𝓡 3) x,
      (∀ i m, (H.metric.restrictOpen U).inner x (e i) (e m) = if i = m then 1 else 0) →
      ∀ a : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        ∃ (γ : ℝ → U) (hγ0 : γ 0 = x)
          (P : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → (r : ℝ) → TangentSpace (𝓡 3) (γ r)),
          (∀ i, P i 0 = hγ0.symm ▸ e i) ∧
          (∀ s ∈ Icc (0 : ℝ) ℓ, γ s ∈ K j ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 2 γ s ∧
            HasGeodesicEquationAt (I := 𝓡 3) (H.metric.restrictOpen U) γ s ∧
            (∀ i, DifferentiableAt ℝ (chartRepAt (I := 𝓡 3) γ (P i) s) s) ∧
            (∀ i, covDerivAlong (I := 𝓡 3) (H.metric.restrictOpen U) γ (P i) s = 0) ∧
            (∀ i m, (H.metric.restrictOpen U).inner (γ s) (P i s) (P m s) = if i = m then 1 else 0) ∧
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s) (1 : ℝ) = P a s))
    (hdef0 : ∀ r ∈ Ioo t (2 * t), ∀ x ∈ K 0,
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (0 + 2)
        (defectJet_S57 S' (H.metric.restrictOpen U) 0 r x)) ≤ wbEta_S82 k ℓ B ε * r)
    (h0 : ∀ j ≤ k, ∀ x ∈ K k, ckErr_S45 H (g t) t⁻¹ f j x < ε / 2) :
    ∀ j ≤ k, ∀ s ∈ Icc t (2 * t), ∀ x ∈ K k, ckErr_S45 H (g s) s⁻¹ f j x < ε := by
  have hC := one_le_stepConst_S82 (E := EuclideanSpace ℝ (Fin 3)) k hℓ
  have hdefs := landau_small_uniform_S82
    (fun j r x => Real.sqrt (normSq0S (H.metric.restrictOpen U) x (j + 2)
      (defectJet_S57 S' (H.metric.restrictOpen U) j r x)))
    (Ioo t (2 * t)) (fun r hr => ht.trans hr.1) K hKm k hC hB
    (fun j hj r _ α β hα0 hβ0 hα hβ =>
      hstep_S82 S' (H.metric.restrictOpen U) K k hℓ hgeo j hj r α β hα0 hβ0 hα hβ)
    hRef (half_pos hε) hdef0
  exact ckErr_window_lt_S57 H g f U hF hinj S' hS ht (by linarith) (le_refl _) hreg hgram hmet k
    (K k) (half_pos hε).le (by linarith) h0 hdefs

end GC.LongTime.Ch12
