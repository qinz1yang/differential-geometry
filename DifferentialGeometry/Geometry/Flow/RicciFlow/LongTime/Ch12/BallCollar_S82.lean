import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WBCore_S82

set_option autoImplicit false

/-!
# CH12-S82 / G2: concentric-ball collar levels (lead ruling on K2)

`ballLevel_S82 H U R k j = {x : ↥U | x ∈ B(2R - j R/(k+1))}`: nested, `K 0 ⊆ B(2R)`, `B(R) ⊆ K k`
(collar width `ℓ = R/(k+1)` between consecutive levels).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.Ch12

/-- the `j`-th concentric level of the collar, as a subset of `↥U`. -/
def ballLevel_S82 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier) (R : ℝ) (k j : ℕ) :
    Set U :=
  {x | (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint (2 * R - j * (R / (k + 1)))}

theorem ballLevel_succ_subset_S82 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier)
    {R : ℝ} (hR : 0 < R) (k j : ℕ) : ballLevel_S82 H U R k (j + 1) ⊆ ballLevel_S82 H U R k j := by
  intro x hx
  have h0 : 0 ≤ R / (k + 1) := by positivity
  exact riemannianBallOf_mono H.metric H.basepoint (by push_cast; nlinarith) hx

theorem ballLevel_zero_subset_S82 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier)
    (R : ℝ) (k : ℕ) {x : U} (hx : x ∈ ballLevel_S82 H U R k 0) :
    (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint (2 * R) := by
  simpa [ballLevel_S82] using hx

theorem ball_subset_ballLevel_S82 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier)
    {R : ℝ} (hR : 0 < R) (k : ℕ) {x : U}
    (hx : (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint R) :
    x ∈ ballLevel_S82 H U R k k := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : R ≤ 2 * R - k * (R / (k + 1)) := by
    have : (k : ℝ) * (R / (k + 1)) ≤ R := by
      rw [← mul_div_assoc, div_le_iff₀ hk]; nlinarith
    linarith
  exact riemannianBallOf_mono H.metric H.basepoint h1 hx


theorem ballLevel_succ_subset_S82_trans (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier)
    {R : ℝ} (hR : 0 < R) (k : ℕ) {j : ℕ} {x : U} (hx : x ∈ ballLevel_S82 H U R k j) :
    x ∈ ballLevel_S82 H U R k 0 := by
  induction j with
  | zero => exact hx
  | succ j ih => exact ih (ballLevel_succ_subset_S82 H U hR k j hx)

/-- **W-B2 core on the concentric collar.**  `K j := ballLevel_S82 H U R k j`, `ℓ := R/(k+1)`; the conclusion is
on `B(R) ⊆ K k`; the threshold is `wbEta_S82 k (R/(k+1)) B ε` (closed formula in `k R B ε`).  Inputs: the
`hCollar` body for these levels (`hgeo`), the coarse jets on `K 0 ⊆ B(2R)`, the order-0 defect bound on `K 0`
(`hdef0`; see state file: NOT a consequence of the C⁰ metric hypothesis), and `ckErr(t) < ε/2` on `B(2R)`. -/
theorem wbCoreBall_S82 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    (k : ℕ) {R B ε t : ℝ} (hR : 0 < R) (hB : 1 ≤ B) (hε : 0 < ε) (ht : 0 < t)
    {D : RealTimeInterval} (S' : SolutionOn (I := 𝓡 3) (M := U) D) (hS : IsSolutionOn S')
    (hreg : Icc t (2 * t) ⊆ D.regular)
    (hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S'.base.metric p.1) x₀ p.2 i j)
        (Icc t (2 * t) ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet))
    (hmet : ∀ r ∈ Icc t (2 * t), S'.base.metric r = pullbackRestrict_S57 H (g r) f U hF hinj)
    (hRef : ∀ j ≤ k + 1, ∀ r ∈ Ioo t (2 * t), ∀ x ∈ ballLevel_S82 H U R k 0,
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (j + 2)
        (defectJet_S57 S' (H.metric.restrictOpen U) j r x)) ≤ B * r)
    (hgeo : ∀ j < k, ∀ x ∈ ballLevel_S82 H U R k (j + 1),
      ∀ e : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → TangentSpace (𝓡 3) x,
      (∀ i m, (H.metric.restrictOpen U).inner x (e i) (e m) = if i = m then 1 else 0) →
      ∀ a : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
        ∃ (γ : ℝ → U) (hγ0 : γ 0 = x)
          (P : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) → (r : ℝ) → TangentSpace (𝓡 3) (γ r)),
          (∀ i, P i 0 = hγ0.symm ▸ e i) ∧
          (∀ s ∈ Icc (0 : ℝ) (R / (k + 1)), γ s ∈ ballLevel_S82 H U R k j ∧
            ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 2 γ s ∧
            HasGeodesicEquationAt (I := 𝓡 3) (H.metric.restrictOpen U) γ s ∧
            (∀ i, DifferentiableAt ℝ (chartRepAt (I := 𝓡 3) γ (P i) s) s) ∧
            (∀ i, covDerivAlong (I := 𝓡 3) (H.metric.restrictOpen U) γ (P i) s = 0) ∧
            (∀ i m, (H.metric.restrictOpen U).inner (γ s) (P i s) (P m s) = if i = m then 1 else 0) ∧
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s) (1 : ℝ) = P a s))
    (hdef0 : ∀ r ∈ Ioo t (2 * t), ∀ x ∈ ballLevel_S82 H U R k 0,
      Real.sqrt (normSq0S (H.metric.restrictOpen U) x (0 + 2)
        (defectJet_S57 S' (H.metric.restrictOpen U) 0 r x)) ≤ wbEta_S82 k (R / (k + 1)) B ε * r)
    (h0 : ∀ j ≤ k, ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (g t) t⁻¹ f j p < ε / 2) :
    ∀ j ≤ k, ∀ s ∈ Icc t (2 * t), ∀ x : U,
      (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint R → ckErr_S45 H (g s) s⁻¹ f j x < ε := by
  have hℓ : 0 < R / ((k : ℝ) + 1) := by positivity
  intro j hj s hs x hx
  exact wbCore_S82 H g f U hF hinj k (ballLevel_S82 H U R k) (ballLevel_succ_subset_S82 H U hR k)
    hℓ hB hε ht S' hS hreg hgram hmet hRef hgeo hdef0
    (fun i hi y hy => h0 i hi y (ballLevel_zero_subset_S82 H U R k
      (ballLevel_succ_subset_S82_trans H U hR k hy))) j hj s hs x
    (ball_subset_ballLevel_S82 H U hR k hx)

end GC.LongTime.Ch12
