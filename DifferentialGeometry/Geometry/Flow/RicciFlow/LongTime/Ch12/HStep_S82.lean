import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DefectJetTower_S82
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GeodesicStep_S75

set_option autoImplicit false

/-!
# CH12-S82 / G2: `hstep` for `defectJet_S57` from `landau_step_S75` (K4 + `sqrt_step_bound_S75`)

`hstep_S82` is exactly the `hstep` binder of `defectJet_small_all_orders_S67` (shape `∀ j < N, ∀ r ∈ R,
∀ α β …`) with the `j`-independent constant `C = 4 n^(N+3) (1 + 1/ℓ)`, `n = dim`.  The only geometric
input is the h-collar `hgeo` (frozen `hCollar` body of `[FROZEN v2] CH12-S75`, `K := K (j+1)`,
`K' := K j`).  No Ricci-flow input is used (K4 is pure `∇_h` algebra).
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- the `j`-independent constant of `hstep_S82`. -/
def stepConst_S82 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (Nord : ℕ) (ℓ : ℝ) : ℝ :=
  4 * (Module.finrank ℝ E : ℝ) ^ (Nord + 3) * (1 + 1 / ℓ)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem one_le_stepConst_S82 (Nord : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    1 ≤ stepConst_S82 E Nord ℓ := by
  have hn : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have h1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ (Nord + 3) := one_le_pow₀ hn
  have h2 : (1 : ℝ) ≤ 1 + 1 / ℓ := by
    have : 0 ≤ 1 / ℓ := by positivity
    linarith
  unfold stepConst_S82
  nlinarith

/-- **`hstep` for the defect jets** (Landau step `landau_step_S75` after the K4 tower identification). -/
theorem hstep_S82 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (h : SmoothRiemannianMetric I M) (K : ℕ → Set M) (Nord : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : ∀ j < Nord, ∀ x ∈ K (j + 1), ∀ e : Fin (Module.finrank ℝ E) → TangentSpace I x,
      (∀ i k, h.inner x (e i) (e k) = if i = k then 1 else 0) →
      ∀ a : Fin (Module.finrank ℝ E), ∃ (γ : ℝ → M) (hγ0 : γ 0 = x)
        (P : Fin (Module.finrank ℝ E) → (r : ℝ) → TangentSpace I (γ r)),
        (∀ i, P i 0 = hγ0.symm ▸ e i) ∧
        (∀ t ∈ Icc 0 ℓ, γ t ∈ K j ∧ ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t ∧
          HasGeodesicEquationAt (I := I) h γ t ∧
          (∀ i, DifferentiableAt ℝ (chartRepAt (I := I) γ (P i) t) t) ∧
          (∀ i, covDerivAlong (I := I) h γ (P i) t = 0) ∧
          (∀ i k, h.inner (γ t) (P i t) (P k t) = if i = k then 1 else 0) ∧
          (mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ) = P a t)) :
    ∀ j, j < Nord → ∀ r : ℝ, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ α) →
      (∀ x ∈ K j, Real.sqrt (normSq0S h x (j + 2 + 2) (defectJet_S57 S h (j + 2) r x)) ≤ β) →
      ∀ x ∈ K (j + 1),
        Real.sqrt (normSq0S h x (j + 1 + 2) (defectJet_S57 S h (j + 1) r x)) ≤
          stepConst_S82 E Nord ℓ * (Real.sqrt (α * β) + α) := by
  intro j hj r α β hα0 hβ0 hα hβ x hx
  have hstep := landau_step_S75 (I := I) (s := j + 2) h
    (defectJetField_S82 (S.base.metric r) h j r)
    (defectJetField_S82 (S.base.metric r) h (j + 1) r)
    (defectJetField_S82 (S.base.metric r) h (j + 2) r)
    (fun y => defectJetField_succ_apply_S82 (S.base.metric r) h j r y)
    (fun y => defectJetField_succ_apply_S82 (S.base.metric r) h (j + 1) r y)
    (K (j + 1)) (K j) hℓ (hgeo j hj)
    (fun y hy => by rw [← defectJet_eq_field_S82]; exact hα y hy)
    (fun y hy => by rw [← defectJet_eq_field_S82]; exact hβ y hy) x hx
  rw [← defectJet_eq_field_S82] at hstep
  have hN : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ (j + 2 + 1) := by
    have hn : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
    exact one_le_pow₀ hn
  have h1 := sqrt_step_bound_S75 hα0 hℓ hN hstep
  refine h1.trans ?_
  have hn : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have hpow : (Module.finrank ℝ E : ℝ) ^ (j + 2 + 1) ≤ (Module.finrank ℝ E : ℝ) ^ (Nord + 3) :=
    pow_le_pow_right₀ hn (by omega)
  have hs : 0 ≤ Real.sqrt (α * β) + α := by positivity
  have hl : 0 ≤ 1 + 1 / ℓ := by positivity
  unfold stepConst_S82
  apply mul_le_mul_of_nonneg_right _ hs
  nlinarith [mul_le_mul_of_nonneg_right hpow hl]

end GC.LongTime.Ch12
