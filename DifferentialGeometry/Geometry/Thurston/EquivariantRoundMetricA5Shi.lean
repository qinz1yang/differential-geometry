import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompleteGlobal

/-!
# Intrinsic derivative bounds of the normalised surface flow

Chapter 7, surface lemma U1, route (a), step a5.1 (lane U1E2), in the terminal form of review 17
§2.1 on the design note D17 (`docs/geometrization/handoffs/20261004-design-u1-ricci-flow-core.md`,
§6). For a Ricci flow `g(t)` on `[0, Tm)` on a compact connected surface with positive initial
scalar curvature put `T* = A₀ / C₀` and let `ĝ(t) = g(t) / (2 (T* - t))` be the normalised metric.

* `surfaceFlow_normalized_curvatureDerivative_bound`: for every `t₀ > 0` and every order `m`,
  `(2 (T* - t))^(m + 2) |∇^m Rm|²_{g(t)} ≤ C` on `[t₀, Tm)`; by parabolic scaling the left side is
  `|∇^m Rm(ĝ(t))|²_{ĝ(t)}`.

The proof needs neither the conditional local Shi estimate with its initial-distance Laplacian
input nor a new Bernstein argument: the any-dimensional global Shi estimate
`shi_complete_global_of_solution` is applied to the flow shifted by `t - τ`, so that the start
time is interior. On `[t - τ, t]` the curvature satisfies `|Rm| = R ≤ K := C / (2 (T* - t))`
(two-dimensional `|Rm|² = R²`, `R > 0` and the normalised upper bound of a3), and
`τ = min (t / 2) K⁻¹`; then `2 (T* - t) / τ ≤ max (4 T* / t₀) C`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]

theorem surfaceFlow_normalized_curvatureDerivative_bound (hdim : Module.finrank ℝ E = 2)
    {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ t ∈ Ico t₀ Tm, ∀ x : M,
      (2 * (surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) - t)) ^
          (m + 2) * nablaKRm04NormSqIntrinsic S m t x ≤ C := by
  intro m
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨C, hC⟩ := surfaceFlow_normalized_scalar_upper hdim S hS hscal
  set Tst := surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0)
  have hTT : Tm ≤ Tst := surfaceFlow_le_extinctionTime hTm S hS hdim hscal
  set C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set B := shiCompleteGlobalBound (Module.finrank ℝ E) m
  set L := max (4 * Tst / t₀) C'
  refine ⟨B ^ 2 * C' ^ 2 * L ^ m, fun t ht x => ?_⟩
  have ht0 : 0 < t := ht₀.trans_le ht.1
  have htT : t < Tm := ht.2
  have hd : 0 < Tst - t := by linarith
  set K := C' / (2 * (Tst - t)) with hKdef
  have hK : 0 < K := by positivity
  set τ := min (t / 2) K⁻¹ with hτdef
  have hτ : 0 < τ := lt_min (by linarith) (inv_pos.mpr hK)
  have hτt : τ < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτK : τ ≤ K⁻¹ := min_le_right _ _
  have hS' := isSolutionOn_timeShiftSolution (I := I) hS (t - τ)
  have hcurv : ∀ s ∈ Icc (0 : ℝ) τ, ∀ y : M,
      nablaKRm04NormSqIntrinsic (timeShiftSolution (I := I) S (t - τ)) 0 s y ≤ K ^ 2 := by
    intro s hs y
    rw [nablaKRm04NormSqIntrinsic_timeShiftSolution]
    have hu : s + (t - τ) ∈ Ico 0 Tm := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hpos := surfaceFlow_scalar_pos S hS hscal hu y
    have hRm : nablaKRm04NormSqIntrinsic S 0 (s + (t - τ)) y = S.scalar (s + (t - τ)) y ^ 2 := by
      have h := normSq0S_metricRm04At_eq_sq_of_finrank_two hdim (S.family.metric (s + (t - τ))) y
      simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
      exact h
    rw [hRm]
    have hRK : S.scalar (s + (t - τ)) y ≤ K := by
      rw [hKdef, le_div_iff₀ (by positivity)]
      calc S.scalar (s + (t - τ)) y * (2 * (Tst - t))
          ≤ S.scalar (s + (t - τ)) y * (2 * (Tst - (s + (t - τ)))) :=
            mul_le_mul_of_nonneg_left (by linarith [hs.2]) hpos.le
        _ ≤ C := hC _ hu y
        _ ≤ C' := le_max_left _ _
    exact pow_le_pow_left₀ hpos.le hRK 2
  have hshi := shi_complete_global_of_solution (I := I) (timeShiftSolution (I := I) S (t - τ)) hS'
    (T := τ) (K := K) (by linarith) (by linarith) hK
    (by rw [timeShiftSolution_metric]; exact RiemannianMetricComplete.of_compact _) hcurv m τ
    ⟨hτ, le_rfl⟩ x
  rw [nablaKRm04NormSqIntrinsic_timeShiftSolution, show τ + (t - τ) = t by ring,
    min_eq_left hτK] at hshi
  set N := nablaKRm04NormSqIntrinsic S m t x
  have hN : 0 ≤ N := nablaKRm04NormSqIntrinsic_nonneg S m t x
  have hN2 : N ≤ (B * K) ^ 2 / τ ^ m := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hshi 2
    rwa [Real.sq_sqrt hN, div_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt hτ.le] at h
  have hdK : 2 * (Tst - t) * K = C' := by
    rw [hKdef]
    field_simp
  have hL : 2 * (Tst - t) / τ ≤ L := by
    rcases min_choice (t / 2) K⁻¹ with h | h
    · rw [hτdef, h, div_le_iff₀ (by linarith)]
      have hTst : 0 < Tst := hTm.trans_le hTT
      have h4 : 4 * Tst / t₀ * (t / 2) ≥ 2 * Tst := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ ht₀]
        nlinarith [ht.1]
      have hL4 : 4 * Tst / t₀ ≤ L := le_max_left _ _
      have hmul : 4 * Tst / t₀ * (t / 2) ≤ L * (t / 2) :=
        mul_le_mul_of_nonneg_right hL4 (by linarith)
      linarith
    · rw [hτdef, h, div_inv_eq_mul, hdK]
      exact le_max_right _ _
  have hid : (2 * (Tst - t)) ^ (m + 2) * ((B * K) ^ 2 / τ ^ m) =
      B ^ 2 * (2 * (Tst - t) * K) ^ 2 * (2 * (Tst - t) / τ) ^ m := by
    rw [div_pow]
    field_simp
    ring
  calc (2 * (Tst - t)) ^ (m + 2) * N ≤ (2 * (Tst - t)) ^ (m + 2) * ((B * K) ^ 2 / τ ^ m) :=
        mul_le_mul_of_nonneg_left hN2 (by positivity)
    _ = B ^ 2 * C' ^ 2 * (2 * (Tst - t) / τ) ^ m := by rw [hid, hdK]
    _ ≤ B ^ 2 * C' ^ 2 * L ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hL m) (by positivity)

end GC.Geometry
