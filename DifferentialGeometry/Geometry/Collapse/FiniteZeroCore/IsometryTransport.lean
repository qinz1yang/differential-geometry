import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

/-!
# Isometry transports of pointed convergence and of cone approximations (LFR49 (d))

LFR49's noncompact branch replaces the model `N` of LFR14 by its carrier `N'` (lane LFR49-A),
which is isometric to `N` through `κ : N' ≃ᵢ N`. The two metric inputs of the LC61 kernel move
along `κ`:

* `pointedGHConverges_of_isometryEquiv`: pointed Gromov–Hausdorff convergence to `(N, q)` gives
  convergence to `(N', κ⁻¹ q)` (post-compose every ball approximation with `κ⁻¹`);
* `hcone_of_isometryEquiv`: Kleiner–Lott approximations of the blow-downs `(R⁻¹ N, q)` to a cone
  give those of `(R⁻¹ N', κ⁻¹ q)` (pre-compose with `κ`, an isometry of the rescaled metrics too).
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry

/-- **Pointed convergence transports along an isometry equivalence of the limit.** -/
theorem pointedGHConverges_of_isometryEquiv {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)]
    {N N' : Type*} [MetricSpace N] [MetricSpace N'] (κ : N' ≃ᵢ N) {P : ∀ i, Y i} {q : N}
    (h : PointedGHConverges P q) : PointedGHConverges P (κ.symm q) := by
  have hc : CompleteSpace N := h.complete_space
  refine ⟨κ.completeSpace, fun R ε hε hεR => ?_⟩
  filter_upwards [h.eventually_approx hε hεR] with n hn
  obtain ⟨f⟩ := hn
  refine ⟨{ error_pos := f.error_pos
            error_lt_radius := f.error_lt_radius
            toFun := fun x => κ.symm (f.toFun x)
            basepoint := by rw [f.basepoint]
            distortion := fun x x' => by
              rw [κ.symm.dist_eq]
              exact f.distortion x x'
            coverage := fun y hy => ?_ }⟩
  obtain ⟨x, hx⟩ := f.coverage (κ y) (by
    rw [← κ.apply_symm_apply q, κ.dist_eq]
    exact hy)
  refine ⟨x, ?_⟩
  rw [← κ.dist_eq, κ.apply_symm_apply]
  exact hx

/-- An isometry equivalence is an isometry equivalence of the rescaled metrics. -/
theorem dist_rescale_isometryEquiv {N N' : Type*} (mN : MetricSpace N) (mN' : MetricSpace N')
    (κ : @IsometryEquiv N' N mN'.toPseudoEMetricSpace mN.toPseudoEMetricSpace) (c : ℝ)
    (hc : 0 < c) (x y : N') :
    @dist N' (mN'.rescale c hc).toDist x y = @dist N (mN.rescale c hc).toDist (κ x) (κ y) := by
  rw [MetricSpace.rescale_dist, MetricSpace.rescale_dist]
  congr 1
  exact (@IsometryEquiv.dist_eq N' N mN'.toPseudoMetricSpace mN.toPseudoMetricSpace κ x y).symm

/-- **Cone approximations of blow-downs transport along an isometry equivalence.** -/
theorem hcone_of_isometryEquiv {N N' C : Type*} [mN : MetricSpace N] [mN' : MetricSpace N']
    [mC : MetricSpace C] (κ : N' ≃ᵢ N) {q : N} {o : C}
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) mC q o τ)) :
    ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N' C (mN'.rescale R⁻¹ (inv_pos.mpr hR)) mC (κ.symm q) o τ) := by
  intro τ hτ hτ1
  obtain ⟨R₀, hR₀⟩ := hcone τ hτ hτ1
  refine ⟨R₀, fun R hR hRR => ?_⟩
  obtain ⟨φ⟩ := hR₀ R hR hRR
  -- plain functions, before the rescaled instances are installed
  obtain ⟨f, hfdef⟩ : ∃ f : N' → N, f = κ := ⟨κ, rfl⟩
  obtain ⟨finv, hfinvdef⟩ : ∃ finv : N → N', finv = κ.symm := ⟨κ.symm, rfl⟩
  have hffinv : ∀ z, f (finv z) = z := fun z => by rw [hfdef, hfinvdef]; exact κ.apply_symm_apply z
  have hq : κ.symm q = finv q := by rw [hfinvdef]
  have hd : ∀ x y : N', @dist N' (mN'.rescale R⁻¹ (inv_pos.mpr hR)).toDist x y =
      @dist N (mN.rescale R⁻¹ (inv_pos.mpr hR)).toDist (f x) (f y) := by
    rw [hfdef]
    exact dist_rescale_isometryEquiv mN mN' κ R⁻¹ (inv_pos.mpr hR)
  rw [hq]
  clear hfdef hfinvdef hq
  let mNR := mN.rescale R⁻¹ (inv_pos.mpr hR)
  let mN'R := mN'.rescale R⁻¹ (inv_pos.mpr hR)
  have hball : ∀ x : N', x ∈ @ball N' mN'R.toPseudoMetricSpace (finv q) τ⁻¹ ↔
      f x ∈ @ball N mNR.toPseudoMetricSpace q τ⁻¹ := by
    intro x
    change @dist N' mN'R.toDist x (finv q) < τ⁻¹ ↔ @dist N mNR.toDist (f x) q < τ⁻¹
    rw [hd, hffinv]
  have himg : (fun x => φ.toFun (f x)) '' @ball N' mN'R.toPseudoMetricSpace (finv q) τ⁻¹ =
      φ.toFun '' @ball N mNR.toPseudoMetricSpace q τ⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, (hball x).mp hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨finv z, (hball _).mpr (by rw [hffinv]; exact hz), ?_⟩
      change φ.toFun (f (finv z)) = φ.toFun z
      rw [hffinv]
  exact ⟨@KleinerLottApprox.mk N' C mN'R mC (finv q) o τ
    φ.error_pos φ.error_lt_one (fun x => φ.toFun (f x))
    (by
      rw [hffinv]
      exact φ.basepoint)
    (fun x hx x' hx' => by
      have h := φ.distortion (f x) ((hball x).mp hx) (f x') ((hball x').mp hx')
      change |@dist C mC.toDist (φ.toFun (f x)) (φ.toFun (f x')) -
        @dist N' mN'R.toDist x x'| ≤ τ
      rw [hd]
      exact h)
    (fun y hy => by
      rw [himg]
      exact φ.coverage y hy)⟩

end DifferentialGeometry.Geometry.Collapse
