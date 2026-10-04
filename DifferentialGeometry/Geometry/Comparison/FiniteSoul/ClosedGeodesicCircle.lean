import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicNormal
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The closed geodesic as an embedded circle (S-SOUL2 adapters SA2, SA1)

For a closed unit geodesic `Φ_ℓ p = p`, injective on `[0, ℓ)` (the circle output of S-SHAPE2 /
S-SOUL2):
* SA2 `proj_geodesicFlow_eq_iff_of_closed`, `geodesicFlow_eq_self_iff_of_closed`: return times are
  exactly `ℓ ℤ` (so `ℓ` is the least period, in position and in phase space);
* SA1 `isClosedEmbedding_lift_proj_geodesicFlow`, `exists_homeomorph_addCircle_range_geodesicFlow`:
  the induced map `AddCircle ℓ → M` is a closed embedding and `range γ ≃ₜ AddCircle ℓ`.
Kernels (topology only): `periodic_eq_iff_of_injOn`, `isClosedEmbedding_periodic_lift`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

/-- **Kernel.** Return times of a periodic map injective on one period. -/
theorem periodic_eq_iff_of_injOn {X : Type*} {f : ℝ → X} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hper : Function.Periodic f ℓ) (hinj : InjOn f (Ico 0 ℓ)) {s t : ℝ} :
    f s = f t ↔ ∃ k : ℤ, s - t = k * ℓ := by
  have hred : ∀ x : ℝ, x - (⌊x / ℓ⌋ : ℝ) * ℓ ∈ Ico 0 ℓ := by
    intro x
    have h1 : (⌊x / ℓ⌋ : ℝ) ≤ x / ℓ := Int.floor_le _
    have h2 : x / ℓ < ⌊x / ℓ⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hℓ] at h1
    rw [div_lt_iff₀ hℓ] at h2
    exact ⟨by linarith, by linarith⟩
  constructor
  · intro h
    have h' : f (s - (⌊s / ℓ⌋ : ℝ) * ℓ) = f (t - (⌊t / ℓ⌋ : ℝ) * ℓ) := by
      rw [hper.sub_int_mul_eq, hper.sub_int_mul_eq]; exact h
    have h3 := hinj (hred s) (hred t) h'
    exact ⟨⌊s / ℓ⌋ - ⌊t / ℓ⌋, by push_cast; linarith⟩
  · rintro ⟨k, hk⟩
    rw [show s = t + k * ℓ by linarith]
    exact hper.int_mul k t

/-- **Kernel.** A continuous periodic map into a Hausdorff space, injective on one period,
induces a closed embedding of the circle. -/
theorem isClosedEmbedding_periodic_lift {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : ℝ → X} {ℓ : ℝ} [hℓ : Fact (0 < ℓ)] (hf : Continuous f) (hper : Function.Periodic f ℓ)
    (hinj : InjOn f (Ico 0 ℓ)) : IsClosedEmbedding (hper.lift : AddCircle ℓ → X) := by
  refine Continuous.isClosedEmbedding (hf.quotient_liftOn' _) ?_
  intro a b hab
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [hper.lift_coe, hper.lift_coe] at hab
  obtain ⟨k, hk⟩ := (periodic_eq_iff_of_injOn hℓ.out hper hinj).1 hab
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [zsmul_eq_mul, hk]⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- A closed orbit of the complete geodesic flow is periodic. -/
theorem periodic_geodesicFlow_of_closed
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hD : g.geodesicFlowDomain = univ) {p : TangentBundle I M} {ℓ : ℝ}
    (hper : g.geodesicFlow p ℓ = p) :
    Function.Periodic (fun t => g.geodesicFlow p t) ℓ := fun t => by
  simpa using geodesicFlow_add_int_mul g hr hD hper t 1

/-- **SA2 (positions).** Along a closed unit geodesic injective on `[0, ℓ)`, two times have the
same position iff they differ by a multiple of `ℓ`. -/
theorem proj_geodesicFlow_eq_iff_of_closed
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {s t : ℝ} :
    (g.geodesicFlow p s).proj = (g.geodesicFlow p t).proj ↔ ∃ k : ℤ, s - t = k * ℓ := by
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hP := periodic_geodesicFlow_of_closed g (one_le_two.trans hr) hD hper
  exact periodic_eq_iff_of_injOn (f := fun t => (g.geodesicFlow p t).proj) hℓ
    (fun t => by simp only [hP t]) hinj

/-- **SA2 (phase space).** `ℓ` is the least period of the orbit: `Φ_T p = p` iff `T ∈ ℓ ℤ`. -/
theorem geodesicFlow_eq_self_iff_of_closed
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {T : ℝ} :
    g.geodesicFlow p T = p ↔ ∃ k : ℤ, T = k * ℓ := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hP := periodic_geodesicFlow_of_closed g hr1 hD hper
  have h0 : g.geodesicFlow p 0 = p := g.geodesicFlow_zero hr1 p
  constructor
  · intro h
    have h1 : (g.geodesicFlow p T).proj = (g.geodesicFlow p 0).proj := by rw [h, h0]
    obtain ⟨k, hk⟩ := (proj_geodesicFlow_eq_iff_of_closed g hr hnorm hℓ hper hinj).1 h1
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    have h2 := hP.int_mul k 0
    simp only [zero_add] at h2
    rw [h2, h0]

/-- **SA1.** The closed geodesic is an embedded circle: the induced map `AddCircle ℓ → M` is a
closed embedding. -/
theorem isClosedEmbedding_lift_proj_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} [Fact (0 < ℓ)] (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) :
    ∃ hP : Function.Periodic (fun t => (g.geodesicFlow p t).proj) ℓ,
      IsClosedEmbedding (hP.lift : AddCircle ℓ → M) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hP := periodic_geodesicFlow_of_closed g hr1 hD hper
  have hP' : Function.Periodic (fun t => (g.geodesicFlow p t).proj) ℓ :=
    fun t => by simp only [hP t]
  have hcont : Continuous (fun t => (g.geodesicFlow p t).proj) := by
    refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a hab => ?_⟩
    have h := g.dist_proj_geodesicFlow_le hr1 hnorm (p := p) (s := a) (t := b)
      (fun τ _ => by rw [hD]; exact mem_univ _)
    rw [hunit, Real.sqrt_one, one_mul] at h
    refine h.trans_lt ?_
    rw [abs_sub_comm, ← Real.dist_eq]; exact hab
  exact ⟨hP', isClosedEmbedding_periodic_lift hcont hP' hinj⟩

/-- **SA1 (homeomorphism form).** The trace of a closed unit geodesic injective on `[0, ℓ)` is
homeomorphic to `AddCircle ℓ`, by `t ↦ γ t`. -/
theorem exists_homeomorph_addCircle_range_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} [Fact (0 < ℓ)] (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) :
    ∃ e : AddCircle ℓ ≃ₜ range (fun t => (g.geodesicFlow p t).proj),
      ∀ t : ℝ, (e (t : AddCircle ℓ) : M) = (g.geodesicFlow p t).proj := by
  obtain ⟨hP, hemb⟩ := isClosedEmbedding_lift_proj_geodesicFlow g hr hnorm hunit hper hinj
  have hrange : range (hP.lift : AddCircle ℓ → M) = range (fun t => (g.geodesicFlow p t).proj) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
      exact ⟨s, (hP.lift_coe s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨(s : AddCircle ℓ), hP.lift_coe s⟩
  exact ⟨hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange), fun t => rfl⟩

end DifferentialGeometry.Geometry.FiniteSoul
