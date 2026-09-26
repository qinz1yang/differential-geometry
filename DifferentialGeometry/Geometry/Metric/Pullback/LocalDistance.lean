import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [IsManifold J ∞ M] [IsManifold I ∞ N] [T2Space N] in
private theorem mfderiv_apply_mfderiv_symm_apply_of_mem_target'
    (e : PartialDiffeomorph I J N M ∞) {x : M} (hx : x ∈ e.target) (v : TangentSpace J x) :
    mfderiv I J e (e.symm x) (mfderiv J I e.symm x v) = v := by
  have hsrc : e.symm x ∈ e.source := e.map_target hx
  have hloc : (fun q => e (e.symm q)) =ᶠ[nhds x] id :=
    Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hx) fun q hq => e.right_inv' hq
  have hcomp := mfderiv_comp x (e.mdifferentiableAt (by decide) hsrc)
    (e.symm.mdifferentiableAt (by decide) hx)
  have h1 : mfderiv J J (fun q => e (e.symm q)) x v =
      mfderiv I J e (e.symm x) (mfderiv J I e.symm x v) :=
    DFunLike.congr_fun hcomp v
  rw [hloc.mfderiv_eq, mfderiv_id] at h1
  exact h1.symm

theorem exists_riemannianEDistOf_localPullMetric_eq_of_ball_subset_range
    (g : SmoothRiemannianMetric J M) {f : N → M} (hf : IsLocalDiffeomorph I J ∞ f)
    (hinj : Function.Injective f) (z : N) {ρ : ℝ}
    (hball : riemannianBallOf g (f z) ρ ⊆ range f) {p : M}
    (hp : riemannianEDistOf g (f z) p < ENNReal.ofReal ρ) :
    ∃ w : N, f w = p ∧
      riemannianEDistOf (localPullMetric g f hf) z w = riemannianEDistOf g (f z) p := by
  obtain ⟨Φ, hs, ht, hΦ⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hf.isLocalDiffeomorphOn univ) isOpen_univ ⟨z, trivial⟩ hinj.injOn
  have hΦf : (Φ : N → M) = f := hΦ
  have hsrc : Φ.source = univ := hs
  have htgt : Φ.target = range f := by rw [← image_univ]; exact ht
  obtain ⟨w, rfl⟩ := hball hp
  refine ⟨w, rfl, le_antisymm ?_ ?_⟩
  · obtain ⟨R, hR0, hlt, hRρ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp
    have hR : 0 < R := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hlt)
    have hsource : riemannianClosedBallOf g (f z) R ⊆ Φ.symm.source := by
      intro x hx
      change x ∈ Φ.target
      rw [htgt]
      exact hball (lt_of_le_of_lt hx hRρ)
    have hupper : ∀ x ∈ riemannianClosedBallOf g (f z) R, ∀ v : TangentSpace J x,
        (localPullMetric g f hf).inner (Φ.symm x) (mfderiv J I (Φ.symm : M → N) x v)
          (mfderiv J I (Φ.symm : M → N) x v) ≤ 1 ^ 2 * g.inner x v v := by
      intro x hx v
      have hxt : x ∈ Φ.target := hsource hx
      have hr : (Φ : N → M) ((Φ.symm : M → N) x) = x := Φ.right_inv' hxt
      rw [localPullMetric_inner, ← hΦf, mfderiv_apply_mfderiv_symm_apply_of_mem_target' Φ hxt,
        hr, one_pow, one_mul]
    have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      g (localPullMetric g f hf) Φ.symm (f z) (f w) hR one_pos hsource hupper hlt
    have hzw : ∀ y : N, (Φ.symm : M → N) (f y) = y := fun y => by
      rw [← hΦf]
      exact Φ.left_inv' (by rw [hsrc]; exact mem_univ y)
    rw [hzw, hzw, ENNReal.ofReal_one, one_mul] at hd
    exact hd
  · by_cases hlt : riemannianEDistOf (localPullMetric g f hf) z w < ENNReal.ofReal ρ
    · have hρ : 0 < ρ := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hlt)
      have hupper : ∀ x ∈ riemannianClosedBallOf (localPullMetric g f hf) z ρ,
          ∀ v : TangentSpace I x, g.inner (Φ x) (mfderiv I J (Φ : N → M) x v)
            (mfderiv I J (Φ : N → M) x v) ≤ 1 ^ 2 * (localPullMetric g f hf).inner x v v := by
        intro x _ v
        rw [localPullMetric_inner, hΦf, one_pow, one_mul]
      have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        (localPullMetric g f hf) g Φ z w hρ one_pos (by rw [hsrc]; exact subset_univ _)
        hupper hlt
      rw [hΦf, ENNReal.ofReal_one, one_mul] at hd
      exact hd
    · exact hp.le.trans (not_lt.mp hlt)

end DifferentialGeometry

end
