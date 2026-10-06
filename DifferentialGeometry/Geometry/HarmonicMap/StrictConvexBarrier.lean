import DifferentialGeometry.Geometry.HarmonicMap.ConvexBarrier
import DifferentialGeometry.Geometry.Operator.Hessian.Positivity
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold
open DifferentialGeometry.Geometry.Operator
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem mfderiv_eq_zero_of_hessian_pos_contact
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {U : ℂ → M} {D : Set ℂ} {C : ℝ}
    (hD : IsOpen D) (hU : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U D)
    (hτ : ∀ z ∈ D, planarTension g U z = 0)
    (hle : ∀ z ∈ D, f (U z) ≤ C)
    {z : ℂ} (hz : z ∈ D) (hcontact : f (U z) = C)
    (hH : ∀ v : TangentSpace I (U z), v ≠ 0 → 0 < hessFun g f (U z) v v) :
    mfderiv 𝓘(ℝ, ℂ) I U z = 0 := by
  have hUz : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U z :=
    hU.contMDiffAt (hD.mem_nhds hz)
  have hmax : IsLocalMax (f ∘ U) z := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (hle y hy).trans_eq hcontact.symm
  have hΔ := DifferentialGeometry.Analysis.laplacian_nonpos_of_localMax
    (((hf.contMDiffAt.of_le (by simp)).comp z hUz).contDiffAt) hmax
  rw [laplacian_comp_of_planarTension_eq_zero g hf hUz (hτ z hz)] at hΔ
  have hnonneg (v : TangentSpace I (U z)) : 0 ≤ hessFun g f (U z) v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (hH v hv).le
  have hOne : mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ) = 0 := by
    by_contra hne
    have hp := hH (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) hne
    linarith [hnonneg (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)]
  have hI : mfderiv 𝓘(ℝ, ℂ) I U z Complex.I = 0 := by
    by_contra hne
    have hp := hH (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) hne
    linarith [hnonneg (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))]
  have hlinear : (mfderiv 𝓘(ℝ, ℂ) I U z).toLinearMap = 0 := by
    apply Complex.basisOneI.ext
    intro i
    fin_cases i
    · change mfderiv 𝓘(ℝ, ℂ) I U z (Complex.basisOneI 0) = 0
      simpa using hOne
    · change mfderiv 𝓘(ℝ, ℂ) I U z (Complex.basisOneI 1) = 0
      simpa using hI
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : ℂ →ₗ[ℝ] TangentSpace I (U z) => L v) hlinear

/-- A weakly confined harmonic map with finitely many critical points on each compact
interior set stays strictly below a level whose Hessian is positive at every contact. -/
theorem lt_of_planarTension_eq_zero_of_hessian_pos_of_finite_critical_set
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {U : ℂ → M} {D : Set ℂ} {C : ℝ}
    (hD : IsOpen D) (hU : ContMDiffOn 𝓘(ℝ, ℂ) I 2 U D)
    (hτ : ∀ z ∈ D, planarTension g U z = 0)
    (hle : ∀ z ∈ D, f (U z) ≤ C)
    (hH : ∀ z ∈ D, f (U z) = C →
      ∀ v : TangentSpace I (U z), v ≠ 0 → 0 < hessFun g f (U z) v v)
    (hfinite : ∀ K : Set ℂ, IsCompact K → K ⊆ D →
      {z ∈ K | mfderiv 𝓘(ℝ, ℂ) I U z = 0}.Finite) :
    ∀ z ∈ D, f (U z) < C := by
  intro x hx
  by_contra! hnot
  have hcontact : f (U x) = C := le_antisymm (hle x hx) hnot
  let P : Set M := {p | ∀ v : TangentSpace I p, v ≠ 0 → 0 < hessFun g f p v v}
  have hP : IsOpen P := by
    simpa only [P, zero_mul] using isOpen_hessFun_gt_mul_inner g hf 0
  have hxP : U x ∈ P := hH x hx hcontact
  have hnear : D ∩ U ⁻¹' P ∈ 𝓝 x :=
    inter_mem (hD.mem_nhds hx)
      ((hU.contMDiffAt (hD.mem_nhds hx)).continuousAt.preimage_mem_nhds
        (hP.mem_nhds hxP))
  obtain ⟨R, hR, hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hRD : closedBall x R ⊆ D := fun _ hz => (hRsub hz).1
  let Z : Set ℂ := {z ∈ closedBall x R | mfderiv 𝓘(ℝ, ℂ) I U z = 0}
  have hZ : Z.Finite := hfinite (closedBall x R) (isCompact_closedBall x R) hRD
  have hbad : IsOpen (Z \ {x})ᶜ := (hZ.subset sdiff_subset).isClosed.isOpen_compl
  have hxnot : x ∈ (Z \ {x})ᶜ := by simp
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (isOpen_ball.mem_nhds (mem_ball_self hR)) (hbad.mem_nhds hxnot))
  have hsmall : closedBall x r ⊆ closedBall x R :=
    fun _ hz => ball_subset_closedBall (hrsub hz).1
  have hrD : closedBall x r ⊆ D := hsmall.trans hRD
  have hpositive (z : ℂ) (hz : z ∈ closedBall x r) :
      ∀ v : TangentSpace I (U z), v ≠ 0 → 0 < hessFun g f (U z) v v := by
    have hp : U z ∈ P := (hRsub (hsmall hz)).2
    exact hp
  have hsphere_strict (z : ℂ) (hz : z ∈ sphere x r) : f (U z) < C := by
    have hzclosed : z ∈ closedBall x r := sphere_subset_closedBall hz
    have hzD : z ∈ D := hrD hzclosed
    by_contra! hle'
    have heq : f (U z) = C := le_antisymm (hle z hzD) hle'
    have hcrit := mfderiv_eq_zero_of_hessian_pos_contact g hf hD hU hτ hle hzD heq
      (hH z hzD heq)
    have hne : z ≠ x := by
      intro heqzx
      subst z
      have hdist := mem_sphere.mp hz
      simp only [dist_self] at hdist
      linarith
    have havoid : z ∉ Z \ {x} := (hrsub hzclosed).2
    apply havoid
    exact ⟨⟨hsmall hzclosed, hcrit⟩, by simpa only [mem_singleton_iff] using hne⟩
  have hqcont : ContinuousOn (f ∘ U) (sphere x r) :=
    hf.continuous.comp_continuousOn
      (hU.continuousOn.mono (sphere_subset_closedBall.trans hrD))
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere x r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hqcont
  have hystrict : f (U y) < C := hsphere_strict y hy
  have hclosure : closure (ball x r) = closedBall x r := closure_ball x hr.ne'
  have hbound := le_boundary_of_planarTension_eq_zero_of_hessian_nonneg
    (U := U) (s := ball x r) (C := f (U y)) g hf
    (by rw [hclosure]; exact isCompact_closedBall x r)
    (by rw [hclosure]; exact hU.continuousOn.mono hrD)
    (by
      intro z hz
      have hzball : z ∈ ball x r := by simpa only [isOpen_ball.interior_eq] using hz
      exact hU.contMDiffAt (hD.mem_nhds (hrD (ball_subset_closedBall hzball))))
    (by
      intro z hz
      have hzball : z ∈ ball x r := by simpa only [isOpen_ball.interior_eq] using hz
      exact hτ z (hrD (ball_subset_closedBall hzball)))
    (by
      intro z hz _ v
      have hzball : z ∈ ball x r := by simpa only [isOpen_ball.interior_eq] using hz
      by_cases hv : v = 0
      · subst v
        simp
      · exact (hpositive z (ball_subset_closedBall hzball) v hv).le)
    (by
      intro z hz
      exact hmax (frontier_ball_subset_sphere hz))
  have hxclosed : x ∈ closure (ball x r) := by
    rw [hclosure]
    exact mem_closedBall_self hr.le
  have hfinal := hbound x hxclosed
  rw [hcontact] at hfinal
  exact (not_le_of_gt hystrict) hfinal

end DifferentialGeometry.Geometry
