import DifferentialGeometry.Geometry.Metric.Sphere.IsometryRepresentation
import DifferentialGeometry.Topology.Covering.DeckDiffeomorph

set_option autoImplicit false
noncomputable section

open Bundle Manifold Metric Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

private theorem tangent_cast_equiv_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {z z' : M} (h : z = z') (D : V ≃L[ℝ] TangentSpace I z) (v w : V) :
    g.inner z (D v) (D w) = g.inner z' ((h ▸ D) v) ((h ▸ D) w) := by
  cases h
  rfl

private theorem tangent_cast_equiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {z z' : M} (h : z = z') (D : V ≃L[ℝ] TangentSpace I z) (v : V) :
    D v = (h ▸ D) v := by
  cases h
  rfl

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (finrank ℝ A = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem exists_coveringDeckGroup_apply_eq_of_roundMetric
    (hn : 0 < n) {p : sphere (0 : A) 1 → M}
    (g : SmoothRiemannianMetric I M)
    (hp : IsLocalDiffeomorph (𝓡 n) I ∞ p)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      (roundMetric (E := A) (n := n)).inner x v w =
        g.inner (p x) (mfderiv (𝓡 n) I p x v) (mfderiv (𝓡 n) I p x w))
    {x y : sphere (0 : A) 1} (hxy : p x = p y) :
    ∃ gamma : coveringDeckGroup p, gamma • x = y := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hfr : 1 < finrank ℝ A := by
    rw [show finrank ℝ A = n + 1 from Fact.out]
    omega
  let _ : PreconnectedSpace (sphere (0 : A) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank hfr) 0 1)
  let D (z : sphere (0 : A) 1) := hp.mfderivToContinuousLinearEquiv (by simp) z
  let Dy : TangentSpace (𝓡 n) y ≃L[ℝ] TangentSpace I (p x) := hxy.symm ▸ D y
  let L : TangentSpace (𝓡 n) x ≃L[ℝ] TangentSpace (𝓡 n) y :=
    (D x).trans Dy.symm
  have hL : ∀ v w,
      (roundMetric (E := A) (n := n)).inner y (L v) (L w) =
        (roundMetric (E := A) (n := n)).inner x v w := by
    intro v w
    rw [hmetric y, hmetric x]
    have hv : Dy (L v) = D x v := Dy.apply_symm_apply _
    have hw : Dy (L w) = D x w := Dy.apply_symm_apply _
    have heval : g.inner (p y) (D y (L v)) (D y (L w)) =
        g.inner (p x) (Dy (L v)) (Dy (L w)) := by
      exact tangent_cast_equiv_inner g hxy.symm (D y) (L v) (L w)
    change g.inner (p y) (D y (L v)) (D y (L w)) = _
    rw [heval, hv, hw]
    rfl
  obtain ⟨e, he, hde⟩ := ambient_iso_of_tan x y L hL
  let phi := sphereDiffeo (n := n) e
  have hphi : phi x = y := Subtype.ext he
  have hcomp : p ∘ phi = p := by
    apply Riemannian.localIso_rigid (roundMetric (E := A) (n := n)) g
      (isLocalDiffeomorph_comp hp phi.isLocalDiffeomorph) hp (p := x)
    · intro z v w
      rw [mfderiv_comp_apply z (hp.contMDiff.mdifferentiableAt (by simp))
        (phi.contMDiff.mdifferentiableAt (by simp)),
        mfderiv_comp_apply z (hp.contMDiff.mdifferentiableAt (by simp))
        (phi.contMDiff.mdifferentiableAt (by simp))]
      change (roundMetric (E := A) (n := n)).inner z v w =
        g.inner (p (phi z))
          (mfderiv (𝓡 n) I p (phi z) (mfderiv (𝓡 n) (𝓡 n) phi z v))
          (mfderiv (𝓡 n) I p (phi z) (mfderiv (𝓡 n) (𝓡 n) phi z w))
      rw [← hmetric]
      exact (roundInner_sphereDiffeo e z v w).symm
    · exact hmetric
    · exact (congrArg p hphi).trans hxy.symm
    · ext v
      rw [mfderiv_comp_apply x (hp.contMDiff.mdifferentiableAt (by simp))
        (phi.contMDiff.mdifferentiableAt (by simp)), hphi]
      change mfderiv (𝓡 n) I p y
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v) =
          mfderiv (𝓡 n) I p x v
      rw [hde]
      have hd : Dy (L v) = D x v := Dy.apply_symm_apply _
      have hraw : D y (L v) = Dy (L v) := by
        exact tangent_cast_equiv_apply hxy.symm (D y) (L v)
      exact hraw.trans hd
  exact ⟨⟨phi.toEquiv, phi.contMDiff.continuous,
    phi.symm.contMDiff.continuous, congrFun hcomp⟩, hphi⟩

theorem isQuotientCoveringMap_coveringDeckGroup_of_roundMetric
    (hn : 0 < n) {p : sphere (0 : A) 1 → M}
    (g : SmoothRiemannianMetric I M)
    (hp : IsLocalDiffeomorph (𝓡 n) I ∞ p) (hsurj : Function.Surjective p)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      (roundMetric (E := A) (n := n)).inner x v w =
        g.inner (p x) (mfderiv (𝓡 n) I p x v) (mfderiv (𝓡 n) I p x w)) :
    IsQuotientCoveringMap p (coveringDeckGroup p) := by
  have hfr : 1 < finrank ℝ A := by
    rw [show finrank ℝ A = n + 1 from Fact.out]
    omega
  let _ : PreconnectedSpace (sphere (0 : A) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank hfr) 0 1)
  exact isQuotientCoveringMap_coveringDeckGroup_of_fiber_transitive
    (isLocalHomeomorph_iff_isCoveringMap.mp hp.isLocalHomeomorph) hsurj
    (fun hxy => exists_coveringDeckGroup_apply_eq_of_roundMetric hn g hp hmetric hxy.symm)

end DifferentialGeometry.Geometry
