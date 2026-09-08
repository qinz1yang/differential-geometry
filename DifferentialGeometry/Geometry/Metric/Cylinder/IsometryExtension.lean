import Mathlib.Analysis.Normed.Operator.Prod
import DifferentialGeometry.Geometry.Metric.Sphere.IsometryExtension
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Euclidean

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W]

private theorem prod_linear_snd_zero
    (L : (V × Real) ≃L[Real] (W × Real))
    (hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2) (v : V) :
    (L (v, 0)).2 = 0 := by
  have h := hsnd (v, 0) (v, 0)
  nlinarith

private theorem prod_linear_symm_snd_zero
    (L : (V × Real) ≃L[Real] (W × Real))
    (hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2) (w : W) :
    (L.symm (w, 0)).2 = 0 := by
  have h := hsnd (L.symm (w, 0)) (L.symm (w, 0))
  rw [L.apply_symm_apply] at h
  nlinarith

private def prodLinearHorizontal
    (L : (V × Real) ≃L[Real] (W × Real))
    (hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2) : V ≃L[Real] W where
  toFun v := (L (v, 0)).1
  invFun w := (L.symm (w, 0)).1
  left_inv v := by
    have h := L.symm_apply_apply (v, 0)
    have hz := prod_linear_snd_zero L hsnd v
    have hpair : ((L (v, 0)).1, 0) = L (v, 0) := Prod.ext rfl hz.symm
    dsimp only
    rw [hpair]
    exact congrArg Prod.fst h
  right_inv w := by
    have h := L.apply_symm_apply (w, 0)
    have hz := prod_linear_symm_snd_zero L hsnd w
    have hpair : ((L.symm (w, 0)).1, 0) = L.symm (w, 0) := Prod.ext rfl hz.symm
    dsimp only
    rw [hpair]
    exact congrArg Prod.fst h
  map_add' v w := by
    have h := congrArg Prod.fst (L.map_add (v, 0) (w, 0))
    simpa using h
  map_smul' a v := by
    have h := congrArg Prod.fst (L.map_smul a (v, 0))
    simpa using h
  continuous_toFun := continuous_fst.comp (L.continuous.comp
    (continuous_id.prodMk continuous_const))
  continuous_invFun := continuous_fst.comp (L.symm.continuous.comp
    (continuous_id.prodMk continuous_const))

private theorem prod_linear_isometry_splitting
    (b : V →L[Real] V →L[Real] Real) (c : W →L[Real] W →L[Real] Real)
    (hc : ∀ w : W, w ≠ 0 → 0 < c w w)
    (L : (V × Real) ≃L[Real] (W × Real))
    (hmetric : ∀ u v, c (L u).1 (L v).1 + (L u).2 * (L v).2 =
      b u.1 v.1 + u.2 * v.2)
    (hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2) :
    ∃ A : V ≃L[Real] W, ∃ ε : Real,
      (ε = 1 ∨ ε = -1) ∧
      (∀ v s, L (v, s) = (A v, ε * s)) ∧
      ∀ v w, c (A v) (A w) = b v w := by
  let A := prodLinearHorizontal L hsnd
  let ε := (L (0, 1)).2
  have heps : ε = 1 ∨ ε = -1 := by
    have h := hsnd (0, 1) (0, 1)
    change ε * ε = 1 * 1 at h
    have hfactor : (ε - 1) * (ε + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hvzero : (L (0, 1)).1 = 0 := by
    by_contra hne
    have hpos := hc _ hne
    have h := hmetric (0, 1) (0, 1)
    rw [hsnd] at h
    simp only [map_zero] at h
    linarith
  have hvertical (s : Real) : L (0, s) = (0, ε * s) := by
    have hpair : ((0 : V), s) = s • ((0 : V), (1 : Real)) := by simp
    rw [hpair, map_smul]
    apply Prod.ext
    · simp [hvzero]
    · change s * ε = ε * s
      exact mul_comm _ _
  refine ⟨A, ε, heps, ?_, ?_⟩
  · intro v s
    have hpair : (v, s) = (v, 0) + (0, s) := by simp
    rw [hpair, map_add, hvertical]
    apply Prod.ext
    · change (L (v, 0)).1 + 0 = A v
      exact add_zero _
    · change (L (v, 0)).2 + ε * s = ε * s
      rw [prod_linear_snd_zero L hsnd, zero_add]
  · intro v w
    have h := hmetric (v, 0) (w, 0)
    rw [hsnd] at h
    change c (L (v, 0)).1 (L (w, 0)).1 = b v w
    simpa only [mul_zero, add_zero] using h

end


private def realAffineIsometryDiffeomorph (ε : Real) (hε : ε = 1 ∨ ε = -1) (a b : Real) :
    Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real where
  toFun s := b + ε * (s - a)
  invFun t := a + ε * (t - b)
  left_inv s := by
    rcases hε with rfl | rfl <;> ring
  right_inv t := by
    rcases hε with rfl | rfl <;> ring
  contMDiff_toFun := (contDiff_const.add (contDiff_const.mul
    (contDiff_id.sub contDiff_const))).contMDiff
  contMDiff_invFun := (contDiff_const.add (contDiff_const.mul
    (contDiff_id.sub contDiff_const))).contMDiff

private theorem realAffineIsometryDiffeomorph_mfderiv
    (ε : Real) (hε : ε = 1 ∨ ε = -1) (a b s v : Real) :
    mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (realAffineIsometryDiffeomorph ε hε a b) s v = ε * v := by
  rw [mfderiv_eq_fderiv]
  have h : HasDerivAt (fun s : Real => b + ε * (s - a)) ε s := by
    simpa using (((hasDerivAt_id s).sub_const a).const_mul ε).const_add b
  change (fderiv Real (fun s : Real => b + ε * (s - a)) s) v = _
  rw [h.hasFDerivAt.fderiv]
  simp [mul_comm]

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  {n : Nat} [Fact (Module.finrank Real A = n + 1)]

private theorem round_cylinder_inner (c : Real) (hc : 0 < c)
    (x : Metric.sphere (0 : A) 1 × Real)
    (u v : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x) :
    ((scaleMetric c hc (roundMetric (E := A) (n := n))).prod
      (euclideanMetric (E := Real))).inner x u v =
    c * (roundMetric (E := A) (n := n)).inner x.1 u.1 v.1 + u.2 * v.2 := by
  rw [SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
  change (scaleMetric c hc (roundMetric (E := A) (n := n))).inner x.1 u.1 v.1 +
    (euclideanMetric (E := Real)).inner x.2 u.2 v.2 = _
  erw [scaleMetric_inner]
  have he : (euclideanMetric (E := Real)).inner x.2 u.2 v.2 = u.2 * v.2 := by
    change v.2 * u.2 = u.2 * v.2
    exact mul_comm _ _
  exact congrArg (_ + ·) he

theorem exists_diffeomorph_of_round_cylinder_tangent_isometry_preserving_vertical
    (c : Real) (hc : 0 < c) (x y : Metric.sphere (0 : A) 1 × Real)
    (L : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) x ≃L[Real]
      TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) y)
    (hmetric : ∀ u v,
      ((scaleMetric c hc (roundMetric (E := A) (n := n))).prod
        (euclideanMetric (E := Real))).inner y (L u) (L v) =
      ((scaleMetric c hc (roundMetric (E := A) (n := n))).prod
        (euclideanMetric (E := Real))).inner x u v)
    (hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2) :
    ∃ Φ : (Metric.sphere (0 : A) 1 × Real) ≃ₘ⟮
        (𝓡 n).prod 𝓘(Real, Real), (𝓡 n).prod 𝓘(Real, Real)⟯
        (Metric.sphere (0 : A) 1 × Real),
      Φ x = y ∧
      (∀ u, mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real)) Φ x u = L u) ∧
      ∀ z u v,
        ((scaleMetric c hc (roundMetric (E := A) (n := n))).prod
          (euclideanMetric (E := Real))).inner (Φ z)
          (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real)) Φ z u)
          (mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real)) Φ z v) =
        ((scaleMetric c hc (roundMetric (E := A) (n := n))).prod
          (euclideanMetric (E := Real))).inner z u v := by
  let _ : FiniteDimensional Real A :=
    FiniteDimensional.of_finrank_eq_succ (Fact.out : Module.finrank Real A = n + 1)
  let g := scaleMetric c hc (roundMetric (E := A) (n := n))
  let L' : (TangentSpace (𝓡 n) x.1 × Real) ≃L[Real]
      (TangentSpace (𝓡 n) y.1 × Real) := L
  obtain ⟨B, ε, hε, hL, hB⟩ := prod_linear_isometry_splitting
    (g.inner x.1) (g.inner y.1) (fun w hw => g.pos y.1 w hw) L'
    (by
      intro u v
      have h := hmetric u v
      erw [round_cylinder_inner, round_cylinder_inner] at h
      exact h)
    hsnd
  have hBround : ∀ u v,
      (roundMetric (E := A) (n := n)).inner y.1 (B u) (B v) =
      (roundMetric (E := A) (n := n)).inner x.1 u v := by
    intro u v
    have h := hB u v
    change c * (roundMetric (E := A) (n := n)).inner y.1 (B u) (B v) =
      c * (roundMetric (E := A) (n := n)).inner x.1 u v at h
    exact (mul_left_cancel₀ hc.ne') h
  obtain ⟨e, he, hde⟩ := ambient_iso_of_tan x.1 y.1 B hBround
  let ψ := realAffineIsometryDiffeomorph ε hε x.2 y.2
  let Φ := (sphereDiffeo (n := n) e).prodCongr ψ
  have hΦD (z : Metric.sphere (0 : A) 1 × Real)
      (u : TangentSpace ((𝓡 n).prod 𝓘(Real, Real)) z) :
      mfderiv ((𝓡 n).prod 𝓘(Real, Real)) ((𝓡 n).prod 𝓘(Real, Real)) Φ z u =
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) z.1 u.1, ε * u.2) := by
    change mfderiv _ _ (Prod.map (sphereDiffeo (n := n) e) ψ) z u = _
    rw [mfderiv_prodMap
      ((sphereDiffeo (n := n) e).contMDiff.mdifferentiableAt (by simp))
      (ψ.contMDiff.mdifferentiableAt (by simp))]
    apply Prod.ext
    · rfl
    · exact realAffineIsometryDiffeomorph_mfderiv ε hε x.2 y.2 z.2 u.2
  refine ⟨Φ, ?_, ?_, ?_⟩
  · apply Prod.ext
    · exact Subtype.ext he
    · change y.2 + ε * (x.2 - x.2) = y.2
      ring
  · intro u
    erw [hΦD, hde]
    exact (hL u.1 u.2).symm
  · intro z u v
    rw [round_cylinder_inner, round_cylinder_inner, hΦD, hΦD]
    have hround := roundInner_sphereDiffeo e z.1 u.1 v.1
    change c * (roundMetric (E := A) (n := n)).inner (sphereDiffeo (n := n) e z.1)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) z.1 u.1)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) z.1 v.1) +
      (ε * u.2) * (ε * v.2) = _
    change c * roundInner (n := n) (sphereDiffeo (n := n) e z.1)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) z.1 u.1)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) z.1 v.1) +
      (ε * u.2) * (ε * v.2) = c * roundInner (n := n) z.1 u.1 v.1 + u.2 * v.2
    erw [hround]
    rcases hε with rfl | rfl <;> ring

end DifferentialGeometry.Geometry
