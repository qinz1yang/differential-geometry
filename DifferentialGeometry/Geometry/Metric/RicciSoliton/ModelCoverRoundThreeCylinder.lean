import DifferentialGeometry.Geometry.Metric.Cylinder.IsometryExtension
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialSplitting
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Rigidity
import DifferentialGeometry.Geometry.Operator.Pullback

set_option autoImplicit false
noncomputable section
open Bundle Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem tangent_cast_equiv_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {z z' : M} (h : z = z') (D : V ≃L[Real] TangentSpace I z) (v w : V) :
    g.inner z (D v) (D w) = g.inner z' ((h ▸ D) v) ((h ▸ D) w) := by
  cases h
  rfl

private theorem tangent_cast_equiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {z z' : M} (h : z = z') (D : V ≃L[Real] TangentSpace I z) (v : V) :
    D v = (h ▸ D) v := by
  cases h
  rfl

private theorem roundThreeCylinderShrinkerMetric_eq_product :
    roundThreeCylinderShrinkerMetric =
      (scaleMetric 2 (by norm_num)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := Real)) := by
  have hs : roundTwoSphereShrinkerMetric =
      scaleMetric 2 (by norm_num)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
      roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
    norm_num
  rw [roundThreeCylinderShrinkerMetric, hs]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem solitonModelCovering_cylinder_hessian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hp : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f p)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    (1 / 2 : Real) * (u.2 * v.2) = Operator.hessFun (I := I) g f (p x)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) I p x u)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) I p x v) := by
  have hh := Operator.hessFun_localPull g p
    (solitonModelCovering_isLocalDiffeomorph hp) f x u v
  rw [← solitonModelCovering_metric_eq_localPull hp] at hh
  have hf : (f : M → Real) ∘ p = roundThreeCylinderShrinkerPotential :=
    (funext (solitonModelCovering_potential hp)).symm
  rw [hf, roundThreeCylinderShrinkerPotential_hessian] at hh
  change (1 / 2 : Real) * (v.2 * u.2) = _ at hh
  simpa only [mul_comm] using hh

theorem exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f p)
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} (hxy : p x = p y) :
    ∃ gamma : coveringDeckGroup p, gamma.1 x = y := by
  let _ : PreconnectedSpace (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  have hp := solitonModelCovering_isLocalDiffeomorph hcover
  let D (z : sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    hp.mfderivToContinuousLinearEquiv (by simp) z
  let Dy : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) y ≃L[Real] TangentSpace I (p x) :=
    hxy.symm ▸ D y
  let L := (D x).trans Dy.symm
  have hD (v) : D y (L v) = D x v :=
    (tangent_cast_equiv_apply hxy.symm (D y) (L v)).trans (Dy.apply_symm_apply _)
  have hL : ∀ u v,
      roundThreeCylinderShrinkerMetric.inner y (L u) (L v) =
        roundThreeCylinderShrinkerMetric.inner x u v := by
    intro u v
    rw [solitonModelCovering_metric hcover, solitonModelCovering_metric hcover]
    have heval : g.inner (p y) (D y (L u)) (D y (L v)) =
        g.inner (p x) (Dy (L u)) (Dy (L v)) :=
      tangent_cast_equiv_inner g hxy.symm (D y) (L u) (L v)
    change g.inner (p y) (D y (L u)) (D y (L v)) = _
    have hu : Dy (L u) = D x u := Dy.apply_symm_apply _
    have hv : Dy (L v) = D x v := Dy.apply_symm_apply _
    rw [heval, hu, hv]
    rfl
  have hsnd : ∀ u v, (L u).2 * (L v).2 = u.2 * v.2 := by
    intro u v
    have hx := solitonModelCovering_cylinder_hessian hcover x u v
    have hy := solitonModelCovering_cylinder_hessian hcover y (L u) (L v)
    change (1 / 2 : Real) * ((L u).2 * (L v).2) =
      Operator.hessFun (I := I) g f (p y) (D y (L u)) (D y (L v)) at hy
    erw [hD, hD, ← hxy] at hy
    change (1 / 2 : Real) * (u.2 * v.2) =
      Operator.hessFun (I := I) g f (p x) (D x u) (D x v) at hx
    linarith [hx, hy]
  obtain ⟨Φ, hΦ, hdΦ, hΦmetric⟩ := exists_diffeomorph_of_round_cylinder_tangent_isometry_preserving_vertical
    2 (by norm_num) x y L (by
      simpa only [← roundThreeCylinderShrinkerMetric_eq_product] using hL) hsnd
  have hΦmetric' : ∀ z u v,
      roundThreeCylinderShrinkerMetric.inner (Φ z)
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real)) Φ z u)
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real)) Φ z v) =
      roundThreeCylinderShrinkerMetric.inner z u v := by
    simpa only [← roundThreeCylinderShrinkerMetric_eq_product] using hΦmetric
  have hcomp : p ∘ Φ = p := by
    apply Riemannian.localIso_rigid roundThreeCylinderShrinkerMetric g
      (isLocalDiffeomorph_comp hp Φ.isLocalDiffeomorph) hp (p := x)
    · intro z u v
      rw [mfderiv_comp_apply z (hp.contMDiff.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp)),
        mfderiv_comp_apply z (hp.contMDiff.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp))]
      exact (hΦmetric' z u v).symm.trans (solitonModelCovering_metric hcover (Φ z) _ _)
    · exact solitonModelCovering_metric hcover
    · exact (congrArg p hΦ).trans hxy.symm
    · ext v
      rw [mfderiv_comp_apply x (hp.contMDiff.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp)), hΦ]
      erw [hdΦ]
      exact hD v
  exact ⟨⟨Φ.toEquiv, Φ.contMDiff.continuous, Φ.symm.contMDiff.continuous, congrFun hcomp⟩, hΦ⟩

theorem solitonModelCovering_roundThreeCylinder_isQuotientCoveringMap
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {p : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential g f p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) := by
  let _ : PreconnectedSpace (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  exact isQuotientCoveringMap_coveringDeckGroup_of_fiber_transitive
    (solitonModelCovering_isCoveringMap hcover) (solitonModelCovering_surjective hcover)
    (fun hxy => exists_coveringDeckGroup_apply_eq_of_solitonModelCovering_roundThreeCylinder hcover hxy.symm)

end DifferentialGeometry.Geometry
