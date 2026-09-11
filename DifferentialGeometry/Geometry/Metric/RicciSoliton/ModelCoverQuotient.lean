import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelQuotient
import DifferentialGeometry.Topology.Covering.QuotientDiffeomorph

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
  {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners Real F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [IsCancelSMul G M] [ContMDiffConstSMul I ∞ G M]

omit [LocallyCompactSpace M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] in
theorem solitonModelCovering_smul_metric
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {p : M → N}
    (hπ : solitonModelCovering h Fpot g f p)
    (hp : IsQuotientCoveringMap p G) (gamma : G) :
    Diffeomorph.pullbackMetric h (MulAction.smulDiffeomorph (n := ∞) I gamma) = h := by
  exact (solitonModelCovering_deck_preserves hπ
    (MulAction.smulDiffeomorph (n := ∞) I gamma) (fun x =>
      hp.apply_eq_iff_mem_orbit.mpr ⟨gamma, rfl⟩)).1

omit [LocallyCompactSpace M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [ContMDiffConstSMul I ∞ G M] in
theorem solitonModelCovering_smul_potential
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {p : M → N}
    (hπ : solitonModelCovering h Fpot g f p)
    (hp : IsQuotientCoveringMap p G) (gamma : G) (x : M) :
    Fpot (gamma • x) = Fpot x := by
  rw [solitonModelCovering_potential hπ, solitonModelCovering_potential hπ]
  exact congrArg f (hp.apply_eq_iff_mem_orbit.mpr ⟨gamma, rfl⟩)

theorem solitonModelCovering_quotient_metric
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {p : M → N}
    (hπ : solitonModelCovering h Fpot g f p)
    (hp : IsQuotientCoveringMap p G) :
    Diffeomorph.pullbackMetricCross g
        (hp.orbitRelQuotientDiffeomorph (solitonModelCovering_isLocalDiffeomorph hπ)) =
      solitonModelQuotientMetric h (solitonModelCovering_smul_metric hπ hp) := by
  let q : M → MulAction.orbitRel.Quotient G M := Quotient.mk''
  let e := hp.orbitRelQuotientDiffeomorph (solitonModelCovering_isLocalDiffeomorph hπ)
  have hq := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (n := ∞) (G := G) (M := M) I
  apply localPullMetric_injective_of_surjective q hq Quotient.mk_surjective
  rw [localPullMetric_solitonModelQuotientMetric]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hcomp : (e : MulAction.orbitRel.Quotient G M → N) ∘ q = p := by
    funext y
    exact hp.orbitRelQuotientDiffeomorph_apply _ y
  have hderiv : mfderiv I J e (q x) ∘L mfderiv I I q x = mfderiv I J p x := by
    have hd := mfderiv_comp x
      (e.contMDiff.mdifferentiableAt (by simp)) (hq.contMDiff.mdifferentiableAt (by simp))
    rw [hcomp] at hd
    exact hd.symm
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner]
  change g.inner (e (q x)) (mfderiv I J e (q x) (mfderiv I I q x v))
    (mfderiv I J e (q x) (mfderiv I I q x w)) = h.inner x v w
  have hv := congrArg (fun L => L v) hderiv
  have hw := congrArg (fun L => L w) hderiv
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [hv, hw, show e (q x) = p x from congrFun hcomp x]
  exact (solitonModelCovering_metric hπ x v w).symm

theorem solitonModelCovering_quotient_potential
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯} {p : M → N}
    (hπ : solitonModelCovering h Fpot g f p)
    (hp : IsQuotientCoveringMap p G) :
    f.comp (hp.orbitRelQuotientDiffeomorph
        (solitonModelCovering_isLocalDiffeomorph hπ)).toContMDiffMap =
      solitonModelQuotientPotential Fpot (solitonModelCovering_smul_potential hπ hp) := by
  apply ContMDiffMap.ext
  intro y
  induction y using Quotient.inductionOn with
  | _ x =>
    change f (hp.orbitRelQuotientDiffeomorph _ (Quotient.mk'' x)) = _
    rw [hp.orbitRelQuotientDiffeomorph_apply, solitonModelQuotientPotential_apply]
    exact (solitonModelCovering_potential hπ x).symm

end DifferentialGeometry.Geometry
