import DifferentialGeometry.Topology.GroupAction.Quotient
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

noncomputable section

open scoped Manifold ContDiff

namespace ContinuousMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]
  {G K : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]
  [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y]
  [ProperlyDiscontinuousSMul G X] [ContinuousConstSMul G X] [IsCancelSMul G X]
  [ProperlyDiscontinuousSMul K Y] [ContinuousConstSMul K Y] [IsCancelSMul K Y]
  {r : ℕ∞ω} [IsManifold I r X] [IsManifold J r Y]
  [ContMDiffConstSMul I r G X] [ContMDiffConstSMul J r K Y]

theorem isLocalDiffeomorph_orbitQuotientMap (f : C(X, Y)) (φ : G → K)
    (heq : ∀ γ x, f (γ • x) = φ γ • f x) (hf : IsLocalDiffeomorph I J r f) :
    IsLocalDiffeomorph I J r (f.orbitQuotientMap φ heq) := by
  let πX := Quotient.mk (MulAction.orbitRel G X)
  have hX := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := G) (M := X) (n := r) I
  have hY := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := K) (M := Y) (n := r) J
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    have hcomp : IsLocalDiffeomorphAt I J r ((f.orbitQuotientMap φ heq) ∘ πX) x :=
      (hf x).comp (K := J) (P := MulAction.orbitRel.Quotient K Y) (hY (f x))
    have hx : (hX x).localInverse (πX x) = x :=
      (hX x).localInverse_left_inv (hX x).localInverse_mem_target
    have hcomp' : IsLocalDiffeomorphAt I J r ((f.orbitQuotientMap φ heq) ∘ πX)
        ((hX x).localInverse (πX x)) := hx.symm ▸ hcomp
    have hlocal := (hX x).localInverse_isLocalDiffeomorphAt.comp (K := J)
      (P := MulAction.orbitRel.Quotient K Y) hcomp'
    refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hlocal
    filter_upwards [(hX x).localInverse_eventuallyEq_right] with y hy
    exact (congrArg (f.orbitQuotientMap φ heq) hy).symm

end ContinuousMap
