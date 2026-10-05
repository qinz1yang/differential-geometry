import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Cycle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyTorusApplications

/-!
# Consumers of L1: the unconditional torus assembly (FC42 packet T4b)

Lane ASM-L1b3 (the corollary lane ASM-TOR left for this moment). With L1
(`exists_solidTorus_of_ballHandleCycle_of_rimProduct`) the plain L1 hypothesis of ASM-TOR's torus
assembly is discharged:
* `DecompositionCertificate.nonempty_rawGraphPresentation_of_badVertexCount_eq_zero`
  (verbatim from `build-logs/scratch/ASM-TOR/T4Targets.lean`);
* `DecompositionCertificate.nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero` (the same in
  the induction measure `μ(D) = 0` of N4).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **T4b (torus assembly; the corrected `dry_torusAssembly`)**, unconditional (verbatim from
`build-logs/scratch/ASM-TOR/T4Targets.lean`). -/
theorem nonempty_rawGraphPresentation_of_badVertexCount_eq_zero [Nonempty W.Carrier]
    (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (hprodD : D.RimProduct) :
    Nonempty (RawGraphPresentation W) :=
  D.nonempty_rawGraphPresentation_of_badVertexCount_eq_zero_of_L1 hsph hbad hnz hslim hprodD
    fun C hprod hint => exists_solidTorus_of_ballHandleCycle_of_rimProduct C hprod hint

/-- **The torus assembly in the induction measure** `μ(D) = 0`, unconditional. -/
theorem nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero [Nonempty W.Carrier]
    (hμ : D.sphereMeasure = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (hprodD : D.RimProduct) :
    Nonempty (RawGraphPresentation W) :=
  D.nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero_of_L1 hμ hnz hslim hprodD
    fun C hprod hint => exists_solidTorus_of_ballHandleCycle_of_rimProduct C hprod hint

end DecompositionCertificate

end GC.GraphManifold.Assembly
