import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ComponentDisk

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Extinction.Width
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] in
theorem differential_subtypeVal (U : TopologicalSpace.Opens Q)
    (v : SmoothDisk (I := I) (Q := U)) (u : SmoothDisk (I := I) (Q := Q))
    (hmap : ∀ z, u.map z = (v.map z : Q)) (z : Disk) (X : ℂ) :
    (v.differential z X : E) = (u.differential z X : E) := by
  have hext : diskExtension u.map = Subtype.val ∘ diskExtension v.map := by
    rw [show (u.map : Disk → Q) = (fun z => (v.map z : Q)) from funext hmap]
    exact diskExtension_subtypeVal U v.map
  have hv : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (diskExtension v.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) :=
    (v.contMDiffOn_extension z z.2).mdifferentiableWithinAt (by simp)
  have hd := mfderivWithin_subtypeVal U (diskExtension v.map)
    (Metric.closedBall (0 : ℂ) 1) (z : ℂ) hv
    (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt
  change mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension v.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X =
    mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X
  rw [hext, hd]
  rfl


theorem conformal_subtypeVal (g : SmoothRiemannianMetric I Q)
    (U : TopologicalSpace.Opens Q)
    (v : SmoothDisk (I := I) (Q := U)) (u : SmoothDisk (I := I) (Q := Q))
    (hmap : ∀ z, u.map z = (v.map z : Q)) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    v.IsConformal (g.restrictOpen U) ↔ u.IsConformal g := by
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  have hd := differential_subtypeVal U v u hmap
  unfold SmoothDisk.IsConformal
  have hi (z : Disk) (X Y : ℂ) :
      (g.restrictOpen U).inner (v.map z) (v.differential z X) (v.differential z Y) =
      g.inner (u.map z) (u.differential z X) (u.differential z Y) := by
    change g.inner (v.map z : Q) (v.differential z X) (v.differential z Y) = _
    rw [hd z X, hd z Y, hmap z]
  simp only [hi]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
