import DifferentialGeometry.Topology.ThreeManifold.AntipodalSphereBall
import DifferentialGeometry.Topology.Covering.AntipodalSphereLift
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

theorem exists_ball_chart_of_antipodal_quotient_sphere_embedding
    (p : S3 → M) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (e : S2 → M) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ G.source ∧ G '' sphere (0 : E3) 1 = range e := by
  obtain ⟨f, hf, hpf, _, hdisj, _⟩ :=
    DifferentialGeometry.Topology.exists_smooth_sphere_lift_disjoint_antipodal
      p hp honto hfib e he
  obtain ⟨B, hB, hBs, hBB⟩ := exists_ball_chart_disjoint_antipodal_of_sphere_embedding f hf hdisj
  let K := B '' closedBall (0 : E3) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hne : K.Nonempty := (nonempty_closedBall.mpr zero_le_one).image B
  have hinj : InjOn p K := by
    intro x hx y hy hxy
    rcases (hfib x y).mp hxy with h | h
    · exact h
    · have heq : x = -y := Subtype.ext h
      exact False.elim (hBB.le_bot ⟨hx, y, hy, heq.symm⟩)
  obtain ⟨P, hP, hPeq⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
      (show IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ p K from fun x => hp x.val)
      hK hne hinj
  let G := B.trans P
  have hGs : closedBall (0 : E3) 1 ⊆ G.source := by
    intro x hx
    exact ⟨hB hx, hP (mem_image_of_mem B hx)⟩
  refine ⟨G, hGs, ?_⟩
  change (P ∘ B) '' sphere (0 : E3) 1 = range e
  rw [image_comp, hBs]
  change P.toFun '' range f = range e
  rw [hPeq, ← range_comp]
  exact congrArg range (funext hpf)

end DifferentialGeometry.Topology.ThreeManifold
