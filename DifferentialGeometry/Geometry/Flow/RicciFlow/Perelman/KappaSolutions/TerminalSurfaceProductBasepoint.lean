import DifferentialGeometry.Geometry.Metric.UniversalCover.Basepoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductModelTransport

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  {a b : M}

private def TerminalSurfaceProduct.changeBasepoint {g : SmoothRiemannianMetric I M}
    (P : let _ : Inhabited M := ⟨a⟩; TerminalSurfaceProduct g)
    (γ : Path.Homotopic.Quotient b a) :
    let _ : Inhabited M := ⟨b⟩; TerminalSurfaceProduct g := by
  let _ : Inhabited M := ⟨a⟩
  let Phi := P.Phi.trans (changeBasepointDiffeomorph I γ)
  have hmetric : Diffeomorph.pullbackMetricCross
      (let _ : Inhabited M := ⟨b⟩; liftedMetric g) Phi =
      P.h.prod (flatModelMetric ℝ) := by
    rw [show Phi = P.Phi.trans (changeBasepointDiffeomorph I γ) from rfl,
      ← Diffeomorph.pullbackMetricCross_trans, pullbackMetric_changeBasepointDiffeomorph]
    exact P.pullbackMetricCross_Phi
  let N := P.S
  let _ : TopologicalSpace N := P.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N := P.charted
  let _ : IsManifold (𝓡 2) ∞ N := P.smooth
  let _ : T2Space N := P.t2
  let _ : SigmaCompactSpace N := P.sigmaCompact
  let _ : ConnectedSpace N := P.connected
  let hN := P.h
  have hc := P.complete
  have hp := P.positive
  let _ : Inhabited M := ⟨b⟩
  refine {
    S := N
    h := hN
    Phi := Phi
    complete := hc
    positive := hp
    product := ?_ }
  intro y s v w u z
  have h := congrArg (fun q : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (N × ℝ) =>
    q.inner (y, s) (v, u) (w, z)) hmetric
  erw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner] at h
  have hflat : (flatModelMetric ℝ).inner s u z = u * z := by
    change inner ℝ u z = u * z
    rw [RCLike.inner_apply]
    simp
    ring
  exact h.trans (congrArg ((hN.inner y v w) + ·) hflat)

theorem nonempty_terminalSurfaceProduct_iff_basepoint [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (a b : M) :
    Nonempty (let _ : Inhabited M := ⟨a⟩; TerminalSurfaceProduct g) ↔
      Nonempty (let _ : Inhabited M := ⟨b⟩; TerminalSurfaceProduct g) := by
  let _ : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  let γ := Path.Homotopic.Quotient.mk (Joined.somePath (PathConnectedSpace.joined b a))
  exact ⟨fun ⟨P⟩ => ⟨P.changeBasepoint γ⟩, fun ⟨P⟩ => ⟨P.changeBasepoint γ.symm⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
