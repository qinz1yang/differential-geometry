import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortAdapterPersistent
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusDecompositionPresentation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- Glue: the `TorusPresentation` of a `DecompositionPresentation` has seam tori equal to the
decomposition seam tori (with `e = id`), so `hseam` of `hglue_of_presentation_CPE2` is automatic
for the presentation supplied by the tree. -/
theorem hseam_of_decompositionPresentation_CPH {M : ConnectedClosedOrientedManifold.{u} 3}
    {D : TorusDecomposition M} (Pr : TorusDecomposition.DecompositionPresentation D) :
    ∀ s : Fin D.boundary.count, ∃ (k : Fin Pr.presentation.pairing.count)
      (e : Torus ≃ₜ Torus), ∀ x, D.reconstructionAtlas.torusInPrime D.reconstruction s x =
        Pr.presentation.seamTorus k (e x) := by
  intro s
  refine ⟨Pr.seamIndex s, Homeomorph.refl _, fun x => ?_⟩
  exact (Pr.seam_zero_eq s x).symm

/-- The cusp torus of port `q` of the `i`-th truncation of a persistent exterior, at time `t`
after its start, as a continuous map into the stage. -/
def portLoopMap_CPH {L : LateCutFamily F K slices} (E : PersistentCuspExterior L.cores)
    (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t) :
    C(Torus, (postStage F.observation t).Carrier) :=
  ⟨fun x => L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).cuspMap q (x, halfZero)), by
    have hc : Continuous fun x : Torus => (E.truncation i).cuspMap q (x, halfZero) := by
      have := ((E.truncation i).cuspEmbedding q).contMDiff.continuous
      exact this.comp (continuous_id.prodMk continuous_const)
    have hmem : ∀ x : Torus, (E.truncation i).cuspMap q (x, halfZero) ∈
        (L.cores.domain i t : Set (L.cores.model i).Carrier) := by
      intro x
      rw [(E.truncation i).cusp_zero q x]
      exact L.cores.advertised_ball i t (E.after_cores.trans ht)
        (E.in_ball i t ht ⟨_, rfl⟩)
    exact (L.cores.smooth i t (E.after_cores.trans ht)).continuousOn.comp_continuous hc hmem⟩

theorem portLoopMap_apply_CPH {L : LateCutFamily F K slices} (E : PersistentCuspExterior L.cores)
    (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t) (x : Torus) :
    portLoopMap_CPH E i q t ht x =
      L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).cuspMap q (x, halfZero)) := rfl

end GC.LongTime.CuspP1
