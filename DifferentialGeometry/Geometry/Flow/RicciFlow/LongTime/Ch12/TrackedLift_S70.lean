import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RmSurvivor_S56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLoss

set_option autoImplicit false

/-!
# CH12-S70 / G1: from forward survival to a smooth survivor lift

If every point `p` of an open set `V ⊆ H.Carrier` is mapped by a smooth `J` into the first stage
`first` of a history and `J p` is the image of a survivor point of the range `[first, last]`, then
the survivor points can be chosen smoothly in `p` (`ContMDiffOn φ V`), with
`backwardSurvivorMap first last hle first (φ p) = J p`.  The lift datum of `hLTF04_lift_k0` is then
`φ` composed with the stage identification `postStage t = stage (activeStage t)`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- Smooth survivor lift on an open set (global-in-`V` form of
`exists_backwardSurvivor_chart_of_point_traces`). -/
theorem exists_lift_on_open_S70 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (first last : Fin (K.eventCount + 1)) (hle : first ≤ last)
    (J : H.Carrier → (K.stage first).Carrier) (V : TopologicalSpace.Opens H.Carrier)
    (hJ : ContMDiffOn (𝓡 3) ThreeModel ∞ J V) (hnon : (V : Set H.Carrier).Nonempty)
    (hA : ∀ p ∈ V, ∃ x : K.backwardSurvivorDomain first last hle,
      K.backwardSurvivorMap first last hle first le_rfl hle x = J p) :
    ∃ φ : H.Carrier → K.backwardSurvivorDomain first last hle,
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧
      ∀ p ∈ V, K.backwardSurvivorMap first last hle first le_rfl hle (φ p) = J p := by
  classical
  choose X hX using hA
  have hJ' : ContMDiff (𝓡 3) ThreeModel ∞ (fun p : V => J p) :=
    hJ.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  obtain ⟨Ξ, hΞ, hΞval, hΞJ, -⟩ := K.exists_backwardSurvivor_chart_of_point_traces first last hle
    (X := V) (I := 𝓡 3) (fun p : V => J p) hJ' (fun p : V => (X p.1 p.2).val)
    (fun p => Classical.choice (X p.1 p.2).property)
    (fun p => hX p.1 p.2)
  obtain ⟨p₀, hp₀⟩ := hnon
  let φ : H.Carrier → K.backwardSurvivorDomain first last hle := fun p =>
    if h : p ∈ V then Ξ ⟨p, h⟩ else Ξ ⟨p₀, hp₀⟩
  have hφV : ∀ x : V, φ x = Ξ x := fun x => dif_pos x.2
  refine ⟨φ, fun p hp => ?_, fun p hp => ?_⟩
  · have h1 : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun x : V => φ x) ⟨p, hp⟩ := by
      have : (fun x : V => φ x) = Ξ := funext hφV
      rw [this]
      exact hΞ.contMDiffAt
    exact (contMDiffAt_subtype_iff.mp h1).contMDiffWithinAt
  · have := hΞJ ⟨p, hp⟩
    rw [← hφV ⟨p, hp⟩] at this
    exact this

end GC.LongTime.Ch12
