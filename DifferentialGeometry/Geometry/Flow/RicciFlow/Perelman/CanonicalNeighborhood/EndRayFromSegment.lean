import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import DifferentialGeometry.Geometry.Metric.Segment

set_option autoImplicit false
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {W : Type*} [MetricSpace W]

theorem exists_endRay_of_isometry_Ico {L : ℝ} (hL : 0 < L) {γ : ℝ → W}
    (hγ : Isometry (fun s : Ico 0 L => γ s)) {f : W → ℝ} (hf : Continuous f)
    (hdiv : Tendsto (f ∘ γ) (𝓝[<] L) atTop) :
    ∃ (E : UniformSpace.Completion W) (a : EndRay E),
      a.length = L ∧ (∀ s, a.point s = γ (L - s)) ∧
      (∀ x : W, (x : UniformSpace.Completion W) ≠ E) := by
  have hcomp : Isometry (fun s : Ico 0 L => (γ s : UniformSpace.Completion W)) :=
    UniformSpace.Completion.coe_isometry.comp hγ
  obtain ⟨E, ⟨hE, hdist⟩, _⟩ := Isometry.exists_endpoint_Ico (X := UniformSpace.Completion W) (γ := fun s => (γ s : UniformSpace.Completion W)) hL hcomp
  have hmem {s : ℝ} (hs : s ∈ Ioc 0 L) : L - s ∈ Ico 0 L := by
    constructor <;> linarith [hs.1, hs.2]
  let a : EndRay E :=
    { length := L
      length_pos := hL
      point := fun s => γ (L - s)
      radial := fun s hs => by simpa only [sub_sub_cancel] using hdist (L - s) (hmem hs)
      minimizing := fun s hs t ht => by
        have h := hγ.dist_eq ⟨L - s, hmem hs⟩ ⟨L - t, hmem ht⟩
        simpa only [Subtype.dist_eq, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm] using h }
  refine ⟨E, a, rfl, fun _ => rfl, ?_⟩
  intro x
  exact (UniformSpace.Completion.ne_coe_of_tendsto_atTop hE hdiv x hf.continuousAt).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
