import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarFamilyFinal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint GC.GraphManifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}

theorem region_eq_familyRegion_LTP1 (E : PersistentCuspExterior cores) (t : ℝ)
    (ht : E.start ≤ t) :
    E.region t = familyRegion_LTP1 E.truncation (fun i => cores.map i t (E.after_cores.trans ht)) := by
  unfold PersistentCuspExterior.region familyRegion_LTP1
  rw [dif_pos ht]

theorem range_inclusion_subset_domain_LTP1 (E : PersistentCuspExterior cores) (t : ℝ)
    (ht : E.start ≤ t) (i : Fin cores.count) :
    range (E.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier) :=
  (E.in_ball i t ht).trans (cores.advertised_ball i t (E.after_cores.trans ht))

/-- **P1b.** At every time `t ≥ E.start` all boundary tori of the pushed truncation cores in the
stage `postStage F.observation t` have a common bicollar
`σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) (stage t)` with `ι = Σ i, Fin count_i`,
source `-1 < s < 1`, whose side `s ≥ 0` is exactly the exterior region `E.region t`. -/
theorem exists_bicollar_of_exterior_LTP1 (E : PersistentCuspExterior cores) (t : ℝ)
    (ht : E.start ≤ t) [Nonempty (TorusIdx_LTP1 E.truncation)] :
    ∃ σ : OpenPartialHomeomorph ((TorusIdx_LTP1 E.truncation × Torus) × ℝ)
        (postStage F.observation t).Carrier,
      σ.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      (∀ (j : TorusIdx_LTP1 E.truncation) (z : Torus),
        σ ((j, z), 0) = cores.map j.1 t (E.after_cores.trans ht)
          ((E.truncation j.1).cuspMap j.2 (z, halfZero))) ∧
      (∀ p ∈ σ.source, σ p ∈ E.region t ↔ 0 ≤ p.2) ∧
      IsClosed (E.region t) ∧
      E.region t \ range (fun x : TorusIdx_LTP1 E.truncation × Torus => σ (x, 0)) ⊆
        interior (E.region t) := by
  have hT := E.after_cores.trans ht
  rw [region_eq_familyRegion_LTP1 E t ht]
  exact exists_family_bicollar_LTP1 E.truncation (fun i => (cores.domain i t : Set _))
    (fun i => cores.map i t hT) (fun i => (cores.domain i t).isOpen)
    (fun i => (cores.smooth i t hT).continuousOn)
    (fun i x hx y hy h => by
      have := (cores.embedding i t hT).isEmbedding.injective
        (show (fun x : cores.domain i t => cores.map i t hT x) ⟨x, hx⟩ =
          (fun x : cores.domain i t => cores.map i t hT x) ⟨y, hy⟩ from h)
      exact congrArg Subtype.val this)
    (fun i i' hii => cores.disjoint t hT hii)
    (fun i => range_inclusion_subset_domain_LTP1 E t ht i)

end GC.LongTime.CuspP1
