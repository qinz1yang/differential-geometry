import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Schauder

variable {iota E F : Type*} {l : Filter iota} [NeBot l]
  [TopologicalSpace F] [T2Space F]

theorem initial_condition_on_of_tendsto
    {uApprox : iota → ParabolicPoint E → F} {u : ParabolicPoint E → F}
    {initialApprox : iota → E → F} {initial : E → F}
    {initialTime : Real} {Omega : Set E}
    (hu : ∀ x ∈ Omega, Tendsto (fun k ↦ uApprox k (parabolicPoint initialTime x)) l
      (nhds (u (parabolicPoint initialTime x))))
    (hinitial : ∀ x ∈ Omega, Tendsto (fun k ↦ initialApprox k x) l (nhds (initial x)))
    (hcondition : ∀ᶠ k in l, ∀ x ∈ Omega,
      uApprox k (parabolicPoint initialTime x) = initialApprox k x) :
    ∀ x ∈ Omega, u (parabolicPoint initialTime x) = initial x := by
  intro x hx
  apply tendsto_nhds_unique (hu x hx)
  exact (hinitial x hx).congr' (hcondition.mono fun _ h ↦ (h x hx).symm)

theorem boundary_condition_on_of_tendsto
    {boundary : Set (ParabolicPoint E)}
    {uApprox boundaryApprox : iota → ParabolicPoint E → F}
    {u boundaryData : ParabolicPoint E → F}
    (hu : ∀ p ∈ boundary, Tendsto (fun k ↦ uApprox k p) l (nhds (u p)))
    (hboundary : ∀ p ∈ boundary,
      Tendsto (fun k ↦ boundaryApprox k p) l (nhds (boundaryData p)))
    (hcondition : ∀ᶠ k in l, Set.EqOn (uApprox k) (boundaryApprox k) boundary) :
    Set.EqOn u boundaryData boundary := by
  intro p hp
  apply tendsto_nhds_unique (hu p hp)
  exact (hboundary p hp).congr' (hcondition.mono fun _ h ↦ (h hp).symm)

end DifferentialGeometry.Analysis.Parabolic

end
