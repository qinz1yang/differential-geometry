import DifferentialGeometry.Topology.PiecewiseLinear.Manifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section PLLocal

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

theorem IsPLWithinAt.mono_of_mem_nhdsWithin {f : M → N} {s t : Set M} {x : M}
    (hf : IsPLWithinAt n m f s x) (hts : t ⊆ s) (ht : t ∈ 𝓝[s] x) :
    IsPLWithinAt n m f t x := by
  have h := (piecewiseAffineProperty_localInvariantProp (n := n)
    (m := m)).liftPropWithinAt_inter' (g := f) ht
  rw [inter_eq_right.mpr hts] at h
  exact h.mpr hf

theorem IsPLOn.mono_of_isOpen {f : M → N} {s t : Set M} (hf : IsPLOn n m f s) (ht : IsOpen t)
    (hts : t ⊆ s) : IsPLOn n m f t := fun x hx =>
  IsPLWithinAt.mono_of_mem_nhdsWithin (hf x (hts hx)) hts
    (mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx))

theorem IsPLOn.isPLAt_of_isOpen {f : M → N} {s : Set M} (hf : IsPLOn n m f s) (hs : IsOpen s)
    {x : M} (hx : x ∈ s) : IsPLAt n m f x := by
  have hnb : s ∈ 𝓝[(univ : Set M)] x := by
    rw [nhdsWithin_univ]
    exact hs.mem_nhds hx
  have h := (piecewiseAffineProperty_localInvariantProp (n := n)
    (m := m)).liftPropWithinAt_inter' (g := f) hnb
  rw [univ_inter] at h
  exact h.mp (hf x hx)

theorem IsPL.isPLOn_of_isOpen {f : M → N} (hf : IsPL n m f) {s : Set M} (hs : IsOpen s) :
    IsPLOn n m f s := fun x hx =>
  IsPLWithinAt.mono_of_mem_nhdsWithin (show IsPLWithinAt n m f univ x from hf x) (subset_univ s)
    (by rw [nhdsWithin_univ]; exact hs.mem_nhds hx)

end PLLocal

end DifferentialGeometry.Topology.PiecewiseLinear
