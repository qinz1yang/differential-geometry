import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothConnectedSum

universe u v
variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
  {c : OrientedBallChart M} {d : OrientedBallChart N} {a : BoundaryAttachment}
  (s : SmoothConnectedSum c d a)
  {E H P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace P] [ChartedSpace H P]

theorem isLocalDiffeomorphAt_inr_comp
    (f : P → d.Punctured) (x : P)
    (hf : IsLocalDiffeomorphAt I (𝓡 3) ∞ (fun y => (f y).val) x)
    (hx : (f x).val ∈ d.interior) :
    let _ := s.charts
    IsLocalDiffeomorphAt I (𝓡 3) ∞ (ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.val.toHomeomorph ∘ f) x := by
  classical
  let _ := s.charts
  let g : P → d.interior := fun y => if hy : (f y).val ∈ d.interior then ⟨(f y).val, hy⟩ else ⟨(f x).val, hx⟩
  have hnb := hf.contMDiffAt.continuousAt.preimage_mem_nhds (d.interior.isOpen.mem_nhds hx)
  have hg : (fun y => (g y).val) =ᶠ[𝓝 x] (fun y => (f y).val) := by
    filter_upwards [hnb] with y hy
    rw [show g y = ⟨(f y).val, hy⟩ from dif_pos hy]
  have hgl : IsLocalDiffeomorphAt I (𝓡 3) ∞ g x :=
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (fun y => (g y).property)
      (IsLocalDiffeomorphAt.of_eventuallyEq hg hf)
  have hcomp := hgl.comp (K := 𝓡 3) (P := s.toConnectedClosedOrientedManifold.Carrier)
    (s.interiorRight_localDiffeomorph (g x))
  apply IsLocalDiffeomorphAt.of_eventuallyEq _ hcomp
  filter_upwards [hnb] with y hy
  change ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.val.toHomeomorph (f y) =
    ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.val (g y)
  rw [show g y = ⟨(f y).val, hy⟩ from dif_pos hy]
  rfl

theorem isLocalDiffeomorphAt_inl_comp
    (f : P → c.Punctured) (x : P)
    (hf : IsLocalDiffeomorphAt I (𝓡 3) ∞ (fun y => (f y).val) x)
    (hx : (f x).val ∈ c.interior) :
    let _ := s.charts
    IsLocalDiffeomorphAt I (𝓡 3) ∞ (ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.val.toHomeomorph ∘ f) x := by
  classical
  let _ := s.charts
  let g : P → c.interior := fun y => if hy : (f y).val ∈ c.interior then ⟨(f y).val, hy⟩ else ⟨(f x).val, hx⟩
  have hnb := hf.contMDiffAt.continuousAt.preimage_mem_nhds (c.interior.isOpen.mem_nhds hx)
  have hg : (fun y => (g y).val) =ᶠ[𝓝 x] (fun y => (f y).val) := by
    filter_upwards [hnb] with y hy
    rw [show g y = ⟨(f y).val, hy⟩ from dif_pos hy]
  have hgl : IsLocalDiffeomorphAt I (𝓡 3) ∞ g x :=
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (fun y => (g y).property)
      (IsLocalDiffeomorphAt.of_eventuallyEq hg hf)
  have hcomp := hgl.comp (K := 𝓡 3) (P := s.toConnectedClosedOrientedManifold.Carrier)
    (s.interiorLeft_localDiffeomorph (g x))
  apply IsLocalDiffeomorphAt.of_eventuallyEq _ hcomp
  filter_upwards [hnb] with y hy
  change ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.val.toHomeomorph (f y) =
    ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.val (g y)
  rw [show g y = ⟨(f y).val, hy⟩ from dif_pos hy]
  rfl

end DifferentialGeometry.Topology.SmoothConnectedSum
