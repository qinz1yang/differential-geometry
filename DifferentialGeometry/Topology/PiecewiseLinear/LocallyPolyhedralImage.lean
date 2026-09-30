import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem IsLocallyPolyhedral.image_of_isPLHomeomorphOn {S U : Set E} {V : Set F} {f : E → F}
    (hS : IsLocallyPolyhedral S) (hSU : S ⊆ U) (hf : IsPLHomeomorphOn f U V) :
    IsLocallyPolyhedral (f '' S) := by
  obtain ⟨hbij, hfpl, hginv⟩ := hf
  rintro y ⟨x, hxS, rfl⟩
  obtain ⟨P, hP, hPS, hPnhds⟩ := hS x hxS
  obtain ⟨W, hWopen, hxW, hWS⟩ := mem_nhdsWithin.mp hPnhds
  have hPU : P ⊆ U := hPS.trans hSU
  have himgP : IsPolyhedron (f '' P) :=
    hP.image_of_isPiecewiseAffineOn (hfpl.mono_of_isPolyhedron hP hPU)
      (hbij.injOn.mono hPU)
  refine ⟨f '' P, himgP, Set.image_mono hPS, ?_⟩
  obtain ⟨O, hOopen, hOeq⟩ := continuousOn_iff'.mp hginv.continuousOn W hWopen
  refine mem_nhdsWithin.mpr ⟨O, hOopen, ?_, ?_⟩
  · have hgx : Function.invFunOn f U (f x) = x := hbij.invOn_invFunOn.1 (hSU hxS)
    have hmem : f x ∈ Function.invFunOn f U ⁻¹' W ∩ V := by
      refine ⟨?_, hbij.mapsTo (hSU hxS)⟩
      rw [mem_preimage, hgx]
      exact hxW
    rw [hOeq] at hmem
    exact hmem.1
  · rintro y ⟨hyO, x', hx'S, rfl⟩
    have hx'U : x' ∈ U := hSU hx'S
    have hmem : f x' ∈ O ∩ V := ⟨hyO, hbij.mapsTo hx'U⟩
    rw [← hOeq] at hmem
    have hgx' : Function.invFunOn f U (f x') = x' := hbij.invOn_invFunOn.1 hx'U
    have hx'W : x' ∈ W := by
      have hpre := hmem.1
      rwa [mem_preimage, hgx'] at hpre
    exact ⟨x', hWS ⟨hx'W, hx'S⟩, rfl⟩

theorem IsLocallyPolyhedral.image_invFunOn_of_isPLHomeomorphOn {T : Set F} {U : Set E}
    {V : Set F} {f : E → F} (hT : IsLocallyPolyhedral T) (hTV : T ⊆ V)
    (hf : IsPLHomeomorphOn f U V) :
    IsLocallyPolyhedral (Function.invFunOn f U '' T) :=
  hT.image_of_isPLHomeomorphOn hTV hf.symm

end DifferentialGeometry.Topology.PiecewiseLinear
