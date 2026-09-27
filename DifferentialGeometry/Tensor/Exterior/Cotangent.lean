import DifferentialGeometry.Tensor.Exterior.Basic

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter FiberBundle
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def ofCotangent
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x))) :
    DifferentialForm I M 1 :=
  ⟨fun x => ContinuousAlternatingMap.ofSubsingleton Real (TangentSpace I x) Real
      (0 : Fin 1) (theta x), by
    intro x₀
    let ea := trivializationAt (E [⋀^Fin 1]→L[Real] Real)
      (Bundle.continuousAlternatingMap Real (Fin 1) E (TangentSpace I) Real
        (Bundle.Trivial M Real)) x₀
    let ec := trivializationAt (E →L[Real] Real)
      (fun x : M => TangentSpace I x →L[Real] Real) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff ea
      (mem_baseSet_trivializationAt (E [⋀^Fin 1]→L[Real] Real)
        (Bundle.continuousAlternatingMap Real (Fin 1) E (TangentSpace I) Real
          (Bundle.Trivial M Real)) x₀)]
    have hc : ContMDiffAt I 𝓘(Real, E →L[Real] Real) ∞
        (fun x : M => (ec ⟨x, theta x⟩).2) x₀ :=
      (Bundle.Trivialization.contMDiffAt_section_iff ec
        (mem_baseSet_trivializationAt (E →L[Real] Real)
          (fun x : M => TangentSpace I x →L[Real] Real) x₀)).mp (htheta x₀)
    let L := (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := Real) (E := E) (F := Real) (0 : Fin 1)).toLinearIsometry.toContinuousLinearMap
    have hL : ContDiff Real ∞ L := L.contDiff
    have hcomp : ContMDiffAt I 𝓘(Real, E [⋀^Fin 1]→L[Real] Real) ∞
        (fun x : M => L ((ec ⟨x, theta x⟩).2)) x₀ :=
      hL.contMDiff.contMDiffAt.comp x₀ hc
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [ea.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt (E [⋀^Fin 1]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin 1) E (TangentSpace I) Real
            (Bundle.Trivial M Real)) x₀),
      ec.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt (E →L[Real] Real)
          (fun x : M => TangentSpace I x →L[Real] Real) x₀)] with x hxa hxc
    rw [continuousAlternatingMap_trivializationAt_apply]
    ext v
    rw [hom_trivializationAt_apply]
    simp [L, ContinuousLinearMap.inCoordinates]
  ⟩

@[simp]
theorem ofCotangent_apply
    (theta : ∀ x : M, TangentSpace I x →L[Real] Real)
    (htheta : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun x : M => TotalSpace.mk' (E →L[Real] Real) x (theta x)))
    (x : M) (v : Fin 1 → TangentSpace I x) :
    ofCotangent theta htheta x v = theta x (v 0) := rfl

end DifferentialForm
end DifferentialGeometry
