import DifferentialGeometry.Bundle.Section
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

section


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contMDiff_tangentSection_of_contDiff {X : ℝ → E → E}
    (hX : ContDiff ℝ ∞ (fun q : ℝ × E => X q.1 q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle 𝓘(ℝ, E) E)) := by
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × E => X q.1 q.2) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := E),
      chartedSpaceSelf_prod (H := ℝ) (H' := E)]
    exact hX.contMDiff
  intro q
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiffAt_snd :
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => q.2) q)
  · refine hg.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [trivializationAt_model_space_apply]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [SigmaCompactSpace M]
variable {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem contMDiff_assembledLoopFamilySection {ι : Type*} [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ).prod I) (ℝ × M) univ)
    {U : ι → Set (ℝ × M)} (hUo : ∀ i, IsOpen (U i)) (hsub : ρ.IsSubordinate U)
    (Y : ι → ℝ → (p : M) → TangentSpace I p)
    (hY : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M)) (U i)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (∑ i, ρ i q • Y i q.1 q.2) : TangentBundle I M)) := by
  classical
  intro q₀
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => q.2) q₀ :=
    contMDiffAt_snd
  have hsmooth : ∀ i ∈ (Finset.univ : Finset ι),
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (ρ i q • Y i q.1 q.2) : TangentBundle I M)) q₀ := by
    intro i _
    by_cases hi : q₀ ∈ tsupport (fun q : ℝ × M => ρ i q)
    · exact ((ρ i).contMDiff.contMDiffAt).smul_bundle
        ((hY i q₀ (hsub i hi)).contMDiffAt ((hUo i).mem_nhds (hsub i hi)))
    · refine (hbase.zero_bundle (F := E) (V := TangentSpace I)).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hi] with q hq
      simp only [hq, Pi.zero_apply, zero_smul]
  exact hbase.sum_bundle (F := E) (V := TangentSpace I) Finset.univ hsmooth

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

