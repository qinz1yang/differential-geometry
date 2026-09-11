import DifferentialGeometry.Topology.Homology.SmallSubspaceInclusion



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}



def integralSmallRelativeChains (U : ι → Set X) (i : ι) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (integralSingularChainToSmall U i)


def integralSmallRelativeSequence (U : ι → Set X) (i : ι) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChainToSmall U i) (cokernel.π _) (cokernel.condition _)


theorem integralSmallRelativeSequence_shortExact (U : ι → Set X) (i : ι) :
    (integralSmallRelativeSequence U i).ShortExact where
  exact := (integralSmallRelativeSequence U i).exact_of_g_is_cokernel (cokernelIsCokernel _)
  mono_f := integralSingularChainToSmall_mono U i
  epi_g := inferInstanceAs (Epi (cokernel.π (integralSingularChainToSmall U i)))



def integralSmallRelativeComparison (U : ι → Set X) (i : ι) :
    integralSmallRelativeChains U i ⟶ integralRelativeChains (U i) :=
  cokernel.map _ _ (𝟙 _) (integralSingularSmallInclusion U)
    (by rw [integralSingularChainToSmall_inclusion, Category.id_comp])


def integralSmallRelativeSequenceComparison (U : ι → Set X) (i : ι) :
    integralSmallRelativeSequence U i ⟶ integralRelativeChainSequence (U i) where
  τ₁ := 𝟙 _
  τ₂ := integralSingularSmallInclusion U
  τ₃ := integralSmallRelativeComparison U i
  comm₁₂ := by
    change (𝟙 _) ≫ integralSingularChainMap (singularSubspaceInclusion (U i)) =
      integralSingularChainToSmall U i ≫ integralSingularSmallInclusion U
    rw [Category.id_comp, integralSingularChainToSmall_inclusion]
  comm₂₃ := (cokernel.π_desc _ _ _).symm



theorem integralSmallRelativeComparison_quasiIso (U : ι → Set X) (i : ι)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, x ∈ U j) :
    QuasiIso (integralSmallRelativeComparison U i) := by
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (integralSmallRelativeSequenceComparison U i)
    (integralSmallRelativeSequence_shortExact U i)
    (integralRelativeChainSequence_shortExact (U i))
    (inferInstanceAs (QuasiIso (𝟙 (integralSingularChains (U i)))))
    (integralSingularSmallInclusion_quasiIso U hU hcover)



def integralSmallRelativeHomologyIso (n : ℕ) (U : ι → Set X) (i : ι)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, x ∈ U j) :
    (integralSmallRelativeChains U i).homology n ≅ integralRelativeHomology n (U i) := by
  letI := integralSmallRelativeComparison_quasiIso U i hU hcover
  exact asIso (HomologicalComplex.homologyMap (integralSmallRelativeComparison U i) n)

end DifferentialGeometry.Topology
