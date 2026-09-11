import DifferentialGeometry.Topology.LoopSpace.Family
import DifferentialGeometry.Topology.LoopSpace.RegularHomotopyClasses



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


def regularLoopFamilyClass (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) : Type _ :=
  letI : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he
  ZerothHomotopy C(familySphere, regularContractibleLoop E M)


def regularLoopFamilyClassInclusion (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e) :
    regularLoopFamilyClass e he → loopFamilyClass M :=
  letI : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he
  let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
    ⟨regularContractibleLoopInclusion, continuous_regularContractibleLoopInclusion e he hemb⟩
  ZerothHomotopy.lift (fun Γ => LoopFamily.classOf (inc.comp Γ))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (continuous_postcomp inc)))

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]



theorem regularLoopFamilyClassInclusion_bijective
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p)) :
    Bijective (regularLoopFamilyClassInclusion e (he.of_le (by exact_mod_cast le_top)) hemb) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
    ⟨regularContractibleLoopInclusion, continuous_regularContractibleLoopInclusion e he₁ hemb⟩
  constructor
  · intro ξ ζ
    induction ξ using ZerothHomotopy.rec with
    | mk Γ =>
      induction ζ using ZerothHomotopy.rec with
      | mk Δ =>
        intro h
        change LoopFamily.classOf (inc.comp Γ) = LoopFamily.classOf (inc.comp Δ) at h
        have hc := (LoopFamily.classOf_eq_iff _ _).mp h
        have hr := regular_contractible_homotopicRel_of_continuous g e he hemb hi Γ Δ ∅
          (fun k hk => False.elim (Set.notMem_empty k hk))
          (ContinuousMap.homotopicRel_empty.mpr hc)
        exact Quotient.sound ((DifferentialGeometry.Topology.homotopic_iff_joined Γ Δ).mp
          (ContinuousMap.homotopicRel_empty.mp hr))
  · intro ξ
    obtain ⟨Γ, hΓ⟩ := LoopFamily.exists_representative ξ
    obtain ⟨S, H, _, _⟩ := exists_regular_contractible_representative g e he hemb Γ
    refine ⟨ZerothHomotopy.mk S, ?_⟩
    change LoopFamily.classOf (inc.comp S) = ξ
    rw [← hΓ]
    exact (LoopFamily.classOf_eq_iff _ _).mpr ⟨H.symm⟩

end DifferentialGeometry.Topology
