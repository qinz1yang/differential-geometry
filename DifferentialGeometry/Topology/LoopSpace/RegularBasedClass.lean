import DifferentialGeometry.Topology.LoopSpace.RegularHomotopyClasses
import DifferentialGeometry.Topology.Homotopy.Map



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M] [Nonempty M]




theorem regularContractibleLoop_homotopyGroupMap_bijective
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (d : ℕ) (q : M) :
    letI : TopologicalSpace (regularContractibleLoop E M) :=
      regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top));
    let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
      ⟨regularContractibleLoopInclusion,
        continuous_regularContractibleLoopInclusion e (he.of_le (by exact_mod_cast le_top)) hemb⟩;
    Bijective (homotopyGroupMap (N := Fin d) inc (regularContractibleLoopConst q)) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
    ⟨regularContractibleLoopInclusion, continuous_regularContractibleLoopInclusion e he₁ hemb⟩
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h r =>
        intro h
        have hc : (inc.comp p.val).HomotopicRel (inc.comp r.val) (Cube.boundary (Fin d)) :=
          Quotient.exact h
        apply Quotient.sound
        exact regular_contractible_homotopicRel_of_continuous g e he hemb hi p.val r.val
          (Cube.boundary (Fin d)) (fun k hk => ⟨q, GenLoop.boundary p k hk⟩) hc
  · intro a
    induction a using Quotient.inductionOn with
    | h p =>
      obtain ⟨S, H, _, hfix⟩ := exists_regular_contractible_representative g e he hemb p.val
      have hSb (k : Fin d → unitInterval) (hk : k ∈ Cube.boundary (Fin d)) :
          S k = regularContractibleLoopConst q := by
        have h := hfix k q (GenLoop.boundary p k hk) 1
        rw [H.apply_one] at h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun γ : contractibleLoop M => γ.val) h
      let r : GenLoop (Fin d) (regularContractibleLoop E M) (regularContractibleLoopConst q) :=
        ⟨S, hSb⟩
      let Hr : p.val.HomotopyRel (inc.comp S) (Cube.boundary (Fin d)) :=
        ⟨H, fun t k hk => (hfix k q (GenLoop.boundary p k hk) t).trans (GenLoop.boundary p k hk).symm⟩
      refine ⟨⟦r⟧, Quotient.sound ?_⟩
      exact ⟨Hr.symm⟩


def regularContractibleLoop_pi2Equiv
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p)) (q : M) :
    letI : TopologicalSpace (regularContractibleLoop E M) :=
      regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top));
    HomotopyGroup (Fin 2) (regularContractibleLoop E M) (regularContractibleLoopConst q) ≃*
      HomotopyGroup (Fin 2) (contractibleLoop M) (ContractibleLoop.constants q) :=
  letI : TopologicalSpace (regularContractibleLoop E M) :=
    regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))
  let inc : C(regularContractibleLoop E M, contractibleLoop M) :=
    ⟨regularContractibleLoopInclusion,
      continuous_regularContractibleLoopInclusion e (he.of_le (by exact_mod_cast le_top)) hemb⟩
  MulEquiv.ofBijective (homotopyGroupMapHom (N := Fin 2) inc (regularContractibleLoopConst q))
    (regularContractibleLoop_homotopyGroupMap_bijective g e he hemb hi 2 q)

end DifferentialGeometry.Topology
