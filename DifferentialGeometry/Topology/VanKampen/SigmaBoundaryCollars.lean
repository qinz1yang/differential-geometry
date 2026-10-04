import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# SigmaBoundaryCollars
-/

set_option autoImplicit false
noncomputable section
open Set Function

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {ι X : Type*} {S : ι → Type*}
  [TopologicalSpace X] [∀ i, TopologicalSpace (S i)]
  {e : ∀ i, S i → X}

def sigma (c : ∀ i, TwoSidedCollar (e i))
    (hd : Pairwise fun i j => Disjoint (c i).range (c j).range) :
    TwoSidedCollar (fun s : Σ i, S i => e s.1 s.2) := by
  let φ : (Σ i, S i × ℝ) → X := fun p => (c p.1).toFun p.2
  have hinj : Injective φ := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst j
      exact congrArg (Sigma.mk i) ((c i).isOpenEmbedding_toFun.injective hxy)
    · exact False.elim (disjoint_left.mp (hd hij) ⟨x, rfl⟩ ⟨y, hxy.symm⟩)
  have hφ : _root_.Topology.IsOpenEmbedding φ :=
    .of_continuous_injective_isOpenMap
      (continuous_sigma fun i => (c i).isOpenEmbedding_toFun.continuous) hinj
      (isOpenMap_sigma.mpr fun i => (c i).isOpenEmbedding_toFun.isOpenMap)
  exact {
    toFun := φ ∘ (Homeomorph.sigmaProdDistrib (X := S) (Y := ℝ))
    isOpenEmbedding_toFun := hφ.comp Homeomorph.sigmaProdDistrib.isOpenEmbedding
    zero_eq := fun s => (c s.1).zero_eq s.2 }

theorem sigma_apply (c : ∀ i, TwoSidedCollar (e i))
    (hd : Pairwise fun i j => Disjoint (c i).range (c j).range)
    (i : ι) (s : S i) (t : ℝ) :
    (sigma c hd).toFun (⟨i, s⟩, t) = (c i).toFun (s, t) := rfl

theorem sigma_range (c : ∀ i, TwoSidedCollar (e i))
    (hd : Pairwise fun i j => Disjoint (c i).range (c j).range) :
    (sigma c hd).range = ⋃ i, (c i).range := by
  ext x
  constructor
  · rintro ⟨⟨⟨i, s⟩, t⟩, rfl⟩
    exact mem_iUnion.mpr ⟨i, ⟨(s, t), rfl⟩⟩
  · intro hx
    obtain ⟨i, ⟨⟨s, t⟩, rfl⟩⟩ := mem_iUnion.mp hx
    exact ⟨(⟨i, s⟩, t), rfl⟩

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
