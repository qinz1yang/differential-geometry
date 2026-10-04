import DifferentialGeometry.Geometry.Metric.LipschitzScaleSelectionFinite

/-!
# Finite packet families from a scale selection (LC87, cover and multiplicity fields)

Blueprint row LC87 (`def:collapse-local-export`, master207A) records finite families of local
packets together with the LC86 cover and overlap bound.  This module is the combinatorial step of
the producer: a finite selection `J` of centres (disjoint `a ρ`-balls, `b ρ`-balls covering the
stratum `S`, multiplicity of the `C ρ`-balls at most `N`) and a packet at each selected centre,
whose plateau contains the `b ρ`-ball and whose domain lies in the `C ρ`-ball, are turned into a
family `F : Fin n → Pk` indexed as in LC87, with distinct centres, disjoint selection balls,
plateaus covering `S` and domain multiplicity at most `N`.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- LC87 producer, combinatorial step: a finite scale selection with a packet at each selected
centre gives a `Fin`-indexed packet family with distinct centres, pairwise disjoint selection
balls, plateaus covering `S` and domain multiplicity at most `N`. -/
theorem exists_fin_packet_family_of_selection {Pk : Type*}
    (center : Pk → X) (plateau domain : Pk → Set X) (pk : X → Pk)
    {S J : Set X} {ρ : X → ℝ} {a b C N : ℝ} (hJ : J.Finite)
    (hcenter : ∀ i ∈ J, center (pk i) = i)
    (hdisj : J.PairwiseDisjoint (fun i => ball i (a * ρ i)))
    (hcover : S ⊆ ⋃ i ∈ J, ball i (b * ρ i))
    (hplateau : ∀ i ∈ J, ball i (b * ρ i) ⊆ plateau (pk i))
    (hdomain : ∀ i ∈ J, domain (pk i) ⊆ ball i (C * ρ i))
    (hmult : ∀ x : X, ((J ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤ N) :
    ∃ (n : ℕ) (F : Fin n → Pk), (∀ k, center (F k) ∈ J) ∧
      Function.Injective (fun k => center (F k)) ∧
      Pairwise (fun k l => Disjoint (ball (center (F k)) (a * ρ (center (F k))))
        (ball (center (F l)) (a * ρ (center (F l))))) ∧
      S ⊆ ⋃ k, plateau (F k) ∧
      ∀ x : X, (({k | x ∈ domain (F k)} : Set (Fin n)).ncard : ℝ) ≤ N := by
  classical
  let e := hJ.toFinset.equivFin
  let c : Fin hJ.toFinset.card → X := fun k => (e.symm k).val
  have hcJ (k : Fin hJ.toFinset.card) : c k ∈ J := hJ.mem_toFinset.mp (e.symm k).property
  have hcinj : Function.Injective c := fun k l h => e.symm.injective (Subtype.ext h)
  have hcF (k : Fin hJ.toFinset.card) : center (pk (c k)) = c k := hcenter _ (hcJ k)
  refine ⟨hJ.toFinset.card, fun k => pk (c k), fun k => (hcF k).symm ▸ hcJ k, ?_, ?_, ?_, ?_⟩
  · intro k l h
    simp only [hcF] at h
    exact hcinj h
  · intro k l hkl
    simp only [hcF]
    exact hdisj (hcJ k) (hcJ l) (hcinj.ne hkl)
  · intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hcover hp)
    let k := e ⟨i, hJ.mem_toFinset.mpr hi⟩
    have hk : c k = i := by simp only [c, k, Equiv.symm_apply_apply]
    refine mem_iUnion.mpr ⟨k, ?_⟩
    have h := hplateau i hi hpi
    rwa [← hk] at h
  · intro x
    refine le_trans ?_ (hmult x)
    have hT : (J ∩ {i | x ∈ ball i (C * ρ i)}).Finite := hJ.subset inter_subset_left
    exact_mod_cast ncard_le_ncard_of_injOn (t := J ∩ {i | x ∈ ball i (C * ρ i)}) c
      (fun k hk => ⟨hcJ k, hdomain (c k) (hcJ k) hk⟩) hcinj.injOn hT

end GC.MetricGeometry
