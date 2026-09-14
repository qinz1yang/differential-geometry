import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreTwoCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MiddleSphereSliceSmoothEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreTubeHalves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonInputReduction

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff ContinuousMap unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

namespace TubeSystem

variable {M : Type u} [TopologicalSpace M] (T : TubeSystem M)

theorem middleSphere_disjoint_puncturedCore (a : T.Index) :
    Disjoint (T.middleSphere a) T.puncturedCore := by
  rw [puncturedCore]
  exact Set.disjoint_left.mpr fun x hx hx' => hx' (Set.mem_iUnion.mpr ⟨a, hx⟩)

theorem puncturedCore_eq_compl_range_union_tubeHalves :
    T.puncturedCore = (⋃ a, range (T.tube a))ᶜ ∪
      ⋃ a, (T.positiveTube a ∪ T.negativeTube a) := by
  ext x
  constructor
  · intro hx
    by_cases hrange : x ∈ ⋃ a, range (T.tube a)
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hrange
      have hne : (T.tubeCoord a x ha).2.1 ≠ 0 := T.tubeCoord_snd_ne_zero hx ha
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr (Set.mem_iUnion.mpr ⟨a, Or.inr ⟨T.tubeCoord a x ha, hlt,
          T.tube_tubeCoord a x ha⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨a, Or.inl ⟨T.tubeCoord a x ha, hgt,
          T.tube_tubeCoord a x ha⟩⟩)
    · exact Or.inl hrange
  · rintro (hx | hx)
    · rw [T.mem_puncturedCore_iff]
      intro a ha
      exact hx (Set.mem_iUnion.mpr ⟨a, T.middleSphere_subset_range a ha⟩)
    · obtain ⟨a, ha | ha⟩ := Set.mem_iUnion.mp hx
      · exact T.positiveTube_subset_puncturedCore a ha
      · exact T.negativeTube_subset_puncturedCore a ha

theorem tubeHalves_inter_puncturedCore (a : T.Index) :
    (T.tubeTop a ∩ T.puncturedCore) ∩ (T.tubeBot a ∩ T.puncturedCore) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  have h1 : x ∈ T.tubeTop a ∩ T.tubeBot a := ⟨hx.1.1, hx.2.1⟩
  rw [T.tubeTop_inter_tubeBot a] at h1
  exact Set.disjoint_left.mp (T.middleSphere_disjoint_puncturedCore a) h1 hx.2.2

theorem puncturedCore_pos_of_mem_tubeHalves_of_mem_tubeTop {a : T.Index} {x : M}
    (hx : x ∈ T.puncturedCore) (htop : x ∈ T.tubeTop a)
    (hhalves : x ∈ T.positiveTube a ∪ T.negativeTube a) : x ∈ T.positiveTube a := by
  rcases hhalves with h | h
  · exact h
  · have ha : x ∈ range (T.tube a) :=
      T.tubeBot_subset_range a (T.negativeTube_subset_tubeBot a h)
    have hle : (T.tubeCoord a x ha).2.1 ≤ 0 :=
      T.nonpos_tubeCoord_of_mem_tubeBot (T.negativeTube_subset_tubeBot a h) ha
    have hne : (T.tubeCoord a x ha).2.1 ≠ 0 := T.tubeCoord_snd_ne_zero hx ha
    have hlt : (T.tubeCoord a x ha).2.1 < 0 := lt_of_le_of_ne hle hne
    have ha' : x ∈ range (T.tube a) := T.tubeTop_subset_range a htop
    have hge : 0 ≤ (T.tubeCoord a x ha').2.1 := T.nonneg_tubeCoord_of_mem_tubeTop htop ha'
    rw [T.tubeCoord_congr a x ha ha'] at hlt
    linarith

private theorem not_pathConnectedSpace_of_isClosed_disjoint_cover {X : Type*} [TopologicalSpace X]
    {P Q : Set X} (hP : IsClosed P) (hQ : IsClosed Q) (hd : Disjoint P Q)
    (hc : P ∪ Q = univ) (hPn : P.Nonempty) (hQn : Q.Nonempty) : ¬ PathConnectedSpace X := by
  have hPeq : P = Qᶜ := by
    ext x
    constructor
    · intro hx
      exact fun hxQ => Set.disjoint_left.mp hd hx hxQ
    · intro hx
      rcases (show x ∈ P ∪ Q from hc ▸ Set.mem_univ x) with h | h
      · exact h
      · exact absurd h hx
  have hQeq : Q = Pᶜ := by
    ext x
    constructor
    · intro hx
      exact fun hxP => Set.disjoint_left.mp hd hxP hx
    · intro hx
      rcases (show x ∈ P ∪ Q from hc ▸ Set.mem_univ x) with h | h
      · exact absurd h hx
      · exact h
  have hPo : IsOpen P := by rw [hPeq]; exact hQ.isOpen_compl
  have hQo : IsOpen Q := by rw [hQeq]; exact hP.isOpen_compl
  intro hpc
  have hpre : IsPreconnected (univ : Set X) :=
    (pathConnectedSpace_iff_univ.mp hpc).isConnected.isPreconnected
  have hne : (univ ∩ P).Nonempty := by rwa [Set.univ_inter]
  have hsub : (univ : Set X) ⊆ P := hpre.subset_left_of_subset_union hPo hQo hd (by rw [hc]) hne
  obtain ⟨y, hy⟩ := hQn
  exact Set.disjoint_left.mp hd (hsub (Set.mem_univ y)) hy

section Obstruction

variable [T2Space M]

theorem not_pathConnectedSpace_of_subset_puncturedTube {a : T.Index}
    {S : Set ↥T.puncturedCore}
    (hS : S ⊆ {u | (u : M) ∈ T.positiveTube a ∪ T.negativeTube a})
    (hp : (S ∩ {u | (u : M) ∈ T.positiveTube a}).Nonempty)
    (hn : (S ∩ {u | (u : M) ∈ T.negativeTube a}).Nonempty) :
    ¬ PathConnectedSpace ↥S := by
  let P : Set ↥S := {u | (u : M) ∈ T.tubeTop a}
  let Q : Set ↥S := {u | (u : M) ∈ T.tubeBot a}
  have hcont : Continuous fun u : ↥S => (u : M) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hP : IsClosed P := by
    have h_eq : P = (fun u : ↥S => (u : M)) ⁻¹' closure (T.positiveTube a) := by
      ext u
      simp only [P, Set.mem_ofPred_eq, Set.mem_preimage, T.closure_positiveTube a]
    rw [h_eq]
    exact isClosed_closure.preimage hcont
  have hQ : IsClosed Q := by
    have h_eq : Q = (fun u : ↥S => (u : M)) ⁻¹' closure (T.negativeTube a) := by
      ext u
      simp only [Q, Set.mem_ofPred_eq, Set.mem_preimage, T.closure_negativeTube a]
    rw [h_eq]
    exact isClosed_closure.preimage hcont
  have hd : Disjoint P Q := by
    rw [Set.disjoint_left]
    intro u huP huQ
    have h1 : (u : M) ∈ T.tubeTop a ∩ T.tubeBot a := ⟨huP, huQ⟩
    rw [T.tubeTop_inter_tubeBot a] at h1
    exact Set.disjoint_left.mp (T.middleSphere_disjoint_puncturedCore a) h1 u.1.2
  have hc : P ∪ Q = univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    rcases hS u.2 with h | h
    · exact Or.inl (T.positiveTube_subset_tubeTop a h)
    · exact Or.inr (T.negativeTube_subset_tubeBot a h)
  obtain ⟨u, huS, huP⟩ := hp
  obtain ⟨v, hvS, hvQ⟩ := hn
  exact not_pathConnectedSpace_of_isClosed_disjoint_cover hP hQ hd hc
    ⟨⟨u, huS⟩, T.positiveTube_subset_tubeTop a huP⟩
    ⟨⟨v, hvS⟩, T.negativeTube_subset_tubeBot a hvQ⟩

theorem not_pathConnectedSpace_puncturedTube (a : T.Index) :
    ¬ PathConnectedSpace ↥({u : ↥T.puncturedCore |
      (u : M) ∈ T.positiveTube a ∪ T.negativeTube a}) := by
  have hy : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp [Sphere, PiLp.norm_single]⟩
  let lp : Set.Icc (-2 : ℝ) 2 := ⟨1, by norm_num, by norm_num⟩
  let ln : Set.Icc (-2 : ℝ) 2 := ⟨-1, by norm_num, by norm_num⟩
  have hpos : T.tube a (hy, lp) ∈ T.positiveTube a := ⟨(hy, lp), by norm_num [lp], rfl⟩
  have hneg : T.tube a (hy, ln) ∈ T.negativeTube a := ⟨(hy, ln), by norm_num [ln], rfl⟩
  have hp : ({u : ↥T.puncturedCore |
      (u : M) ∈ T.positiveTube a ∪ T.negativeTube a} ∩
      {u | (u : M) ∈ T.positiveTube a}).Nonempty :=
    ⟨⟨T.tube a (hy, lp), T.positiveTube_subset_puncturedCore a hpos⟩, Or.inl hpos, hpos⟩
  have hn : ({u : ↥T.puncturedCore |
      (u : M) ∈ T.positiveTube a ∪ T.negativeTube a} ∩
      {u | (u : M) ∈ T.negativeTube a}).Nonempty :=
    ⟨⟨T.tube a (hy, ln), T.negativeTube_subset_puncturedCore a hneg⟩, Or.inr hneg, hneg⟩
  exact T.not_pathConnectedSpace_of_subset_puncturedTube (fun _ h => h) hp hn

theorem not_pathConnectedSpace_puncturedCollar (a : T.Index) {ε : ℝ} (hε : 0 < ε) :
    ¬ PathConnectedSpace ↥({u : ↥T.puncturedCore | (u : M) ∈ T.tube a ''
      {z : TubeDomain | 0 < |(z.2 : ℝ)| ∧ |(z.2 : ℝ)| < ε}}) := by
  have hy : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp [Sphere, PiLp.norm_single]⟩
  have hδpos : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
  have hδlt : min (ε / 2) 1 < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let lp : Set.Icc (-2 : ℝ) 2 := ⟨min (ε / 2) 1, by
    exact ⟨by linarith [min_le_right (ε / 2) 1], by linarith [min_le_right (ε / 2) 1]⟩⟩
  let ln : Set.Icc (-2 : ℝ) 2 := ⟨-(min (ε / 2) 1), by
    exact ⟨by linarith [min_le_right (ε / 2) 1], by linarith [min_le_right (ε / 2) 1]⟩⟩
  have hpos : T.tube a (hy, lp) ∈ T.positiveTube a := ⟨(hy, lp), hδpos, rfl⟩
  have hneg : T.tube a (hy, ln) ∈ T.negativeTube a := ⟨(hy, ln), by dsimp [ln]; linarith, rfl⟩
  have hlp : (lp : ℝ) = min (ε / 2) 1 := rfl
  have hln : (ln : ℝ) = -(min (ε / 2) 1) := rfl
  have hcolpos : T.tube a (hy, lp) ∈ T.tube a ''
      {z : TubeDomain | 0 < |(z.2 : ℝ)| ∧ |(z.2 : ℝ)| < ε} := by
    refine ⟨(hy, lp), ?_, rfl⟩
    change 0 < |(lp : ℝ)| ∧ |(lp : ℝ)| < ε
    rw [hlp, abs_of_pos hδpos]
    exact ⟨hδpos, hδlt⟩
  have hcolneg : T.tube a (hy, ln) ∈ T.tube a ''
      {z : TubeDomain | 0 < |(z.2 : ℝ)| ∧ |(z.2 : ℝ)| < ε} := by
    refine ⟨(hy, ln), ?_, rfl⟩
    change 0 < |(ln : ℝ)| ∧ |(ln : ℝ)| < ε
    rw [hln, abs_neg, abs_of_pos hδpos]
    exact ⟨by linarith, hδlt⟩
  have hp : ({u : ↥T.puncturedCore | (u : M) ∈ T.tube a ''
      {z : TubeDomain | 0 < |(z.2 : ℝ)| ∧ |(z.2 : ℝ)| < ε}} ∩
      {u | (u : M) ∈ T.positiveTube a}).Nonempty :=
    ⟨⟨T.tube a (hy, lp), T.positiveTube_subset_puncturedCore a hpos⟩, hcolpos, hpos⟩
  have hn : ({u : ↥T.puncturedCore | (u : M) ∈ T.tube a ''
      {z : TubeDomain | 0 < |(z.2 : ℝ)| ∧ |(z.2 : ℝ)| < ε}} ∩
      {u | (u : M) ∈ T.negativeTube a}).Nonempty :=
    ⟨⟨T.tube a (hy, ln), T.negativeTube_subset_puncturedCore a hneg⟩, hcolneg, hneg⟩
  refine T.not_pathConnectedSpace_of_subset_puncturedTube ?_ hp hn
  rintro u ⟨z, hz, hzu⟩
  have hz0 : (z.2 : ℝ) ≠ 0 := abs_pos.mp hz.1
  change (u : M) ∈ T.positiveTube a ∪ T.negativeTube a
  rw [← hzu]
  rcases lt_or_gt_of_ne hz0 with hlt | hgt
  · exact Or.inr ⟨z, hlt, rfl⟩
  · exact Or.inl ⟨z, hgt, rfl⟩

end Obstruction

structure MiddleSphereSides (a : T.Index) : Type u where
  A : Set M
  B : Set M
  isOpen_A : IsOpen A
  isOpen_B : IsOpen B
  disjoint : Disjoint A B
  union_eq : A ∪ B = (T.middleSphere a)ᶜ
  positiveTube_subset : T.positiveTube a ⊆ A
  negativeTube_subset : T.negativeTube a ⊆ B

def middleSphereSeparation (T : TubeSystem M) : Prop :=
  ∀ a : T.Index, Nonempty (T.MiddleSphereSides a)

section Sides

variable {T}

theorem puncturedCore_subset_sides {a : T.Index} (H : T.MiddleSphereSides a) :
    T.puncturedCore ⊆ H.A ∪ H.B := by
  intro x hx
  rw [H.union_eq]
  exact fun h => (T.mem_puncturedCore_iff x).mp hx a h

theorem isOpen_preimage_side_A {a : T.Index} (H : T.MiddleSphereSides a) :
    IsOpen ((Subtype.val : ↥T.puncturedCore → M) ⁻¹' H.A) :=
  H.isOpen_A.preimage continuous_subtype_val

theorem isOpen_preimage_side_B {a : T.Index} (H : T.MiddleSphereSides a) :
    IsOpen ((Subtype.val : ↥T.puncturedCore → M) ⁻¹' H.B) :=
  H.isOpen_B.preimage continuous_subtype_val

theorem preimage_side_A_union_preimage_side_B {a : T.Index} (H : T.MiddleSphereSides a) :
    ((Subtype.val : ↥T.puncturedCore → M) ⁻¹' H.A) ∪
      ((Subtype.val : ↥T.puncturedCore → M) ⁻¹' H.B) = univ :=
  Set.eq_univ_of_forall fun u => T.puncturedCore_subset_sides H u.2

theorem preimage_side_A_inter_preimage_side_B {a : T.Index} (H : T.MiddleSphereSides a) :
    ((Subtype.val : ↥T.puncturedCore → M) ⁻¹' H.A) ∩
      ((Subtype.val : ↥T.puncturedCore → M) ⁻¹' H.B) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨u, huA, huB⟩
  exact Set.disjoint_left.mp H.disjoint huA huB

end Sides

private def neckTubeSystem : TubeSystem TubeDomain where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => ContinuousMap.id TubeDomain
  embedding := fun _ => Topology.IsEmbedding.id
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

private theorem neckTubeSystem_middleSphere :
    (neckTubeSystem).middleSphere PUnit.unit = {z : TubeDomain | (z.2 : ℝ) = 0} := by
  simp [TubeSystem.middleSphere, neckTubeSystem]

private theorem neckTubeSystem_positiveTube :
    (neckTubeSystem).positiveTube PUnit.unit = {z : TubeDomain | 0 < (z.2 : ℝ)} := by
  simp [TubeSystem.positiveTube, neckTubeSystem]

private theorem neckTubeSystem_negativeTube :
    (neckTubeSystem).negativeTube PUnit.unit = {z : TubeDomain | (z.2 : ℝ) < 0} := by
  simp [TubeSystem.negativeTube, neckTubeSystem]

private def neckTubeSystemSides : (neckTubeSystem).MiddleSphereSides PUnit.unit where
  A := {z : TubeDomain | 0 < (z.2 : ℝ)}
  B := {z : TubeDomain | (z.2 : ℝ) < 0}
  isOpen_A := isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
  isOpen_B := isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  disjoint := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 : (0 : ℝ) < (z.2 : ℝ) := hz
    have h2 : (z.2 : ℝ) < 0 := hz'
    exact absurd h1 (not_lt.mpr h2.le)
  union_eq := by
    rw [neckTubeSystem_middleSphere]
    ext z
    constructor
    · rintro (h | h)
      · exact fun hz => (ne_of_gt h) hz
      · exact fun hz => (ne_of_lt h) hz
    · intro hz
      have hz' : (z.2 : ℝ) ≠ 0 := fun h => hz h
      rcases lt_or_gt_of_ne hz' with h | h
      · exact Or.inr h
      · exact Or.inl h
  positiveTube_subset := by rw [neckTubeSystem_positiveTube]
  negativeTube_subset := by rw [neckTubeSystem_negativeTube]

private theorem neckTubeSystem_middleSphereSeparation :
    (neckTubeSystem).middleSphereSeparation :=
  fun _ => ⟨neckTubeSystemSides⟩

section CutSystem

variable [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

structure PuncturedCoreCutSystem (c : ConnectedComponents ↥T.core) : Type u where
  n : ℕ
  W : ℕ → Set ↥T.puncturedCore
  L : ℕ → Set ↥T.puncturedCore
  R : ℕ → Set ↥T.puncturedCore
  isOpen_L : ∀ k, IsOpen (L k)
  isOpen_R : ∀ k, IsOpen (R k)
  cover : ∀ k, W k ⊆ L k ∪ R k
  next : ∀ k, W (k + 1) = W k ∩ L k ∨ W (k + 1) = W k ∩ R k
  simplyConnected_overlap : ∀ k, SimplyConnectedSpace ↥(W k ∩ (L k ∩ R k))
  pathConnected_left : ∀ k, PathConnectedSpace ↥(W k ∩ L k)
  pathConnected_right : ∀ k, PathConnectedSpace ↥(W k ∩ R k)
  terminal : W n = T.puncturedCoreComponent c
  base : SimplyConnectedSpace ↥(W 0)

namespace PuncturedCoreCutSystem

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] {T : TubeSystem M} {c : ConnectedComponents ↥T.core}

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
def toCutChain (d : T.PuncturedCoreCutSystem c) : T.PuncturedCoreCutChain c where
  n := d.n
  W := d.W
  L := d.L
  R := d.R
  isOpen_L := d.isOpen_L
  isOpen_R := d.isOpen_R
  cover := d.cover
  next := d.next
  simplyConnected_overlap := d.simplyConnected_overlap
  pathConnected_left := d.pathConnected_left
  pathConnected_right := d.pathConnected_right
  terminal := d.terminal

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem simplyConnectedSpace_puncturedCoreComponent (d : T.PuncturedCoreCutSystem c) :
    SimplyConnectedSpace ↥(T.puncturedCoreComponent c) :=
  T.simplyConnectedSpace_puncturedCoreComponent_of_cutChain d.toCutChain d.base

end PuncturedCoreCutSystem

end CutSystem

end TubeSystem

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem puncturedCoreCutChainProducer_of_isEmpty_index
    [IsEmpty E.trace.tubes.Index] [LocallyConnectedSpace ↥E.trace.tubes.core]
    [SimplyConnectedSpace P.Carrier] : E.PuncturedCoreCutChainProducer := by
  intro c _
  have hsc : SimplyConnectedSpace
      ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :=
    E.trace.tubes.simplyConnectedSpace_puncturedCoreComponent_of_isEmpty_index
      (fun a => E.tube_smooth a) (E.childCoreComponent c)
  exact ⟨TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent E.trace.tubes
    (E.childCoreComponent c) hsc, hsc⟩

def PuncturedCoreCutSystemProducer : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      Nonempty (E.trace.tubes.PuncturedCoreCutSystem (E.childCoreComponent c))

theorem puncturedCoreCutChainProducer_of_cutSystemProducer
    (h : E.PuncturedCoreCutSystemProducer) : E.PuncturedCoreCutChainProducer :=
  fun c hpar => (h c hpar).elim fun d => ⟨d.toCutChain, d.base⟩

theorem puncturedCoreCutSystemProducer_of_middleSphereCuttingSeparation
    (h : E.middleSphereCuttingSeparation) : E.PuncturedCoreCutSystemProducer :=
  fun c hpar =>
    let hsc : SimplyConnectedSpace
        ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) := h c hpar
    let ch := TubeSystem.PuncturedCoreCutChain.ofSimplyConnectedComponent E.trace.tubes
      (E.childCoreComponent c) hsc
    ⟨{ n := ch.n
       W := ch.W
       L := ch.L
       R := ch.R
       isOpen_L := ch.isOpen_L
       isOpen_R := ch.isOpen_R
       cover := ch.cover
       next := ch.next
       simplyConnected_overlap := ch.simplyConnected_overlap
       pathConnected_left := ch.pathConnected_left
       pathConnected_right := ch.pathConnected_right
       terminal := ch.terminal
       base := hsc }⟩

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
