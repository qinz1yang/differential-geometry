import DifferentialGeometry.Topology.Manifold.BallEmbedding.Defs
import DifferentialGeometry.Topology.Manifold.DiffeomorphFamily
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingSupport

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def BallEmbeddingAmbientIsotopic (ι : Type u) (U : Type u) [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o) : Prop :=
  ∃ H : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞,
    H 0 = Diffeomorph.refl ThreeModel U ∞ ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => H q.1 q.2) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (H q.1).symm q.2) ∧
    ∃ K : Set U, IsCompact K ∧
      (∀ t, Set.EqOn (H t) (id : U → U) Kᶜ) ∧
      (∀ t, Set.EqOn (H t).symm (id : U → U) Kᶜ) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ i : ι, ∀ x : ThreeSpace,
        x ∈ Metric.closedBall 0 r → H 1 ((e i).chart x) = (e' i).chart x

def SupportedBallEmbeddingIsotopy (ι : Type u) (U : Type u) [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o) : Prop :=
  ∃ (J : ι → ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (V : ι → Set U) (r : ℝ),
    (∀ i, ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J i q.1 q.2)) ∧
    (∀ i, ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J i q.1).symm q.2)) ∧
    (∀ i, J i 0 = Diffeomorph.refl ThreeModel U ∞) ∧
    (∀ i, IsCompact (V i)) ∧
    (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
    (∀ i t, Set.EqOn (J i t) (id : U → U) (V i)ᶜ) ∧
    0 < r ∧ r ≤ 1 ∧
    (∀ i, ∀ x : ThreeSpace, x ∈ Metric.closedBall 0 r →
      J i 1 ((e i).chart x) = (e' i).chart x) ∧
    (∀ i j, i ≠ j → ∀ x : ThreeSpace, x ∈ Metric.closedBall 0 r →
      (e i).chart x ∉ V j)

theorem ballEmbeddingAmbientIsotopic_of_supportedBallEmbeddingIsotopy {ι : Type u} [Finite ι]
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} {e e' : ι → OrientedBallEmbedding U o}
    (h : SupportedBallEmbeddingIsotopy ι U o e e') :
    BallEmbeddingAmbientIsotopic ι U o e e' := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨J, V, r, hJc, hJi, hJ0, hVc, hVd, hVfix, hr0, hr1, hJ1, havoid⟩ := h
  have hfix : ∀ (i : ι) (t : ℝ) (x : U), x ∉ V i → (J i t) x = x ∧ (J i t).symm x = x :=
    fun i t x hx =>
      ⟨by simpa using hVfix i t hx, by
        have hx' : (J i t) x = x := by simpa using hVfix i t hx
        calc (J i t).symm x = (J i t).symm ((J i t) x) := by rw [hx']
          _ = x := (J i t).symm_apply_apply x⟩
  refine ⟨fun t => diffeomorphList J
      (Finset.univ : Finset ι).toList (fun _ => t),
    diffeomorphList_univ_diagonal_zero J hJ0,
    contMDiff_diffeomorphList_univ_diagonal J hJc,
    contMDiff_diffeomorphList_univ_diagonal_symm J hJi,
    ⋃ i, V i, isCompact_iUnion hVc, ?_, ?_, r, hr0, hr1, ?_⟩
  · intro t x hx
    exact diffeomorphList_diagonal_apply_eq_of_forall_notMem
      J V hfix (Finset.univ : Finset ι).toList (fun _ => t) (y := x)
      (fun i _ hyi => hx (Set.mem_iUnion.mpr ⟨i, hyi⟩))
  · intro t x hx
    exact eqOn_symm_of_eqOn_compl
      (Φ := diffeomorphList J
        (Finset.univ : Finset ι).toList (fun _ => t))
      (K := ⋃ i, V i)
      (fun y hy =>
        diffeomorphList_diagonal_apply_eq_of_forall_notMem
          J V hfix (Finset.univ : Finset ι).toList (fun _ => t) (y := y)
          (fun i _ hyi => hy (Set.mem_iUnion.mpr ⟨i, hyi⟩))) hx
  · intro i x hx
    have hmem : i ∈ (Finset.univ : Finset ι).toList := Finset.mem_toList.mpr (Finset.mem_univ i)
    rw [diffeomorphList_diagonal_one_apply_eq_of_disjoint_support
      J V hVd hfix (Finset.univ : Finset ι).toList (Finset.nodup_toList _) hmem
      (fun j _ hji => havoid i j (Ne.symm hji) x hx)]
    exact hJ1 i x hx

theorem supportedBallEmbeddingIsotopy_self {ι : Type u} {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e : ι → OrientedBallEmbedding U o) :
    SupportedBallEmbeddingIsotopy ι U o e e :=
  ⟨fun _ _ => Diffeomorph.refl ThreeModel U ∞, fun _ => ∅, 1, fun _ => contMDiff_snd,
    fun _ => contMDiff_snd, fun _ => rfl, fun _ => isCompact_empty, fun _ _ _ => by simp,
    fun _ _ _ _ => rfl, by norm_num, le_rfl, fun _ _ _ => rfl,
    fun _ _ _ _ _ => by simp⟩

theorem ballEmbeddingAmbientIsotopic_self {ι : Type u} {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e : ι → OrientedBallEmbedding U o) :
    BallEmbeddingAmbientIsotopic ι U o e e :=
  ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, rfl, contMDiff_snd, contMDiff_snd,
    ∅, isCompact_empty, fun _ _ _ => rfl, fun _ _ _ => rfl, 1, by norm_num, le_rfl,
    fun _ _ _ => rfl⟩

theorem ballEmbeddingAmbientIsotopic_of_isEmpty {ι : Type u} [IsEmpty ι] {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o) :
    BallEmbeddingAmbientIsotopic ι U o e e' :=
  ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, rfl, contMDiff_snd, contMDiff_snd,
    ∅, isCompact_empty, fun _ _ _ => rfl, fun _ _ _ => rfl, 1, by norm_num, le_rfl,
    fun i => isEmptyElim i⟩

theorem supportedBallEmbeddingIsotopy_of_isEmpty {ι : Type u} [IsEmpty ι]
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o) :
    SupportedBallEmbeddingIsotopy ι U o e e' :=
  ⟨fun _ _ => Diffeomorph.refl ThreeModel U ∞, fun _ => ∅, 1, fun _ => contMDiff_snd,
    fun _ => contMDiff_snd, fun _ => rfl, fun _ => isCompact_empty, fun _ _ _ => by simp,
    fun _ _ _ _ => rfl, by norm_num, le_rfl, fun i => isEmptyElim i,
    fun i => isEmptyElim i⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
