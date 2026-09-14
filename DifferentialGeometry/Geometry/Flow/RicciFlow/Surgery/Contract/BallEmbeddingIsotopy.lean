import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Reconstruction
import DifferentialGeometry.Topology.Manifold.DiffeomorphFamily
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingSupport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingRelativeIsotopy

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem eqOn_symm_of_eqOn_compl {Φ : Diffeomorph I I M M ∞} {K : Set M}
    (h : Set.EqOn Φ id Kᶜ) : Set.EqOn Φ.symm id Kᶜ := by
  intro x hx
  have h1 : Φ x = x := h hx
  calc Φ.symm x = Φ.symm (Φ x) := by rw [h1]
    _ = x := Φ.symm_apply_apply x

end DifferentialGeometry.Topology.Manifold

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

def SupportedBallEmbeddingIsotopy (ι : Type u) [Fintype ι] (U : Type u) [TopologicalSpace U]
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

theorem ballEmbeddingIsotopy_iff_ambientIsotopic :
    ballEmbeddingIsotopy.{u} ↔
      ∀ (ι : Type u) [Fintype ι] (U : Type u) [TopologicalSpace U]
        [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
        (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o),
        (Pairwise fun i j =>
          Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
            ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) →
        (Pairwise fun i j =>
          Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
            ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) →
        BallEmbeddingAmbientIsotopic ι U o e e' :=
  Iff.rfl

theorem ballEmbeddingAmbientIsotopic_of_supportedBallEmbeddingIsotopy {ι : Type u} [Fintype ι]
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} {e e' : ι → OrientedBallEmbedding U o}
    (h : SupportedBallEmbeddingIsotopy ι U o e e') :
    BallEmbeddingAmbientIsotopic ι U o e e' := by
  classical
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

theorem ballEmbeddingIsotopy_of_supportedBallEmbeddingIsotopy
    (h : ∀ (ι : Type u) [Fintype ι] (U : Type u) [TopologicalSpace U]
      [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
      (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o),
      SupportedBallEmbeddingIsotopy ι U o e e') :
    ballEmbeddingIsotopy.{u} := by
  rw [ballEmbeddingIsotopy_iff_ambientIsotopic]
  intro ι _ U _ _ _ _ _ o e e' _ _
  exact ballEmbeddingAmbientIsotopic_of_supportedBallEmbeddingIsotopy (h ι U o e e')

theorem supportedBallEmbeddingIsotopy_self {ι : Type u} [Fintype ι] {U : Type u}
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

theorem supportedBallEmbeddingIsotopy_of_isEmpty {ι : Type u} [Fintype ι] [IsEmpty ι]
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o) :
    SupportedBallEmbeddingIsotopy ι U o e e' :=
  ⟨fun _ _ => Diffeomorph.refl ThreeModel U ∞, fun _ => ∅, 1, fun _ => contMDiff_snd,
    fun _ => contMDiff_snd, fun _ => rfl, fun _ => isCompact_empty, fun _ _ _ => by simp,
    fun _ _ _ _ => rfl, by norm_num, le_rfl, fun i => isEmptyElim i,
    fun i => isEmptyElim i⟩

def OrientedBallEmbedding.ofOrientedBallChart
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) :
    OrientedBallEmbedding M.Carrier M.orientation where
  chart := c.chart
  closedBall_subset_source := c.closedBall_subset_source
  preserves_orientation := c.preserves_orientation

theorem ballEmbeddingAmbientIsotopic_of_ballMarkingIsotopic
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (I : Type u) [Fintype I] (B B' : DifferentialGeometry.Topology.BallMarking M I)
    (h : B.Isotopic B') :
    BallEmbeddingAmbientIsotopic I M.Carrier M.orientation
      (fun i => OrientedBallEmbedding.ofOrientedBallChart (B.ball i))
      (fun i => OrientedBallEmbedding.ofOrientedBallChart (B'.ball i)) := by
  obtain ⟨H, hHc, hHi, hH0, hH1⟩ := h
  refine ⟨H, hH0, hHc, hHi, Set.univ, isCompact_univ, ?_, ?_, 1, by norm_num, le_rfl,
    fun i x hx => hH1 i x (Metric.closedBall_subset_closedBall (by norm_num) hx)⟩
  · intro t x hx
    exact absurd (Set.mem_univ x) hx
  · intro t x hx
    exact absurd (Set.mem_univ x) hx

theorem ballEmbeddingAmbientIsotopic_standardThreeSphere :
    BallEmbeddingAmbientIsotopic PUnit
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}.orientation
      (fun _ => OrientedBallEmbedding.ofOrientedBallChart
        (DifferentialGeometry.Topology.orientedBallChart
          DifferentialGeometry.Topology.standardThreeSphereLift.{u}))
      (fun _ => OrientedBallEmbedding.ofOrientedBallChart
        (DifferentialGeometry.Topology.OrientedBallChart.affine
          (DifferentialGeometry.Topology.orientedBallChart
            DifferentialGeometry.Topology.standardThreeSphereLift.{u})
          (0 : ThreeSpace) (1 / 2) (by norm_num) (by norm_num))) := by
  exact ballEmbeddingAmbientIsotopic_of_ballMarkingIsotopic PUnit _ _
    (DifferentialGeometry.Topology.BallMarking.singleton_isotopic_of_affine
      (DifferentialGeometry.Topology.orientedBallChart
        DifferentialGeometry.Topology.standardThreeSphereLift.{u})
      (0 : ThreeSpace) (1 / 2) (by norm_num) (by norm_num))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
