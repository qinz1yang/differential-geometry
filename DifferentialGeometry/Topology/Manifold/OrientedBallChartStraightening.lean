import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BallEmbeddingFamilyStraightening
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology (BallChart)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def OrientedBallEmbedding.toBallChart {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] {o : ManifoldOrientation ThreeModel U 3}
    (e : OrientedBallEmbedding U o) : BallChart 3 (𝓡 3) U where
  chart := e.chart
  closedBall_subset_source := e.closedBall_subset_source

theorem OrientedBallEmbedding.comp_chart_apply {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (e : OrientedBallEmbedding U o)
    (Φ : Diffeomorph ThreeModel ThreeModel U U ∞) (x : ThreeSpace) :
    (e.chart.trans Φ.toPartialDiffeomorph) x = Φ (e.chart x) := by
  change (e.chart.toOpenPartialHomeomorph.trans
    Φ.toPartialDiffeomorph.toOpenPartialHomeomorph) x = Φ (e.chart x)
  rw [OpenPartialHomeomorph.trans_apply]
  rfl

theorem OrientedBallEmbedding.preserves_orientation_comp {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (e : OrientedBallEmbedding U o)
    (Φ : Diffeomorph ThreeModel ThreeModel U U ∞) (hΦ : Φ.preservesOrientation o o) :
    ∀ x, ∀ hx : x ∈ (e.chart.trans Φ.toPartialDiffeomorph).source,
      Orientation.map (Fin 3)
        (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
          (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞
            (e.chart.trans Φ.toPartialDiffeomorph) hx) (by simp)).toLinearEquiv
        (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
      o.orientation ((e.chart.trans Φ.toPartialDiffeomorph) x) := by
  intro x hx
  have hxsrc : x ∈ e.chart.source := by
    change x ∈ (e.chart.toOpenPartialHomeomorph.trans
      Φ.toPartialDiffeomorph.toOpenPartialHomeomorph).source at hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx.1
  let A : TangentSpace ThreeModel x ≃ₗ[ℝ] TangentSpace ThreeModel (e.chart x) :=
    (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
      (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ e.chart hxsrc)
      (by simp)).toLinearEquiv
  let B : TangentSpace ThreeModel (e.chart x) ≃ₗ[ℝ]
      TangentSpace ThreeModel (Φ (e.chart x)) :=
    (Φ.mfderivToContinuousLinearEquiv (by simp) (e.chart x)).toLinearEquiv
  have hchain := mfderiv_comp (x := x)
    (f := fun y : ThreeSpace => e.chart y) (g := fun y : U => Φ y)
    (Φ.mdifferentiable (by simp) (e.chart x))
    (PartialDiffeomorph.mdifferentiableAt e.chart (by simp) hxsrc)
  have hchain' : mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => Φ (e.chart y)) x =
      (mfderiv ThreeModel ThreeModel (fun y : U => Φ y) (e.chart x)).comp
        (mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => e.chart y) x) := hchain
  have hL : (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞
          (e.chart.trans Φ.toPartialDiffeomorph) hx) (by simp)).toLinearEquiv = A.trans B := by
    apply LinearEquiv.ext
    intro v
    change mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => Φ (e.chart y)) x v = B (A v)
    have hA : A v = mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => e.chart y) x v := rfl
    change mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => Φ (e.chart y)) x v =
      (mfderiv ThreeModel ThreeModel (fun y : U => Φ y) (e.chart x)) (A v)
    rw [hA, DFunLike.congr_fun hchain' v, ContinuousLinearMap.comp_apply]
  have hpres := e.preserves_orientation x hxsrc
  change Orientation.map (Fin 3) A
      (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
    o.orientation (e.chart x) at hpres
  rw [hL, OrientedBallEmbedding.comp_chart_apply e Φ x,
    ← DifferentialGeometry.VectorBundle.map_orientation_trans_between A B, hpres,
    hΦ (e.chart x)]

theorem OrientedBallEmbedding.isCompact_closedBall_image {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (e : OrientedBallEmbedding U o) :
    IsCompact (e.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
  e.toBallChart.isCompact_closedBall_image

def OrientedBallEmbedding.comp {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] {o : ManifoldOrientation ThreeModel U 3}
    (e : OrientedBallEmbedding U o) (Φ : Diffeomorph ThreeModel ThreeModel U U ∞)
    (hΦ : Φ.preservesOrientation o o) : OrientedBallEmbedding U o where
  chart := e.chart.trans Φ.toPartialDiffeomorph
  closedBall_subset_source := fun _ hx => ⟨e.closedBall_subset_source hx, trivial⟩
  preserves_orientation := e.preserves_orientation_comp Φ hΦ

def orientedBallChartIsotopicAwayFromCompact {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o) (C : Set U) :
    Prop :=
  ∃ (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (K : Set U),
    IsCompact K ∧ Disjoint K C ∧ J 0 = Diffeomorph.refl ThreeModel U ∞ ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2) ∧
    (∀ t, Set.EqOn (J t) (id : U → U) Kᶜ) ∧
    (∀ t, Set.EqOn (J t).symm (id : U → U) Kᶜ) ∧
    ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, J 1 (b.chart x) = b'.chart x

def orientedBallChartStraighteningAwayFromCompact : Prop :=
  ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
    (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o) (C : Set U),
    IsCompact C →
    Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
    Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
    orientedBallChartIsotopicAwayFromCompact o b b' C

def isotopyPreservesOrientation : Prop :=
  ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
    (o : ManifoldOrientation ThreeModel U 3)
    (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞),
    J 0 = Diffeomorph.refl ThreeModel U ∞ →
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2) →
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2) →
    (J 1).preservesOrientation o o

private def orientedIsotopyConcat {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) :
    ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ :=
  fun t => (J (Real.smoothTransition t)).trans (J' (Real.smoothTransition t))

private lemma orientedIsotopyConcat_zero {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : J 0 = Diffeomorph.refl ThreeModel U ∞)
    (hJ' : J' 0 = Diffeomorph.refl ThreeModel U ∞) :
    orientedIsotopyConcat J J' 0 = Diffeomorph.refl ThreeModel U ∞ := by
  change (J (Real.smoothTransition 0)).trans (J' (Real.smoothTransition 0)) = _
  rw [Real.smoothTransition.zero, hJ, hJ', Diffeomorph.refl_trans]

private lemma contMDiff_orientedIsotopyConcat {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2))
    (hJ' : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J' q.1 q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => orientedIsotopyConcat J J' q.1 q.2) := by
  have hσ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Real.smoothTransition q.1) :=
    (Real.smoothTransition.contDiff.contMDiff).comp contMDiff_fst
  have h₁ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J (Real.smoothTransition q.1) q.2) :=
    hJ.comp (hσ.prodMk contMDiff_snd)
  have h₂ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J' (Real.smoothTransition q.1) (J (Real.smoothTransition q.1) q.2)) :=
    hJ'.comp (hσ.prodMk h₁)
  exact h₂

private lemma contMDiff_orientedIsotopyConcat_symm {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2))
    (hJ' : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J' q.1).symm q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (orientedIsotopyConcat J J' q.1).symm q.2) := by
  have hσ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Real.smoothTransition q.1) :=
    (Real.smoothTransition.contDiff.contMDiff).comp contMDiff_fst
  have h₁ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J' (Real.smoothTransition q.1)).symm q.2) :=
    hJ'.comp (hσ.prodMk contMDiff_snd)
  have h₂ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J (Real.smoothTransition q.1)).symm
        ((J' (Real.smoothTransition q.1)).symm q.2)) :=
    hJ.comp (hσ.prodMk h₁)
  exact h₂

private lemma orientedIsotopyConcat_apply_eq_of_notMem {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    {K K' : Set U} (hJ : ∀ t, Set.EqOn (J t) (id : U → U) Kᶜ)
    (hJ' : ∀ t, Set.EqOn (J' t) (id : U → U) K'ᶜ) {t : ℝ} {x : U}
    (hx : x ∉ K ∪ K') : orientedIsotopyConcat J J' t x = x := by
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxK' : x ∉ K' := fun h => hx (Or.inr h)
  have h1 : J (Real.smoothTransition t) x = x := hJ _ hxK
  have h2 : J' (Real.smoothTransition t) x = x := hJ' _ hxK'
  change J' (Real.smoothTransition t) (J (Real.smoothTransition t) x) = x
  rw [h1, h2]

private lemma orientedIsotopyConcat_symm_apply_eq_of_notMem {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    {K K' : Set U} (hJ : ∀ t, Set.EqOn (J t).symm (id : U → U) Kᶜ)
    (hJ' : ∀ t, Set.EqOn (J' t).symm (id : U → U) K'ᶜ) {t : ℝ} {x : U}
    (hx : x ∉ K ∪ K') : (orientedIsotopyConcat J J' t).symm x = x := by
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxK' : x ∉ K' := fun h => hx (Or.inr h)
  have h1 : (J' (Real.smoothTransition t)).symm x = x := hJ' _ hxK'
  have h2 : (J (Real.smoothTransition t)).symm x = x := hJ _ hxK
  change (J (Real.smoothTransition t)).symm ((J' (Real.smoothTransition t)).symm x) = x
  rw [h1, h2]

private lemma orientedIsotopyConcat_one_preservesOrientation {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3}
    (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : (J 1).preservesOrientation o o) (hJ' : (J' 1).preservesOrientation o o) :
    (orientedIsotopyConcat J J' 1).preservesOrientation o o := by
  change ((J (Real.smoothTransition 1)).trans (J' (Real.smoothTransition 1))).preservesOrientation
    o o
  rw [Real.smoothTransition.one]
  exact Diffeomorph.preservesOrientation_trans hJ hJ'

private lemma exists_orientedAmbientIsotopy_matching_finset
    (h : orientedBallChartStraighteningAwayFromCompact.{u})
    (horient : isotopyPreservesOrientation.{u})
    {ι : Type u} {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] [ConnectedSpace U] (o : ManifoldOrientation ThreeModel U 3)
    (E E' : ι → OrientedBallEmbedding U o)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint ((E i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((E j).chart '' Metric.closedBall (0 : ThreeSpace) 1))
    (hdisj' : ∀ i j, i ≠ j →
      Disjoint ((E' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((E' j).chart '' Metric.closedBall (0 : ThreeSpace) 1))
    (l : Finset ι) :
    ∃ (H : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (K : Set U),
      H 0 = Diffeomorph.refl ThreeModel U ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (H q.1).symm q.2) ∧
      IsCompact K ∧
      (∀ t, Set.EqOn (H t) (id : U → U) Kᶜ) ∧
      (∀ t, Set.EqOn (H t).symm (id : U → U) Kᶜ) ∧
      (H 1).preservesOrientation o o ∧
      ∀ i ∈ l, ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
        H 1 ((E i).chart x) = (E' i).chart x := by
  classical
  revert E E'
  refine Finset.induction_on l ?_ ?_
  · intro E E' hdisj hdisj'
    exact ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, ∅, rfl, contMDiff_snd, contMDiff_snd,
      isCompact_empty, (fun _ _ _ => rfl), (fun _ _ _ => rfl),
      Diffeomorph.preservesOrientation_refl o, fun i hi => by simp at hi⟩
  · intro a l ha ih E E' hdisj hdisj'
    obtain ⟨H, K, hH0, hHc, hHi, hK, hKfix, hKfixi, hH1o, hmatch⟩ := ih E E' hdisj hdisj'
    let Ba : OrientedBallEmbedding U o := (E a).comp (H 1) hH1o
    let C : Set U := ⋃ i : {i : ι // i ∈ l},
      (E' i.1).chart '' Metric.closedBall (0 : ThreeSpace) 1
    have hC : IsCompact C := by
      change IsCompact (⋃ i : {i : ι // i ∈ l},
        (E' i.1).chart '' Metric.closedBall (0 : ThreeSpace) 1)
      exact @isCompact_iUnion U _ {i : ι // i ∈ l}
        (fun i => (E' i.1).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        (Finset.finite_toSet l).to_subtype (fun i => (E' i.1).isCompact_closedBall_image)
    have hCmem {y : U} (hy : y ∈ C) :
        ∃ i : {i : ι // i ∈ l}, ∃ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
          (E' i.1).chart x = y := by
      simpa only [C, Set.mem_iUnion, Set.mem_image] using hy
    have hCmem' (i : ι) (hi : i ∈ l) {x : ThreeSpace}
        (hx : x ∈ Metric.closedBall (0 : ThreeSpace) 1) : (E' i).chart x ∈ C := by
      simp only [C, Set.mem_iUnion, Set.mem_image]
      exact ⟨⟨i, hi⟩, x, hx, rfl⟩
    have himg (i : ι) (hi : i ∈ l) :
        (E' i).chart '' Metric.closedBall (0 : ThreeSpace) 1 =
          H 1 '' ((E i).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(E i).chart x, ⟨x, hx, rfl⟩, hmatch i hi x hx⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, hzy⟩
        exact ⟨x, hx, (hmatch i hi x hx).symm.trans hzy⟩
    have hBa : Ba.chart '' Metric.closedBall (0 : ThreeSpace) 1 =
        H 1 '' ((E a).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
      have hfun : (Ba.chart : ThreeSpace → U) = ⇑(H 1) ∘ ⇑((E a).chart) :=
        funext fun x => OrientedBallEmbedding.comp_chart_apply (E a) (H 1) x
      rw [hfun, Set.image_comp]
    have hdisjBa : Disjoint (Ba.chart '' Metric.closedBall (0 : ThreeSpace) 1) C := by
      rw [hBa, Set.disjoint_left]
      intro y hy hyC
      obtain ⟨u, hu, rfl⟩ := hy
      obtain ⟨i, x, hx, hxy⟩ := hCmem hyC
      have hmem : H 1 u ∈ (E' i.1).chart '' Metric.closedBall (0 : ThreeSpace) 1 := by
        rw [← hxy]
        exact ⟨x, hx, rfl⟩
      rw [himg i.1 i.2] at hmem
      obtain ⟨v, hv, hvEq⟩ := hmem
      have hvu : v = u := (H 1).injective hvEq
      have hu' : u ∈ (E i.1).chart '' Metric.closedBall (0 : ThreeSpace) 1 := by
        rw [← hvu]
        exact hv
      exact Set.disjoint_left.mp (hdisj a i.1 (fun heq => ha (heq ▸ i.2))) hu hu'
    have hdisjBb : Disjoint ((E' a).chart '' Metric.closedBall (0 : ThreeSpace) 1) C := by
      rw [Set.disjoint_left]
      intro y hy hyC
      obtain ⟨i, x, hx, hxy⟩ := hCmem hyC
      exact Set.disjoint_left.mp (hdisj' a i.1 (fun heq => ha (heq ▸ i.2))) hy (by
        rw [← hxy]
        exact ⟨x, hx, rfl⟩)
    obtain ⟨J, K', hK', hKC, hJ0, hJc, hJi, hKfix', hKfixi', hJmatch⟩ :=
      h U o Ba (E' a) C hC hdisjBa hdisjBb
    have hJ1o : (J 1).preservesOrientation o o := horient U o J hJ0 hJc hJi
    refine ⟨orientedIsotopyConcat H J, K ∪ K',
      orientedIsotopyConcat_zero H J hH0 hJ0,
      contMDiff_orientedIsotopyConcat H J hHc hJc,
      contMDiff_orientedIsotopyConcat_symm H J hHi hJi, hK.union hK', ?_, ?_,
      orientedIsotopyConcat_one_preservesOrientation H J hH1o hJ1o, ?_⟩
    · intro t x hx
      exact orientedIsotopyConcat_apply_eq_of_notMem H J hKfix hKfix' hx
    · intro t x hx
      exact orientedIsotopyConcat_symm_apply_eq_of_notMem H J hKfixi hKfixi' hx
    · intro i hi x hx
      rw [Finset.mem_insert] at hi
      rcases hi with hia | hi
      · rw [hia]
        change J (Real.smoothTransition 1) (H (Real.smoothTransition 1) ((E a).chart x)) =
          (E' a).chart x
        rw [Real.smoothTransition.one]
        exact hJmatch x hx
      · change J (Real.smoothTransition 1) (H (Real.smoothTransition 1) ((E i).chart x)) =
          (E' i).chart x
        rw [Real.smoothTransition.one, hmatch i hi x hx]
        exact hKfix' 1 (fun hmem => Set.disjoint_left.mp hKC hmem (hCmem' i hi hx))

theorem ballEmbeddingAmbientIsotopic_of_orientedBallChartStraighteningAwayFromCompact
    (h : orientedBallChartStraighteningAwayFromCompact.{u})
    (horient : isotopyPreservesOrientation.{u})
    {ι : Type u} [Finite ι]
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] [ConnectedSpace U] (o : ManifoldOrientation ThreeModel U 3)
    (e e' : ι → OrientedBallEmbedding U o)
    (he : ∀ i j, i ≠ j →
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1))
    (he' : ∀ i j, i ≠ j →
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) :
    BallEmbeddingAmbientIsotopic ι U o e e' := by
  let s : Finset ι := Set.finite_univ.toFinset
  have hs : ∀ i, i ∈ s := fun i => by simp [s]
  obtain ⟨H, K, hH0, hHc, hHi, hK, hKfix, hKfixi, -, hmatch⟩ :=
    exists_orientedAmbientIsotopy_matching_finset h horient o e e' he he' s
  exact ⟨H, hH0, hHc, hHi, K, hK, hKfix, hKfixi, 1, by norm_num, le_rfl,
    fun i x hx => hmatch i (hs i) x hx⟩

theorem ballEmbeddingIsotopy_of_orientedBallChartStraighteningAwayFromCompact
    (h : orientedBallChartStraighteningAwayFromCompact.{u})
    (horient : isotopyPreservesOrientation.{u}) :
    ballEmbeddingIsotopy.{u} := by
  rw [ballEmbeddingIsotopy_iff_ambientIsotopic]
  intro ι _ U _ _ _ _ _ o e e' he he'
  exact ballEmbeddingAmbientIsotopic_of_orientedBallChartStraighteningAwayFromCompact
    h horient o e e' he he'

private theorem exists_notMem_of_isCompact_threeSpace {K : Set ThreeSpace} (hK : IsCompact K) :
    ∃ x₀ : ThreeSpace, x₀ ∉ K := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ThreeSpace)).mp hK.isBounded
  refine ⟨EuclideanSpace.single (0 : Fin 3) (|r| + 1), fun hmem => ?_⟩
  have hle : ‖EuclideanSpace.single (0 : Fin 3) (|r| + 1)‖ ≤ r := by
    have h1 := hr hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h1
  rw [PiLp.norm_single, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < |r| + 1)] at hle
  linarith [le_abs_self r]

private def negModelDiffeomorph : Diffeomorph ThreeModel ThreeModel ThreeSpace ThreeSpace ∞ where
  toEquiv := Equiv.neg ThreeSpace
  contMDiff_toFun := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_neg
  contMDiff_invFun := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_neg

private def identityBallChart : BallChart 3 (𝓡 3) ThreeSpace where
  chart := (Diffeomorph.refl ThreeModel ThreeSpace ∞).toPartialDiffeomorph
  closedBall_subset_source := fun _ _ => trivial

private def negBallChart : BallChart 3 (𝓡 3) ThreeSpace where
  chart := negModelDiffeomorph.toPartialDiffeomorph
  closedBall_subset_source := fun _ _ => trivial

private def negLinearEquiv : ThreeSpace ≃ₗ[ℝ] ThreeSpace where
  toFun := fun y => -y
  invFun := fun y => -y
  left_inv := by intro y; simp
  right_inv := by intro y; simp
  map_add' := by intro a b; rw [neg_add, add_comm]
  map_smul' := by intro c y; simp

private theorem det_negLinearEquiv :
    LinearMap.det ((negLinearEquiv : ThreeSpace →ₗ[ℝ] ThreeSpace)) = -1 := by
  have h : (negLinearEquiv : ThreeSpace →ₗ[ℝ] ThreeSpace) =
      (-1 : ThreeSpace →ₗ[ℝ] ThreeSpace) := LinearMap.ext fun _ => rfl
  rw [h, ← neg_one_smul ℝ (1 : ThreeSpace →ₗ[ℝ] ThreeSpace), LinearMap.det_smul]
  norm_num

theorem not_ballChartStraighteningAwayFromCompact :
    ¬ ballChartStraighteningAwayFromCompact.{0} := by
  intro h
  obtain ⟨J, K, hK, -, hJ0, hJc, hJi, hKfix, hKfixi, hmatch0⟩ :=
    h ThreeSpace identityBallChart negBallChart ∅
      isCompact_empty (by simp) (by simp)
  have hmatch : ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, J 1 x = -x :=
    fun x hx => hmatch0 x hx
  obtain ⟨x₀, hx₀⟩ := exists_notMem_of_isCompact_threeSpace hK
  let o : ManifoldOrientation ThreeModel ThreeSpace 3 :=
    Classical.choice
      (DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_of_simply_connected
        (E := ThreeSpace) (M := ThreeSpace) (n := 3) (by simp))
  have hpres : (J 1).preservesOrientation o o := by
    refine Diffeomorph.preservesOrientation_of_eq_at (J 1) o o x₀ ?_
    have hmem : Kᶜ ∈ 𝓝 x₀ := hK.isClosed.isOpen_compl.mem_nhds hx₀
    have hev : (J 1) =ᶠ[𝓝 x₀] (id : ThreeSpace → ThreeSpace) :=
      Filter.eventuallyEq_of_mem hmem fun y hy => hKfix 1 hy
    have hder : ((J 1).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv =
        LinearEquiv.refl ℝ (TangentSpace ThreeModel x₀) := by
      refine LinearEquiv.ext fun v => ?_
      change mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => (J 1) y) x₀ v = v
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_eq_fderiv, fderiv_id]
      exact ContinuousLinearMap.id_apply v
    rw [hder]
    change Orientation.map (Fin 3) (LinearEquiv.refl ℝ ThreeSpace) (o.orientation x₀) =
      o.orientation ((J 1) x₀)
    rw [Orientation.map_refl, hKfix 1 hx₀]
    rfl
  have h0 : (J 1) 0 = 0 := by
    simpa using hmatch 0 (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
  have hev0 : (J 1) =ᶠ[𝓝 (0 : ThreeSpace)] (fun y : ThreeSpace => -y) :=
    Filter.eventuallyEq_of_mem (Metric.closedBall_mem_nhds (0 : ThreeSpace) (by norm_num))
      fun y hy => hmatch y hy
  have hL : ((J 1).mfderivToContinuousLinearEquiv (by simp) (0 : ThreeSpace)).toLinearEquiv =
      negLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv ThreeModel ThreeModel (fun y : ThreeSpace => (J 1) y) 0 v = -v
    rw [Filter.EventuallyEq.mfderiv_eq hev0, mfderiv_eq_fderiv, fderiv_fun_neg,
      show fderiv ℝ (fun y : ThreeSpace => y) 0 = ContinuousLinearMap.id ℝ ThreeSpace
        from fderiv_id]
    rfl
  have hpres0 := hpres 0
  rw [h0] at hpres0
  rw [hL] at hpres0
  have hcard : Fintype.card (Fin 3) =
      Module.finrank ℝ (TangentSpace ThreeModel (0 : ThreeSpace)) := by
    change Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace
    simp
  have hpos := (Orientation.map_eq_iff_det_pos (o.orientation 0) negLinearEquiv hcard).mp hpres0
  change 0 < LinearMap.det ((negLinearEquiv : ThreeSpace →ₗ[ℝ] ThreeSpace)) at hpos
  rw [det_negLinearEquiv] at hpos
  norm_num at hpos

theorem orientedBallChartIsotopicAwayFromCompact_self {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (b : OrientedBallEmbedding U o) (C : Set U) :
    orientedBallChartIsotopicAwayFromCompact o b b C :=
  ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, ∅, isCompact_empty, by simp, rfl,
    contMDiff_snd, contMDiff_snd, (fun _ _ _ => rfl), (fun _ _ _ => rfl), fun _ _ => rfl⟩

theorem orientedBallChartIsotopicAwayFromCompact_of_eqOn_closedBall {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (b b' : OrientedBallEmbedding U o) (C : Set U)
    (h : ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, b'.chart x = b.chart x) :
    orientedBallChartIsotopicAwayFromCompact o b b' C :=
  ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, ∅, isCompact_empty, by simp, rfl,
    contMDiff_snd, contMDiff_snd, (fun _ _ _ => rfl), (fun _ _ _ => rfl),
    fun x hx => by rw [Diffeomorph.coe_refl, id_eq, h x hx]⟩

theorem ballChartIsotopicAwayFromCompact_of_orientedBallChartIsotopicAwayFromCompact
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} {b b' : OrientedBallEmbedding U o} {C : Set U}
    (h : orientedBallChartIsotopicAwayFromCompact o b b' C) :
    ballChartIsotopicAwayFromCompact b.toBallChart b'.toBallChart C := by
  obtain ⟨J, K, hK, hKC, hJ0, hJc, hJi, hfix, hfixi, hmatch⟩ := h
  exact ⟨J, K, hK, hKC, hJ0, hJc, hJi, hfix, hfixi, hmatch⟩

theorem orientedBallChartStraighteningAwayFromCompact_hypotheses_satisfiable {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3)
    (b : OrientedBallEmbedding U o) :
    ∃ (b' : OrientedBallEmbedding U o) (C : Set U), IsCompact C ∧
      Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      orientedBallChartIsotopicAwayFromCompact o b b' C :=
  ⟨b, ∅, isCompact_empty, by simp, by simp,
    orientedBallChartIsotopicAwayFromCompact_self b ∅⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem isotopyPreservesOrientation_satisfiable {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) :
    ∃ J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞,
      J 0 = Diffeomorph.refl ThreeModel U ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (J q.1).symm q.2) ∧
      (J 1).preservesOrientation o o :=
  ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, rfl, contMDiff_snd, contMDiff_snd,
    Diffeomorph.preservesOrientation_refl o⟩

theorem isotopyPreservesOrientation_of_eqOn_compl_of_isCompact {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U] [PreconnectedSpace U]
    {o : ManifoldOrientation ThreeModel U 3} (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    {K : Set U} (hK : IsCompact K) (hne : (Kᶜ).Nonempty)
    (hfix : ∀ t, Set.EqOn (J t) (id : U → U) Kᶜ) :
    ∀ t, (J t).preservesOrientation o o := by
  obtain ⟨x, hx⟩ := hne
  have hmem : Kᶜ ∈ 𝓝 x := hK.isClosed.isOpen_compl.mem_nhds hx
  intro t
  refine Diffeomorph.preservesOrientation_of_eventuallyEq_id (x₀ := x) (J t) ?_
  exact Filter.eventuallyEq_of_mem hmem fun y hy => hfix t hy

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
