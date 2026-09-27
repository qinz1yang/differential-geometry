import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BallEmbeddingIsotopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BallEmbeddingIsotopyObstruction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology (BallChart)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def ballChartComp {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    (c : BallChart 3 (𝓡 3) U) (Φ : Diffeomorph ThreeModel ThreeModel U U ∞) :
    BallChart 3 (𝓡 3) U where
  chart := c.chart.trans Φ.toPartialDiffeomorph
  closedBall_subset_source := fun _ hx => ⟨c.closedBall_subset_source hx, trivial⟩

private lemma ballChartComp_chart_apply {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (c : BallChart 3 (𝓡 3) U)
    (Φ : Diffeomorph ThreeModel ThreeModel U U ∞) (x : ThreeSpace) :
    (ballChartComp c Φ).chart x = Φ (c.chart x) := by
  change (c.chart.trans Φ.toPartialDiffeomorph).toPartialEquiv.toFun x = Φ (c.chart x)
  rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_apply]
  rfl

private lemma ballChartComp_chart_image {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (c : BallChart 3 (𝓡 3) U)
    (Φ : Diffeomorph ThreeModel ThreeModel U U ∞) (s : Set ThreeSpace) :
    (ballChartComp c Φ).chart '' s = Φ '' (c.chart '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c.chart x, ⟨x, hx, rfl⟩, (ballChartComp_chart_apply c Φ x).symm⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, ballChartComp_chart_apply c Φ x⟩

def ballChartIsotopicAwayFromCompact {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (b b' : BallChart 3 (𝓡 3) U) (C : Set U) : Prop :=
  ∃ (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (K : Set U),
    IsCompact K ∧ Disjoint K C ∧ J 0 = Diffeomorph.refl ThreeModel U ∞ ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2) ∧
    (∀ t, Set.EqOn (J t) (id : U → U) Kᶜ) ∧
    (∀ t, Set.EqOn (J t).symm (id : U → U) Kᶜ) ∧
    ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1, J 1 (b.chart x) = b'.chart x

def ballChartStraighteningAwayFromCompact : Prop :=
  ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] (b b' : BallChart 3 (𝓡 3) U) (C : Set U),
    IsCompact C →
    Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
    Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
    ballChartIsotopicAwayFromCompact b b' C

private def ambientIsotopyConcat {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) :
    ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ :=
  fun t => (J (Real.smoothTransition t)).trans (J' (Real.smoothTransition t))

private lemma ambientIsotopyConcat_zero {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : J 0 = Diffeomorph.refl ThreeModel U ∞)
    (hJ' : J' 0 = Diffeomorph.refl ThreeModel U ∞) :
    ambientIsotopyConcat J J' 0 = Diffeomorph.refl ThreeModel U ∞ := by
  change (J (Real.smoothTransition 0)).trans (J' (Real.smoothTransition 0)) = _
  rw [Real.smoothTransition.zero, hJ, hJ', Diffeomorph.refl_trans]

private lemma contMDiff_ambientIsotopyConcat {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2))
    (hJ' : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J' q.1 q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => ambientIsotopyConcat J J' q.1 q.2) := by
  have hσ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Real.smoothTransition q.1) :=
    (Real.smoothTransition.contDiff.contMDiff).comp contMDiff_fst
  have h₁ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J (Real.smoothTransition q.1) q.2) :=
    hJ.comp (hσ.prodMk contMDiff_snd)
  have h₂ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J' (Real.smoothTransition q.1)
        (J (Real.smoothTransition q.1) q.2)) :=
    hJ'.comp (hσ.prodMk h₁)
  exact h₂

private lemma contMDiff_ambientIsotopyConcat_symm {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2))
    (hJ' : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J' q.1).symm q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (ambientIsotopyConcat J J' q.1).symm q.2) := by
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

private lemma ambientIsotopyConcat_apply_eq_of_notMem {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    {K K' : Set U} (hJ : ∀ t, Set.EqOn (J t) (id : U → U) Kᶜ)
    (hJ' : ∀ t, Set.EqOn (J' t) (id : U → U) K'ᶜ) {t : ℝ} {x : U}
    (hx : x ∉ K ∪ K') : ambientIsotopyConcat J J' t x = x := by
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxK' : x ∉ K' := fun h => hx (Or.inr h)
  have h1 : J (Real.smoothTransition t) x = x := hJ _ hxK
  have h2 : J' (Real.smoothTransition t) x = x := hJ' _ hxK'
  change J' (Real.smoothTransition t) (J (Real.smoothTransition t) x) = x
  rw [h1, h2]

private lemma ambientIsotopyConcat_symm_apply_eq_of_notMem {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    {K K' : Set U} (hJ : ∀ t, Set.EqOn (J t).symm (id : U → U) Kᶜ)
    (hJ' : ∀ t, Set.EqOn (J' t).symm (id : U → U) K'ᶜ) {t : ℝ} {x : U}
    (hx : x ∉ K ∪ K') : (ambientIsotopyConcat J J' t).symm x = x := by
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxK' : x ∉ K' := fun h => hx (Or.inr h)
  have h1 : (J' (Real.smoothTransition t)).symm x = x := hJ' _ hxK'
  have h2 : (J (Real.smoothTransition t)).symm x = x := hJ _ hxK
  change (J (Real.smoothTransition t)).symm ((J' (Real.smoothTransition t)).symm x) = x
  rw [h1, h2]

theorem BallEmbeddingAmbientIsotopic.trans {ι : Type u} {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} {e e' e'' : ι → OrientedBallEmbedding U o}
    (h : BallEmbeddingAmbientIsotopic ι U o e e')
    (h' : BallEmbeddingAmbientIsotopic ι U o e' e'') :
    BallEmbeddingAmbientIsotopic ι U o e e'' := by
  obtain ⟨J, hJ0, hJc, hJi, K, hK, hKfix, hKfixi, r, hr0, hr1, hJmatch⟩ := h
  obtain ⟨J', hJ'0, hJ'c, hJ'i, K', hK', hK'fix, hK'fixi, r', hr'0, hr'1, hJ'match⟩ := h'
  refine ⟨ambientIsotopyConcat J J', ambientIsotopyConcat_zero J J' hJ0 hJ'0,
    contMDiff_ambientIsotopyConcat J J' hJc hJ'c, contMDiff_ambientIsotopyConcat_symm J J' hJi hJ'i,
    K ∪ K', hK.union hK', ?_, ?_, min r r', lt_min hr0 hr'0, (min_le_left r r').trans hr1,
    fun i x hx => ?_⟩
  · intro t x hx
    exact ambientIsotopyConcat_apply_eq_of_notMem J J' hKfix hK'fix hx
  · intro t x hx
    exact ambientIsotopyConcat_symm_apply_eq_of_notMem J J' hKfixi hK'fixi hx
  · change J' (Real.smoothTransition 1) (J (Real.smoothTransition 1) ((e i).chart x)) =
      (e'' i).chart x
    rw [Real.smoothTransition.one,
      hJmatch i x (Metric.closedBall_subset_closedBall (min_le_left _ _) hx),
      hJ'match i x (Metric.closedBall_subset_closedBall (min_le_right _ _) hx)]


private lemma exists_ambientIsotopy_matching_finset
    (h : ballChartStraighteningAwayFromCompact.{u}) {ι : Type u} {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] (E E' : ι → BallChart 3 (𝓡 3) U)
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
      ∀ i ∈ l, ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
        H 1 ((E i).chart x) = (E' i).chart x := by
  classical
  revert E E'
  refine Finset.induction_on l ?_ ?_
  · intro E E' hdisj hdisj'
    exact ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, ∅, rfl, contMDiff_snd, contMDiff_snd,
      isCompact_empty, (fun _ _ _ => rfl), (fun _ _ _ => rfl), fun i hi => by simp at hi⟩
  · intro a l ha ih E E' hdisj hdisj'
    obtain ⟨H, K, hH0, hHc, hHi, hK, hKfix, hKfixi, hmatch⟩ := ih E E' hdisj hdisj'
    let Ba : BallChart 3 (𝓡 3) U := ballChartComp (E a) (H 1)
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
        H 1 '' ((E a).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
      ballChartComp_chart_image (E a) (H 1) _
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
      h U Ba (E' a) C hC hdisjBa hdisjBb
    refine ⟨ambientIsotopyConcat H J, K ∪ K', ambientIsotopyConcat_zero H J hH0 hJ0,
      contMDiff_ambientIsotopyConcat H J hHc hJc,
      contMDiff_ambientIsotopyConcat_symm H J hHi hJi, hK.union hK', ?_, ?_, ?_⟩
    · intro t x hx
      exact ambientIsotopyConcat_apply_eq_of_notMem H J hKfix hKfix' hx
    · intro t x hx
      exact ambientIsotopyConcat_symm_apply_eq_of_notMem H J hKfixi hKfixi' hx
    · intro i hi x hx
      rw [Finset.mem_insert] at hi
      rcases hi with hia | hi
      · rw [hia]
        change J (Real.smoothTransition 1) (H (Real.smoothTransition 1) ((E a).chart x)) =
          (E' a).chart x
        rw [Real.smoothTransition.one, ← ballChartComp_chart_apply (E a) (H 1) x, hJmatch x hx]
      · change J (Real.smoothTransition 1) (H (Real.smoothTransition 1) ((E i).chart x)) =
          (E' i).chart x
        rw [Real.smoothTransition.one, hmatch i hi x hx]
        exact hKfix' 1 (fun hmem => Set.disjoint_left.mp hKC hmem (hCmem' i hi hx))

theorem ballEmbeddingAmbientIsotopic_of_ballChartStraighteningAwayFromCompact
    (h : ballChartStraighteningAwayFromCompact.{u}) {ι : Type u} [Finite ι] {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o)
    (he : ∀ i j, i ≠ j →
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1))
    (he' : ∀ i j, i ≠ j →
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) :
    BallEmbeddingAmbientIsotopic ι U o e e' := by
  let s : Finset ι := Set.finite_univ.toFinset
  have hs : ∀ i, i ∈ s := fun i => by simp [s]
  let E : ι → BallChart 3 (𝓡 3) U :=
    fun i => ⟨(e i).chart, (e i).closedBall_subset_source⟩
  let E' : ι → BallChart 3 (𝓡 3) U :=
    fun i => ⟨(e' i).chart, (e' i).closedBall_subset_source⟩
  have hE : ∀ i, (E i).chart = (e i).chart := fun _ => rfl
  have hE' : ∀ i, (E' i).chart = (e' i).chart := fun _ => rfl
  have hdisj : ∀ i j, i ≠ j →
      Disjoint ((E i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((E j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    rw [hE i, hE j]
    exact he i j hij
  have hdisj' : ∀ i j, i ≠ j →
      Disjoint ((E' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((E' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    rw [hE' i, hE' j]
    exact he' i j hij
  obtain ⟨H, K, hH0, hHc, hHi, hK, hKfix, hKfixi, hmatch⟩ :=
    exists_ambientIsotopy_matching_finset h E E' hdisj hdisj' s
  refine ⟨H, hH0, hHc, hHi, K, hK, hKfix, hKfixi, 1, by norm_num, le_rfl, fun i x hx => ?_⟩
  exact hmatch i (hs i) x hx

theorem ballEmbeddingIsotopy_of_ballChartStraighteningAwayFromCompact
    (h : ballChartStraighteningAwayFromCompact.{u}) : ballEmbeddingIsotopy.{u} := by
  rw [ballEmbeddingIsotopy_iff_ambientIsotopic]
  intro ι _ U _ _ _ _ _ o e e' he he'
  exact ballEmbeddingAmbientIsotopic_of_ballChartStraighteningAwayFromCompact h o e e' he he'


theorem ballChartIsotopicAwayFromCompact_self {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (b : BallChart 3 (𝓡 3) U) :
    ballChartIsotopicAwayFromCompact b b ∅ := by
  refine ⟨fun _ => Diffeomorph.refl ThreeModel U ∞, ∅, isCompact_empty, by simp, rfl,
    contMDiff_snd, contMDiff_snd, ?_, ?_, ?_⟩
  · intro t x hx
    rfl
  · intro t x hx
    rfl
  · intro x hx
    rfl

theorem ballChartIsotopicAwayFromCompact_affine {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U]
    (c : BallChart 3 (𝓡 3) U) (hr : 0 < Real.exp (-1))
    (hs : ‖(0 : ThreeSpace)‖ + 2 * Real.exp (-1) ≤ 2) :
    ballChartIsotopicAwayFromCompact c (c.affine 0 (Real.exp (-1)) hr hs) ∅ := by
  obtain ⟨J, hJc, hJi, hJ0, hJrad, K, hK, -, -, hKfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall
      (φ := c.chart) (r := 2) (by norm_num) c.closedBall_subset_source isOpen_univ
      (subset_univ _)
  refine ⟨J, K, hK, by simp, hJ0, hJc, hJi, (fun t x hx => (hKfix t x hx).1),
    (fun t x hx => (hKfix t x hx).2), fun x hx => ?_⟩
  rw [BallChart.affine_apply c 0 (Real.exp (-1)) hr hs x, zero_add]
  exact hJrad 1 x zero_le_one (Metric.closedBall_subset_closedBall (by norm_num) hx)


theorem not_ballEmbeddingAmbientIsotopy : ¬ ballEmbeddingAmbientIsotopy.{u} := by
  intro h
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{u}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  set s' : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) with hs'def
  set z : ThreeSpace := (7 / 5 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hzdef
  set x : ThreeSpace := (-(2 / 5) : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hxdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hnorm' : ‖s'‖ = 3 / 2 := by
    rw [hs'def, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hznorm : ‖z‖ = 7 / 5 := by
    rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 5)]
    simp
  have hxnorm : ‖x‖ = 2 / 5 := by
    rw [hxdef, norm_smul]
    simp
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hs : ‖s‖ + 2 * (1 / 4 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have hs' : ‖s'‖ + 2 * (1 / 4 : ℝ) ≤ 2 := by rw [hnorm']; norm_num
  have hbig : 1 + (1 / 4 : ℝ) < ‖s‖ := by rw [hnorm]; norm_num
  have hbig' : 1 + (1 / 4 : ℝ) < ‖s'‖ := by rw [hnorm']; norm_num
  let d : DifferentialGeometry.Topology.OrientedBallChart M := c.affine s (1 / 4) hr hs
  let d' : DifferentialGeometry.Topology.OrientedBallChart M := c.affine s' (1 / 4) hr hs'
  let eFin : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d
  let eFin' : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d'
  let e : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => eFin i.down
  let e' : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => eFin' i.down
  have hchartc : (OrientedBallEmbedding.ofOrientedBallChart c).chart = c.chart := rfl
  have hchartd : (OrientedBallEmbedding.ofOrientedBallChart d).chart = d.chart := rfl
  have hchartd' : (OrientedBallEmbedding.ofOrientedBallChart d').chart = d'.chart := rfl
  have hdisjc : Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      (d.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    disjoint_chart_image_closedBall_affine c s (1 / 4) hr hs hbig
  have hdisjc' : Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      (d'.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    disjoint_chart_image_closedBall_affine c s' (1 / 4) hr hs' hbig'
  have he0 : eFin 0 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [eFin]
  have he1 : eFin 1 = OrientedBallEmbedding.ofOrientedBallChart d := by simp [eFin]
  have he0' : eFin' 0 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [eFin']
  have he1' : eFin' 1 = OrientedBallEmbedding.ofOrientedBallChart d' := by simp [eFin']
  have hdisjFin : Pairwise fun i j : Fin 2 =>
      Disjoint ((eFin i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((eFin j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [he0, he1, hchartc, hchartd] using hdisjc
    · simpa [he0, he1, hchartc, hchartd] using hdisjc.symm
    · exact absurd rfl hij
  have hdisjFin' : Pairwise fun i j : Fin 2 =>
      Disjoint ((eFin' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((eFin' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [he0', he1', hchartc, hchartd'] using hdisjc'
    · simpa [he0', he1', hchartc, hchartd'] using hdisjc'.symm
    · exact absurd rfl hij
  have hdisj : Pairwise fun i j : ULift.{u, 0} (Fin 2) =>
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    fun i j hij => hdisjFin (i := i.down) (j := j.down) fun hd => hij (ULift.down_injective hd)
  have hdisj' : Pairwise fun i j : ULift.{u, 0} (Fin 2) =>
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    fun i j hij => hdisjFin' (i := i.down) (j := j.down) fun hd => hij (ULift.down_injective hd)
  obtain ⟨H, -, -, -, -, K, -, -, -, hball⟩ :=
    h (ULift.{u, 0} (Fin 2)) M.Carrier M.orientation e e' hdisj hdisj'
  have he1e : e (ULift.up 1) = OrientedBallEmbedding.ofOrientedBallChart d := by
    simp [e, eFin]
  have he0e : e (ULift.up 0) = OrientedBallEmbedding.ofOrientedBallChart c := by
    simp [e, eFin]
  have he1'e : e' (ULift.up 1) = OrientedBallEmbedding.ofOrientedBallChart d' := by
    simp [e', eFin']
  have he0'e : e' (ULift.up 0) = OrientedBallEmbedding.ofOrientedBallChart c := by
    simp [e', eFin']
  have hz2 : z ∈ Metric.closedBall (0 : ThreeSpace) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, hznorm]
    norm_num
  have hx2 : x ∈ Metric.closedBall (0 : ThreeSpace) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, hxnorm]
    norm_num
  have hvec : s + (1 / 4 : ℝ) • x = z := by
    rw [hsdef, hxdef, hzdef]
    simp only [smul_smul, ← add_smul]
    norm_num
  have hsame : (e (ULift.up 1)).chart x = (e (ULift.up 0)).chart z := by
    rw [he1e, he0e, hchartd, hchartc,
      DifferentialGeometry.Topology.OrientedBallChart.affine_apply c s (1 / 4) hr hs x, hvec]
  have hEq : (e' (ULift.up 1)).chart x = (e' (ULift.up 0)).chart z := by
    have h1 := hball (ULift.up 1) x hx2
    have h0 := hball (ULift.up 0) z hz2
    rw [hsame] at h1
    exact h1.symm.trans h0
  have hsrc : s' + (1 / 4 : ℝ) • x ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right]
    have hquarter : ‖(1 / 4 : ℝ) • x‖ = (1 / 4) * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc ‖s' + (1 / 4 : ℝ) • x‖ ≤ ‖s'‖ + ‖(1 / 4 : ℝ) • x‖ := norm_add_le _ _
      _ = ‖s'‖ + (1 / 4) * ‖x‖ := by rw [hquarter]
      _ ≤ 3 / 2 + (1 / 4) * (2 / 5) := by rw [hnorm', hxnorm]
      _ ≤ 2 := by norm_num
  have hsrc0 : z ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right, hznorm]
    norm_num
  rw [he1'e, he0'e, hchartd', hchartc,
    DifferentialGeometry.Topology.OrientedBallChart.affine_apply c s' (1 / 4) hr hs' x] at hEq
  have hvec' : s' + (1 / 4 : ℝ) • x = z :=
    c.chart.toPartialEquiv.injOn hsrc hsrc0 hEq
  have hne : s' + (1 / 4 : ℝ) • x ≠ z := by
    intro hcontra
    have hc := congrArg (fun y : ThreeSpace => y 1) hcontra
    rw [hs'def, hxdef, hzdef] at hc
    simp at hc
  exact hne hvec'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
