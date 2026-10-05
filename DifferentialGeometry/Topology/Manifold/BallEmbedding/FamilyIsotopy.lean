import DifferentialGeometry.Topology.ClosedBallComplement
import DifferentialGeometry.Topology.Manifold.BallEmbedding.RelativeIsotopy
import DifferentialGeometry.Topology.Manifold.IsotopyOrientation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

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
    {ι : Type v} {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] [PreconnectedSpace U] (o : ManifoldOrientation ThreeModel U 3)
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
    have hCcompl : IsPreconnected (Cᶜ : Set U) := by
      let _ : Finite {i : ι // i ∈ l} := (Finset.finite_toSet l).to_subtype
      have hrank : 1 < Module.rank ℝ ThreeSpace := by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
        norm_num
      change IsPreconnected ((⋃ i : {i : ι // i ∈ l},
        (E' i.1).chart '' Metric.closedBall (0 : ThreeSpace) 1)ᶜ : Set U)
      apply DifferentialGeometry.Topology.isPreconnected_compl_iUnion_image_closedBall
        (fun i : {i : ι // i ∈ l} => (E' i.1).chart.toOpenPartialHomeomorph)
        (fun _ => (1 : ℝ)) hrank (fun _ => zero_le_one)
      · intro i x hx
        exact (E' i.1).closedBall_subset_source
          (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx)
      · intro i j hij
        exact hdisj' i.1 j.1 (fun heq => hij (Subtype.ext heq))
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
      OrientedBallEmbedding.exists_isotopy_eqOn_closedBall_of_isPreconnected_compl
        o Ba (E' a) C hC hCcompl hdisjBa hdisjBb
    have hJ1o : (J 1).preservesOrientation o o :=
      preservesOrientation_of_jointlySmooth_isotopy o J hJ0 hJc 1
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

theorem OrientedBallEmbedding.exists_isotopy_eqOn_closedBall_family
    {ι : Type v} [Finite ι]
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] [PreconnectedSpace U] (o : ManifoldOrientation ThreeModel U 3)
    (e e' : ι → OrientedBallEmbedding U o)
    (he : ∀ i j, i ≠ j →
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1))
    (he' : ∀ i j, i ≠ j →
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) :
    ∃ (H : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) (K : Set U),
      H 0 = Diffeomorph.refl ThreeModel U ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (H q.1).symm q.2) ∧
      IsCompact K ∧
      (∀ t, Set.EqOn (H t) (id : U → U) Kᶜ) ∧
      (∀ t, Set.EqOn (H t).symm (id : U → U) Kᶜ) ∧
      (H 1).preservesOrientation o o ∧
      ∀ i, ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
        H 1 ((e i).chart x) = (e' i).chart x := by
  classical
  let s : Finset ι := Set.finite_univ.toFinset
  have hs : ∀ i, i ∈ s := fun i => by simp [s]
  obtain ⟨H, K, hH0, hHc, hHi, hK, hKfix, hKfixi, hH1o, hmatch⟩ :=
    exists_orientedAmbientIsotopy_matching_finset o e e' he he' s
  exact ⟨H, K, hH0, hHc, hHi, hK, hKfix, hKfixi, hH1o,
    fun i x hx => hmatch i (hs i) x hx⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
