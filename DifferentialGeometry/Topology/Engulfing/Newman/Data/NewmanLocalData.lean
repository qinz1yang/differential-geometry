import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalOptimalApproximation
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.GridSubdivision
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry
open scoped _root_.Topology ContinuousMap

section CompactControl

variable {Z M : Type*} [TopologicalSpace Z] [PseudoMetricSpace M]

theorem exists_perturbation_control (g : C(Z, M)) {A : Set Z} (hA : IsCompact A)
    {V X : Set M} (hV : IsOpen V) (hX : IsClosed X)
    (hgV : g '' A ⊆ V) (hgX : Disjoint (g '' A) X) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : Z → M, (∀ x ∈ A, dist (f x) (g x) < ε) →
      f '' A ⊆ V ∧ Disjoint (f '' A) X := by
  have hsub : g '' A ⊆ V ∩ Xᶜ := fun y hy =>
    ⟨hgV hy, fun hyX => disjoint_left.mp hgX hy hyX⟩
  obtain ⟨ε, hε, hthick⟩ := (hA.image g.continuous).exists_thickening_subset_open
    (hV.inter hX.isOpen_compl) hsub
  refine ⟨ε, hε, fun f hf => ?_⟩
  have hnew : f '' A ⊆ V ∩ Xᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    apply hthick
    exact mem_thickening_iff.mpr ⟨g x, mem_image_of_mem g hx, hf x hx⟩
  exact ⟨fun _ hy => (hnew hy).1,
    disjoint_left.mpr (fun _ hy hyX => (hnew hy).2 hyX)⟩

theorem exists_finite_perturbation_control {ι : Type*} (I : Finset ι) (g : C(Z, M))
    (A : ι → Set Z) (V X : ι → Set M)
    (hA : ∀ i ∈ I, IsCompact (A i)) (hV : ∀ i ∈ I, IsOpen (V i))
    (hX : ∀ i ∈ I, IsClosed (X i)) (hgV : ∀ i ∈ I, g '' A i ⊆ V i)
    (hgX : ∀ i ∈ I, Disjoint (g '' A i) (X i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : Z → M, (∀ x, dist (f x) (g x) < ε) →
      ∀ i ∈ I, f '' A i ⊆ V i ∧ Disjoint (f '' A i) (X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, fun _ _ _ hi => (Finset.notMem_empty _ hi).elim⟩
  | @insert i I hi ih =>
    obtain ⟨δ, hδ, hδcontrol⟩ := exists_perturbation_control g
      (hA i (Finset.mem_insert_self _ _)) (hV i (Finset.mem_insert_self _ _))
      (hX i (Finset.mem_insert_self _ _)) (hgV i (Finset.mem_insert_self _ _))
      (hgX i (Finset.mem_insert_self _ _))
    obtain ⟨η, hη, hηcontrol⟩ := ih
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hV j (Finset.mem_insert_of_mem hj))
      (fun j hj => hX j (Finset.mem_insert_of_mem hj))
      (fun j hj => hgV j (Finset.mem_insert_of_mem hj))
      (fun j hj => hgX j (Finset.mem_insert_of_mem hj))
    refine ⟨min δ η, lt_min hδ hη, fun f hf j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hδcontrol f (fun x _ => (hf x).trans_le (min_le_left _ _))
    · exact hηcontrol f (fun x => (hf x).trans_le (min_le_right _ _)) j hj

end CompactControl

section LocalData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] {n p : ℕ}

structure BufferedChart (M : Type*) [TopologicalSpace M] (n : ℕ) where
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  center : EuclideanSpace ℝ (Fin n)
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  radii_lt : innerRadius < outerRadius
  outer_subset : closedBall center outerRadius ⊆ chart.target

def BufferedChart.core (b : BufferedChart M n) : Set M :=
  b.chart.source ∩ b.chart ⁻¹' ball b.center b.innerRadius

theorem BufferedChart.isOpen_core (b : BufferedChart M n) : IsOpen b.core :=
  b.chart.isOpen_inter_preimage isOpen_ball

theorem exists_bufferedChart_at (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {x : M} (hx : x ∈ e.source) :
    ∃ b : BufferedChart M n, b.chart = e ∧ x ∈ b.core := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let b : BufferedChart M n :=
    { chart := e
      center := e x
      innerRadius := δ / 4
      outerRadius := δ / 2
      inner_pos := by positivity
      radii_lt := by linarith
      outer_subset := (closedBall_subset_ball (by linarith : δ / 2 < δ)).trans hball }
  refine ⟨b, rfl, hx, ?_⟩
  exact mem_ball_self b.inner_pos

structure AdaptedPiecewiseLinearChart (K L : SimplicialComplex ℝ E) (g : C(K.space, M))
    (X : Set M) (n p : ℕ) extends BufferedChart M n where
  fixed_affine : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → g x ∈ toBufferedChart.core →
      chart (g x) = A x.1
  fixed_injective : InjOn (fun x : K.space => chart (g x))
    (Subtype.val ⁻¹' L.space ∩ g ⁻¹' toBufferedChart.core)
  obstacle : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))
  obstacle_finite : obstacle.faces.Finite
  obstacle_dimension : ∀ s ∈ obstacle.faces, s.card ≤ p + 1
  obstacle_contains : chart '' (X ∩ toBufferedChart.core) ⊆ obstacle.space

structure FiniteAdaptedPiecewiseLinearCover (K L : SimplicialComplex ℝ E) (g : C(K.space, M))
    (X : Set M) (n p : ℕ) where
  count : ℕ
  data : Fin count → AdaptedPiecewiseLinearChart K L g X n p
  covers : ∀ x : K.space, ∃ i, g x ∈ (data i).toBufferedChart.core
  obstacle_closed : IsClosed X

def AdaptedPiecewiseLinearChart.withMap {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
    (b : AdaptedPiecewiseLinearChart K L g X n p) (f : C(K.space, M))
    (hfix : ∀ x : K.space, x.1 ∈ L.space → f x = g x) : AdaptedPiecewiseLinearChart K L f X n p where
  toBufferedChart := b.toBufferedChart
  fixed_affine := by
    intro s hs
    obtain ⟨T, hT⟩ := b.fixed_affine s hs
    refine ⟨T, fun x hx hsource => ?_⟩
    have heq := hfix x (L.convexHull_subset_space hs hx)
    rw [heq]
    exact hT x hx (heq ▸ hsource)
  fixed_injective := by
    intro x hx y hy hxy
    have hxfix := hfix x hx.1
    have hyfix := hfix y hy.1
    change b.chart (f x) = b.chart (f y) at hxy
    rw [hxfix, hyfix] at hxy
    have hxcore : g x ∈ b.toBufferedChart.core := by rw [← hxfix]; exact hx.2
    have hycore : g y ∈ b.toBufferedChart.core := by rw [← hyfix]; exact hy.2
    exact b.fixed_injective ⟨hx.1, hxcore⟩ ⟨hy.1, hycore⟩ hxy
  obstacle := b.obstacle
  obstacle_finite := b.obstacle_finite
  obstacle_dimension := b.obstacle_dimension
  obstacle_contains := b.obstacle_contains

def FiniteAdaptedPiecewiseLinearCover.withMap {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
    (b : FiniteAdaptedPiecewiseLinearCover K L g X n p) (f : C(K.space, M))
    (hfix : ∀ x : K.space, x.1 ∈ L.space → f x = g x)
    (hcover : ∀ x : K.space, ∃ i, f x ∈ (b.data i).toBufferedChart.core) :
    FiniteAdaptedPiecewiseLinearCover K L f X n p where
  count := b.count
  data i := (b.data i).withMap f hfix
  covers := hcover
  obstacle_closed := b.obstacle_closed

end LocalData

section ChartSubdivision

variable {E M ι : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M]

theorem exists_open_cover_edge_stellar_refinement
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : C(K.space, M))
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x : K.space, ∃ i, g x ∈ U i)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ (P : SimplicialComplex ℝ E) (I : Finset ι),
      P.faces.Finite ∧ P.space = K.space ∧ simplicialRefines P K ∧
      (∀ s ∈ P.faces, s.card ≤ d + 1) ∧ EdgeStellarRefinement K P ∧
      ∀ s ∈ P.faces, ∃ i ∈ I,
        ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → g x ∈ U i := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  let V : ι → Set K.space := fun i => g ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage g.continuous
  have hCov : (univ : Set K.space) ⊆ ⋃ i, V i :=
    fun x _ => by obtain ⟨i, hi⟩ := hcover x; exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover V hV hCov
  have hCovI : (univ : Set K.space) ⊆ ⋃ i : I, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hI hx)
    obtain ⟨hiI, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i, hiI⟩, hxi⟩
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i : I => hV i) hCovI
  obtain ⟨P, hP, hspace, href, hdim, hmesh, hstellar⟩ :=
    exists_fine_edge_stellar_refinement K hK hd hδ
  refine ⟨P, I, hP, hspace, href, hdim, hstellar, ?_⟩
  intro s hs
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_faces hs
  have haK : a ∈ K.space := hspace ▸ P.subset_space hs ha
  obtain ⟨i, hi⟩ := hδcover ⟨a, haK⟩ (mem_univ _)
  refine ⟨i.1, i.2, fun x hx => hi ?_⟩
  apply mem_ball.mpr
  change dist x.1 a < δ
  exact (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
    hx (subset_convexHull ℝ _ ha)).trans_lt (hmesh s hs)

theorem exists_buffered_chart_edge_stellar_refinement {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : C(K.space, M))
    (b : ι → BufferedChart M n) (hcover : ∀ x : K.space, ∃ i, g x ∈ (b i).core)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ (P : SimplicialComplex ℝ E) (I : Finset ι),
      P.faces.Finite ∧ P.space = K.space ∧ simplicialRefines P K ∧
      (∀ s ∈ P.faces, s.card ≤ d + 1) ∧ EdgeStellarRefinement K P ∧
      ∀ s ∈ P.faces, ∃ i ∈ I,
        ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) →
          g x ∈ (b i).chart.source ∧
            (b i).chart (g x) ∈ ball (b i).center (b i).innerRadius :=
  exists_open_cover_edge_stellar_refinement K hK g (fun i => (b i).core)
    (fun i => (b i).isOpen_core) hcover hd

end ChartSubdivision

section Expansion

variable {E M ι : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M]

theorem exists_chart_refinement_preserving_expansions {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : C(K.space, M))
    (b : ι → BufferedChart M n) (hcover : ∀ x : K.space, ∃ i, g x ∈ (b i).core)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ (P : SimplicialComplex ℝ E) (I : Finset ι),
      P.faces.Finite ∧ P.space = K.space ∧ simplicialRefines P K ∧
      (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      (∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn P A C) ∧
      ∀ s ∈ P.faces, ∃ i ∈ I,
        ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → g x ∈ (b i).core := by
  classical
  obtain ⟨P, I, hP, hspace, href, hdim, hstellar, hcharts⟩ :=
    exists_buffered_chart_edge_stellar_refinement K hK g b hcover hd
  refine ⟨P, I, hP, hspace, href, hdim, ?_, hcharts⟩
  intro A C hAC
  exact hstellar.preserves (fun T => FiniteSimplexExpansionIn T A C)
    (fun _ d h => d.preserves_finite_expansion h) hAC

end Expansion

section LocalModification

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [PseudoMetricSpace M] {n p d : ℕ}

omit [FiniteDimensional ℝ E] in
theorem FiniteAdaptedPiecewiseLinearCover.exists_reuse_tolerance
    {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
    (b : FiniteAdaptedPiecewiseLinearCover K L g X n p) (hK : K.faces.Finite) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : C(K.space, M),
      (∀ x : K.space, x.1 ∈ L.space → f x = g x) →
      (∀ x, dist (f x) (g x) < ε) → Nonempty (FiniteAdaptedPiecewiseLinearCover K L f X n p) := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  let V : Set M := ⋃ i, (b.data i).toBufferedChart.core
  have hV : IsOpen V := isOpen_iUnion (fun i => (b.data i).toBufferedChart.isOpen_core)
  have hgV : g '' univ ⊆ V := by
    rintro _ ⟨x, _, rfl⟩
    obtain ⟨i, hi⟩ := b.covers x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ε, hε, hcontrol⟩ := exists_perturbation_control g isCompact_univ hV
    isClosed_empty hgV (disjoint_empty _)
  refine ⟨ε, hε, fun f hfix hnear => ?_⟩
  have hnew := (hcontrol f (fun x _ => hnear x)).1
  refine ⟨b.withMap f hfix (fun x => ?_)⟩
  exact mem_iUnion.mp (hnew (mem_image_of_mem f (mem_univ x)))

structure LocalOptimalModel (K : SimplicialComplex ℝ E)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (G : C(K.space, M))
    (A : Set E) (d : ℕ) where
  source : SimplicialComplex ℝ E
  source_finite : source.faces.Finite
  source_refines : simplicialRefines source K
  source_dimension : ∀ s ∈ source.faces, s.card ≤ d + 1
  core_subset : A ⊆ source.space
  inclusion : C(source.space, K.space)
  inclusion_val : ∀ x, (inclusion x).1 = x.1
  neighborhood : Set K.space
  neighborhood_closed : IsClosed neighborhood
  core_interior : (Subtype.val ⁻¹' A : Set K.space) ⊆ interior neighborhood
  vertices : E → EuclideanSpace ℝ (Fin n)
  correction : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)
  general_position : ∀ s : Finset E, (s : Set E) ⊆ source.vertices → s.card ≤ n + 1 →
    AffineIndependent ℝ (fun x : s => vertices x)
  image_in_chart : ∀ x, G (inclusion x) ∈ e.source
  eq_candidate : ∀ x, inclusion x ∈ neighborhood →
    e (G (inclusion x)) = correctedInterpolant source source_finite vertices correction x
  affine_refinement : ∃ Q : SimplicialComplex ℝ E, Q.faces.Finite ∧ Q.space = source.space ∧
    simplicialRefines Q source ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧
    ∀ s ∈ Q.faces,
      (∀ x : source.space, x.1 ∈ convexHull ℝ (s : Set E) → inclusion x ∈ neighborhood) →
      ∃ T : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ x : source.space, x.1 ∈ convexHull ℝ (s : Set E) → e (G (inclusion x)) = T x.1

theorem AdaptedPiecewiseLinearChart.exists_local_modification
    {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
    (b : AdaptedPiecewiseLinearChart K L g X n p) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    {A : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space)
    (hcore : ∀ x : K.space, x.1 ∈ A → g x ∈ b.toBufferedChart.core)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(K.space, M),
      (∀ x, g x ∉ b.toBufferedChart.core → G x = g x) ∧
      (∀ x : K.space, x.1 ∈ L.space → G x = g x) ∧
      (∀ x, dist (G x) (g x) < ε) ∧ Nonempty (LocalOptimalModel K b.chart G A d) := by
  have hopen : IsOpen (g ⁻¹' b.toBufferedChart.core) :=
    b.toBufferedChart.isOpen_core.preimage g.continuous
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
  have hAU : A ⊆ U := by
    intro x hx
    have h := hcore ⟨x, hAK hx⟩ hx
    change (⟨x, hAK hx⟩ : K.space) ∈ g ⁻¹' b.toBufferedChart.core at h
    rw [← hUeq] at h
    exact h
  have hUm (x : K.space) (hx : x.1 ∈ U) : g x ∈ b.toBufferedChart.core := by
    change x ∈ g ⁻¹' b.toBufferedChart.core
    rw [← hUeq]
    exact hx
  have hfixed : ∀ s ∈ L.faces, ∃ T : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → x.1 ∈ U → b.chart (g x) = T x.1 := by
    intro s hs
    obtain ⟨T, hT⟩ := b.fixed_affine s hs
    exact ⟨T, fun x hx hxU => hT x hx (hUm x hxU)⟩
  have hinj : InjOn (fun x : K.space => b.chart (g x)) (Subtype.val ⁻¹' (L.space ∩ U)) := by
    intro x hx y hy hxy
    exact b.fixed_injective ⟨hx.1, hUm x hx.2⟩ ⟨hy.1, hUm y hy.2⟩ hxy
  obtain ⟨G, P, hP, κ, B, w, H, href, hdim, hAP, -, hκ, hB, hAB,
    hgp, hGout, hGfix, hGnear, hGsource, hGcore, hPL⟩ :=
    exists_local_optimal_approximation K hK L hLK hd b.chart g b.center b.radii_lt b.outer_subset hε
      hA hAK hU hAU (fun x hx => (hUm x hx).1)
      (fun x hx => ball_subset_closedBall (hUm x hx).2) hfixed hinj
  refine ⟨G, fun x hx => hGout x (fun hxU => hx (hUm x hxU)), hGfix, hGnear, ?_⟩
  exact ⟨⟨P, hP, href, hdim, hAP, κ, hκ, B, hB, hAB, w, H, hgp, hGsource, hGcore, hPL⟩⟩

theorem AdaptedPiecewiseLinearChart.exists_local_modification_preserving {ι : Type*}
    {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
    (b : AdaptedPiecewiseLinearChart K L g X n p) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    {A : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space)
    (hcore : ∀ x : K.space, x.1 ∈ A → g x ∈ b.toBufferedChart.core)
    (I : Finset ι) (C : ι → Set K.space) (V Z : ι → Set M)
    (hC : ∀ i ∈ I, IsCompact (C i)) (hV : ∀ i ∈ I, IsOpen (V i))
    (hZ : ∀ i ∈ I, IsClosed (Z i)) (hgV : ∀ i ∈ I, g '' C i ⊆ V i)
    (hgZ : ∀ i ∈ I, Disjoint (g '' C i) (Z i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(K.space, M),
      (∀ x, g x ∉ b.toBufferedChart.core → G x = g x) ∧
      (∀ x : K.space, x.1 ∈ L.space → G x = g x) ∧
      (∀ x, dist (G x) (g x) < ε) ∧ Nonempty (LocalOptimalModel K b.chart G A d) ∧
      ∀ i ∈ I, G '' C i ⊆ V i ∧ Disjoint (G '' C i) (Z i) := by
  obtain ⟨δ, hδ, hcontrol⟩ := exists_finite_perturbation_control I g C V Z hC hV hZ hgV hgZ
  obtain ⟨G, hGout, hGfix, hGnear, hmodel⟩ :=
    b.exists_local_modification hK hLK hd hA hAK hcore (lt_min hε hδ)
  exact ⟨G, hGout, hGfix, fun x => (hGnear x).trans_le (min_le_left _ _), hmodel,
    hcontrol G (fun x => (hGnear x).trans_le (min_le_right _ _))⟩

end LocalModification

section MembraneRefinement

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [PseudoMetricSpace M] {n p d : ℕ}

theorem FiniteAdaptedPiecewiseLinearCover.exists_refinement_with_local_modifications
    {K L : SimplicialComplex ℝ E} {g : C(K.space, M)} {X : Set M}
    (b : FiniteAdaptedPiecewiseLinearCover K L g X n p) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ P : SimplicialComplex ℝ E,
      P.faces.Finite ∧ P.space = K.space ∧ simplicialRefines P K ∧
      (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      (∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn P A C) ∧
      ∀ s ∈ P.faces, ∃ i : Fin b.count, ∀ ε : ℝ, 0 < ε →
        ∃ G : C(K.space, M),
          (∀ x, g x ∉ (b.data i).toBufferedChart.core → G x = g x) ∧
          (∀ x : K.space, x.1 ∈ L.space → G x = g x) ∧
          (∀ x, dist (G x) (g x) < ε) ∧
          Nonempty (LocalOptimalModel K (b.data i).chart G (convexHull ℝ (s : Set E)) d) := by
  obtain ⟨P, I, hP, hspace, href, hdim, hexp, hcharts⟩ :=
    exists_chart_refinement_preserving_expansions K hK g
      (fun i => (b.data i).toBufferedChart) b.covers hd
  refine ⟨P, hP, hspace, href, hdim, hexp, ?_⟩
  intro s hs
  obtain ⟨i, -, hi⟩ := hcharts s hs
  refine ⟨i, fun ε hε => ?_⟩
  exact (b.data i).exists_local_modification hK hLK hd
    (s.finite_toSet.isCompact_convexHull ℝ)
    (fun x hx => hspace ▸ P.convexHull_subset_space hs hx) hi hε

end MembraneRefinement

end DifferentialGeometry.Topology.Engulfing
