import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionOfFamilyBCF
import DifferentialGeometry.Topology.Ehresmann.LocalTrivOverArcBCF
import DifferentialGeometry.Topology.Ehresmann.LoopBundleBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChartComponentsBCF

/-!
# The circle-bundle pieces over the components of the base curve (lane S-BCF03b; BCF03 G7, P4–P7)

Abstract kernel (no geometry of the chain): `S ⊆ Wt` is compact-closed, `f : Wt → H` is the circle
map with circle charts over `Γ = f '' S`, and `S` is saturated by the whole fibres of `f`
(`hsat`). The base curve `Γ` is a finite disjoint union of arcs `a k` and loops `l j`
(`exists_components_of_halfCharts_BCF`); the pieces are `P k = S ∩ f⁻¹(component k)`.

* `compSet_BCF`: the component sets of the arcs and loops;
* `piece_BCF`: the piece over a component;
* `piece_closed_BCF`, `piece_eq_source_BCF`, `piece_nonempty_BCF`, `piece_disjoint_BCF`,
  `iUnion_piece_BCF`: closed nonempty pairwise disjoint pieces covering `S`, `P k = X ∩ f⁻¹ G k`;
* `isPreconnected_piece_BCF`: the pieces are preconnected (annulus image / loop bundle);
* `annulus_param_piece_BCF` (P6) and `circle_base_piece_BCF` (P7): the parametrizations demanded
  by `EmbeddedFacePartition_BCF`, with the end circles equal to the whole end fibres.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

section Components

variable {H : Type*} {n m : ℕ}

/-- The base set of a component: an arc `a k '' [0, 1]` or a loop `range (l j)`. -/
def compSet_BCF (a : Fin n → ℝ → H) (l : Fin m → Circle → H) : Fin n ⊕ Fin m → Set H
  | .inl k => a k '' Icc 0 1
  | .inr j => range (l j)

theorem compSet_disjoint_BCF {a : Fin n → ℝ → H} {l : Fin m → Circle → H}
    (haa : ∀ k k', k ≠ k' → Disjoint (a k '' Icc 0 1) (a k' '' Icc 0 1))
    (hll : ∀ j j', j ≠ j' → Disjoint (range (l j)) (range (l j')))
    (hal : ∀ k j, Disjoint (a k '' Icc 0 1) (range (l j))) :
    Pairwise (Disjoint on compSet_BCF a l) := by
  intro k k' hkk'
  rcases k with k | j <;> rcases k' with k' | j'
  · exact haa k k' fun h => hkk' (by rw [h])
  · exact hal k j'
  · exact (hal k' j).symm
  · exact hll j j' fun h => hkk' (by rw [h])

variable [TopologicalSpace H] [T2Space H]

theorem isClosed_compSet_BCF {a : Fin n → ℝ → H} {l : Fin m → Circle → H}
    (ha : ∀ k, ContinuousOn (a k) (Icc 0 1)) (hl : ∀ j, Continuous (l j))
    (k : Fin n ⊕ Fin m) : IsClosed (compSet_BCF a l k) := by
  rcases k with k | j
  · exact (isCompact_Icc.image_of_continuousOn (ha k)).isClosed
  · exact (isCompact_range (hl j)).isClosed

end Components


section Pieces

variable {Wt H : Type*} {n m : ℕ} {S X : Set Wt} {f : Wt → H} {a : Fin n → ℝ → H}
  {l : Fin m → Circle → H}

/-- The piece of `S` over the component `k` of the base curve. -/
def piece_BCF (S : Set Wt) (f : Wt → H) (a : Fin n → ℝ → H) (l : Fin m → Circle → H)
    (k : Fin n ⊕ Fin m) : Set Wt :=
  S ∩ f ⁻¹' compSet_BCF a l k

theorem piece_subset_BCF (k : Fin n ⊕ Fin m) : piece_BCF S f a l k ⊆ S := inter_subset_left

theorem piece_eq_source_BCF (hSX : S ⊆ X) (hsat : ∀ p ∈ S, ∀ q ∈ X, f q = f p → q ∈ S)
    (hcov : f '' S = ⋃ k, compSet_BCF a l k) (k : Fin n ⊕ Fin m) :
    piece_BCF S f a l k = X ∩ f ⁻¹' compSet_BCF a l k := by
  ext q
  constructor
  · rintro ⟨hqS, hqk⟩
    exact ⟨hSX hqS, hqk⟩
  · rintro ⟨hqX, hqk⟩
    have : f q ∈ f '' S := hcov ▸ mem_iUnion.mpr ⟨k, hqk⟩
    obtain ⟨p, hpS, hpq⟩ := this
    exact ⟨hsat p hpS q hqX hpq.symm, hqk⟩

theorem iUnion_piece_BCF (hcov : f '' S = ⋃ k, compSet_BCF a l k) :
    (⋃ k, piece_BCF S f a l k) = S := by
  ext p
  constructor
  · intro hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact hk.1
  · intro hp
    have : f p ∈ ⋃ k, compSet_BCF a l k := hcov ▸ mem_image_of_mem f hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp this
    exact mem_iUnion.mpr ⟨k, hp, hk⟩

theorem piece_disjoint_BCF (hdisj : Pairwise (Disjoint on compSet_BCF a l)) :
    Pairwise (Disjoint on piece_BCF S f a l) := fun _ _ hkk' =>
  ((hdisj hkk').preimage f).mono inter_subset_right inter_subset_right

theorem piece_nonempty_BCF (hcov : f '' S = ⋃ k, compSet_BCF a l k)
    (k : Fin n ⊕ Fin m) : (piece_BCF S f a l k).Nonempty := by
  have hne : (compSet_BCF a l k).Nonempty := by
    rcases k with k | j
    · exact ⟨a k 0, 0, ⟨le_refl _, zero_le_one⟩, rfl⟩
    · exact range_nonempty _
  obtain ⟨y, hy⟩ := hne
  have : y ∈ f '' S := hcov ▸ mem_iUnion.mpr ⟨k, hy⟩
  obtain ⟨p, hpS, rfl⟩ := this
  exact ⟨p, hpS, hy⟩

end Pieces

section PiecesTop

variable {Wt H : Type*} [TopologicalSpace Wt] [TopologicalSpace H] {n m : ℕ} {S X : Set Wt}
  {f : Wt → H} {a : Fin n → ℝ → H} {l : Fin m → Circle → H}

theorem piece_closed_BCF [T2Space H] (hS : IsClosed S) (hf : ContinuousOn f S)
    (ha : ∀ k, ContinuousOn (a k) (Icc 0 1)) (hl : ∀ j, Continuous (l j))
    (k : Fin n ⊕ Fin m) : IsClosed (piece_BCF S f a l k) :=
  hf.preimage_isClosed_of_isClosed hS (isClosed_compSet_BCF ha hl k)

/-- The whole fibre over a point with a circle chart is the circle slice of the chart. -/
theorem fibre_eq_range_of_chart_BCF {B₀ : Set H} {y : H}
    (hch : ∃ (σ : E2 → H) (φ : E2 × Circle → Wt) (O : Set H) (x₀ : E2), σ x₀ = y ∧
      IsEmbedding σ ∧ IsOpen O ∧ range σ = B₀ ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x) :
    ∃ g : Circle → Wt, Continuous g ∧ range g = X ∩ f ⁻¹' {y} := by
  obtain ⟨σ, φ, O, x₀, hx₀, hσ, hO, hσr, hφc, hφi, hφr, hφf⟩ := hch
  refine ⟨fun z => φ (x₀, z), hφc.comp (by fun_prop), ?_⟩
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    have hq : φ (x₀, z) ∈ range φ := mem_range_self _
    rw [hφr] at hq
    exact ⟨hq.1, by rw [mem_preimage, mem_singleton_iff, hφf, hx₀]⟩
  · rintro ⟨hqX, hqy⟩
    have hqy' : f q = y := hqy
    have hqr : q ∈ range φ := by
      rw [hφr]
      exact ⟨hqX, ⟨x₀, by rw [hx₀, hqy']⟩⟩
    obtain ⟨⟨x, z⟩, rfl⟩ := hqr
    have hx : x = x₀ := hσ.injective (by rw [← hφf x z, hqy', hx₀])
    subst hx
    exact ⟨z, rfl⟩

end PiecesTop


section PiecesParam

variable {Wt H : Type*} [TopologicalSpace Wt] [T2Space Wt] [TopologicalSpace H] {n m : ℕ}
  {S X : Set Wt} {f : Wt → H} {a : Fin n → ℝ → H} {l : Fin m → Circle → H} {B₀ : Set H}

/-- **P6, the annulus parametrization of the piece over an arc** (the end circles are the whole
fibres over the two ends). -/
theorem annulus_param_piece_BCF (hSX : S ⊆ X) (hsat : ∀ p ∈ S, ∀ q ∈ X, f q = f p → q ∈ S)
    (hcov : f '' S = ⋃ k, compSet_BCF a l k) (hB : f '' S ⊆ B₀)
    (hch : ∀ y ∈ f '' S, ∃ (σ : E2 → H) (φ : E2 × Circle → Wt) (O : Set H) (x₀ : E2),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = B₀ ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x)
    (ha : ∀ k, ContinuousOn (a k) (Icc 0 1) ∧ InjOn (a k) (Icc 0 1)) (k : Fin n) :
    ∃ e : Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1 → Wt, Continuous e ∧ Injective e ∧
      range e = piece_BCF S f a l (.inl k) ∧
      e '' {q | (q.2 : ℝ) = 0} = X ∩ f ⁻¹' {a k 0} ∧
      e '' {q | (q.2 : ℝ) = 1} = X ∩ f ⁻¹' {a k 1} := by
  have hGΓ : a k '' Icc 0 1 ⊆ f '' S := hcov ▸ subset_iUnion (compSet_BCF a l) (.inl k)
  obtain ⟨e, hec, hei, her, -, he0, he1⟩ := exists_annulus_param_BCF (X := X) (f := f)
    (Bs := B₀) (a := a k) (ha k).1 (ha k).2 (hGΓ.trans hB) fun y hy => hch y (hGΓ hy)
  let φs : Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1 ≃ₜ Circle × Icc (0 : ℝ) 1 :=
    circleSphereHomeomorph_BCF.symm.prodCongr (Homeomorph.refl _)
  have himg : ∀ r : ℝ, ∀ s : Set (Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1),
      s = {q | (q.2 : ℝ) = r} → (fun q => e (φs q)) '' s = e '' {q | (q.2 : ℝ) = r} := by
    intro r s hs
    subst hs
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨φs q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨φs.symm q, by simpa [φs] using hq, by simp⟩
  refine ⟨fun q => e (φs q), hec.comp φs.continuous, fun q q' h => φs.injective (hei h), ?_,
    ?_, ?_⟩
  · have hc : compSet_BCF a l (.inl k) = a k '' Icc 0 1 := rfl
    rw [piece_eq_source_BCF hSX hsat hcov, hc, ← her]
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φs q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨φs.symm q, by simp⟩
  · rw [himg 0 _ rfl, he0]
  · rw [himg 1 _ rfl, he1]

omit [T2Space Wt] in
/-- **P7, the projection of the piece over a loop to the circle.** -/
theorem circle_base_piece_BCF [T2Space H] (hSX : S ⊆ X)
    (hsat : ∀ p ∈ S, ∀ q ∈ X, f q = f p → q ∈ S) (hcov : f '' S = ⋃ k, compSet_BCF a l k)
    (hB : f '' S ⊆ B₀) (hf : ContinuousOn f X)
    (hch : ∀ y ∈ f '' S, ∃ (σ : E2 → H) (φ : E2 × Circle → Wt) (O : Set H) (x₀ : E2),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = B₀ ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x)
    (hl : ∀ j, Continuous (l j) ∧ Injective (l j)) (j : Fin m) :
    ∃ p : piece_BCF S f a l (.inr j) → Circle, Continuous p ∧ IsOpenMap p := by
  have hGΓ : range (l j) ⊆ f '' S := hcov ▸ subset_iUnion (compSet_BCF a l) (.inr j)
  obtain ⟨p, hpc, hpo, -⟩ := exists_circleBase_of_loop_BCF (X := X) (f := f) (Bs := B₀)
    (l := l j) (hl j).1 (hl j).2 (hGΓ.trans hB) hf (E := E2) (Q := Circle) (fun y hy => by
      obtain ⟨σ, φ, O, x₀, h1, h2, h3, h4, h5, -, h7, h8⟩ := hch y (hGΓ hy)
      exact ⟨σ, φ, O, x₀, h1, h2, h3, h4, h5, h7, h8⟩)
  let ψ : piece_BCF S f a l (.inr j) ≃ₜ (X ∩ f ⁻¹' range (l j) : Set Wt) :=
    Homeomorph.setCongr (piece_eq_source_BCF hSX hsat hcov (.inr j))
  exact ⟨fun q => p (ψ q), hpc.comp ψ.continuous, hpo.comp ψ.isOpenMap⟩


/-- **The pieces are preconnected** (an annulus over an arc, a circle bundle over a loop). -/
theorem isPreconnected_piece_BCF (hSX : S ⊆ X) (hsat : ∀ p ∈ S, ∀ q ∈ X, f q = f p → q ∈ S)
    (hcov : f '' S = ⋃ k, compSet_BCF a l k) (hB : f '' S ⊆ B₀)
    (hch : ∀ y ∈ f '' S, ∃ (σ : E2 → H) (φ : E2 × Circle → Wt) (O : Set H) (x₀ : E2),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = B₀ ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x)
    (ha : ∀ k, ContinuousOn (a k) (Icc 0 1) ∧ InjOn (a k) (Icc 0 1))
    (hl : ∀ j, Continuous (l j) ∧ Injective (l j)) (k : Fin n ⊕ Fin m) :
    IsPreconnected (piece_BCF S f a l k) := by
  rcases k with k | j
  · obtain ⟨e, hec, -, her, -, -⟩ := annulus_param_piece_BCF hSX hsat hcov hB hch ha k
    have : PreconnectedSpace (Metric.sphere (0 : E2) 1) :=
      (circleSphereHomeomorph_BCF.surjective.connectedSpace
        circleSphereHomeomorph_BCF.continuous).toPreconnectedSpace
    have : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
    rw [← her]
    exact isPreconnected_range hec
  · have hGΓ : range (l j) ⊆ f '' S := hcov ▸ subset_iUnion (compSet_BCF a l) (.inr j)
    have hfib : ∀ y ∈ range (l j), IsPreconnected (X ∩ f ⁻¹' {y}) := by
      intro y hy
      obtain ⟨g, hgc, hgr⟩ := fibre_eq_range_of_chart_BCF (hch y (hGΓ hy))
      rw [← hgr]
      exact isPreconnected_range hgc
    have hne : ∀ y ∈ range (l j), (X ∩ f ⁻¹' {y}).Nonempty := by
      intro y hy
      obtain ⟨g, hgc, hgr⟩ := fibre_eq_range_of_chart_BCF (hch y (hGΓ hy))
      rw [← hgr]
      exact range_nonempty _
    have h := isPreconnected_preimage_loop_BCF (X := X) (f := f) (Bs := B₀) (l := l j) (E := E2)
      (Q := Circle) (hl j).1 (hGΓ.trans hB) (fun y hy => by
        obtain ⟨σ, φ, O, x₀, h1, h2, h3, h4, h5, -, h7, h8⟩ := hch y (hGΓ hy)
        exact ⟨σ, φ, O, x₀, h1, h2, h3, h4, h5, h7, h8⟩) hne hfib
    rw [piece_eq_source_BCF hSX hsat hcov (.inr j)]
    exact h

end PiecesParam

end DifferentialGeometry.Topology.Surface
