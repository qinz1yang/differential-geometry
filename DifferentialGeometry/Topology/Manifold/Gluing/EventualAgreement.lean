import DifferentialGeometry.Topology.Compactness.FiniteRefinement
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates
import Mathlib.Data.Set.UnionLift
import Mathlib.Order.Filter.AtTopBot.Basic

section

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι M E F H H' : Type*} [Finite ι]
  [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H'] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {N : ℕ → Type*} [∀ k, TopologicalSpace (N k)] [∀ k, ChartedSpace H' (N k)]
  {n : WithTop ℕ∞}

theorem exists_contMDiffOn_eventually_eqOn_of_finite_cover
    (V : Set M) (W : ι → Set M) (hW : ∀ i, IsOpen (W i))
    (hV : V ⊆ ⋃ i, W i) (f : ι → ∀ k, M → N k) (b : ∀ k, N k)
    (hsmooth : ∀ i, ∀ᶠ k in atTop, ContMDiffOn I J n (f i k) (W i))
    (hcompat : ∀ i j, ∀ᶠ k in atTop,
      EqOn (f i k) (f j k) (V ∩ W i ∩ W j)) :
    ∃ F : ∀ k, M → N k,
      (∀ k, ContMDiffOn I J n (F k) V) ∧
      (∀ᶠ k in atTop, ∀ i, EqOn (F k) (f i k) (V ∩ W i)) ∧
      ∀ k x, x ∉ V → F k x = b k := by
  classical
  have htail : ∀ᶠ k in atTop,
      (∀ i, ContMDiffOn I J n (f i k) (W i)) ∧
      (∀ i j, ∀ x ∈ V ∩ W i ∩ W j, f i k x = f j k x) := by
    rw [Filter.eventually_and]
    constructor
    · exact (Filter.eventually_all).2 hsmooth
    · exact (Filter.eventually_all).2 (fun i => (Filter.eventually_all).2 (hcompat i))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp htail
  let S : ι → Set M := fun i => V ∩ W i
  have hSV : V ⊆ ⋃ i, S i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hV hx)
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  let glued : ∀ k, K ≤ k → V → N k := fun k hk =>
    Set.iUnionLift S (fun i z => f i k z)
      (fun i j x hxi hxj => (hK k hk).2 i j x ⟨⟨hxi.1, hxi.2⟩, hxj.2⟩)
      V hSV
  let extended : ∀ k, K ≤ k → M → N k := fun k hk =>
    Function.extend Subtype.val (glued k hk) (fun _ => b k)
  have hext : ∀ k hk i, EqOn (extended k hk) (f i k) (V ∩ W i) := by
    intro k hk i x hx
    change Function.extend Subtype.val (glued k hk) (fun _ => b k)
      ((⟨x, hx.1⟩ : V) : M) = f i k x
    rw [Subtype.val_injective.extend_apply]
    simpa [glued, S] using (Set.iUnionLift_of_mem (S := S) (f := fun i z => f i k z) (T := V)
      ⟨x, hx.1⟩ hx)
  let F : ∀ k, M → N k := fun k =>
    if hk : K ≤ k then extended k hk else fun _ => b k
  refine ⟨F, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : K ≤ k
    · simp only [F, dif_pos hk]
      apply contMDiffOn_of_locally_contMDiffOn
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hV hx)
      refine ⟨W i, hW i, hi, ?_⟩
      exact ((hK k hk).1 i).congr_mono (hext k hk i) inter_subset_right
    · simp only [F, dif_neg hk]
      exact contMDiffOn_const
  · filter_upwards [eventually_ge_atTop K] with k hk i
    simp only [F, dif_pos hk]
    exact hext k hk i
  · intro k x hx
    by_cases hk : K ≤ k
    · simp only [F, dif_pos hk, extended]
      apply Function.extend_apply'
      rintro ⟨y, hy⟩
      exact hx (hy ▸ y.property)
    · simp only [F, dif_neg hk]

end DifferentialGeometry.Topology.Manifold

end

end

section

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A X E F H H' : Type*} [TopologicalSpace X]
  [LocallyCompactSpace X] [RegularSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H'] [ChartedSpace H X]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {Y : ℕ → Type*} [∀ k, TopologicalSpace (Y k)] [∀ k, ChartedSpace H' (Y k)]
  {n : WithTop ℕ∞}

theorem exists_contMDiffOn_eventually_eqOn_of_isCompact_closure
    (V : Set X) (hV : IsCompact (closure V))
    (O : A → Set X) (hO : ∀ a, IsOpen (O a)) (hcover : closure V ⊆ ⋃ a, O a)
    (f : A → ∀ k, X → Y k) (b : ∀ k, Y k)
    (hsmooth : ∀ a, ∀ᶠ k in atTop, ContMDiffOn I J n (f a k) (O a))
    (hcompat : ∀ a a' (L : Set X), IsCompact L → L ⊆ O a ∩ O a' →
      ∀ᶠ k in atTop, EqOn (f a k) (f a' k) L) :
    ∃ F : ∀ k, X → Y k,
      (∀ k, ContMDiffOn I J n (F k) V) ∧
      (∀ a (L : Set X), IsCompact L → L ⊆ V ∩ O a →
        ∀ᶠ k in atTop, EqOn (F k) (f a k) L) ∧
      ∀ k x, x ∉ V → F k x = b k := by
  classical
  have hchoose : ∀ x : closure V, ∃ a : A, (x : X) ∈ O a := by
    intro x
    exact mem_iUnion.mp (hcover x.property)
  choose sigma hsigma using hchoose
  obtain ⟨t, W, hW, ht⟩ := hV.exists_finite_subcover_isCompact_closure
    (fun x => O (sigma x)) (fun x => (hO (sigma x)).mem_nhds (hsigma x))
  have hWV : V ⊆ ⋃ i : t, W i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (subset_closure hx))
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hlocal : ∀ i : t, ∀ᶠ k in atTop,
      ContMDiffOn I J n (f (sigma i.val) k) (W i.val) := by
    intro i
    exact (hsmooth (sigma i.val)).mono fun _ hk =>
      hk.mono (fun x hx => (hW i.val).2.2.2 (subset_closure hx))
  have hoverlap : ∀ i j : t, ∀ᶠ k in atTop,
      EqOn (f (sigma i.val) k) (f (sigma j.val) k) (V ∩ W i.val ∩ W j.val) := by
    intro i j
    have htail := hcompat (sigma i.val) (sigma j.val)
      (closure (W i.val) ∩ closure (W j.val))
      ((hW i.val).2.2.1.inter_right isClosed_closure)
      (fun x hx => ⟨(hW i.val).2.2.2 hx.1, (hW j.val).2.2.2 hx.2⟩)
    exact htail.mono fun _ hk x hx => hk ⟨subset_closure hx.1.2, subset_closure hx.2⟩
  obtain ⟨F, hFsmooth, hFlocal, hFout⟩ :=
    exists_contMDiffOn_eventually_eqOn_of_finite_cover V
      (fun i : t => W i.val) (fun i => (hW i.val).1) hWV
      (fun i : t => f (sigma i.val)) b hlocal hoverlap
  refine ⟨F, hFsmooth, ?_, hFout⟩
  intro a L hL hLV
  have hcompare : ∀ i : t, ∀ᶠ k in atTop,
      EqOn (f (sigma i.val) k) (f a k) (L ∩ closure (W i.val)) := by
    intro i
    exact hcompat (sigma i.val) a (L ∩ closure (W i.val))
      (hL.inter_right isClosed_closure)
      (fun x hx => ⟨(hW i.val).2.2.2 hx.2, (hLV hx.1).2⟩)
  filter_upwards [hFlocal, Filter.eventually_all.mpr hcompare] with k hk hck x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hWV (hLV hx).1)
  exact (hk i ⟨(hLV hx).1, hi⟩).trans (hck i ⟨hx, subset_closure hi⟩)

end DifferentialGeometry.Topology.Manifold

end

end

section

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι Q E G H : Type*} [TopologicalSpace Q] [LocallyCompactSpace Q] [RegularSpace Q]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace H]
  [ChartedSpace E Q] {J : ModelWithCorners 𝕜 G H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  {n : WithTop ℕ∞}

theorem exists_contMDiffOn_eventually_eqOn_of_open_coordinate_cover
    (U : TopologicalSpace.Opens E) (inc : ι → U → Q)
    (hinj : ∀ i, Function.Injective (inc i))
    (hinc : ∀ i, IsLocalDiffeomorph (modelWithCornersSelf 𝕜 E)
      (modelWithCornersSelf 𝕜 E) n (inc i))
    (V : Set Q) (hV : IsCompact (closure V))
    (hcover : ∀ q ∈ closure V, ∃ i z, inc i z = q)
    (W : ι × U → Set E) (hW : ∀ a, IsOpen (W a))
    (hcenter : ∀ a : ι × U, (a.2 : E) ∈ W a)
    (f : (ι × U) → ∀ k, E → M k) (b : ∀ k, M k)
    (hsmooth : ∀ a, ∀ᶠ k in atTop,
      ContMDiffOn (modelWithCornersSelf 𝕜 E) J n (f a k) (W a))
    (hcompat : ∀ a a' (L : Set Q), IsCompact L →
      L ⊆ (inc a.1 '' (Subtype.val ⁻¹' W a)) ∩
        (inc a'.1 '' (Subtype.val ⁻¹' W a')) →
      ∀ᶠ k in atTop, EqOn
        (Function.extend (inc a.1) (fun z : U => f a k z) (fun _ => b k))
        (Function.extend (inc a'.1) (fun z : U => f a' k z) (fun _ => b k)) L) :
    ∃ F : ∀ k, Q → M k,
      (∀ k, ContMDiffOn (modelWithCornersSelf 𝕜 E) J n (F k) V) ∧
      (∀ a (L : Set Q), IsCompact L →
        L ⊆ V ∩ (inc a.1 '' (Subtype.val ⁻¹' W a)) →
        ∀ᶠ k in atTop, EqOn (F k)
          (Function.extend (inc a.1) (fun z : U => f a k z) (fun _ => b k)) L) ∧
      ∀ k q, q ∉ V → F k q = b k := by
  apply exists_contMDiffOn_eventually_eqOn_of_isCompact_closure V hV
    (fun a => inc a.1 '' (Subtype.val ⁻¹' W a))
    (fun a => (hinc a.1).isOpenMap _ ((hW a).preimage continuous_subtype_val))
  · intro q hq
    obtain ⟨i, z, rfl⟩ := hcover q hq
    exact mem_iUnion.mpr ⟨(i, z), z, hcenter (i, z), rfl⟩
  · intro a
    exact (hsmooth a).mono fun _ hk =>
      contMDiffOn_extend_from_open_coordinates U (hinc a.1) (hinj a.1)
        (fun _ => b _) (hW a) hk
  · exact hcompat

end DifferentialGeometry.Topology.Manifold

end

end
