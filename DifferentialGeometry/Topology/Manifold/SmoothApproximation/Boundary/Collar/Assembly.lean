import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Helpers
import DifferentialGeometry.Topology.Manifold.Diffeomorph.OfHomeomorph
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Assembly of the collar straightening: from local pieces to a `C¹` diffeomorphism

`eventually_exists_diffeomorph_of_collar_pieces`: let `h : A ≃ₜ B` be a homeomorphism of compact
manifolds with boundary (model `𝓡∂ (n + 1)`) and `f j : A → B` be `C¹` maps such that

* every point of `A` has an open neighbourhood on which eventually every `f j` is injective with
  invertible `mfderiv` (local pieces), and `f j → h` locally uniformly;
* `f j` maps boundary to boundary (read off defining functions `rA`, `rB`);
* `f j = h` on `{rA > δ j}`, and `h` maps `{rA ≤ δ j}` into the collar `{rB < aB / 2}` of `B`.

Then eventually every `f j` is a `C¹` diffeomorphism. Injectivity: the W2 argument (pieces and
separation off the pieces). Surjectivity without a boundary inverse function theorem: the image of
the interior is open (invariance of domain) and closed in the interior of `B`; a missed interior
point `y` would lie in the collar `{rB < aB / 2}` (since `f j = h` far from `∂A`), but the whole
collar segment through `y` up to height `aB` is connected and misses the image as well. Boundary
points of `B` are limits of interior points along the collar. Finally
`Homeomorph.toDiffeomorphOfIsInvertibleMFDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

private theorem eventually_forall_of_isCompact' {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {P : ℕ → X → Prop}
    (hP : ∀ x ∈ S, ∃ N ∈ 𝓝 x, ∀ᶠ j in atTop, ∀ z ∈ N, P j z) :
    ∀ᶠ j in atTop, ∀ z ∈ S, P j z := by
  refine hS.induction_on (p := fun T => ∀ᶠ j in atTop, ∀ z ∈ T, P j z) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun _ _ hz => hz.elim
  · intro s t hst ht
    exact ht.mono fun j hj z hz => hj z (hst hz)
  · intro s t hs ht
    filter_upwards [hs, ht] with j hj1 hj2 z hz
    exact hz.elim (hj1 z) (hj2 z)
  · intro x hx
    obtain ⟨N, hN, hev⟩ := hP x hx
    exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, hev⟩

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  [IsManifold (𝓡∂ (n + 1)) ∞ A] [CompactSpace A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
  [IsManifold (𝓡∂ (n + 1)) ∞ B] [T2Space B]

/-- **Assembly of the collar straightening.** -/
theorem eventually_exists_diffeomorph_of_collar_pieces (h : A ≃ₜ B) {f : ℕ → A → B}
    (hf : ∀ j, ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) 1 (f j))
    (hpiece : ∀ a : A, ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∀ᶠ j in atTop,
      InjOn (f j) N ∧ ∀ x ∈ N, (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) x).IsInvertible)
    (hLU : ∀ (a : A) (V : Set B), IsOpen V → h a ∈ V →
      ∃ N ∈ 𝓝 a, ∀ᶠ j in atTop, MapsTo (f j) N V)
    {rA : A → ℝ} (hrA : Continuous rA) (hrA0 : ∀ x, 0 ≤ rA x)
    (hrAz : ∀ x, rA x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x)
    {rB : B → ℝ} (hrB : Continuous rB) (hrB0 : ∀ y, 0 ≤ rB y)
    (hrBz : ∀ y, rB y = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint y)
    {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    {cB : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB → B} (hcB : Continuous cB)
    (hcB0 : ∀ q, cB (q, ⟨0, le_rfl, (Fact.out : (0 : ℝ) < aB).le⟩) = q)
    (hrcB : ∀ q, rB (cB q) = q.2.val)
    {πB : B → BoundaryManifold (𝓡∂ (n + 1)) B}
    (hcπB : ∀ y (hy : rB y < aB), cB (πB y, ⟨rB y, hrB0 y, hy.le⟩) = y)
    (hbd : ∀ j x, rA x = 0 → rB (f j x) = 0)
    {δ : ℕ → ℝ} (hfar : ∀ j x, δ j < rA x → f j x = h x)
    (hnear : ∀ j x, rA x ≤ δ j → rB (h x) < aB / 2) :
    ∀ᶠ j in atTop, ∃ Φ : A ≃ₘ^1⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B, ⇑Φ = f j := by
  have haB : (0 : ℝ) < aB := Fact.out
  -- local pieces
  choose N hNo haN hNev using hpiece
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.2 ⟨x, haN x⟩)
  have hpieces : ∀ᶠ j in atTop, ∀ a ∈ t,
      InjOn (f j) (N a) ∧ ∀ x ∈ N a, (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) x).IsInvertible :=
    (eventually_all_finset t).2 fun a _ => hNev a
  -- separation off the pieces
  set Z : Set (A × A) := univ \ ⋃ a ∈ t, N a ×ˢ N a with hZdef
  have hZ : IsCompact Z :=
    isCompact_univ.diff (isOpen_biUnion fun a _ => (hNo a).prod (hNo a))
  have hsep : ∀ᶠ j in atTop, ∀ z ∈ Z, f j z.1 ≠ f j z.2 := by
    apply eventually_forall_of_isCompact' hZ
    rintro ⟨x, x'⟩ hz
    have hne : x ≠ x' := by
      rintro rfl
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact hz.2 (mem_iUnion₂.2 ⟨a, ha, ⟨hxa, hxa⟩⟩)
    obtain ⟨V₁, V₂, hV₁, hV₂, hx₁, hx₂, hdisj⟩ := t2_separation (h.injective.ne hne)
    obtain ⟨N₁, hN₁, hev₁⟩ := hLU x V₁ hV₁ hx₁
    obtain ⟨N₂, hN₂, hev₂⟩ := hLU x' V₂ hV₂ hx₂
    refine ⟨N₁ ×ˢ N₂, prod_mem_nhds hN₁ hN₂, ?_⟩
    filter_upwards [hev₁, hev₂] with j hj₁ hj₂ z hz'
    exact hdisj.ne_of_mem (hj₁ hz'.1) (hj₂ hz'.2)
  filter_upwards [hpieces, hsep] with j hpj hsj
  have hinv : ∀ x, (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) x).IsInvertible := by
    intro x
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact (hpj a ha).2 x hxa
  have hinj : Injective (f j) := by
    intro x x' heq
    by_contra hne
    by_cases hz : (x, x') ∈ Z
    · exact hsj _ hz heq
    · have hmem : (x, x') ∈ ⋃ a ∈ t, N a ×ˢ N a := by
        by_contra hc
        exact hz ⟨mem_univ _, hc⟩
      obtain ⟨a, ha, hxa, hxa'⟩ := mem_iUnion₂.1 hmem
      exact hne ((hpj a ha).1 hxa hxa' heq)
  -- surjectivity
  have hfc : Continuous (f j) := (hf j).continuous
  set W : Set A := {x | 0 < rA x} with hWdef
  have hWo : IsOpen W := isOpen_lt continuous_const hrA
  have hWi : ∀ x ∈ W, (𝓡∂ (n + 1)).IsInteriorPoint x := fun x hx => by
    rw [(𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint]
    intro hb
    exact (ne_of_gt hx) ((hrAz x).mpr hb)
  have hfW : IsOpen (f j '' W) :=
    isOpen_image_of_injOn_interior hWo hfc.continuousOn hinj.injOn hWi
  have hrange : IsClosed (range (f j)) := (isCompact_range hfc).isClosed
  set D : Set B := {y | 0 < rB y} ∩ (range (f j))ᶜ with hDdef
  have hDo : IsOpen D := (isOpen_lt continuous_const hrB).inter hrange.isOpen_compl
  have hdisj : Disjoint D (f j '' W) := by
    rw [Set.disjoint_left]
    rintro y hyD ⟨x, -, rfl⟩
    exact hyD.2 ⟨x, rfl⟩
  have hcover : {y | 0 < rB y} ⊆ D ∪ f j '' W := by
    intro y hy
    by_cases hr : y ∈ range (f j)
    · obtain ⟨x, rfl⟩ := hr
      refine Or.inr ⟨x, ?_, rfl⟩
      by_contra hx
      have h0 : rA x = 0 := le_antisymm (not_lt.mp hx) (hrA0 x)
      have hy' : 0 < rB (f j x) := hy
      rw [hbd j x h0] at hy'
      exact lt_irrefl _ hy'
    · exact Or.inl ⟨hy, hr⟩
  have hDsmall : ∀ y ∈ D, rB y < aB / 2 := by
    intro y hy
    by_cases hlt : δ j < rA (h.symm y)
    · have h1 := hfar j _ hlt
      rw [h.apply_symm_apply] at h1
      exact (hy.2 ⟨_, h1⟩).elim
    · have h1 := hnear j _ (not_lt.mp hlt)
      rwa [h.apply_symm_apply] at h1
  have hpos : ∀ y, 0 < rB y → y ∈ range (f j) := by
    intro y hy
    by_contra hyr
    have hyD : y ∈ D := ⟨hy, hyr⟩
    have hya : rB y < aB := (hDsmall y hyD).trans (half_lt_self haB)
    set σ : ℝ → B := fun s => cB (πB y, projIcc 0 aB haB.le s) with hσ
    have hσc : Continuous σ := hcB.comp (continuous_const.prodMk continuous_projIcc)
    have hseg : σ '' Ioc 0 aB ⊆ D := by
      refine (isPreconnected_Ioc.image σ hσc.continuousOn).subset_left_of_subset_union hDo hfW
        hdisj ?_ ?_
      · rintro _ ⟨s, hs, rfl⟩
        apply hcover
        change 0 < rB (cB (πB y, projIcc 0 aB haB.le s))
        rw [hrcB, projIcc_of_mem _ (Ioc_subset_Icc_self hs)]
        exact hs.1
      · refine ⟨y, ⟨rB y, ⟨hy, hya.le⟩, ?_⟩, hyD⟩
        change cB (πB y, projIcc 0 aB haB.le (rB y)) = y
        rw [projIcc_of_mem _ ⟨hrB0 y, hya.le⟩]
        exact hcπB y hya
    have hend := hDsmall _ (hseg ⟨aB, ⟨haB, le_rfl⟩, rfl⟩)
    change rB (cB (πB y, projIcc 0 aB haB.le aB)) < aB / 2 at hend
    rw [hrcB, projIcc_right] at hend
    linarith
  have hsurj : Surjective (f j) := by
    intro y
    by_cases hy : 0 < rB y
    · exact hpos y hy
    · have h0 : rB y = 0 := le_antisymm (not_lt.mp hy) (hrB0 y)
      set q : BoundaryManifold (𝓡∂ (n + 1)) B := ⟨y, (hrBz y).mp h0⟩ with hq
      have hc : Continuous (fun s : ℝ => cB (q, projIcc 0 aB haB.le s)) :=
        hcB.comp (continuous_const.prodMk continuous_projIcc)
      have hq0 : cB (q, projIcc 0 aB haB.le 0) = y := by
        rw [projIcc_left]
        exact hcB0 q
      have h1 : Tendsto (fun s : ℝ => cB (q, projIcc 0 aB haB.le s)) (𝓝 0)
          (𝓝 (cB (q, projIcc 0 aB haB.le 0))) := hc.tendsto 0
      rw [hq0] at h1
      have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), cB (q, projIcc 0 aB haB.le s) ∈ range (f j) := by
        filter_upwards [Ioo_mem_nhdsGT haB] with s hs
        apply hpos
        rw [hrcB, projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩]
        exact hs.1
      exact hrange.mem_of_tendsto (h1.mono_left nhdsWithin_le_nhds) hev
  -- the diffeomorphism
  let φ : A ≃ₜ B := hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (f j) ⟨hinj, hsurj⟩)
  exact ⟨φ.toDiffeomorphOfIsInvertibleMFDeriv (hf j) hinv, rfl⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
