import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamBaseArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExpandedSquareCrosscuts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.square_seam_base_arc {θ : ℝ × ℝ → ℝ × ℝ}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) {e : ℝ} (he1 : e ≤ 1) :
    let γ := fun t : ℝ => θ (t / 2 + 1 / 2, 0)
    IsPLHomeomorphOn γ (Icc (-e) e) (γ '' Icc (-e) e) ∧
      γ '' Icc (-e) e ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  let I := Icc (-e / 2 + 1 / 2) (e / 2 + 1 / 2)
  have hI : I ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hη : IsPLHomeomorphOn (fun t : ℝ => t / 2 + 1 / 2) (Icc (-e) e) I := by
    simpa only [I, div_eq_mul_inv, mul_comm, one_mul] using
      (isPLHomeomorphOn_mul_add_Icc (m := (1 / 2 : ℝ)) (c := 1 / 2)
        (a := -e) (b := e) (by norm_num) rfl rfl)
  have hθ' := hθ.restrict (isHPolytope_Icc.isPolyhedron.prod
    (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
    (prod_mono hI (singleton_subset_iff.mpr (by norm_num)))
  have hγ := (hη.trans
    (isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_prod_const (0 : ℝ))).trans hθ'
  have hbd := hθ.image_frontier rfl (isClosed_Icc.prod isClosed_Icc)
    (isClosed_Icc.prod isClosed_Icc)
  refine ⟨hγ.image_eq.symm ▸ hγ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  apply hbd.subset
  refine ⟨(t / 2 + 1 / 2, 0), ?_, rfl⟩
  rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
  refine Or.inl ⟨?_, by simp⟩
  constructor <;> linarith [ht.1, ht.2]

theorem IsCylindricalDiagram.mapsTo_carrier_of_signed_seam_formula
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    {g : B × ℝ → E} {γ : ℝ → B} {ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hν : MapsTo ν (stdSimplexBoundary 2) (stdSimplexBoundary 2)) {a b : Bool} {e : ℝ}
    (he : e ≤ 1)
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q →
      ∀ t ∈ Icc (0 : ℝ) e, g (γ t, s) = f (t • fourSpokeModelLeaf (if a then 0 else 2), q))
    (hneg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-e) 0,
        g (γ t, s) = f ((-t) • fourSpokeModelLeaf (if b then 1 else 3), q)) :
    ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (fun t => g (γ t, s)) (Icc (-e) e) C := by
  intro s hs t ht
  change g (γ t, s) ∈ C
  obtain ⟨q, hq, heq⟩ := stdTriangleLoop_image.symm.subset
    (hν (stdTriangleLoop_image.subset (mem_image_of_mem _ hs)))
  have hspoke (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (k : Fin 4) :
      r • fourSpokeModelLeaf k ∈ spliceSquare := by
    apply segment_zero_fourSpokeModelLeaf_subset k
    rw [segment_eq_image]
    exact ⟨r, hr, by simp⟩
  by_cases ht0 : 0 ≤ t
  · rw [hpos s hs q hq heq.symm t ⟨ht0, ht.2⟩]
    exact hf.image_eq.subset (mem_image_of_mem f ⟨hspoke t ⟨ht0, ht.2.trans he⟩ _, hq⟩)
  · rw [hneg s hs q hq heq.symm t ⟨ht.1, (not_le.mp ht0).le⟩]
    exact hf.image_eq.subset (mem_image_of_mem f
      ⟨hspoke (-t) ⟨by linarith, by linarith [ht.1]⟩ _, hq⟩)

theorem synchronized_base_arcs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ℝ × ℝ) × ℝ → E} {f : Fin 2 → (ℝ × ℝ) × ℝ → E}
    {C : Fin 2 → Set E} {θ : Fin 2 → ℝ × ℝ → ℝ × ℝ} {a : Fin 2 → ℝ × ℝ}
    {e : Fin 2 → ℝ} {ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)} {α β : Fin 2 → Bool}
    (hθ : ∀ k, IsPLHomeomorphOn (θ k) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) (hcore : ∀ k, θ k (1 / 2, 0) = a k)
    (he : ∀ k, 0 < e k) (he1 : ∀ k, e k ≤ 1 / 2)
    (hν : ∀ k, MapsTo (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2))
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k)) (hdis : Disjoint (C 0) (C 1))
    (hpos : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (0 : ℝ) (e k),
        g (θ k (t / 2 + 1 / 2, 0), s) =
          f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q))
    (hneg : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν k (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-e k) 0,
        g (θ k (t / 2 + 1 / 2, 0), s) =
          f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q)) :
    let d := min (e 0) (e 1)
    let γ := fun (k : Fin 2) (t : ℝ) => θ k (t / 2 + 1 / 2, 0)
    0 < d ∧ (∀ k, d ≤ e k) ∧
      (∀ k, IsPLHomeomorphOn (γ k) (Icc (-d) d) (γ k '' Icc (-d) d)) ∧
      (∀ k, γ k '' Icc (-d) d ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ k, γ k 0 = a k) ∧ Disjoint (γ 0 '' Icc (-d) d) (γ 1 '' Icc (-d) d) := by
  let d := min (e 0) (e 1)
  let γ := fun (k : Fin 2) (t : ℝ) => θ k (t / 2 + 1 / 2, 0)
  have hde (k : Fin 2) : d ≤ e k := by
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hd1 : d ≤ 1 := (hde 0).trans ((he1 0).trans (by norm_num))
  have hγ (k : Fin 2) := (hθ k).square_seam_base_arc hd1
  have hcarrier (k : Fin 2) : MapsTo (fun t => g (γ k t, 0)) (Icc (-d) d) (C k) :=
    ((hf k).mapsTo_carrier_of_signed_seam_formula (hν k)
      ((he1 k).trans (by norm_num)) (hpos k) (hneg k) 0 (by norm_num)).mono_left
        (Icc_subset_Icc (neg_le_neg (hde k)) (hde k))
  refine ⟨lt_min (he 0) (he 1), hde, fun k => (hγ k).1, fun k => (hγ k).2, ?_, ?_⟩
  · intro k
    simpa only [γ, zero_div, zero_add] using hcore k
  · apply disjoint_left.mpr
    rintro p ⟨s, hs, hsp⟩ ⟨t, ht, htp⟩
    have hleft := hcarrier 0 hs
    have hright := hcarrier 1 ht
    change γ 0 s = p at hsp
    change γ 1 t = p at htp
    change g (γ 0 s, 0) ∈ C 0 at hleft
    change g (γ 1 t, 0) ∈ C 1 at hright
    rw [hsp] at hleft
    rw [htp] at hright
    exact disjoint_left.mp hdis hleft hright

end DifferentialGeometry.Topology.PiecewiseLinear
