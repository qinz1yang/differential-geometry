import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedBandAlternation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularSideParity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem lateral_open_subset_one_side {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) {f : (Fin 3 → ℝ) × ℝ → X}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (frontier A)) :
    f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior A ∨
      f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Aᶜ := by
  have hconn := ((isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))).image f
    (hf.mono (prod_mono_right Ioo_subset_Icc_self))
  apply hconn.isPreconnected.subset_or_subset isOpen_interior hA.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset)
  intro x hx
  by_cases hxi : x ∈ interior A
  · exact Or.inl hxi
  · exact Or.inr fun hxA => disjoint_left.mp hdis hx ⟨subset_closure hxA, hxi⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_ordered_band_sides_eq_of_parity
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {σ : Fin (cnt e) → Fin (cnt e)} (hσ : Function.Injective σ)
    {D₀ D₁ : Fin (cnt e) → Set M₂}
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (Pg e (σ r)) ∧
      IsPLCellOn 2 (D₁ r) (Pg e (σ r)) ∧
      D₀ r ∪ D₁ r = G (ends e).2 '' CpBd (ends e).2 ∧
      D₀ r ∩ D₁ r = Pg e (σ r))
    (hmono : Monotone D₀) (hanti : Antitone D₁)
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    {f : ℕ → (Fin 3 → ℝ) × ℝ → M₂}
    (hbands : ∀ r (hr : r + 1 < cnt e),
      ContinuousOn (f r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn (f r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      f r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        D₁ ⟨r, by omega⟩ ∩ D₀ ⟨r + 1, hr⟩ ∧
      f r '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ ⟨r, by omega⟩) ∧
      f r '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ ⟨r + 1, hr⟩) ∧
      f r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
      Disjoint (f r '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
        (G (ends e).1 '' CpBd (ends e).1))
    {i j : ℕ} (hi : i + 1 < cnt e) (hj : j + 1 < cnt e)
    (hpar : i % 2 = j % 2) :
    (f i '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        interior (G (ends e).1 '' Cp (ends e).1) ∧
      f j '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        interior (G (ends e).1 '' Cp (ends e).1)) ∨
    (f i '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
      f j '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ) := by
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcell := (hCp (ends e).1).image (hGp (ends e).1)
  apply Set.same_side_of_local_alternation (n := cnt e - 1)
    (disjoint_compl_right.mono_left interior_subset) ?_ ?_ ?_ (by omega) (by omega) hpar
  · intro r _
    exact ((isConnected_stdSimplexBoundary 0).nonempty.prod
      (nonempty_Ioo.mpr (zero_lt_one : (0 : ℝ) < 1))).image (f r)
  · intro r hr
    obtain ⟨hf, -, -, -, -, -, hempty⟩ := hbands r (by omega)
    exact lateral_open_subset_one_side hcell.isCompact.isClosed hf
      (hcell.boundary_eq_frontier ▸ hempty)
  · intro r hr
    obtain ⟨hf, hfi, himagef, hfzero, hfone, hfB, hfempty⟩ := hbands r (by omega)
    obtain ⟨hg, hgi, himageg, hgzero, hgone, hgB, hgempty⟩ := hbands (r + 1) (by omega)
    exact section34_opposite_ordered_band_sides hprep hpack e hσ hcap hmono hanti hdis
      (i := ⟨r, by omega⟩) (j := ⟨r + 1, by omega⟩) (k := ⟨r + 1 + 1, by omega⟩)
      (by exact_mod_cast Nat.lt_succ_self r) (by exact_mod_cast Nat.lt_succ_self (r + 1))
      hf hfi hg hgi himagef himageg hfzero hfone hgzero hgone (union_subset hfB hgB)
      hfempty hgempty

end DifferentialGeometry.Topology.PiecewiseLinear
