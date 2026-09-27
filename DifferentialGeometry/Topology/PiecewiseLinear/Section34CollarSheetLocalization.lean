import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingFaceIsolation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

theorem exists_section34_collar_sheet_localization
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i j : ℕ} {D F : Set M₂}
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j))
    {P R L : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hR : IsCompact R) (hRP : R ⊆ P)
    (hfront : u '' frontier R = D ∪ F)
    (hL : L ∈ 𝓝ˢ[frontier R] (frontier R ∩ u ⁻¹' (Pg e i ∪ Pg e j)))
    {c : ℝ} (hc : 0 < c)
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : ContinuousOn ρ (frontier R ×ˢ Icc (0 : ℝ) c))
    (hρP : MapsTo ρ (frontier R ×ˢ Icc (0 : ℝ) c) P)
    (hbottom : ∀ x ∈ frontier R, ρ (x, 0) = x)
    (hpositive : MapsTo ρ (frontier R ×ˢ Ioc (0 : ℝ) c) Rᶜ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ c ∧ ∀ x ∈ frontier R, ∀ t ∈ Ioc (0 : ℝ) d,
      u (ρ (x, t)) ∈ G (ends e).1 '' CpBd (ends e).1 ∪
        G (ends e).2 '' CpBd (ends e).2 → x ∈ L := by
  obtain ⟨V, hV, hJV, hVL⟩ := mem_nhdsSetWithin.mp hL
  let K := frontier R \ V
  have hfrontP : frontier R ⊆ P := hR.isClosed.frontier_subset.trans hRP
  have hK : IsCompact K :=
    (hR.of_isClosed_subset isClosed_frontier hR.isClosed.frontier_subset).diff hV
  have hKP : K ⊆ P := sdiff_subset.trans hfrontP
  have huK : IsCompact (u '' K) := hK.image_of_continuousOn (hu.continuousOn.mono hKP)
  obtain ⟨hF, hD, -⟩ := hfill.face_annuli_and_intersection
  have hnoJ : Disjoint (u '' K) (Pg e i ∪ Pg e j) := by
    refine disjoint_left.mpr ?_
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx.2 (hJV ⟨hx.1, hy⟩)
  obtain ⟨O₀, O₁, hO₀, hO₁, hK₀, hK₁, -, -, -, hO₀A, hO₀B, hO₁B, hO₁A⟩ :=
    exists_section34_filling_face_isolation hprep hpack e hfill
      (huK.inter_right hF.isCompact.isClosed) (huK.inter_right hD.isCompact.isClosed)
      (fun x hx => ⟨hx.2, fun hj => disjoint_left.mp hnoJ hx.1 hj⟩)
      (fun x hx => ⟨hx.2, fun hj => disjoint_left.mp hnoJ hx.1 hj⟩)
      isOpen_univ (subset_univ _)
  have hKO : u '' K ⊆ O₀ ∪ O₁ := by
    rintro y hy
    have hyfront := hfront.subset ((image_mono sdiff_subset) hy)
    rcases hyfront with hyD | hyF
    · exact Or.inr (hK₁ ⟨hy, hyD⟩)
    · exact Or.inl (hK₀ ⟨hy, hyF⟩)
  have hOtrace : (O₀ ∪ O₁) ∩ (G (ends e).1 '' CpBd (ends e).1 ∪
      G (ends e).2 '' CpBd (ends e).2) ⊆ D ∪ F := by
    rintro y ⟨hyO | hyO, hyA | hyB⟩
    · exact Or.inr (hO₀A ⟨subset_closure hyO, hyA⟩).1
    · exact (disjoint_left.mp hO₀B (subset_closure hyO) hyB).elim
    · exact (disjoint_left.mp hO₁A (subset_closure hyO) hyA).elim
    · exact Or.inl (hO₁B ⟨subset_closure hyO, hyB⟩).1
  have hprod : K ×ˢ Icc (0 : ℝ) c ⊆ frontier R ×ˢ Icc (0 : ℝ) c :=
    prod_mono_left sdiff_subset
  have hcomp : ContinuousOn (fun z => u (ρ z)) (K ×ˢ Icc (0 : ℝ) c) :=
    hu.continuousOn.comp (hρ.mono hprod) (hρP.mono_left hprod)
  obtain ⟨d, hd, hdc, hshort⟩ := exists_short_product_image_subset_of_compact hK hc hcomp
    (mapsTo_univ _ _) (fun x hx => by rw [hbottom x hx.1]; exact mem_image_of_mem u hx)
    (mem_nhdsSetWithin.mpr ⟨O₀ ∪ O₁, hO₀.union hO₁, hKO, inter_subset_left⟩)
  refine ⟨d, hd, hdc, ?_⟩
  intro x hx t ht hsheet
  by_contra hxL
  have hxK : x ∈ K := ⟨hx, fun hxV => hxL (hVL ⟨hxV, hx⟩)⟩
  have hyO := hshort (mem_image_of_mem (fun z => u (ρ z))
    (show (x, t) ∈ K ×ˢ Icc (0 : ℝ) d from ⟨hxK, ht.1.le, ht.2⟩))
  obtain ⟨z, hz, hzu⟩ := hfront.symm.subset (hOtrace ⟨hyO, hsheet⟩)
  have hzt : z = ρ (x, t) :=
    hu.injOn (hfrontP hz) (hρP ⟨hx, ht.1.le, ht.2.trans hdc⟩) hzu
  exact hpositive ⟨hx, ht.1, ht.2.trans hdc⟩ (hzt ▸ hR.isClosed.frontier_subset hz)

end DifferentialGeometry.Topology.PiecewiseLinear
