import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskMotion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SupportedVertexModification
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingPreservation

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

theorem section34_disk_motion_active_trace
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (I : Set (Fin (cnt e)))
    (ψ : M₂ ≃ₜ M₂) {K : Set M₂} (hK : IsCompact K) (hKS : K ⊆ interior (Sp e))
    (hfix : EqOn ψ id Kᶜ) (hrimA : Disjoint K (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)))
    (hrim : Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hkeep : ∀ j : I, Disjoint K (Pg e j.1.val))
    (hcancel : G (ends e).1 '' CpBd (ends e).1 ∩ ψ '' (G (ends e).2 '' CpBd (ends e).2) =
      ⋃ j : I, Pg e j.1.val) :
    let G' := section34VertexModification G (ends e).2 ψ
    (G' (ends e).1 '' CpBd (ends e).1 ∩ G' (ends e).2 '' CpBd (ends e).2 ⊆
      G' (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
        G' (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) ∩ interior (Tp e)) ∧
    (G' (ends e).1 '' Ab₀ e ⊆ interior (G' (ends e).2 '' Cp (ends e).2) ∧
      Disjoint (G' (ends e).1 '' Ab₁ e) (G' (ends e).2 '' Cp (ends e).2)) ∧
    (G' (ends e).2 '' Bb e ⊆ interior (Sp e) ∧
      Disjoint (G' (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) (Tp e)) ∧
    G' (ends e).1 '' Aa e ∩ G' (ends e).2 '' Bb e = ⋃ j : I, Pg e j.1.val ∧
    (∀ j : I, IsPolyhedralSphere (n := 3) 1 (Pg e j.1.val)) ∧
    (Pairwise fun j k : I => Disjoint (Pg e j.1.val) (Pg e k.1.val)) ∧
    ∀ y ∈ G' (ends e).1 '' Aa e ∩ G' (ends e).2 '' Bb e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' (G' (ends e).1 '' Aa e ∩ c.source))
          (c '' (G' (ends e).2 '' Bb e ∩ c.source)) (c y) := by
  let G' := section34VertexModification G (ends e).2 ψ
  obtain ⟨-, -, -, -, -, -, -, -, hends, -, -, -, -, -, hAa, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hmeetOld, hsideOld, hBbOld, -, -, -, -, -, -, -, -, hPg, hdis,
    hcross, -⟩ := hpack
  have hGa : G' (ends e).1 = G (ends e).1 :=
    section34VertexModification_of_ne G (ends e).2 ψ (hends e).1
  have hGb : G' (ends e).2 = ψ ∘ G (ends e).2 :=
    section34VertexModification_self G (ends e).2 ψ
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hBB : Bb e ⊆ CpBd (ends e).2 := (hBb e).1
  have hfixPg (j : I) : EqOn ψ id (Pg e j.1.val) :=
    fun _ hx => hfix (disjoint_right.mp (hkeep j) hx)
  have hfull : G' (ends e).1 '' CpBd (ends e).1 ∩ G' (ends e).2 '' CpBd (ends e).2 =
      ⋃ j : I, Pg e j.1.val := by rw [hGa, hGb, image_comp]; exact hcancel
  have hmeet : G' (ends e).1 '' CpBd (ends e).1 ∩ G' (ends e).2 '' CpBd (ends e).2 ⊆
      G' (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
        G' (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) ∩ interior (Tp e) := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hfull ▸ hy)
    have hold := (hPg e j.1.val j.1.isLt).2 hyj
    have hbdOld : y ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 :=
      ⟨image_mono (sdiff_subset.trans hAB) hold.1, image_mono (sdiff_subset.trans hBB) hold.2⟩
    refine ⟨⟨?_, ?_⟩, (hmeetOld e hbdOld).2⟩
    · rw [hGa]
      exact hold.1
    · rw [hGb, image_comp]
      exact ⟨y, hold.2, hfixPg j hyj⟩
  have htr : G' (ends e).1 '' Aa e ∩ G' (ends e).2 '' Bb e = ⋃ j : I, Pg e j.1.val := by
    apply Subset.antisymm
    · intro y hy
      exact hfull ▸ And.intro (image_mono hAB hy.1) (image_mono hBB hy.2)
    · intro y hy
      have hm := hmeet (hfull.symm ▸ hy)
      exact ⟨image_mono sdiff_subset hm.1.1, image_mono sdiff_subset hm.1.2⟩
  have hfixS : EqOn ψ id (interior (Sp e))ᶜ :=
    hfix.mono (compl_subset_compl.mpr hKS)
  have hψS : ψ '' interior (Sp e) = interior (Sp e) :=
    image_eq_of_homeomorph_eqOn_compl_of_subset ψ hfixS Subset.rfl
  have hfixRim : EqOn ψ id (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) :=
    fun _ hx => hfix (disjoint_right.mp hrim hx)
  have hfixA : EqOn ψ id (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) :=
    fun _ hx => hfix (disjoint_right.mp hrimA hx)
  have hside : G' (ends e).1 '' Ab₀ e ⊆ interior (G' (ends e).2 '' Cp (ends e).2) ∧
      Disjoint (G' (ends e).1 '' Ab₁ e) (G' (ends e).2 '' Cp (ends e).2) := by
    rw [hGa, hGb, image_comp, ← ψ.image_interior]
    constructor
    · intro x hx
      exact ⟨x, (hsideOld e).1 hx, hfixA (image_mono subset_union_left hx)⟩
    · apply disjoint_left.mpr
      rintro x hxA ⟨y, hy, hyx⟩
      have hxy : y = x := ψ.injective
        (hyx.trans (hfixA (image_mono subset_union_right hxA)).symm)
      exact disjoint_left.mp (hsideOld e).2 hxA (hxy ▸ hy)
  refine ⟨hmeet, hside, ⟨?_, ?_⟩, htr, fun j => (hPg e j.1.val j.1.isLt).1, ?_, ?_⟩
  · change G' (ends e).2 '' Bb e ⊆ interior (Sp e)
    rw [hGb, image_comp, ← hψS]
    exact image_mono (hBbOld e).1
  · change Disjoint (G' (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) (Tp e)
    rw [hGb, image_comp, hfixRim.image_eq, image_id]
    exact (hBbOld e).2
  · intro j k hjk
    exact hdis e j.1.val j.1.isLt k.1.val k.1.isLt
      (fun h => hjk (Subtype.ext (Fin.ext h)))
  · intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (htr ▸ hy)
    have hold := (hPg e j.1.val j.1.isLt).2 hyj
    obtain ⟨c, hc, hyc, hcrossc⟩ := hcross e y
      ⟨image_mono sdiff_subset hold.1, image_mono sdiff_subset hold.2⟩
    refine ⟨c, hc, hyc, ?_⟩
    change HasPLCrossingAt (c '' (G' (ends e).1 '' Aa e ∩ c.source))
      (c '' (G' (ends e).2 '' Bb e ∩ c.source)) (c y)
    rw [hGa, hGb, image_comp]
    exact hcrossc.image_right_of_fixed_neighborhood ψ hK.isClosed.isOpen_compl hfix
      (disjoint_right.mp (hkeep j) hyj) hyc

end DifferentialGeometry.Topology.PiecewiseLinear
