import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingFaceIsolation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeRims
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostCarrierCancellation

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

theorem section34_band_forbidden_boundary
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i j : ℕ} {D F : Set M₂}
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j))
    (hFA : F ⊆ G (ends e).1 '' Aa e)
    (hDT : D ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e)) :
    let Z := (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ∪ G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∪
      closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)
    IsClosed Z ∧ Z ⊆ G (ends e).1 '' CpBd (ends e).1 ∪ G (ends e).2 '' CpBd (ends e).2 ∧
      Disjoint Z (D ∪ F) := by
  obtain ⟨hF, hD, -⟩ := hfill.face_annuli_and_intersection
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, -, -, -, -, -, -, -, -, -, -, -, hRT,
    hfirst, hsecond, -⟩ := hfill
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, hBrim, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hAB : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hBB : G (ends e).2 '' Bb e ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    image_mono (hBb e).1
  obtain ⟨hannA, hannB⟩ := section34_piercing_annuli hprep hpack e
  have hrims := section34_first_rims_subset_inner_frontier hprep hpack e
  have hendsD : Pg e i ∪ Pg e j ⊆ D := union_subset hD.first_subset hD.second_subset
  have hJdis : Disjoint (Pg e i ∪ Pg e j) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) :=
    disjoint_interior_frontier.mono (hendsD.trans (hDT.trans inter_subset_right)) hrims
  obtain ⟨hc⟩ := hcellA.nonempty_chartedSpace_boundary
  let _ := hc
  have hFrim : Disjoint F (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
    rw [image_union] at hJdis ⊢
    exact hF.disjoint_ends_of_subset_within hannA hAB hFA hJdis
  have hDrim : Disjoint D (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) :=
    disjoint_interior_frontier.mono (hDT.trans inter_subset_right) hrims
  have hT : D ∪ F ⊆ Tp e := by
    rintro x (hxD | hxF)
    · exact interior_subset (hDT hxD).2
    · exact hRT (hfirst.symm.subset hxF).2
  have hBrim' : Disjoint (D ∪ F) (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) :=
    (hBrim e).2.symm.mono_left hT
  have hcontact : (D ∪ F) ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
      G (ends e).2 '' Bb e := by
    rintro x ⟨hxD | hxF, hxB⟩
    · exact (hDT hxD).1
    · exact (hDT (hsecond.subset ⟨hxB, (hfirst.symm.subset hxF).2⟩)).1
  have houtside := hcellB.disjoint_closure_sdiff_of_annular_contact
    hannB hBB hcontact (by rwa [← image_union])
  have hBs : IsClosed (G (ends e).2 '' CpBd (ends e).2) :=
    hcellB.boundary_eq_frontier ▸ isClosed_frontier
  have hArimB : G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [image_union]
    exact (union_subset hannA.first_subset hannA.second_subset).trans hAB
  have hBrimB : G (ends e).2 '' (Bb₀ e ∪ Bb₁ e) ⊆ G (ends e).2 '' CpBd (ends e).2 := by
    rw [image_union]
    exact (union_subset hannB.first_subset hannB.second_subset).trans hBB
  refine ⟨?_, ?_, ?_⟩
  · exact (((by rw [image_union]; exact (hannA.ends_isCompact.1.union
      hannA.ends_isCompact.2).isClosed) :
      IsClosed (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e))).union
      (by rw [image_union]; exact (hannB.ends_isCompact.1.union
        hannB.ends_isCompact.2).isClosed)).union isClosed_closure
  · exact union_subset (union_subset (hArimB.trans subset_union_left)
      (hBrimB.trans subset_union_right))
      ((closure_minimal sdiff_subset hBs).trans subset_union_right)
  · exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨(disjoint_union_left.mpr ⟨hDrim, hFrim⟩).symm, hBrim'.symm⟩, houtside.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
