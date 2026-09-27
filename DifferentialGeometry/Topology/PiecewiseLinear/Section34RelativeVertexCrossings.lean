/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedSurfaceGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexSupportedMoves
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundarySphere
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn

open Set Topology Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem mapsTo_of_fixed_complement {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) {S : Set X} (hf : EqOn f id Sᶜ) : MapsTo f S S := by
  intro x hx
  by_contra hnot
  have heq : f x = x := f.injective (hf hnot)
  exact hnot (heq.symm ▸ hx)

private theorem image_eq_of_fixed_complement {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) {S : Set X} (hf : EqOn f id Sᶜ) : f '' S = S := by
  apply Subset.antisymm (image_subset_iff.mpr (mapsTo_of_fixed_complement f hf))
  intro y hy
  refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
  by_contra hnot
  have heq : y = f.symm y := (f.apply_symm_apply y).symm.trans (hf hnot)
  exact hnot (heq ▸ hy)

private theorem image_mem_iff_of_eqOn {X : Type*} [TopologicalSpace X]
    {f g : X ≃ₜ X} {S A : Set X} {y : X} (hy : y ∈ S)
    (hf : f '' S = S) (hg : g '' S = S) (heq : EqOn f g S) :
    y ∈ f '' A ↔ y ∈ g '' A := by
  have hback (k : X ≃ₜ X) (hk : k '' S = S) {x : X} (hx : k x = y) : x ∈ S := by
    obtain ⟨z, hz, hzy⟩ := hk.symm.subset hy
    exact k.injective (hzy.trans hx.symm) ▸ hz
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (heq (hback f hf hxy)).symm.trans hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (heq (hback g hg hxy)).trans hxy⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [HasGroupoid M₁ (plGroupoid 3)]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  [HasGroupoid M₂ (plGroupoid 3)]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {h : M₁ → M₂} {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε κ : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G₀ : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
  {c : Section34VertexIndex 𝒦 𝒦' → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}

theorem exists_section34_relative_vertex_crossings
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hG₀ : ∀ w, IsPLHomeomorphInto 3 (G₀ w) (Cc w))
    (hclose : ∀ w, ∀ x ∈ Cc w, dist (G₀ w x) (h x) < ε w)
    (hc : ∀ w, c w ∈ (plGroupoid 3).maximalAtlas M₂)
    (hchart : ∀ w, G₀ w '' Cc w ⊆ (c w).source) (hκ : ∀ w, 0 < κ w) :
    ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
      (∀ w x, dist (G w x) (G₀ w x) < κ w) ∧
      (∀ w, G w '' Cc w ⊆ (c w).source) ∧
      ∀ e, ∀ y ∈ (G (ends e).1 '' CpBd (ends e).1) ∩
          (G (ends e).2 '' CpBd (ends e).2),
        HasPLCrossingAt
          (c (ends e).1 '' ((G (ends e).1 '' CpBd (ends e).1) ∩ (c (ends e).1).source))
          (c (ends e).1 '' ((G (ends e).2 '' CpBd (ends e).2) ∩ (c (ends e).1).source))
          (c (ends e).1 y) := by
  classical
  obtain ⟨-, hCc, hsub, -, hCp, -, -, -, hends, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdis⟩ := hprep
  let V := section34CellThickening h Cp ε
  let Ω (e : Section34EdgeIndex 𝒦 𝒦') :=
    (V (ends e).1 ∩ V (ends e).2) ∩ (c (ends e).1).source
  let A (w : Section34VertexIndex 𝒦 𝒦') := G₀ w '' CpBd w
  have hA (w : Section34VertexIndex 𝒦 𝒦') :
      IsPolyhedralManifoldWithBoundary (n := 3) 2 (A w) := by
    have hb := (hCp w).image ((hG₀ w).mono_of_isPLCellOn (hCp w) (hsub w).2.1)
    exact hb.isPolyhedralSphere_boundary.isPolyhedralManifold.isPolyhedralManifoldWithBoundary
  have hAV (w : Section34VertexIndex 𝒦 𝒦') : A w ⊆ V w := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion₂.mpr ⟨x, (hCp w).boundary_subset hx,
      hclose w x ((hsub w).2.1 ((hCp w).boundary_subset hx))⟩
  have hAC (w : Section34VertexIndex 𝒦 𝒦') : A w ⊆ (c w).source :=
    (image_mono ((hCp w).boundary_subset.trans (hsub w).2.1)).trans (hchart w)
  have hVopen (w : Section34VertexIndex 𝒦 𝒦') : IsOpen (V w) :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hΩopen (e : Section34EdgeIndex 𝒦 𝒦') : IsOpen (Ω e) :=
    ((hVopen _).inter (hVopen _)).inter (c _).open_source
  have hΩdis : Pairwise (Disjoint on Ω) :=
    fun e d hed => (hdis e d hed).mono inter_subset_left inter_subset_left
  have hmove (e : Section34EdgeIndex 𝒦 𝒦') :=
    exists_small_isPL_homeomorph_surface_crossing_in_chart (hA (ends e).1) (hA (ends e).2)
      (c (ends e).1) (hc _) (hΩopen e)
      (fun y hy => ⟨⟨⟨hAV _ hy.1, hAV _ hy.2⟩, hAC _ hy.1⟩, hAC _ hy.1⟩)
      (hκ (ends e).1)
  choose φ hφ hφinv hφclose hφfix hφchart hφtrace hφcross using hmove
  obtain ⟨Φ, hΦ, -, hΦclose, hΦeq, hΦid, hΦimage, hΦfix⟩ :=
    exists_section34_vertex_supported_moves (fun e => (hends e).2.1) hΩdis hκ hφ hφinv
      hφfix (fun e y _ => hφclose e y)
  let G (w : Section34VertexIndex 𝒦 𝒦') := Φ w ∘ G₀ w
  have hGimage (w : Section34VertexIndex 𝒦 𝒦') : G w '' CpBd w = Φ w '' A w :=
    image_comp _ _ _
  have hΦV (w : Section34VertexIndex 𝒦 𝒦') : MapsTo (Φ w) (V w) (V w) := by
    apply mapsTo_of_fixed_complement
    intro x hx
    apply hΦfix w
    intro hs
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hs
    apply hx
    simpa only [← he] using hxe.1.1
  have hΦC (w : Section34VertexIndex 𝒦 𝒦') :
      MapsTo (Φ w) (c w).source (c w).source := by
    apply mapsTo_of_fixed_complement
    intro x hx
    apply hΦfix w
    intro hs
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hs
    apply hx
    simpa only [← he] using hxe.2
  have hGC (w : Section34VertexIndex 𝒦 𝒦') : G w '' Cc w ⊆ (c w).source := by
    rintro _ ⟨x, hx, rfl⟩
    exact hΦC w (hchart w (mem_image_of_mem _ hx))
  refine ⟨G, ?_, fun w x => hΦclose w (G₀ w x), hGC, ?_⟩
  · intro w
    exact ((hΦ w).comp_isPLOn (hG₀ w).isPLOn).isPLHomeomorphInto (hCc w).isCompact
      (fun x hx y hy hxy => (hG₀ w).injOn hx hy ((Φ w).injective hxy))
  · intro e y hy
    have hyΩ : y ∈ Ω e := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · obtain ⟨x, hx, hxy⟩ := hy.1
        rw [← hxy]
        exact hΦV _ (hAV _ ⟨x, hx, rfl⟩)
      · obtain ⟨x, hx, hxy⟩ := hy.2
        rw [← hxy]
        exact hΦV _ (hAV _ ⟨x, hx, rfl⟩)
      · exact hGC _ (image_mono ((hCp _).boundary_subset.trans (hsub _).2.1) hy.1)
    have hφΩ : φ e '' Ω e = Ω e := image_eq_of_fixed_complement _ (hφfix e)
    have ha (z : M₂) (hz : z ∈ Ω e) :
        z ∈ φ e '' A (ends e).1 ↔ z ∈ G (ends e).1 '' CpBd (ends e).1 := by
      rw [hGimage]
      exact (image_mem_iff_of_eqOn hz (hΦimage _ e) hφΩ (hΦeq e)).symm
    have hb (z : M₂) (hz : z ∈ Ω e) :
        z ∈ A (ends e).2 ↔ z ∈ G (ends e).2 '' CpBd (ends e).2 := by
      rw [hGimage]
      have hi := hΦid (ends e).2 e (hends e).1.symm
      have hh := image_mem_iff_of_eqOn (g := Homeomorph.refl M₂) (A := A (ends e).2)
        hz (hΦimage _ e) (by simp) hi
      simpa using hh.symm
    have hycross : y ∈ φ e '' A (ends e).1 ∩ A (ends e).2 :=
      ⟨(ha y hyΩ).mpr hy.1, (hb y hyΩ).mpr hy.2⟩
    apply (hφcross e y hycross).congr
    · apply eventually_mem_chart_image_iff_of_eventually (c (ends e).1) hyΩ.2
      filter_upwards [(hΩopen e).mem_nhds hyΩ] with z hz
      exact ha z hz
    · apply eventually_mem_chart_image_iff_of_eventually (c (ends e).1) hyΩ.2
      filter_upwards [(hΩopen e).mem_nhds hyΩ] with z hz
      exact hb z hz

end DifferentialGeometry.Topology.PiecewiseLinear
