import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesKernel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2

/-!
# FC39 GROUP G: existence of the global face functions V2 (F6, `stub_exists_globalFaceFunctions`)

Lane FC39-G-GFF(b), external draft 58 §二 F6, dispositions D58-1 / D58-3. The frozen target
`stub_exists_globalFaceFunctions` over the revised structure `GlobalFaceFunctionsV2` (D58-1):

* `chart_coords_regular_GGFF` — the two coordinates of a chart `κ : PartialDiffeomorph (𝓡 2)
  𝓘(ℝ, ℝ × ℝ)` have nonzero differentials on the source and jointly onto differentials;
* `exists_globalFaceFunctions_GGFF (Rw) : Nonempty (GlobalFaceFunctionsV2 Rw)` — **the target**:
  the kernel `exists_globalFaceFunctions_kernel_GGFF` on the circle base `M = Rw.circle.Base` with
  `K = C₁`, labels = ALL actual faces `Rw.CircleFace` (finite, `finite_circleFace_GTR`; a label
  with empty trace gets a negative function), traces `B f = Rw.baseTrace f` (compact,
  `isCompact_baseTrace_GTR`), corners = the registered rim base points (`rimBase_injective_GSAFE`,
  `finite_edgeEnd_GSAFE`) with labels `vertical e.component`, `horizontal (horizontal e)` and the
  corner chart `X = κ_e¹`, `Y = κ_e²` of the labelled tube on the shrunk corner atlas neighbourhood
  of `exists_corner_atlas_GTR`; `K \ ⋃ B ⊆ int K` from `frontier_cbase_eq_iUnion_baseTrace_GTR`;
  two labels only at rim base points (`label_classification_GTR`); the single-label local defining
  function from `labelled_baseTrace_atlas_GTR`. `Face := Rw.CircleFace`, `actualFace := refl`;
* `exists_preparedV2_GGFF` — every row tuple extends to prepared rows V2.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The coordinates of a chart** `κ : N → ℝ × ℝ` are regular on the source, with jointly
surjective differentials. -/
theorem chart_coords_regular_GGFF {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    (κ : PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) N (ℝ × ℝ) ∞) {c : N} (hc : c ∈ κ.source) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x => (κ x).1) c ≠ 0 ∧
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x => (κ x).2) c ≠ 0 ∧
      Surjective fun w : TangentSpace (𝓡 2) c =>
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x => (κ x).1) c w,
          mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x => (κ x).2) c w) := by
  have hκd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c :=
    ((κ.contMDiffOn_toFun c hc).contMDiffAt (κ.open_source.mem_nhds hc)).mdifferentiableAt
      (by simp)
  obtain ⟨D, hD⟩ := (κ.isLocalDiffeomorphAt _ _ _ hc).isInvertible_mfderiv (by simp)
  have hsurj : Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c) := by
    rw [← hD]
    exact D.surjective
  have h1 : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun x => (κ x).1) c
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c)) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasMFDerivAt.comp c hκd.hasMFDerivAt
  have h2 : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun x => (κ x).2) c
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c)) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasMFDerivAt.comp c hκd.hasMFDerivAt
  rw [h1.mfderiv, h2.mfderiv]
  refine ⟨fun h => ?_, fun h => ?_, fun r => ?_⟩
  · obtain ⟨w, hw⟩ := hsurj (1, 0)
    have := DFunLike.congr_fun h w
    change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c w).1 = 0 at this
    rw [hw] at this
    exact one_ne_zero this
  · obtain ⟨w, hw⟩ := hsurj (0, 1)
    have := DFunLike.congr_fun h w
    change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c w).2 = 0 at this
    rw [hw] at this
    exact one_ne_zero this
  · obtain ⟨w, hw⟩ := hsurj r
    refine ⟨w, ?_⟩
    change ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c w).1, (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) κ c w).2) = r
    rw [hw]
    rfl

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **GROUP G, `stub_exists_globalFaceFunctions` over V2 (D58-1).** Every row tuple has global
face functions V2. -/
theorem exists_globalFaceFunctions_GGFF (Rw : FC39RowsV2 W E) :
    Nonempty (GlobalFaceFunctionsV2 Rw) := by
  classical
  have hfin := Rw.finite_circleFace_GTR
  have hfinE := Rw.finite_edgeEnd_GSAFE
  -- the corner atlas
  have hatl := fun e => Rw.exists_corner_atlas_GTR e
  choose V hpV hVb hVK hVa hVb' hVo using hatl
  set X : Rw.edge.EdgeEnd → Rw.circle.Base → ℝ := fun e c => (Rw.labelledTubes.chart e c).1
  set Y : Rw.edge.EdgeEnd → Rw.circle.Base → ℝ := fun e c => (Rw.labelledTubes.chart e c).2
  have hsrc : ∀ e, ∀ c ∈ V e, c ∈ (Rw.labelledTubes.chart e).source := fun e c hc => by
    rw [Rw.labelledTubes.chart_source]
    exact hVb e hc
  have hreg := fun e c (hc : c ∈ V e) => chart_coords_regular_GGFF (Rw.labelledTubes.chart e)
    (hsrc e c hc)
  have hcen := Rw.labelledTubes.chart_center
  obtain ⟨base, fn, hKb, hsm, hzr, hbase, hface, hdepth, hind, hdouble, hcan⟩ :=
    exists_globalFaceFunctions_kernel_GGFF (M := Rw.circle.Base) (K := Rw.circle.cbase)
      Rw.circle.cbase_compact (fun f => Rw.baseTrace f)
      (fun f => (Rw.isCompact_baseTrace_GTR f).isClosed) (fun f c hc => hc.1)
      (fun c hcK hcB => by
        by_contra hint
        have hfr : c ∈ frontier Rw.circle.cbase := ⟨subset_closure hcK, hint⟩
        rw [Rw.frontier_cbase_eq_iUnion_baseTrace_GTR] at hfr
        obtain ⟨f, hf⟩ := mem_iUnion.1 hfr
        exact hcB f hf)
      (fun e => Rw.junctions.rimBase e.1) Rw.rimBase_injective_GSAFE
      (fun e => .vertical e.component) (fun e => .horizontal (Rw.junctions.horizontal e))
      (fun e h => by cases h) (fun e => (V e : Set Rw.circle.Base)) (fun e => (V e).isOpen) hpV
      X Y
      (fun e => ((ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiff.comp_contMDiffOn
        (Rw.labelledTubes.chart e).contMDiffOn_toFun).mono fun c hc => hsrc e c hc)
      (fun e => ((ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiff.comp_contMDiffOn
        (Rw.labelledTubes.chart e).contMDiffOn_toFun).mono fun c hc => hsrc e c hc)
      (fun e => by simp only [X, hcen e]) (fun e => by simp only [Y, hcen e])
      (fun e c hc => (hreg e c hc).1) (fun e c hc => (hreg e c hc).2.1)
      (fun e => (hreg e _ (hpV e)).2.2)
      (fun e c hc hX hY => by
        apply (Rw.labelledTubes.chart e).toPartialEquiv.injOn (hsrc e c hc)
          (hsrc e _ (hpV e))
        rw [hcen e]
        exact Prod.ext hX hY)
      hVK
      (fun e c hc => hVa e c hc)
      (fun e c hc => hVb' e c hc)
      (fun e g h1 h2 => hVo e g h1 h2)
      (fun c f g hfg hf hg => by
        obtain ⟨e, he, -⟩ := Rw.label_classification_GTR hf hg hfg
        exact ⟨e, he.symm⟩)
      (fun f c hc hsing => by
        have hfr : c ∈ frontier Rw.circle.cbase := by
          rw [Rw.frontier_cbase_eq_iUnion_baseTrace_GTR]
          exact mem_iUnion.2 ⟨f, hc⟩
        obtain ⟨U, hcU, L, φ, hL, -, -, hφ, hsurj, hcb, -⟩ := Rw.labelled_baseTrace_atlas_GTR hfr
        have hfL : f ∈ L := (hL f).2 hc
        have hLf : ∀ g ∈ L, g = f := fun g hg => by
          by_contra h
          exact hsing g h ((hL g).1 hg)
        obtain ⟨hsmf, -, hBf⟩ := hφ f hfL
        refine ⟨U, U.isOpen, hcU, φ f, hsmf, fun h0 => ?_, fun y hy => ?_, fun y hy hyK => ?_⟩
        · obtain ⟨w, hw⟩ := hsurj fun _ : L => (1 : ℝ)
          have h1 : mderivR_GTR (𝓡 2) (φ f) c w = 1 := congrFun hw ⟨f, hfL⟩
          have h2 : mderivR_GTR (𝓡 2) (φ f) c = 0 := h0
          rw [h2] at h1
          exact zero_ne_one (h1 : (0 : ℝ) = 1)
        · have h := Set.ext_iff.1 hcb y
          simp only [mem_inter_iff, mem_ofPred_eq] at h
          constructor
          · intro hyK
            exact (h.1 ⟨hyK, hy⟩).2 f hfL
          · intro hle
            exact (h.2 ⟨hy, fun g hg => (hLf g hg).symm ▸ hle⟩).1
        · have h := Set.ext_iff.1 hBf y
          simp only [mem_inter_iff, mem_ofPred_eq] at h
          constructor
          · intro h0
            exact (h.2 ⟨hy, hyK, h0⟩).1
          · intro hyB
            exact (h.1 ⟨hyB, hy⟩).2.2)
  exact ⟨{
    base := base
    cbase_subset := hKb
    Face := Rw.CircleFace
    finite := hfin
    actualFace := Equiv.refl _
    fn := fn
    smooth := hsm
    zero_regular := hzr
    base_eq := hbase
    face_eq := hface
    depth_le_two := hdepth
    double_independent := hind
    double_registered := fun c hc f f' hff' hf hf' => by
      obtain ⟨e, he, hlab, hneg⟩ := hdouble c hc f f' hff' hf hf'
      exact ⟨e, he, hlab, hneg⟩
    canonical_near_corner := fun e => by
      obtain ⟨O, hpO, hOsub, hOF⟩ := hcan e
      exact ⟨O, hpO, fun c hc => ⟨(hOsub hc).1, hVb e (hOsub hc).2⟩, hOF⟩ }⟩

/-- **The prepared rows V2 exist over every row tuple.** -/
theorem exists_preparedV2_GGFF (Rw : FC39RowsV2 W E) : ∃ Pr : FC39PreparedV2 W E, Pr.rows = Rw :=
  ⟨⟨Rw, (exists_globalFaceFunctions_GGFF Rw).some⟩, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
