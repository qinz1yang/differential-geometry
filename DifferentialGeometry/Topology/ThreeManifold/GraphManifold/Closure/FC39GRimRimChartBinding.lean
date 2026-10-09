import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimChartKit
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimChartRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimFlowEdgeHandle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceTop
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskOrientedIsotopy
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K4–K7, binding G6): the per-end rim charts

Lane FC39-G-RIMBOXc, dispositions D62-3 (b)–(i). At the end `b` of the new flow handle of an
interval component `i` (`FC39GRimFlowEdgeHandle.lean`; `e = endpointEquiv (i, b)`):

* the raw-tube box at the central rim FIRST (tube lemma, D62-3 (g));
* the end profile `q (s) = descended_e (proj (F (θ₀, 0, endCoord b s)))` (`q 0 = 0` by `face_eq` at the
  rim, `q ≥ 0` inward by `edge_side`, `q' 0 ≠ 0` by `descended_regular`; D62-3 (d)) and its scaled
  inverse `τ` (G3);
* the scale `lam` frozen LAST (D62-3 (e)): below the profile scale, the corner-chart scale
  (`exists_cornerChartScale_GRIM`, D62-3 (h)), `δ/4` and `η/4`;
* the rim chart `χ (θ, x, y) = F (θ, lam x, endCoord b (τ y))` (the SAME flow at both ends,
  D62-3 (c)) as a partial diffeomorphism on `S¹ × rimBox 2`, with `rim_proj`, `target_full` (fibre
  clopen argument), `rim_label`, `RimProductAt` (a short proof from the inner matching
  `Hm (w, t) = Fl_t (C w)`, D62-3 (b)), the closure in `safe.corner e` (compact tube over the closed
  box, D62-3 (i)), `height_eq`, `horizontal_eq`, target in the raw tube.

* `FC39PreparedV2.exists_endRimChart_GRIM` — the per-end kernel on an abstract boundaryless slab;
* `FC39PreparedV2.exists_handleRimCharts_GRIM` — the binding (= planned statement (B) of
  `build-logs/scratch/FC39-G-RIMBOX/TargetsHandleChart.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsRCB_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothRCB_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## `endCoord` arithmetic -/

theorem endCoord_zero_GRIM (b : Bool) : endCoord b 0 = ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) := by
  cases b <;> simp [endCoord, iccEnd]

theorem endCoord_sub_zero_GRIM (b : Bool) (s : ℝ) : |endCoord b s - endCoord b 0| = |s| := by
  cases b <;> simp [endCoord, abs_neg]

theorem endCoord_affine_GRIM (b : Bool) (s : ℝ) :
    endCoord b s = (if b then -1 else 1) * s + (if b then 1 else 0) := by
  cases b
  · simp [endCoord]
  · simp [endCoord]
    ring

theorem endCoord_mem_window_GRIM (b : Bool) {ε s : ℝ} (hs : |s| < ε / 2) :
    endCoord b s ∈ Ioo (-(ε / 2)) (1 + ε / 2) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hs
  cases b <;> simp only [endCoord, Bool.false_eq_true, ite_false, ite_true] <;>
    constructor <;> linarith

theorem endCoord_mem_Icc_GRIM (b : Bool) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    endCoord b s ∈ Icc (0 : ℝ) 1 := by
  cases b <;> simp only [endCoord, Bool.false_eq_true, ite_false, ite_true]
  · exact hs
  · exact ⟨by linarith [hs.2], by linarith [hs.1]⟩

section PerEnd

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ Y]

/-- **The per-end rim chart (sheet §3 K4–K7)** on an abstract boundaryless slab `Y` mapped into the
edge source by `j` and into the carrier by the partial diffeomorphism `ι` (= `j` on all of `Y`). -/
theorem FC39PreparedV2.exists_endRimChart_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (i : Fin Pr.rows.edgeModels.intervalCount)
    (b : Bool) {V : Set Pr.rows.edge.Base} (hV : IsOpen V) {φ : Pr.rows.edge.Base → ℝ}
    (hφ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V) (hφinj : InjOn φ V)
    (hφβ : ∀ t, φ (Pr.rows.edgeModels.intervalBase i t) = t)
    (hrange : range (Pr.rows.edgeModels.intervalBase i) ⊆ V) {ε : ℝ} (hε : 0 < ε)
    (j : Y → Pr.rows.edge.source) (hj : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ∞ j)
    (hjV : ∀ y, Pr.rows.edge.proj (j y) ∈ V)
    (ι : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model Y W.Carrier ∞)
    (hιs : ι.source = univ) (hιj : ∀ y, ι y = (j y : W.Carrier))
    (H : EdgeHandle W) (Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → Y)
    (hHm : ∀ p, H.map p = (j (Hm p) : W.Carrier))
    (hrim : (fun w => H.map (w, iccEnd b)) '' diskRim =
      Pr.rows.edge.rim (Pr.rows.edgeModels.intervalBase i (iccEnd b)))
    {δ r' : ℝ} {U : TopologicalSpace.Opens Y}
    (Fl : ℝ → U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 3)), 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ U)
    (C : EuclideanSpace ℝ (Fin 2) → Y) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδr : δ ≤ r')
    (hFl : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      ∞ (fun q : ℝ × U => Fl q.1 q.2))
    (hFlP : ∀ z : U, φ (Pr.rows.edge.proj (j z)) = 0 →
      -r' ≤ Pr.rows.edge.level - Pr.rows.edge.height (j z) →
      ∀ t ∈ Ioo (-(ε / 2)) (1 + ε / 2), φ (Pr.rows.edge.proj (j (Fl t z))) = t)
    (hFlB : ∀ (z : U) (t : ℝ), |Pr.rows.edge.level - Pr.rows.edge.height (j z)| < r' →
      Pr.rows.edge.level - Pr.rows.edge.height (j (Fl t z)) =
        Pr.rows.edge.level - Pr.rows.edge.height (j z))
    (hC : ContMDiffOn (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ C {z | |‖z‖ - 1| < δ})
    (hCinj : InjOn C {z | |‖z‖ - 1| < δ})
    (hCimm : ∀ z, |‖z‖ - 1| < δ →
      Injective (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) C z))
    (hCP : ∀ z, |‖z‖ - 1| < δ → φ (Pr.rows.edge.proj (j (C z))) = 0 ∧
      Pr.rows.edge.level - Pr.rows.edge.height (j (C z)) = 1 - ‖z‖)
    (hCU : ∀ z, |‖z‖ - 1| < δ → C z ∈ U)
    (hHmC : ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1), 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
      ∃ hw : C w ∈ U, Hm (w, t) = ((Fl (t : ℝ) ⟨C w, hw⟩ : U) : Y)) :
    ∃ (lam : ℝ) (κ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞)
      (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞),
      0 < lam ∧
      κ.source = rimBox 3 ∧
      (∀ v ∈ rimBox 3, Pr.rows.labelledTubes.chart (Pr.rows.edgeModels.endpointEquiv (i, b))
        (κ v) = lam • v) ∧
      κ (0, 0) = Pr.rows.junctions.rimBase (Pr.rows.edgeModels.endpointEquiv (i, b)).1 ∧
      κ.target ⊆ (safe.cornerBase (Pr.rows.edgeModels.endpointEquiv (i, b)) : Set _) ∩
        (Pr.globalFaces.base : Set Pr.rows.circle.Base) ∧
      (∀ v ∈ rimBox 3,
        Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
            (.vertical (Pr.rows.edgeModels.endpointEquiv (i, b)).component)) (κ v) =
          -(lam * v.1) ∧
        Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.horizontal
            (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b))))) (κ v) =
          -(lam * v.2)) ∧
      (∀ f v, f ≠ Pr.globalFaces.actualFace.symm
            (.vertical (Pr.rows.edgeModels.endpointEquiv (i, b)).component) →
        f ≠ Pr.globalFaces.actualFace.symm (.horizontal
            (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b)))) →
        v ∈ rimBox 3 → Pr.globalFaces.fn f (κ v) < 0) ∧
      (∀ p, p ∈ χ.source ↔ p.2 ∈ rimBox 2) ∧
      (∀ p ∈ χ.source, ∃ hx : χ p ∈ Pr.rows.circle.domain,
        Pr.rows.circle.proj ⟨χ p, hx⟩ = κ p.2) ∧
      χ.target = Pr.rows.circle.tube (κ '' rimBox 2) ∧
      χ '' {p | p.2 = (0, 0)} = (fun x : ClosedCell 2 => H.map (x, iccEnd b)) '' diskRim ∧
      RimProductAt χ H b ∧
      closure χ.target ⊆ safe.corner (Pr.rows.edgeModels.endpointEquiv (i, b)) ∧
      (∀ p ∈ χ.source, ∃ hx : χ p ∈ Pr.rows.edge.source,
        Pr.rows.edge.height ⟨χ p, hx⟩ - Pr.rows.edge.level = lam * p.2.1) ∧
      (∀ p ∈ χ.source, Pr.rows.slim.residualFn
        (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b))) (χ p) =
          lam * p.2.2) ∧
      χ.target ⊆ Pr.rows.labelledTubes.tube (Pr.rows.edgeModels.endpointEquiv (i, b)) := by
  classical
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set e := Pr.rows.edgeModels.endpointEquiv (i, b) with he
  have he1 : e.1 = Pr.rows.edgeModels.intervalBase i (iccEnd b) :=
    Pr.rows.edgeModels.endpointEquiv_apply i b
  have hecb : e.1 ∈ Pr.rows.edge.cbase := Pr.rows.edge.frontier_cbase_subset e.2
  -- the axial coordinate and the height on the slab
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ) ∞
      (fun y : Y => φ (Pr.rows.edge.proj (j y))) := fun y =>
    (hφ.contMDiffAt (hV.mem_nhds (hjV y))).comp y ((Pr.rows.edge.proj_smooth.comp hj) y)
  have hCP1 : ∀ z, |‖z‖ - 1| < δ → φ (Pr.rows.edge.proj (j (C z))) = 0 ∧
      Pr.rows.edge.level - Pr.rows.edge.height (j (C z)) = 1 * (1 - ‖z‖) := fun z hz =>
    ⟨(hCP z hz).1, by rw [one_mul]; exact (hCP z hz).2⟩
  obtain ⟨hFsm, -, -, hFval⟩ :=
    rimParam_props_GRIM (P := fun y : Y => φ (Pr.rows.edge.proj (j y)))
      (B := fun y : Y => Pr.rows.edge.level - Pr.rows.edge.height (j y)) hg Fl hFl hFlP hFlB C
      one_pos hδ1 (by rw [one_mul]; exact hδr) hC hCinj hCimm hCP1 hCU
  set F := rimParam_GRIM Fl C 1 with hFdef
  set ΩF : Set (Circle × (ℝ × ℝ)) :=
    {p | |p.2.1| < 1 * δ ∧ p.2.2 ∈ Ioo (-(ε / 2)) (1 + ε / 2)} with hΩFdef
  have hΩF : IsOpen ΩF :=
    (isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (isOpen_Ioo.preimage (continuous_snd.comp continuous_snd))
  have hwin0 : ∀ s : ℝ, |s| < ε / 2 → endCoord b s ∈ Ioo (-(ε / 2)) (1 + ε / 2) :=
    fun s hs => endCoord_mem_window_GRIM b hs
  -- (1) the central rim is the old end rim of the handle
  have hcentral : ∀ θ : Circle, F (θ, (0, endCoord b 0)) = Hm (circleRimPoint θ, iccEnd b) := by
    intro θ
    have hw : 1 - δ < ‖((circleRimPoint θ : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ := by
      rw [mem_diskRim_iff.mp (circleRimPoint_mem_diskRim θ)]
      linarith
    obtain ⟨hCw, hHmw⟩ := hHmC (circleRimPoint θ) (iccEnd b) hw
    rw [hHmw, hFdef]
    have hpol : rimPolar_GRIM 1 (θ, 0) =
        ((circleRimPoint θ : ClosedCell 2) : EuclideanSpace ℝ (Fin 2)) := by
      rw [circleRimPoint_val]
      simp [rimPolar_GRIM, planeOfCircle]
    unfold rimParam_GRIM
    simp only
    rw [hpol, flowExt_of_mem_GRIM Fl hCw, endCoord_zero_GRIM]
  have hcentralRim : ∀ θ : Circle,
      (j (F (θ, (0, endCoord b 0))) : W.Carrier) ∈ Pr.rows.edge.rim e.1 := by
    intro θ
    rw [hcentral, ← hHm, he1, ← hrim]
    exact ⟨circleRimPoint θ, circleRimPoint_mem_diskRim θ, rfl⟩
  have hrimFib : Pr.rows.edge.rim e.1 = Pr.rows.circle.fibre (Pr.rows.junctions.rimBase e.1) :=
    Pr.rows.junctions.rim_fibre e.1 hecb
  have hfibTube : Pr.rows.circle.fibre (Pr.rows.junctions.rimBase e.1) ⊆
      Pr.rows.circle.tube (Pr.rows.labelledTubes.base e) :=
    Pr.rows.circle.fibre_subset_tube_GTR (Pr.rows.labelledTubes.rimBase_mem e)
  have hcentralProj : ∀ θ : Circle, Pr.rows.edge.proj (j (F (θ, (0, endCoord b 0)))) = e.1 := by
    intro θ
    obtain ⟨x', ⟨hx'1, -⟩, hx'e⟩ := hcentralRim θ
    have : x' = j (F (θ, (0, endCoord b 0))) := Subtype.ext hx'e
    rw [← this]
    exact hx'1
  -- (2) the raw-tube box at the central rim (D62-3 (g))
  have hFcont : ContinuousOn (fun q => (j (F q) : W.Carrier)) ΩF :=
    (continuous_subtype_val.comp hj.continuous).comp_continuousOn hFsm.continuousOn
  have hTo : IsOpen (Pr.rows.circle.tube (Pr.rows.labelledTubes.base e)) :=
    Pr.rows.circle.isOpen_tube_GTR (Pr.rows.labelledTubes.base e).isOpen
  have hz₀ : ∀ θ : Circle, (θ, ((0 : ℝ), endCoord b 0)) ∈ ΩF ∧
      (fun q => (j (F q) : W.Carrier)) (θ, ((0 : ℝ), endCoord b 0)) ∈
        Pr.rows.circle.tube (Pr.rows.labelledTubes.base e) := by
    intro θ
    refine ⟨⟨by rw [abs_zero, one_mul]; exact hδ0, hwin0 0 (by rw [abs_zero]; linarith)⟩, ?_⟩
    exact hfibTube (hrimFib ▸ hcentralRim θ)
  obtain ⟨η, hη, hbox⟩ := exists_tube_box_GRIM (fun q => (j (F q) : W.Carrier)) hΩF hFcont hTo
    ((0 : ℝ), endCoord b 0) hz₀
  -- the descended equation on the raw tube
  have hdesc : ∀ y : Y, (j y : W.Carrier) ∈ Pr.rows.circle.tube (Pr.rows.labelledTubes.base e) →
      Pr.rows.slim.residualFn (Pr.rows.junctions.horizontal e) (j y) =
        Pr.rows.labelledTubes.descended e (Pr.rows.edge.proj (j y)) := by
    intro y hy
    obtain ⟨y', hy', hy'e⟩ := hy
    obtain ⟨hx, hxe⟩ := Pr.rows.labelledTubes.descended_eq e y' hy'
    have h1 : (⟨(y' : W.Carrier), hx⟩ : Pr.rows.edge.source) = j y := Subtype.ext hy'e
    rw [← hy'e, hxe, h1]
  -- (3) the end profile
  set δ₀ : ℝ := min η (ε / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hη (by linarith)
  have hδ₀η : δ₀ ≤ η := min_le_left _ _
  have hδ₀ε : δ₀ ≤ ε / 2 := min_le_right _ _
  set γ : ℝ → Pr.rows.edge.Base :=
    fun s => Pr.rows.edge.proj (j (F ((1 : Circle), ((0 : ℝ), endCoord b s)))) with hγdef
  have hγΩ : ∀ s, |s| < ε / 2 → ((1 : Circle), ((0 : ℝ), endCoord b s)) ∈ ΩF := fun s hs =>
    ⟨by rw [abs_zero, one_mul]; exact hδ0, hwin0 s hs⟩
  have hγsm : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ (Ioo (-δ₀) δ₀) := by
    have hc : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ∞
        (fun s : ℝ => ((1 : Circle), ((0 : ℝ), endCoord b s))) :=
      contMDiff_const.prodMk
        ((contDiff_const.prodMk (contDiff_endCoord_comp_GRIM contDiff_id b)).contMDiff)
    exact (Pr.rows.edge.proj_smooth.comp hj).comp_contMDiffOn (hFsm.comp hc.contMDiffOn
      fun s hs => hγΩ s (abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩))
  have hγ0 : γ 0 = e.1 := hcentralProj 1
  have hφγ : ∀ s, |s| < ε / 2 → φ (γ s) = endCoord b s := fun s hs =>
    (hFval _ (hγΩ s hs).1 (hγΩ s hs).2).1
  obtain ⟨Ud, hUde, hUd⟩ := Pr.rows.labelledTubes.descended_smooth e
  have hdγ0 : Pr.rows.labelledTubes.descended e (γ 0) = 0 := by
    have hx := hcentralRim 1
    rw [hrimFib] at hx
    obtain ⟨y', hy', hy'e⟩ := hx
    have hy'b : Pr.rows.circle.proj y' ∈ Pr.rows.labelledTubes.base e := by
      rw [mem_preimage, mem_singleton_iff] at hy'
      rw [hy']
      exact Pr.rows.labelledTubes.rimBase_mem e
    have hface := Pr.rows.labelledTubes.face_eq e y' hy'b
    rw [mem_preimage, mem_singleton_iff] at hy'
    rw [hy', Pr.rows.labelledTubes.chart_center e] at hface
    have hd := hdesc (F ((1 : Circle), ((0 : ℝ), endCoord b 0)))
      (hfibTube (hrimFib ▸ hcentralRim 1))
    rw [← hy'e] at hd
    change Pr.rows.labelledTubes.descended e (γ 0) = 0
    rw [hγdef]
    simp only
    rw [← hd, ← hface]
  have hcomp_eq : (Pr.rows.edgeModels.componentEquiv (.inl i)) = e.component := by
    refine ActualComponent.eq_of_mem (z := e.1) ?_
      (mem_connectedComponentIn (Pr.rows.edge.frontier_cbase_subset e.2))
    rw [← Pr.rows.edgeModels.intervalBase_range i, he1]
    exact mem_range_self _
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ Pr.rows.labelledTubes.descended e (γ s) := by
    have hm : Ioo (0 : ℝ) (min δ₀ 1) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (lt_min hδ₀ one_pos)
    filter_upwards [hm] with s hs
    have hsδ : s < δ₀ := lt_of_lt_of_le hs.2 (min_le_left _ _)
    have hs1 : s < 1 := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hsε : |s| < ε / 2 := by rw [abs_of_pos hs.1]; linarith
    set x := j (F ((1 : Circle), ((0 : ℝ), endCoord b s))) with hx
    -- in the raw tube
    have hxT : (x : W.Carrier) ∈ Pr.rows.circle.tube (Pr.rows.labelledTubes.base e) :=
      (hbox 1 0 (endCoord b s) (by rw [sub_zero, abs_zero]; exact hη)
        (by rw [endCoord_sub_zero_GRIM, abs_of_pos hs.1]; linarith)).2
    -- on the vertical face of the component
    have hxlev : Pr.rows.edge.height x = Pr.rows.edge.level := by
      have h := (hFval _ (hγΩ s hsε).1 (hγΩ s hsε).2).2
      simp only [neg_zero] at h
      linarith
    have hIcc : endCoord b s ∈ Icc (0 : ℝ) 1 := endCoord_mem_Icc_GRIM b ⟨hs.1.le, hs1.le⟩
    have hxproj : Pr.rows.edge.proj x = Pr.rows.edgeModels.intervalBase i ⟨endCoord b s, hIcc⟩ :=
      hφinj (hjV _) (hrange (mem_range_self _)) (by rw [hφβ]; exact hφγ s hsε)
    have hxwhole : (x : W.Carrier) ∈ Pr.rows.edge.wholeComponent e.component := by
      refine ⟨x, ⟨?_, hxlev.le⟩, rfl⟩
      rw [← hcomp_eq, ← Pr.rows.edgeModels.intervalBase_range i, hxproj]
      exact mem_range_self _
    obtain ⟨y', hy', hy'e⟩ := hxT
    have hside := (Pr.rows.labelledTubes.edge_side hy').mp (hy'e ▸ hxwhole)
    have hface := Pr.rows.labelledTubes.face_eq e y' hy'
    have hd := hdesc _ (hy'e ▸ ⟨y', hy', rfl⟩ :
      (x : W.Carrier) ∈ Pr.rows.circle.tube (Pr.rows.labelledTubes.base e))
    have h2 : 0 ≤ Pr.rows.slim.residualFn (Pr.rows.junctions.horizontal e) (x : W.Carrier) := by
      rw [← hy'e, ← hface]
      exact hside.1
    rw [hd] at h2
    exact h2
  have ha : (if b then (-1 : ℝ) else 1) ≠ 0 := by
    cases b <;> norm_num
  obtain ⟨l₁, hl₁, hprof⟩ := exists_endProfile_of_curve_GRIM (N := Pr.rows.edge.Base) Ud.isOpen hUd
    (by rw [hγ0]; exact hUde) hδ₀ hγsm hV hφ (by rw [hγ0, he1]; exact hrange (mem_range_self _))
    ha (fun s hs => by
      rw [hφγ s (abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩), endCoord_affine_GRIM])
    (by rw [hγ0]; exact Pr.rows.labelledTubes.descended_regular e) hdγ0 hpos hδ₀
  -- (4) the corner chart
  obtain ⟨l₂, hl₂, hcorner⟩ := Pr.exists_cornerChartScale_GRIM safe e
  -- (5) the scale, frozen LAST (D62-3 (e))
  set lam : ℝ := min (min l₁ l₂) (min (δ / 4) (η / 4)) with hlamdef
  have hlam : 0 < lam := lt_min (lt_min hl₁ hl₂) (lt_min (by linarith) (by linarith))
  have hlam1 : lam ≤ l₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hlam2 : lam ≤ l₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hlamδ : lam ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hlamη : lam ≤ η / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨τ, hτc, hτ0, hτy⟩ := hprof lam hlam hlam1
  obtain ⟨κ, hκs, hκv, hκch, hκ0, hκt, hκbox, hκnf, hκoth⟩ := hcorner lam hlam hlam2
  -- (6) the scaled rim parametrization
  have hτw : ∀ y ∈ Icc (-3 : ℝ) 3, endCoord b (τ y) ∈ Ioo (-(ε / 2)) (1 + ε / 2) := fun y hy =>
    hwin0 _ (abs_lt.mpr ⟨by linarith [(hτy y hy).2.2.1], by linarith [(hτy y hy).2.2.2]⟩)
  obtain ⟨hGsm, hGinj, hGimm, hGval⟩ :=
    rimParamReparam_props_GRIM (P := fun y : Y => φ (Pr.rows.edge.proj (j y)))
      (B := fun y : Y => Pr.rows.edge.level - Pr.rows.edge.height (j y)) hg Fl hFl hFlP hFlB C
      hδ1 hδr hC hCinj hCimm hCP hCU hlam (by linarith) hτc (fun y hy => (hτy y hy).2.1) b hτw
  set G := rimParam_GRIM Fl C 1 ∘ rimReparam_GRIM lam τ b with hGdef
  have hIcc3 : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 → p.2.2 ∈ Icc (-3 : ℝ) 3 := fun p hp =>
    ⟨(abs_lt.mp hp.2).1.le, (abs_lt.mp hp.2).2.le⟩
  -- (7) the points of the parametrization
  have hGtube : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 →
      (j (G p) : W.Carrier) ∈ Pr.rows.circle.tube (Pr.rows.labelledTubes.base e) := by
    intro p hp
    have hy := hτy _ (hIcc3 p hp)
    refine (hbox p.1 (lam * p.2.1) (endCoord b (τ p.2.2)) ?_ ?_).2
    · rw [sub_zero, abs_mul, abs_of_pos hlam]
      nlinarith [hp.1, abs_nonneg p.2.1]
    · rw [endCoord_sub_zero_GRIM]
      exact abs_lt.mpr ⟨by linarith [hy.2.2.1], by linarith [hy.2.2.2]⟩
  have hGh : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 →
      Pr.rows.edge.height (j (G p)) - Pr.rows.edge.level = lam * p.2.1 := by
    intro p hp
    have h := (hGval p hp).2
    linarith
  have hGres : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 →
      Pr.rows.slim.residualFn (Pr.rows.junctions.horizontal e) (j (G p)) = lam * p.2.2 := by
    intro p hp
    have hy := hτy _ (hIcc3 p hp)
    have hτε : |τ p.2.2| < ε / 2 :=
      abs_lt.mpr ⟨by linarith [hy.2.2.1], by linarith [hy.2.2.2]⟩
    have hproj : Pr.rows.edge.proj (j (G p)) = γ (τ p.2.2) :=
      hφinj (hjV _) (hjV _) (by rw [(hGval p hp).1, hφγ _ hτε])
    rw [hdesc _ (hGtube p hp), hproj]
    exact hy.1
  have hGproj : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 →
      ∃ hx : (j (G p) : W.Carrier) ∈ Pr.rows.circle.domain,
        Pr.rows.circle.proj ⟨j (G p), hx⟩ = κ p.2 := by
    intro p hp
    obtain ⟨hxd, -, -, hpr⟩ := Pr.rows.proj_eq_chart_symm_GRIM e (hGtube p hp) (j (G p)).2
      (hGh p hp) (hGres p hp)
    refine ⟨hxd, ?_⟩
    rw [hpr, hκv]
    rfl
  -- (8) the rim chart
  have h23 : ∀ v : ℝ × ℝ, v ∈ rimBox 2 → v ∈ rimBox 3 := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  obtain ⟨χ, hχs, hχv⟩ := exists_rimChart_of_param_GRIM ι hιs G
    (hGsm.mono fun p hp => h23 p.2 hp) (hGinj.mono fun p hp => h23 p.2 hp)
    (fun p hp => hGimm p (h23 p.2 hp))
  have hχj : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 2 → χ p = (j (G p) : W.Carrier) :=
    fun p hp => (hχv p hp).trans (hιj _)
  have hκsrc : ∀ v ∈ rimBox 3, κ v ∈ (Pr.rows.labelledTubes.chart e).source := by
    intro v hv
    rw [hκv]
    exact (Pr.rows.labelledTubes.chart e).toPartialEquiv.map_target
      (hκbox v (abs_le.mpr ⟨(abs_lt.mp hv.1).1.le, (abs_lt.mp hv.1).2.le⟩)
        (abs_le.mpr ⟨(abs_lt.mp hv.2).1.le, (abs_lt.mp hv.2).2.le⟩)).1
  have hχproj : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 2 →
      ∃ hx : χ p ∈ Pr.rows.circle.domain, Pr.rows.circle.proj ⟨χ p, hx⟩ = κ p.2 := by
    intro p hp
    obtain ⟨hxd, hpr⟩ := hGproj p (h23 _ hp)
    have heq := hχj p hp
    refine ⟨heq ▸ hxd, ?_⟩
    have h1 : (⟨χ p, heq ▸ hxd⟩ : Pr.rows.circle.domain) = ⟨j (G p), hxd⟩ := Subtype.ext heq
    rw [h1]
    exact hpr
  -- target_full (D62-3 (g))
  have htarget : χ.target = Pr.rows.circle.tube (κ '' rimBox 2) := by
    apply Subset.antisymm
    · intro x hx
      have hsrc : χ.symm x ∈ χ.source := χ.toPartialEquiv.map_target hx
      have hxeq : χ (χ.symm x) = x := χ.toPartialEquiv.right_inv hx
      have hv2 := (hχs _).mp hsrc
      obtain ⟨hxd, hpr⟩ := hχproj _ hv2
      refine ⟨⟨χ (χ.symm x), hxd⟩, ?_, hxeq⟩
      rw [mem_preimage, hpr]
      exact mem_image_of_mem κ hv2
    · rintro _ ⟨y, ⟨v, hv, hyv⟩, rfl⟩
      have hsrcv : ∀ θ : Circle, (θ, v) ∈ χ.source := fun θ => (hχs _).mpr hv
      have hcont : Continuous (fun θ : Circle => χ (θ, v)) :=
        χ.contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) hsrcv
      have hfib : range (fun θ : Circle => χ (θ, v)) ⊆ Pr.rows.circle.fibre (κ v) := by
        rintro _ ⟨θ, rfl⟩
        obtain ⟨hxd, hpr⟩ := hχproj (θ, v) hv
        exact ⟨⟨_, hxd⟩, by rw [mem_preimage, hpr]; rfl, rfl⟩
      have hTf : Pr.rows.circle.fibre (κ v) ∩ χ.target ⊆ range (fun θ : Circle => χ (θ, v)) := by
        rintro x ⟨⟨x', hx', hx'e⟩, hxT⟩
        have hsrc : χ.symm x ∈ χ.source := χ.toPartialEquiv.map_target hxT
        have hxeq : χ (χ.symm x) = x := χ.toPartialEquiv.right_inv hxT
        have hv2 := (hχs _).mp hsrc
        obtain ⟨hxd, hpr⟩ := hχproj _ hv2
        have hpx : Pr.rows.circle.proj ⟨χ (χ.symm x), hxd⟩ = κ v := by
          have h1 : (⟨χ (χ.symm x), hxd⟩ : Pr.rows.circle.domain) = x' :=
            Subtype.ext (hxeq.trans hx'e.symm)
          rw [h1]
          exact hx'
        have hvv : (χ.symm x).2 = v := by
          refine κ.toPartialEquiv.injOn ?_ ?_ (hpr.symm.trans hpx)
          · rw [hκs]
            exact h23 _ hv2
          · rw [hκs]
            exact h23 _ hv
        refine ⟨(χ.symm x).1, ?_⟩
        change χ ((χ.symm x).1, v) = x
        rw [← hvv]
        exact hxeq
      have hrange := Pr.rows.circle.range_eq_fibre_GRIM (fun θ : Circle => χ (θ, v)) hcont hfib
        χ.open_target (by rintro _ ⟨θ, rfl⟩; exact χ.toPartialEquiv.map_source (hsrcv θ)) hTf
      have hmem : (y : W.Carrier) ∈ Pr.rows.circle.fibre (κ v) := ⟨y, by
        rw [mem_preimage, mem_singleton_iff]; exact hyv.symm, rfl⟩
      rw [← hrange] at hmem
      obtain ⟨θ, hθ⟩ := hmem
      rw [← hθ]
      exact χ.toPartialEquiv.map_source (hsrcv θ)
  -- the central circle
  have hχ0 : ∀ θ : Circle, χ (θ, (0, 0)) = H.map (circleRimPoint θ, iccEnd b) := by
    intro θ
    rw [hχj (θ, (0, 0)) ⟨by norm_num, by norm_num⟩, hHm]
    congr 2
    change F (rimReparam_GRIM lam τ b (θ, ((0 : ℝ), (0 : ℝ)))) = _
    simp only [rimReparam_GRIM, mul_zero, hτ0]
    exact hcentral θ
  -- RimProductAt: a short proof from the inner matching (D62-3 (b))
  have hplane : ∀ θ : Circle, ‖planeOfCircle θ‖ = 1 := by
    intro θ
    unfold planeOfCircle
    rw [LinearIsometryEquiv.norm_map]
    exact Circle.norm_coe θ
  have hprod : RimProductAt χ H b := by
    refine ⟨2, by norm_num, le_rfl, LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)),
      fun x => 1 + lam * x, τ, contDiff_const.add (contDiff_const.mul contDiff_id), hτc,
      by simp, hτ0, fun x hx => ⟨?_, ?_⟩,
      fun y hy => (hτy y ⟨by linarith [hy.1], by linarith [hy.2]⟩).2.1, ?_⟩
    · nlinarith [hx.1]
    · have hd : HasDerivAt (fun x : ℝ => 1 + lam * x) (lam * 1) x :=
        ((hasDerivAt_id x).const_mul lam).const_add 1
      rw [hd.deriv, mul_one]
      exact hlam
    · intro θ x y w t hx hx' hy hy' hw ht
      have hxy : (x, y) ∈ rimBox 2 :=
        ⟨abs_lt.mpr ⟨hx, by linarith⟩, abs_lt.mpr ⟨by linarith, hy'⟩⟩
      have hρ : 0 < 1 + lam * x := by nlinarith
      have hnw : ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 + lam * x := by
        rw [hw, norm_smul, LinearIsometryEquiv.coe_refl, id_eq, hplane, mul_one,
          Real.norm_of_nonneg hρ.le]
      obtain ⟨hCw, hHmw⟩ := hHmC w t (by rw [hnw]; nlinarith)
      have hpol : rimPolar_GRIM 1 (θ, lam * x) = (w : EuclideanSpace ℝ (Fin 2)) := by
        rw [hw]
        simp [rimPolar_GRIM]
      have hG : G (θ, (x, y)) = Hm (w, t) := by
        rw [hHmw]
        change F (rimReparam_GRIM lam τ b (θ, (x, y))) = _
        simp only [rimReparam_GRIM, ← ht]
        rw [hFdef]
        unfold rimParam_GRIM
        simp only
        rw [hpol, flowExt_of_mem_GRIM Fl hCw]
      rw [hχj (θ, (x, y)) hxy, hHm, hG]
  -- the closure lies in the safe tube (D62-3 (i))
  have hbox2 : ∀ v ∈ Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2, |v.1| ≤ 3 ∧ |v.2| ≤ 3 := fun v hv =>
    ⟨abs_le.mpr ⟨by linarith [hv.1.1], by linarith [hv.1.2]⟩,
      abs_le.mpr ⟨by linarith [hv.2.1], by linarith [hv.2.2]⟩⟩
  have hclos : closure χ.target ⊆ safe.corner e := by
    set K2 : Set Pr.rows.circle.Base :=
      (fun v : ℝ × ℝ => (Pr.rows.labelledTubes.chart e).toPartialEquiv.symm (lam • v)) ''
        (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) with hK2
    have hK2c : IsCompact K2 := by
      refine (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn ?_
      refine (Pr.rows.labelledTubes.chart e).symm.contMDiffOn.continuousOn.comp
        (continuous_const_smul lam).continuousOn ?_
      intro v hv
      exact (hκbox v (hbox2 v hv).1 (hbox2 v hv).2).1
    have hT2c : IsCompact (Pr.rows.circle.tube K2) := Pr.rows.circle.isCompact_tube_GSAFE hK2c
    have hsub1 : χ.target ⊆ Pr.rows.circle.tube K2 := by
      rw [htarget]
      apply Pr.rows.circle.tube_mono_GSAFE
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨v, ⟨⟨by linarith [(abs_lt.mp hv.1).1], by linarith [(abs_lt.mp hv.1).2]⟩,
        ⟨by linarith [(abs_lt.mp hv.2).1], by linarith [(abs_lt.mp hv.2).2]⟩⟩, (hκv v).symm⟩
    have hsub2 : Pr.rows.circle.tube K2 ⊆ safe.corner e := by
      apply Pr.rows.circle.tube_mono_GSAFE
      rintro _ ⟨v, hv, rfl⟩
      exact (hκbox v (hbox2 v hv).1 (hbox2 v hv).2).2
    exact (closure_minimal hsub1 hT2c.isClosed).trans hsub2
  -- the target lies in the raw tube
  have hraw : χ.target ⊆ Pr.rows.labelledTubes.tube e := by
    rw [htarget]
    apply Pr.rows.circle.tube_mono_GSAFE
    rintro _ ⟨v, hv, rfl⟩
    have h := hκsrc v (h23 v hv)
    rwa [Pr.rows.labelledTubes.chart_source e] at h
  -- rim_label
  have hlabel : χ '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => H.map (x, iccEnd b)) '' diskRim := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' : p = (p.1, (0, 0)) := Prod.ext rfl hp
      rw [hp', hχ0]
      exact ⟨circleRimPoint p.1, circleRimPoint_mem_diskRim _, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨θ, rfl⟩ := exists_circleRimPoint_eq hw
      exact ⟨(θ, (0, 0)), rfl, hχ0 θ⟩
  -- height and horizontal equations
  have hheight : ∀ p ∈ χ.source, ∃ hx : χ p ∈ Pr.rows.edge.source,
      Pr.rows.edge.height ⟨χ p, hx⟩ - Pr.rows.edge.level = lam * p.2.1 := by
    intro p hp
    have hp2 := (hχs p).mp hp
    have heq := hχj p hp2
    refine ⟨heq ▸ (j (G p)).2, ?_⟩
    have h1 : (⟨χ p, heq ▸ (j (G p)).2⟩ : Pr.rows.edge.source) = j (G p) := Subtype.ext heq
    rw [h1]
    exact hGh p (h23 _ hp2)
  have hhor : ∀ p ∈ χ.source, Pr.rows.slim.residualFn (Pr.rows.junctions.horizontal e) (χ p) =
      lam * p.2.2 := by
    intro p hp
    have hp2 := (hχs p).mp hp
    rw [hχj p hp2]
    exact hGres p (h23 _ hp2)
  exact ⟨lam, κ, χ, hlam, hκs, hκch, hκ0, hκt, hκnf, hκoth, hχs,
    fun p hp => hχproj p ((hχs p).mp hp), htarget, hlabel, hprod, hclos, hheight, hhor, hraw⟩

end PerEnd

/-- **G6: the new handle of component `i` with, at each end, its corner chart and rim chart**
(planned statement (B) of `build-logs/scratch/FC39-G-RIMBOX/TargetsHandleChart.lean`). -/
theorem FC39PreparedV2.exists_handleRimCharts_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (i : Fin Pr.rows.edgeModels.intervalCount) :
    ∃ H : EdgeHandle W,
      range H.map =
        Pr.rows.edge.wholeComponent (Pr.rows.edgeModels.componentEquiv (.inl i)) ∧
      (∀ w t, ∃ hx : H.map (w, t) ∈ Pr.rows.edge.source,
        Pr.rows.edge.proj ⟨H.map (w, t), hx⟩ = Pr.rows.edgeModels.intervalBase i t) ∧
      (∀ t, range (fun w => H.map (w, t)) =
        Pr.rows.edge.disk (Pr.rows.edgeModels.intervalBase i t)) ∧
      (∀ t, (fun w => H.map (w, t)) '' diskRim =
        Pr.rows.edge.rim (Pr.rows.edgeModels.intervalBase i t)) ∧
      ∀ b : Bool,
        ∃ (lam : ℝ) (κ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞)
          (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞),
          0 < lam ∧
          κ.source = rimBox 3 ∧
          (∀ v ∈ rimBox 3, Pr.rows.labelledTubes.chart (Pr.rows.edgeModels.endpointEquiv (i, b))
            (κ v) = lam • v) ∧
          κ (0, 0) = Pr.rows.junctions.rimBase (Pr.rows.edgeModels.endpointEquiv (i, b)).1 ∧
          κ.target ⊆ (safe.cornerBase (Pr.rows.edgeModels.endpointEquiv (i, b)) : Set _) ∩
            (Pr.globalFaces.base : Set Pr.rows.circle.Base) ∧
          (∀ v ∈ rimBox 3,
            Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
                (.vertical (Pr.rows.edgeModels.endpointEquiv (i, b)).component)) (κ v) =
              -(lam * v.1) ∧
            Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.horizontal
                (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b))))) (κ v) =
              -(lam * v.2)) ∧
          (∀ f v, f ≠ Pr.globalFaces.actualFace.symm
                (.vertical (Pr.rows.edgeModels.endpointEquiv (i, b)).component) →
            f ≠ Pr.globalFaces.actualFace.symm (.horizontal
                (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b)))) →
            v ∈ rimBox 3 → Pr.globalFaces.fn f (κ v) < 0) ∧
          (∀ p, p ∈ χ.source ↔ p.2 ∈ rimBox 2) ∧
          (∀ p ∈ χ.source, ∃ hx : χ p ∈ Pr.rows.circle.domain,
            Pr.rows.circle.proj ⟨χ p, hx⟩ = κ p.2) ∧
          χ.target = Pr.rows.circle.tube (κ '' rimBox 2) ∧
          χ '' {p | p.2 = (0, 0)} = (fun x : ClosedCell 2 => H.map (x, iccEnd b)) '' diskRim ∧
          RimProductAt χ H b ∧
          closure χ.target ⊆ safe.corner (Pr.rows.edgeModels.endpointEquiv (i, b)) ∧
          (∀ p ∈ χ.source, ∃ hx : χ p ∈ Pr.rows.edge.source,
            Pr.rows.edge.height ⟨χ p, hx⟩ - Pr.rows.edge.level = lam * p.2.1) ∧
          (∀ p ∈ χ.source, Pr.rows.slim.residualFn
            (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b))) (χ p) =
              lam * p.2.2) ∧
          χ.target ⊆ Pr.rows.labelledTubes.tube (Pr.rows.edgeModels.endpointEquiv (i, b)) := by
  obtain ⟨V, hV, φ, ε, hε, hrange, hφ, hφβ, hφinj, -, -, hrest⟩ :=
    Pr.rows.edgeModels.exists_flowEdgeHandle_GRIM i
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
    (M := W.pieceInterior (edgeSlab_GRIM Pr.rows.edge V hV))
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (W.pieceInterior (edgeSlab_GRIM Pr.rows.edge V hV)) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  obtain ⟨H, Hm, hHm, hwhole, hproj, hdisk, hrim, δ, r', U, Fl, C, hδ0, hδ1, hδr, hFl, -, -,
    hFlP, hFlB, hC, hCinj, hCimm, hCP, hCU, hHmC⟩ := hrest
  have _ : Nonempty (W.pieceInterior (edgeSlab_GRIM Pr.rows.edge V hV)) :=
    ⟨Hm (⟨0, by simp⟩, iccEnd false)⟩
  obtain ⟨ι, hιs, hιv⟩ := exists_pieceInterior_partialDiffeomorph_GRIM
    (edgeSlab_GRIM Pr.rows.edge V hV)
  have hj : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ∞
      (edgeSlabIncl_GRIM Pr.rows.edge V hV) :=
    (contMDiff_inclusion (pieceInterior_edgeSlab_le_GRIM Pr.rows.edge V hV)).comp
      (DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id
      W.model ∞ (M := W.pieceInterior (edgeSlab_GRIM Pr.rows.edge V hV)))
  refine ⟨H, hwhole, hproj, hdisk, hrim, fun b => ?_⟩
  exact Pr.exists_endRimChart_GRIM safe i b hV hφ hφinj hφβ hrange hε
    (edgeSlabIncl_GRIM Pr.rows.edge V hV) hj (fun y => y.2.1.snd) ι hιs (fun y => hιv y) H Hm hHm
    (hrim (iccEnd b)) Fl C hδ0 hδ1 hδr hFl hFlP hFlB hC hCinj hCimm hCP hCU hHmC

end GC.GraphManifold.Assembly.FC39P0
