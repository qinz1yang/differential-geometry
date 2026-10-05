import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimCornerScale
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0AdaptedV2
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K6, K7): the row-level pieces of the per-end rim charts

Lane FC39-G-RIMBOXc, dispositions D62-3 (e), (g), (h).

* `exists_pieceInterior_partialDiffeomorph_GRIM` — the inclusion of a piece interior (interior charts
  `𝓘(ℝ, ℝ³)`) into the carrier (model with boundary) as a partial diffeomorphism with source
  everything (`liftTargetOpen` of the interior-atlas diffeomorphism);
* `FC39PreparedV2.exists_cornerChartScale_GRIM` — the corner chart `κ_e = chart_e⁻¹ (lam ·)` on
  `rimBox 3` for every small scale (ONE `lam` for both coordinates, D62-3 (h)): the closed box `3`
  lands in `safe.cornerBase e ∩ V_e^can ∩ GF.base ∩ {other face functions < 0}` (the LOCAL witness
  `V_e^can` of `canonical_near_corner`), whence the two normal forms and the negativity of the other
  global face functions on `rimBox 3`;
* `FC39RowsV2.proj_eq_chart_symm_GRIM` — a point of the raw tube with height `level + X` and
  horizontal function `Y` projects to `chart_e⁻¹ (X, Y)` (D62-3 (g): height_eq / face_eq of the tube).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **The inclusion of a piece interior as a partial diffeomorphism** (interior charts → carrier
model), defined on the whole piece interior. -/
theorem exists_pieceInterior_partialDiffeomorph_GRIM (O : TopologicalSpace.Opens W.Carrier)
    [Nonempty (W.pieceInterior O)] :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior O)
    ∃ ι : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model (W.pieceInterior O)
        W.Carrier ∞, ι.source = univ ∧ ∀ y, ι y = (y : W.Carrier) := by
  intro _
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  let Ψ := (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞
    (M := W.pieceInterior O)).symm
  exact ⟨PartialDiffeomorph.liftTargetOpen Ψ.toPartialDiffeomorph rfl, rfl, fun _ => rfl⟩

/-- **The corner chart of an endpoint at every small scale** (sheet §3 K6, D62-3 (e), (h)). -/
theorem FC39PreparedV2.exists_cornerChartScale_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (e : Pr.rows.edge.EdgeEnd) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ lam, 0 < lam → lam ≤ l₀ →
      ∃ κ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞,
        κ.source = rimBox 3 ∧
        (∀ v, κ v = (Pr.rows.labelledTubes.chart e).toPartialEquiv.symm (lam • v)) ∧
        (∀ v ∈ rimBox 3, Pr.rows.labelledTubes.chart e (κ v) = lam • v) ∧
        κ (0, 0) = Pr.rows.junctions.rimBase e.1 ∧
        κ.target ⊆ (safe.cornerBase e : Set _) ∩ (Pr.globalFaces.base : Set Pr.rows.circle.Base) ∧
        (∀ v : ℝ × ℝ, |v.1| ≤ 3 → |v.2| ≤ 3 →
          lam • v ∈ (Pr.rows.labelledTubes.chart e).target ∧
          (Pr.rows.labelledTubes.chart e).toPartialEquiv.symm (lam • v) ∈ safe.cornerBase e) ∧
        (∀ v ∈ rimBox 3,
          Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.vertical e.component)) (κ v) =
            -(lam * v.1) ∧
          Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
            (.horizontal (Pr.rows.junctions.horizontal e))) (κ v) = -(lam * v.2)) ∧
        (∀ f v, f ≠ Pr.globalFaces.actualFace.symm (.vertical e.component) →
          f ≠ Pr.globalFaces.actualFace.symm (.horizontal (Pr.rows.junctions.horizontal e)) →
          v ∈ rimBox 3 → Pr.globalFaces.fn f (κ v) < 0) := by
  classical
  set GF := Pr.globalFaces with hGF
  set κ₀ := Pr.rows.labelledTubes.chart e with hκ₀
  set fv := GF.actualFace.symm (.vertical e.component) with hfv
  set fh := GF.actualFace.symm (.horizontal (Pr.rows.junctions.horizontal e)) with hfh
  have _ : Finite GF.Face := GF.finite
  obtain ⟨Vc, hVc0, hVcsub, hVc⟩ := GF.canonical_near_corner e
  have hsrc : Pr.rows.junctions.rimBase e.1 ∈ κ₀.source := by
    rw [hκ₀, Pr.rows.labelledTubes.chart_source e]
    exact Pr.rows.labelledTubes.rimBase_mem e
  have hc0 : κ₀ (Pr.rows.junctions.rimBase e.1) = 0 := Pr.rows.labelledTubes.chart_center e
  -- the open set of good base points
  set A : GF.Face → Set Pr.rows.circle.Base := fun f =>
    {c | c ∈ GF.base ∧ (f ≠ fv → f ≠ fh → GF.fn f c < 0)} with hA
  have hAo : ∀ f, IsOpen (A f) := by
    intro f
    by_cases h : f ≠ fv ∧ f ≠ fh
    · have hset : A f = (GF.base : Set _) ∩ GF.fn f ⁻¹' Iio 0 := by
        ext c
        simp only [hA, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio]
        exact ⟨fun hc => ⟨hc.1, hc.2 h.1 h.2⟩, fun hc => ⟨hc.1, fun _ _ => hc.2⟩⟩
      rw [hset]
      exact (GF.smooth f).continuousOn.isOpen_inter_preimage GF.base.isOpen isOpen_Iio
    · have hset : A f = (GF.base : Set _) := by
        ext c
        simp only [hA, mem_ofPred_eq, SetLike.mem_coe]
        refine ⟨fun hc => hc.1, fun hc => ⟨hc, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩⟩
      rw [hset]
      exact GF.base.isOpen
  set O : Set Pr.rows.circle.Base :=
    (safe.cornerBase e : Set _) ∩ (Vc : Set _) ∩ ((GF.base : Set _) ∩ ⋂ f, A f) with hO
  have hOo : IsOpen O :=
    ((safe.cornerBase e).isOpen.inter Vc.isOpen).inter (GF.base.isOpen.inter (isOpen_iInter_of_finite hAo))
  -- the rim base point is good
  have hcanon0 := hVc _ hVc0
  have hfv0 : GF.fn fv (Pr.rows.junctions.rimBase e.1) = 0 := by
    rw [hcanon0.1, ← hκ₀, hc0]
    simp
  have hfh0 : GF.fn fh (Pr.rows.junctions.rimBase e.1) = 0 := by
    rw [hcanon0.2, ← hκ₀, hc0]
    simp
  have hvh : fv ≠ fh := by
    intro h
    have := GF.actualFace.symm.injective h
    cases this
  have hbase0 : Pr.rows.junctions.rimBase e.1 ∈ GF.base := (hVcsub hVc0).1
  obtain ⟨-, -, -, hneg⟩ := GF.double_registered _ hbase0 fv fh hvh hfv0 hfh0
  have hcO : Pr.rows.junctions.rimBase e.1 ∈ O := by
    refine ⟨⟨safe.rimBase_mem e, hVc0⟩, hbase0, mem_iInter.mpr fun f => ⟨hbase0, fun h1 h2 => ?_⟩⟩
    exact hneg f h1 h2
  obtain ⟨l₀, hl₀, hscale⟩ := exists_cornerScale_GRIM κ₀ hsrc hc0 hOo hcO (by norm_num : (0 : ℝ) < 3)
  refine ⟨l₀, hl₀, fun lam hlam hll => ?_⟩
  have hbox : ∀ v ∈ rimBox 3, lam • v ∈ κ₀.target :=
    fun v hv => (hscale lam hlam hll v hv.1.le hv.2.le).1
  have hgood : ∀ v ∈ rimBox 3, κ₀.toPartialEquiv.symm (lam • v) ∈ O :=
    fun v hv => (hscale lam hlam hll v hv.1.le hv.2.le).2
  refine ⟨scaledChart_GRIM κ₀ lam 3 hlam hbox, rfl, fun v => rfl,
    fun v hv => chart_scaledChart_GRIM κ₀ lam 3 hlam hbox hv, ?_, ?_, fun v h1 h2 =>
      ⟨(hscale lam hlam hll v h1 h2).1, (hscale lam hlam hll v h1 h2).2.1.1⟩, fun v hv => ?_,
    fun f v h1 h2 hv => ?_⟩
  · change κ₀.toPartialEquiv.symm (lam • ((0 : ℝ), (0 : ℝ))) = _
    rw [show lam • ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) by simp, ← hc0]
    exact κ₀.toPartialEquiv.left_inv hsrc
  · intro c hc
    have hc' : c = κ₀.toPartialEquiv.symm (lam • (lam⁻¹ • κ₀ c)) := by
      rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
      exact (κ₀.toPartialEquiv.left_inv hc.1).symm
    have hmem := hgood _ hc.2
    rw [← hc'] at hmem
    exact ⟨hmem.1.1, hmem.2.1⟩
  · have hmem := hgood v hv
    have hk := chart_scaledChart_GRIM κ₀ lam 3 hlam hbox hv
    obtain ⟨h1, h2⟩ := hVc _ hmem.1.2
    change GF.fn fv (κ₀.toPartialEquiv.symm (lam • v)) = _ ∧
      GF.fn fh (κ₀.toPartialEquiv.symm (lam • v)) = _
    rw [h1, h2]
    change -(κ₀ (scaledChart_GRIM κ₀ lam 3 hlam hbox v)).1 = _ ∧
      -(κ₀ (scaledChart_GRIM κ₀ lam 3 hlam hbox v)).2 = _
    rw [hk]
    simp
  · have hmem := hgood v hv
    exact (mem_iInter.mp hmem.2.2 f).2 h1 h2

/-- **A raw-tube point projects to `chart_e⁻¹ (X, Y)`** when its height is `level + X` and its
horizontal function is `Y`. -/
theorem FC39RowsV2.proj_eq_chart_symm_GRIM (Rw : FC39RowsV2 W E) (e : Rw.edge.EdgeEnd)
    {x : W.Carrier} (hx : x ∈ Rw.circle.tube (Rw.labelledTubes.base e))
    (hxs : x ∈ Rw.edge.source) {X Y : ℝ}
    (hX : Rw.edge.height ⟨x, hxs⟩ - Rw.edge.level = X)
    (hY : Rw.slim.residualFn (Rw.junctions.horizontal e) x = Y) :
    ∃ hxd : x ∈ Rw.circle.domain,
      Rw.circle.proj ⟨x, hxd⟩ ∈ Rw.labelledTubes.base e ∧
      Rw.labelledTubes.chart e (Rw.circle.proj ⟨x, hxd⟩) = (X, Y) ∧
      Rw.circle.proj ⟨x, hxd⟩ = (Rw.labelledTubes.chart e).toPartialEquiv.symm (X, Y) := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y.2, hy, ?_, ?_⟩
  · obtain ⟨hxs', hh⟩ := Rw.labelledTubes.height_eq e y hy
    have hf := Rw.labelledTubes.face_eq e y hy
    refine Prod.ext ?_ ?_
    · rw [hh, ← hX]
    · rw [hf, ← hY]
  · have hch : Rw.labelledTubes.chart e (Rw.circle.proj y) = (X, Y) := by
      obtain ⟨hxs', hh⟩ := Rw.labelledTubes.height_eq e y hy
      have hf := Rw.labelledTubes.face_eq e y hy
      refine Prod.ext ?_ ?_
      · rw [hh, ← hX]
      · rw [hf, ← hY]
    have hsrc : Rw.circle.proj y ∈ (Rw.labelledTubes.chart e).source := by
      rw [Rw.labelledTubes.chart_source e]
      exact hy
    rw [← hch]
    exact ((Rw.labelledTubes.chart e).toPartialEquiv.left_inv hsrc).symm

end GC.GraphManifold.Assembly.FC39P0
