/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ModelTorusTraceCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicDiskLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U W : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {η : M₁ → ℝ} {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem exists_section34_vertex_disk_of_disjoint_face_trace_model
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (t : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hwt : Section34Incident w.1 t.1) {J : Set M₂}
    (hJ : ∃ (J₀ : Set E3) (v : E3 → M₂), IsPLSphere 1 J₀ ∧
      IsPLHomeomorphInto 3 v J₀ ∧ J = v '' J₀)
    (hJV : J ⊆ section34VertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJF : Disjoint J (fblBd t))
    (hJγ : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
      Disjoint J (section34SplitDiskImage srcBd f₁ e)) :
    ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
        Disjoint D (section34SplitDiskImage src f₁ e) := by
  classical
  have hf₁ := hgraph.2.2.1
  obtain ⟨P, u, hP, hu, hUP, hfront⟩ := exists_section34FaceTorus_intrinsic_model hcut hgraph t
  let T := section34FaceTorus (section34VertexBallImage src f₁) t
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hVT : section34VertexBallImage src f₁ w ⊆ T :=
    fun x hx => mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hx⟩
  have hTN : T ⊆ ⋃ v, section34VertexBallImage src f₁ v := by
    intro x hx
    obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
  have hJT : J ⊆ T := hJV.trans hVT
  have hJΘ : J ⊆ frontier T := fun x hx =>
    ⟨subset_closure (hJT hx), fun hi => (hJN hx).2 (interior_mono hTN hi)⟩
  have hright : ∀ y ∈ T, u (g y) = y := by
    intro y hy
    apply hu.injOn.bijOn_image.invOn_invFunOn.2
    rwa [hUP]
  have hmodelJ : IsPLSphere 1 (g '' J) := by
    obtain ⟨J₀, v, hJ₀, hv, hJv⟩ := hJ
    have hsub : v '' J₀ ⊆ u '' P := by rwa [← hJv, hUP]
    have hcomp := hv.isPLHomeomorphOn_invFunOn_comp hJ₀.isPolyhedron hu hsub
    rw [hJv, ← image_comp]
    exact hJ₀.of_isPLHomeomorphOn hcomp
  have hmodelΘ : g '' J ⊆ frontier P := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hfront.symm.subset (hJΘ hy)
    rw [← hzy, hleft (hP.isPolyhedron.isClosed.frontier_subset hz)]
    exact hz
  have himageJ : u '' (g '' J) = J := by
    rw [image_image]
    calc
      (u ∘ g) '' J = id '' J := image_congr fun y hy => hright y (hJT hy)
      _ = J := image_id J
  have htop : IsTopologicalSolidTorus T := by
    change IsTopologicalSolidTorus (section34FaceTorus (section34VertexBallImage src f₁) t)
    rw [← hUP]
    exact hP.isTopologicalSolidTorus_image hu
  let eH := htop.integralSingularHomologyOneEquivInt
  let _ : Nontrivial (integralSingularHomology 1 T) :=
    ⟨⟨eH.symm 0, eH.symm 1, fun heq => zero_ne_one (eH.symm.injective heq)⟩⟩
  obtain ⟨ι, hι, F, hF, hdis, hmodeltrace, -, -, -, htrace⟩ :=
    exists_finite_section34Trace_model_circles hcut hf₁ hinv t hP hu hUP hfront
  let _ := hι
  have hFΘ : ∀ i, F i ⊆ frontier P := fun i x hx =>
    (hmodeltrace.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)).1
  have hcarry : CarriesFirstHomologyOnto (u '' ⋃ i, F i) T := by
    rw [image_iUnion, ← htrace]
    exact hinv.2.2.2.2.2.2.1 t
  have hdisF : ∀ i, Disjoint (g '' J) (F i) := by
    intro i
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ hxF
    have hxtrace := hmodeltrace.symm.subset (mem_iUnion.mpr ⟨i, hxF⟩)
    have hux : u x = y := by rw [← hyx, hright y (hJT hy)]
    exact disjoint_left.mp hJF hy (hux ▸ hxtrace.2)
  have hΘT : u '' frontier P ⊆ T :=
    (image_mono hP.isPolyhedron.isClosed.frontier_subset).trans hUP.subset
  have hnull : (⟨inclusion ((image_mono hmodelΘ).trans hΘT),
      continuous_inclusion _⟩ : C(u '' (g '' J), T)).Nullhomotopic := by
    exact (hcut.isPLCellOn_vertexBallImage hf₁ w).nullhomotopic_inclusion
      (himageJ.subset.trans hJV) hVT
  obtain ⟨D, q, hq, hDΘ, hJq⟩ :=
    hP.isPLTorus_frontier.exists_disk_of_nullhomotopic_image_circle_disjoint_carrier
      hF hFΘ hdis (hu.continuousOn.mono hP.isPolyhedron.isClosed.frontier_subset)
      (hu.injOn.mono hP.isPolyhedron.isClosed.frontier_subset) hΘT hcarry hmodelJ
      hmodelΘ hdisF hnull
  have hJdis : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
      Disjoint (g '' J) (g '' section34SplitDiskImage srcBd f₁ e) := by
    intro e he
    have heT := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset.trans
      (hcut.splitDiskImage_subset_faceTorus hf₁ t e he)
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hzy : z = y := by
      rw [← hright z (heT hz), ← hright y (hJT hy), hzx, hyx]
    exact disjoint_left.mp (hJγ e he) hy (hzy ▸ hz)
  obtain ⟨hDV, hDE⟩ := hcut.intrinsic_disk_subset_vertexBall_of_boundary_subset hf₁
    t w hwt hP hu hUP hq hDΘ (by rw [← hJq]; exact image_mono hJV)
      (by simpa only [← hJq] using hJdis)
  have hDP : D ⊆ P := hDΘ.trans hP.isPolyhedron.isClosed.frontier_subset
  have hDpoly : IsPolyhedron D := (IsPLBall.isPolyhedron ⟨q, hq⟩)
  refine ⟨u '' D, ⟨D, q, u, hq, hu.mono_of_polyhedron hDpoly hDP, rfl, ?_⟩, ?_, ?_⟩
  · rw [← hJq, himageJ]
  · rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hDV hz
    rw [← hyz, hright y (hVT ((hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_subset hy))]
    exact hy
  · intro e he
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxE
    apply disjoint_left.mp (hDE e he) hz
    exact ⟨u z, hxE, hu.injOn.leftInvOn_invFunOn (hDP hz)⟩

theorem exists_section34_vertex_disk_of_disjoint_face_trace
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (t : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hwt : Section34Incident w.1 t.1) {J : Set M₂}
    (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJV : J ⊆ section34VertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJF : Disjoint J (fblBd t))
    (hJγ : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
      Disjoint J (section34SplitDiskImage srcBd f₁ e)) :
    ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
        Disjoint D (section34SplitDiskImage src f₁ e) := by
  obtain ⟨P, u, hP, hu, hUP, -⟩ := exists_section34FaceTorus_intrinsic_model hcut hgraph t
  have hJT : J ⊆ u '' P := by
    rw [hUP]
    exact fun x hx => mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hJV hx⟩
  let C := Function.invFunOn u P '' J
  have hC : IsPLSphere 1 C := hu.isPLSphere_invFunOn_image hJ hJT
  have hCP : C ⊆ P := by
    rintro x ⟨y, hy, rfl⟩
    exact hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hJT hy)
  have hJC : J = u '' C := by
    rw [image_image]
    exact ((image_congr fun y hy =>
      hu.injOn.bijOn_image.invOn_invFunOn.2 (hJT hy)).trans (image_id J)).symm
  exact exists_section34_vertex_disk_of_disjoint_face_trace_model hinv hcut hgraph t w hwt
    ⟨C, u, hC, hu.mono_of_polyhedron hC.isPolyhedron hCP, hJC⟩ hJV hJN hJF hJγ

end DifferentialGeometry.Topology.PiecewiseLinear
