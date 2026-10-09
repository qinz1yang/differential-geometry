import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorBoundaryHomeo

/-!
# CP1-D8 (G1): the boundary time `τ = cores.start = E.start`

Right-sided constancy of the exterior kernel at the base time (equality), via the smooth window
at `cores.start` (closed time set `[start, c)`) and the time reparametrisation `φ`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem hresBoundary_CPD8 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) (hb : ¬ L.cores.start < E.start) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, s.1 < E.start + ε →
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q E.start le_rfl) x).ker := by
  classical
  have hEs : E.start = L.cores.start := le_antisymm (not_lt.mp hb) E.after_cores
  have hcomp : ∀ j, IsCompact (range (E.truncation j).inclusion) := fun j =>
    isCompact_range (E.truncation j).inclusion.continuous
  have hdom : ∀ j, range (E.truncation j).inclusion ⊆ L.cores.domain j L.cores.start := by
    intro j y hy
    rw [← hEs]
    exact L.cores.advertised_ball j E.start E.after_cores (E.in_ball j E.start le_rfl hy)
  obtain ⟨N, Fs, Ls, hFL, c, U, D, hc, hUo, hSU, hUd, hJh, hst⟩ :=
    exists_boundaryWindow_CPD8 L.cores (fun j => range (E.truncation j).inclusion) hcomp hdom
  have hsJ : L.cores.start ∈ Ico L.cores.start c := ⟨le_rfl, hc⟩
  obtain ⟨δ, hδ, hconst⟩ := exists_right_const_activeStage_CPD7 (F.observation.history N)
    (hJh _ hsJ).1 (hJh _ hsJ).2
  refine ⟨min (c - L.cores.start) δ, lt_min (sub_pos.mpr hc) hδ, fun s hs => ?_⟩
  have hs1 : s.1 < L.cores.start + min (c - L.cores.start) δ := by have h := hs; linarith [hEs]
  have hsc : L.cores.start ≤ s.1 := hEs ▸ s.2
  have hsJ' : s.1 ∈ Ico L.cores.start c := ⟨hsc, by linarith [min_le_left (c - L.cores.start) δ]⟩
  have hE0 : E.start ∈ Ico L.cores.start c := hEs ▸ hsJ
  have hseq := hconst s.1 (hJh _ hsJ').1 (hJh _ hsJ').2 hsc
    (by linarith [min_le_right (c - L.cores.start) δ])
  have hact : (F.observation.history N).activeStage ⟨E.start, (hJh _ hE0).1, (hJh _ hE0).2⟩ =
      (F.observation.history N).activeStage ⟨L.cores.start, (hJh _ hsJ).1, (hJh _ hsJ).2⟩ := by
    have : (⟨E.start, (hJh _ hE0).1, (hJh _ hE0).2⟩ : Icc (0 : ℝ) (F.observation.history N).horizon) =
        ⟨L.cores.start, (hJh _ hsJ).1, (hJh _ hsJ).2⟩ := Subtype.ext hEs
    rw [this]
  obtain ⟨e, he⟩ := exists_regionHomeo_of_boundaryWindow_CPD8 E N Fs Ls hFL c U D hUo hSU hUd hJh
    hst E.start s.1 le_rfl hEs s.2 hE0 hsJ' (hact.trans hseq.symm)
  have : portLoopRegionMap_CPD3 E i q s.1 s.2 =
      (e : C(E.region E.start, E.region s.1)).comp
        (portLoopRegionMap_CPD3 E i q E.start le_rfl) :=
    ContinuousMap.ext fun z => (he i q z).symm
  rw [this, kernel_comp_homeomorph]

end GC.LongTime.CuspP1
