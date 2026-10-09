/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicExcessCrossingsReturn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicReturnOperations

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

theorem exists_section34BigonSlide_of_excess_meridian_crossings
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hJ : IsPLSphere 1 J) (hJΘ : J ⊆ frontier P)
    (hJu : IsPolyhedralSphere (n := 3) 1 (u '' J))
    (hJT : u '' J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hcarry : CarriesFirstHomologyOnto (u '' J)
      (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hmore : ∃ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 ∧
      ((u '' J) ∩ section34SplitDiskImage srcBd f₁ e).Nontrivial) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) fblBd t := by
  obtain ⟨w, e, B, α, hwinc, _, hα, hBJ, hBS, hends, hmeet⟩ :=
    exists_intrinsic_returning_arc_of_excess_meridian_crossings hinv hcut hgraph s
      hP hu hUP hJ hJΘ hJu hJT hcarry hmore
  have hVP : section34VertexBallImage src f₁ w ⊆ u '' P := by
    rw [hUP]
    exact fun x hx => mem_section34FaceTorus_iff.mpr ⟨w, hwinc, hx⟩
  have hBP : B ⊆ P := hBJ.trans (hJΘ.trans hP.isPolyhedron.isClosed.frontier_subset)
  have hBtrace : B ⊆ u ⁻¹' (fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v)) :=
    fun x hx => hJT (mem_image_of_mem u (hBJ hx))
  exact exists_section34BigonSlide_of_returning_model_trace_arc hcut hgraph hinv hnc s w e
    hu hVP hα hBP (fun x hx => (hBtrace hx).1) hBS (fun x hx => (hBtrace hx).2) hends hmeet

end DifferentialGeometry.Topology.PiecewiseLinear
