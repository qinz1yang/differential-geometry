/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicReturnCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicReturnDescent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicReturnDisks

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

theorem exists_section34BigonSlide_of_returning_model_trace_arc
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e : Section34EdgeIndex 𝒦 𝒦') {P B : Set E3} {u : E3 → M₂} {β : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P)
    (hVP : section34VertexBallImage src f₁ w ⊆ u '' P)
    (hβ : IsPLHomeomorphOn β (Icc 0 1) B) (hBP : B ⊆ P)
    (hBF : B ⊆ u ⁻¹' fblBd s) (hBS : B ⊆ u ⁻¹' section34VertexBallImage srcBd f₁ w)
    (hBN : B ⊆ u ⁻¹' frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hends : ({β 0, β 1} : Set E3) ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e)
    (hmeet : B ∩ u ⁻¹' (⋃ d, section34SplitDiskImage src f₁ d) = {β 0, β 1}) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) fblBd t := by
  have hf₁ := hgraph.2.2.1
  obtain ⟨R₀, D₀, q₀, δ₀, hδ₀, hδ₀0, hδ₀1, hR₀, hBR₀, hq₀, hq₀B,
    hD₀P, hD₀loc, hD₀E, hother⟩ :=
    exists_section34_model_return_disk_avoiding_split_disks hcut hf₁ hinv s w e hu hVP
      hβ hBP hBF hBS hBN hends hmeet (fun J hJ hJV hJN t hwt hJF hJE =>
        exists_section34_vertex_disk_of_disjoint_face_trace_model hinv hcut hgraph
          t w hwt hJ hJV hJN hJF hJE)
  let g := Function.invFunOn u P
  let S := g '' section34VertexBallImage srcBd f₁ w
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  obtain ⟨r, hr, hrS⟩ := hV.exists_isPLHomeomorphOn_invFunOn hu hVP
  have hS : IsPLSphere 2 S := by
    change IsPLSphere 2 (g '' section34VertexBallImage srcBd f₁ w)
    rw [hrS]
    exact hr.isPLSphere_image_stdSimplexBoundary
  have hD₀S : D₀ ⊆ S := fun x hx => ⟨u x, (hD₀loc hx).1, hleft (hD₀P hx)⟩
  apply exists_section34BigonSlide_of_model_return_disk_crosscuts hcut hf₁ hinv s w e
    hu hS hβ hBF hδ₀ hδ₀0 hδ₀1 hR₀ hBR₀ hq₀ hq₀B hD₀S hD₀P hD₀loc hD₀E hother
  intro t B R D q β δ hβ hBF _ _ _ hRR₀ hBR hq hqB hDD₀ _ hdirty
  exact exists_section34_model_trace_crosscut_in_return_disk hcut hgraph hinv hnc t w e
    hu hβ hBF (hRR₀.trans hR₀) hBR hq hqB (hDD₀.trans hD₀P) (hDD₀.trans hD₀loc)
    (fun d hd => (hother d hd).mono_left hDD₀) hdirty

end DifferentialGeometry.Topology.PiecewiseLinear
