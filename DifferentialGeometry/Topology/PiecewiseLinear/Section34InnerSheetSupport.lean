import DifferentialGeometry.Topology.PiecewiseLinear.Section34ContactSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeRims

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

theorem exists_section34_inner_sheet_support
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {D : Set M₂} (hD : IsCompact D) (hDT : D ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e)) :
    ∃ O : Set M₂, IsOpen O ∧ IsCompact (closure O) ∧ D ⊆ O ∧
      closure O ⊆ interior (Tp e) ∩ G (ends e).2 '' interior (Sn e) ∧
      closure O ⊆ interior (Sp e) ∩ interior (Q (ends e).1) ∩ interior (Q (ends e).2) ∧
      Disjoint (closure O) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint (closure O) (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      ∀ d, d ≠ e → ((ends e).2 = (ends d).1 ∨ (ends e).2 = (ends d).2) →
        Disjoint (closure O) (G (ends e).2 '' Sn d) := by
  have hTp := section34_inner_tube_isCompact hprep hpack e
  have hTS := section34_inner_tube_subset_interior_outer hprep hpack e
  have hArim := section34_first_rims_subset_inner_frontier hprep hpack e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSnCc, hSnDis, -, -, -, hBbSn, -⟩ :=
    hprep
  obtain ⟨hG, hQ, hcross, -, -, -, -, -, hBrim, -⟩ := hpack
  let b := (ends e).2
  have hSn : interior (Sn e) ⊆ Cc b :=
    interior_subset.trans (hSnCc e b (Or.inr rfl))
  have hGB : IsOpen (G b '' interior (Sn e)) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      ((hG b).continuousOn.mono hSn) ((hG b).injOn.mono hSn)
  have hQa : G b '' interior (Sn e) ⊆ interior (Q (ends e).1) :=
    interior_maximal ((image_mono interior_subset).trans (hcross e).1) hGB
  have hQb : G b '' interior (Sn e) ⊆ interior (Q b) :=
    interior_maximal ((image_mono hSn).trans (hQ b)) hGB
  let V := interior (Tp e) ∩ G b '' interior (Sn e)
  have hV : IsOpen V := isOpen_interior.inter hGB
  have hDV : D ⊆ V := fun x hx =>
    ⟨(hDT hx).2, image_mono (hBbSn e).1 (hDT hx).1⟩
  obtain ⟨O, hO, hDO, hOV⟩ := hD.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hDV)
  refine ⟨O, hO, hTp.of_isClosed_subset isClosed_closure
    (fun x hx => interior_subset (hOV hx).1), hDO, hOV, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨hTS (interior_subset (hOV hx).1), hQa (hOV hx).2⟩, hQb (hOV hx).2⟩
  · exact disjoint_left.mpr fun x hx hxA => (hArim hxA).2 (hOV hx).1
  · exact disjoint_left.mpr fun x hx hxB =>
      disjoint_left.mp (hBrim e).2 hxB (interior_subset (hOV hx).1)
  · intro d hd hdb
    apply disjoint_left.mpr
    rintro x hx ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hzx⟩ := (hOV hx).2
    have hyz := (hG b).injOn (hSnCc d b hdb hy) (hSn hz) (hyx.trans hzx.symm)
    exact disjoint_left.mp (hSnDis e d hd.symm) (hyz ▸ interior_subset hz) hy

end DifferentialGeometry.Topology.PiecewiseLinear
