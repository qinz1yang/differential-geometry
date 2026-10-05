import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChart
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# Compact one-dimensional subsets with half-line graph charts (lane B-BCF134; shared `K₃` kernel)

Review 74, D74-9 (shared kernel `exists_compact_oneManifold_choice74`, package K0): a subset `T` of a
normed space `H` lying in a one-dimensional base `Bs` and described near each of its points by a
smooth HALF-LINE GRAPH CHART is a smooth one-manifold with boundary modelled on `EuclideanHalfSpace 1`.

* `HalfChart_BCF Bs T`: a continuous linear `L : H →L[ℝ] ℝ`, an offset `κ`, a map `π : ℝ → H` smooth on
  an open `W ⊆ ℝ` with `L (π t) + κ = t` on `W`, `π '' W ⊆ Bs` relatively open, and an open `O ⊆ H`
  with `T ∩ O = π '' (V ∩ [0, ∞))` for an open `V ⊆ W`;
* `HalfChart_BCF.toChart`: the chart `z ↦ L z + κ` of `T` with values in the half-line;
* `HalfChartCover_BCF Bs T`: a half chart at every point; `HalfChartCover_BCF.chartedSpace_BCF` (a definition
  of `↥T`) carries the charted space structure, `IsManifold (𝓡∂ 1) ∞`;
* `HalfChartCover_BCF.isInteriorPoint_iff_BCF`: a point is an interior point of the manifold iff it lies
  in the relative interior of `T` in `Bs`;
* `HalfChartCover_BCF.contMDiff_incl_BCF`, `HalfChartCover_BCF.mfderiv_incl_injective_BCF`: the
  inclusion into `H` is smooth with injective differential.

Relative interiors are written `Subtype.val '' interior (Subtype.val ⁻¹' Z : Set Bs)`.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Topology.Manifold.OneManifold

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A half-line graph chart** of `T ⊆ Bs ⊆ H`: the affine coordinate `z ↦ L z + κ` inverts the smooth
map `π` on the open parameter set `W`, `π '' W` is relatively open in `Bs`, and `T` meets the open set
`O` exactly in `π '' (V ∩ [0, ∞))` for an open `V ⊆ W`. -/
structure HalfChart_BCF (Bs T : Set H) where
  /-- The linear part of the coordinate. -/
  L : H →L[ℝ] ℝ
  /-- The offset of the coordinate. -/
  κ : ℝ
  /-- The parametrization. -/
  π : ℝ → H
  /-- The open parameter domain of `π`. -/
  W : Set ℝ
  /-- The open set of chart parameters (its nonnegative part is used). -/
  V : Set ℝ
  /-- The open set of `H` cut out by the chart. -/
  O : Set H
  isOpen_W : IsOpen W
  isOpen_V : IsOpen V
  V_subset : V ⊆ W
  smooth : ContDiffOn ℝ ∞ π W
  coord : ∀ t ∈ W, L (π t) + κ = t
  mem : ∀ t ∈ W, π t ∈ Bs
  relOpen : ∃ G : Set H, IsOpen G ∧ G ∩ Bs = π '' W
  isOpen_O : IsOpen O
  inter_eq : T ∩ O = π '' (V ∩ Ici 0)

namespace HalfChart_BCF

variable {Bs T : Set H} (d : HalfChart_BCF Bs T)

/-- A point of `T ∩ O` is `π t` for its coordinate `t ∈ V ∩ [0, ∞)`. -/
theorem exists_param_BCF {z : H} (hzT : z ∈ T) (hzO : z ∈ d.O) :
    d.L z + d.κ ∈ d.V ∩ Ici 0 ∧ d.π (d.L z + d.κ) = z := by
  have hz : z ∈ d.π '' (d.V ∩ Ici 0) := d.inter_eq ▸ ⟨hzT, hzO⟩
  obtain ⟨t, ht, rfl⟩ := hz
  rw [d.coord t (d.V_subset ht.1)]
  exact ⟨ht, rfl⟩

/-- The coordinate of a chart point is nonnegative. -/
theorem coord_nonneg_BCF {z : H} (hzT : z ∈ T) (hzO : z ∈ d.O) : 0 ≤ d.L z + d.κ :=
  (d.exists_param_BCF hzT hzO).1.2

/-- `T ∩ O ⊆ Bs`. -/
theorem mem_base_BCF {z : H} (hzT : z ∈ T) (hzO : z ∈ d.O) : z ∈ Bs := by
  obtain ⟨ht, hz⟩ := d.exists_param_BCF hzT hzO
  rw [← hz]
  exact d.mem _ (d.V_subset ht.1)

/-- `π` is continuous on `W`. -/
theorem continuousOn_π_BCF : ContinuousOn d.π d.W := d.smooth.continuousOn

/-- `π` is injective on `W`. -/
theorem injOn_π_BCF : InjOn d.π d.W := fun s hs t ht hst => by
  rw [← d.coord s hs, ← d.coord t ht, hst]

open scoped Classical in
/-- The inverse of the chart: `π` of the coordinate when it lies in `T`, else the base point `y₀`. -/
def invF (y₀ : T) (x : EuclideanHalfSpace 1) : T :=
  if h : d.π (x.val 0) ∈ T then ⟨d.π (x.val 0), h⟩ else y₀

theorem invF_val (y₀ : T) {x : EuclideanHalfSpace 1} (h : d.π (x.val 0) ∈ T) :
    ((d.invF y₀ x : T) : H) = d.π (x.val 0) := by
  unfold invF
  rw [dite_eq_left h]

/-- A target parameter is sent by `π` into `T ∩ O`. -/
theorem π_mem_of_target_BCF {x : EuclideanHalfSpace 1} (hx : x.val 0 ∈ d.V) :
    d.π (x.val 0) ∈ T ∩ d.O :=
  d.inter_eq ▸ ⟨x.val 0, ⟨hx, x.2⟩, rfl⟩

/-- **The chart** of `T` defined by the half chart `d` (`y₀` is the default value of the inverse off
the target). -/
def toChart (y₀ : T) : OpenPartialHomeomorph T (EuclideanHalfSpace 1) where
  toFun z := halfPt (d.L z + d.κ)
  invFun := d.invF y₀
  source := Subtype.val ⁻¹' d.O
  target := {x | x.val 0 ∈ d.V}
  map_source' := by
    intro z hz
    have h := d.exists_param_BCF z.2 hz
    change (halfPt (d.L z + d.κ)).val 0 ∈ d.V
    rw [halfPt_val_zero_of_nonneg h.1.2]
    exact h.1.1
  map_target' := by
    intro x hx
    have hmem := d.π_mem_of_target_BCF hx
    change ((d.invF y₀ x : T) : H) ∈ d.O
    rw [d.invF_val y₀ hmem.1]
    exact hmem.2
  left_inv' := by
    intro z hz
    have h := d.exists_param_BCF z.2 hz
    have hv : (halfPt (d.L z + d.κ)).val 0 = d.L z + d.κ := halfPt_val_zero_of_nonneg h.1.2
    apply Subtype.ext
    rw [d.invF_val y₀ (by rw [hv, h.2]; exact z.2), hv, h.2]
  right_inv' := by
    intro x hx
    have hmem := d.π_mem_of_target_BCF hx
    change halfPt (d.L ((d.invF y₀ x : T) : H) + d.κ) = x
    rw [d.invF_val y₀ hmem.1, d.coord _ (d.V_subset hx)]
    exact halfPt_coord x
  open_source := d.isOpen_O.preimage continuous_subtype_val
  open_target := d.isOpen_V.preimage continuous_coord
  continuousOn_toFun :=
    (continuous_halfPt.comp ((d.L.continuous.comp continuous_subtype_val).add
      continuous_const)).continuousOn
  continuousOn_invFun := by
    refine Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff.mpr ?_
    have hc : ContinuousOn (fun x : EuclideanHalfSpace 1 => d.π (x.val 0)) {x | x.val 0 ∈ d.V} :=
      d.continuousOn_π_BCF.comp continuous_coord.continuousOn fun x hx => d.V_subset hx
    refine hc.congr fun x hx => ?_
    exact d.invF_val y₀ (d.π_mem_of_target_BCF hx).1

@[simp] theorem toChart_apply (y₀ : T) (z : T) :
    d.toChart y₀ z = halfPt (d.L z + d.κ) := rfl

theorem toChart_source (y₀ : T) :
    (d.toChart y₀).source = Subtype.val ⁻¹' d.O := rfl

theorem toChart_target (y₀ : T) :
    (d.toChart y₀).target = {x | x.val 0 ∈ d.V} := rfl

/-- The inverse chart on the target is `π` of the coordinate. -/
theorem toChart_symm_apply_val (y₀ : T) {x : EuclideanHalfSpace 1}
    (hx : x ∈ (d.toChart y₀).target) : (((d.toChart y₀).symm x : T) : H) = d.π (x.val 0) :=
  d.invF_val y₀ (d.π_mem_of_target_BCF hx).1

/-- A chart point with positive coordinate lies in the relative interior of `T` in `Bs`. -/
theorem mem_relInterior_of_pos_BCF {z : H} (hzT : z ∈ T) (hzO : z ∈ d.O)
    (hpos : 0 < d.L z + d.κ) :
    z ∈ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
  obtain ⟨ht, hz⟩ := d.exists_param_BCF hzT hzO
  obtain ⟨G, hG, hGB⟩ := d.relOpen
  set J : Set ℝ := d.V ∩ Ioi 0 with hJ
  refine mem_image_interior_preimage_val_iff.mpr ⟨d.mem_base_BCF hzT hzO,
    G ∩ (fun w => d.L w + d.κ) ⁻¹' J,
    hG.inter ((d.isOpen_V.inter isOpen_Ioi).preimage (d.L.continuous.add continuous_const)),
    ⟨?_, ht.1, hpos⟩, ?_⟩
  · have : z ∈ G ∩ Bs := hGB ▸ ⟨_, d.V_subset ht.1, hz⟩
    exact this.1
  · rintro w ⟨⟨hwG, hwJ⟩, hwB⟩
    obtain ⟨s, hs, rfl⟩ : w ∈ d.π '' d.W := hGB ▸ ⟨hwG, hwB⟩
    have hcs : d.L (d.π s) + d.κ = s := d.coord s hs
    have hsJ : s ∈ J := hcs ▸ hwJ
    have : d.π s ∈ T ∩ d.O := d.inter_eq ▸ ⟨s, ⟨hsJ.1, mem_Ici.mpr (le_of_lt hsJ.2)⟩, rfl⟩
    exact this.1

/-- A chart point with coordinate `0` is not in the relative interior of `T` in `Bs`. -/
theorem not_mem_relInterior_of_eq_zero_BCF {z : H} (hzT : z ∈ T) (hzO : z ∈ d.O)
    (hzero : d.L z + d.κ = 0) :
    z ∉ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
  intro hz
  obtain ⟨-, G, hG, hzG, hGT⟩ := mem_image_interior_preimage_val_iff.mp hz
  obtain ⟨ht, hπ⟩ := d.exists_param_BCF hzT hzO
  rw [hzero] at ht hπ
  have hW : d.W ∈ 𝓝 (0 : ℝ) := d.isOpen_W.mem_nhds (d.V_subset ht.1)
  have hcont : ContinuousAt d.π 0 := d.continuousOn_π_BCF.continuousAt hW
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), d.π s ∈ G ∩ d.O :=
    hcont.preimage_mem_nhds ((hG.inter d.isOpen_O).mem_nhds (hπ ▸ ⟨hzG, hzO⟩))
  have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ d.W := hW
  have hev : ∀ᶠ s in 𝓝[<] (0 : ℝ), (d.π s ∈ G ∩ d.O ∧ s ∈ d.W) ∧ s < 0 :=
    ((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, ⟨hsGO, hsW⟩, hs0⟩ := hev.exists
  have hsT : d.π s ∈ T := hGT ⟨hsGO.1, d.mem s hsW⟩
  obtain ⟨r, hr, hrs⟩ : d.π s ∈ d.π '' (d.V ∩ Ici 0) := d.inter_eq ▸ ⟨hsT, hsGO.2⟩
  have : r = s := d.injOn_π_BCF (d.V_subset hr.1) hsW hrs
  exact absurd (this ▸ hr.2 : (0 : ℝ) ≤ s) (not_le.mpr hs0)

/-- For a point of the model range, `(𝓡∂ 1).symm` does not change the underlying vector. -/
theorem val_symm_of_mem_range_BCF {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ range (𝓡∂ 1)) :
    ((𝓡∂ 1).symm x).val = x := by
  obtain ⟨p, rfl⟩ := hx
  rw [ModelWithCorners.left_inv]
  rfl

/-- `x ↦ π (x 0)` is smooth on `{x | x 0 ∈ W}`. -/
theorem contDiffOn_π_comp_BCF :
    ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1) => d.π (x 0)) {x | x 0 ∈ d.W} :=
  d.smooth.comp (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff.contDiffOn
    fun _ hx => hx

/-- **Smooth coordinate changes** between two half charts (in the model `𝓡∂ 1`). -/
theorem contDiffOn_transition_BCF (d' : HalfChart_BCF Bs T) (y₀ y₀' : T) :
    ContDiffOn ℝ ∞ ((𝓡∂ 1) ∘ ((d.toChart y₀).symm ≫ₕ d'.toChart y₀') ∘ (𝓡∂ 1).symm)
      ((𝓡∂ 1).symm ⁻¹' ((d.toChart y₀).symm ≫ₕ d'.toChart y₀').source ∩ range (𝓡∂ 1)) := by
  have hsingle : ContDiff ℝ ∞ (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) := by
    have h : (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) =
        fun r => r • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      funext r
      ext i
      fin_cases i
      simp
    rw [h]
    exact contDiff_id.smul contDiff_const
  have hg : ContDiffOn ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 1) => EuclideanSpace.single (0 : Fin 1) (d'.L (d.π (x 0)) + d'.κ))
      {x | x 0 ∈ d.W} :=
    hsingle.comp_contDiffOn ((d'.L.contDiff.comp_contDiffOn d.contDiffOn_π_comp_BCF).add
      contDiffOn_const)
  refine (hg.mono ?_).congr ?_
  · rintro x ⟨hx, hxr⟩
    have h1 : ((𝓡∂ 1).symm x).val 0 ∈ d.V := hx.1
    rw [val_symm_of_mem_range_BCF hxr] at h1
    exact d.V_subset h1
  · rintro x ⟨hx, hxr⟩
    have hval := val_symm_of_mem_range_BCF hxr
    have htgt : (𝓡∂ 1).symm x ∈ (d.toChart y₀).target := hx.1
    have hz := d.toChart_symm_apply_val y₀ htgt
    rw [hval] at hz
    have hzO : (((d.toChart y₀).symm ((𝓡∂ 1).symm x) : T) : H) ∈ d'.O := hx.2
    have hnn := d'.coord_nonneg_BCF ((d.toChart y₀).symm ((𝓡∂ 1).symm x)).2 hzO
    rw [hz] at hnn
    change (𝓡∂ 1) (halfPt (d'.L (((d.toChart y₀).symm ((𝓡∂ 1).symm x) : T) : H) + d'.κ)) = _
    rw [hz, model_halfPt hnn]

/-- The coordinate of a chart point read off from the chart. -/
theorem toChart_val_zero_BCF (y₀ : T) {z : T} (hz : (z : H) ∈ d.O) :
    (d.toChart y₀ z).val 0 = d.L z + d.κ :=
  halfPt_val_zero_of_nonneg (d.coord_nonneg_BCF z.2 hz)

end HalfChart_BCF

/-- **A half-chart cover of `T`**: a half chart at every point of `T`. -/
structure HalfChartCover_BCF (Bs T : Set H) where
  /-- The half chart chosen at a point. -/
  chart : T → HalfChart_BCF Bs T
  mem : ∀ y : T, (y : H) ∈ (chart y).O

namespace HalfChartCover_BCF

variable {Bs T : Set H} (A : HalfChartCover_BCF Bs T)

/-- `T ⊆ Bs`. -/
theorem subset_base_BCF (A : HalfChartCover_BCF Bs T) : T ⊆ Bs := fun y hy =>
  (A.chart ⟨y, hy⟩).mem_base_BCF hy (A.mem ⟨y, hy⟩)

/-- **The charted space of a half-chart cover** (a definition, not an instance: the structure depends
on `A`; the lemmas below take any charted space on `↥T` whose atlas consists of half charts). -/
abbrev chartedSpace_BCF : ChartedSpace (EuclideanHalfSpace 1) T where
  atlas := range fun y : T => (A.chart y).toChart y
  chartAt y := (A.chart y).toChart y
  mem_chart_source y := A.mem y
  chart_mem_atlas y := ⟨y, rfl⟩

/-- Every chart of `chartedSpace_BCF` is a half chart. -/
theorem mem_atlas_BCF :
    letI := A.chartedSpace_BCF
    ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ (d : HalfChart_BCF Bs T) (y₀ : T), e = d.toChart y₀ := by
  rintro e ⟨y, rfl⟩
  exact ⟨A.chart y, y, rfl⟩


end HalfChartCover_BCF

section Atlas

variable {Bs T : Set H} [ChartedSpace (EuclideanHalfSpace 1) T]

/-- **A charted space on `↥T` whose atlas consists of half charts is a smooth manifold.** -/
theorem isManifold_of_halfCharts_BCF
    (hA : ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ (d : HalfChart_BCF Bs T) (y₀ : T),
      e = d.toChart y₀) :
    IsManifold (𝓡∂ 1) ∞ T := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨d, y₀, rfl⟩ := hA e he
  obtain ⟨d', y₀', rfl⟩ := hA e' he'
  exact d.contDiffOn_transition_BCF d' y₀ y₀'

/-- **The inclusion in a chart**: near `extChartAt y y`, `val ∘ (extChartAt y).symm` is `x ↦ π (x 0)`
for the half chart `d` of `chartAt y`. -/
theorem val_comp_extChartAt_symm_BCF {d : HalfChart_BCF Bs T} {y₀ y : T}
    (he : chartAt (EuclideanHalfSpace 1) y = d.toChart y₀) :
    (fun x => (((extChartAt (𝓡∂ 1) y).symm x : T) : H)) =ᶠ[𝓝[range (𝓡∂ 1)] (extChartAt (𝓡∂ 1) y y)]
      fun x => d.π (x 0) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡∂ 1) y] with x hx
  rw [extChartAt_target] at hx
  have hval := HalfChart_BCF.val_symm_of_mem_range_BCF hx.2
  have htgt : (𝓡∂ 1).symm x ∈ (d.toChart y₀).target := by
    have h := hx.1
    rw [he] at h
    exact h
  rw [extChartAt_coe_symm, Function.comp_apply, he, d.toChart_symm_apply_val y₀ htgt, hval]

/-- The point `extChartAt y y` has first coordinate in `V`. -/
theorem extChartAt_self_mem_BCF {d : HalfChart_BCF Bs T} {y₀ y : T}
    (he : chartAt (EuclideanHalfSpace 1) y = d.toChart y₀) :
    (extChartAt (𝓡∂ 1) y y) 0 ∈ d.V ∧ d.π ((extChartAt (𝓡∂ 1) y y) 0) = y := by
  have hyO : (y : H) ∈ d.O := by
    have h := mem_chart_source (EuclideanHalfSpace 1) y
    rw [he] at h
    exact h
  have h0 : (extChartAt (𝓡∂ 1) y y) 0 = d.L y + d.κ := by
    rw [extChartAt_coe, Function.comp_apply, he]
    exact d.toChart_val_zero_BCF y₀ hyO
  rw [h0]
  exact ⟨(d.exists_param_BCF y.2 hyO).1.1, (d.exists_param_BCF y.2 hyO).2⟩

variable [IsManifold (𝓡∂ 1) ∞ T]

/-- **Interior points are the relative interior points**: a point of `T` is an interior point of the
manifold iff it lies in the relative interior of `T` in `Bs`. -/
theorem isInteriorPoint_iff_BCF
    (hA : ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ (d : HalfChart_BCF Bs T) (y₀ : T),
      e = d.toChart y₀) {y : T} :
    (𝓡∂ 1).IsInteriorPoint y ↔ (y : H) ∈ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
  obtain ⟨d, y₀, he⟩ := hA _ (chart_mem_atlas (EuclideanHalfSpace 1) y)
  have hyO : (y : H) ∈ d.O := by
    have h := mem_chart_source (EuclideanHalfSpace 1) y
    rw [he] at h
    exact h
  rw [isInteriorPoint_iff_coord_pos (chart_mem_atlas (EuclideanHalfSpace 1) y)
    (mem_chart_source (EuclideanHalfSpace 1) y), he, d.toChart_val_zero_BCF y₀ hyO]
  constructor
  · exact d.mem_relInterior_of_pos_BCF y.2 hyO
  · intro hy
    by_contra hle
    exact d.not_mem_relInterior_of_eq_zero_BCF y.2 hyO
      (le_antisymm (not_lt.mp hle) (d.coord_nonneg_BCF y.2 hyO)) hy

omit [IsManifold (𝓡∂ 1) ∞ T] in
/-- **The inclusion `↥T → H` is smooth.** -/
theorem contMDiff_val_BCF
    (hA : ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ (d : HalfChart_BCF Bs T) (y₀ : T),
      e = d.toChart y₀) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ (Subtype.val : T → H) := by
  intro y
  obtain ⟨d, y₀, he⟩ := hA _ (chart_mem_atlas (EuclideanHalfSpace 1) y)
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
  have hmem := (extChartAt_self_mem_BCF he).1
  have hg : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1) => d.π (x 0)) (extChartAt (𝓡∂ 1) y y) :=
    d.contDiffOn_π_comp_BCF.contDiffAt
      ((d.isOpen_W.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous).mem_nhds
        (d.V_subset hmem))
  exact hg.contDiffWithinAt.congr_of_eventuallyEq (val_comp_extChartAt_symm_BCF he)
    ((val_comp_extChartAt_symm_BCF he).self_of_nhdsWithin
      (extChartAt_target_subset_range y (mem_extChartAt_target y)))

omit [IsManifold (𝓡∂ 1) ∞ T] in
/-- **The differential of the inclusion `↥T → H` is injective.** -/
theorem mfderiv_val_injective_BCF
    (hA : ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ (d : HalfChart_BCF Bs T) (y₀ : T),
      e = d.toChart y₀) (y : T) :
    Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (Subtype.val : T → H) y) := by
  obtain ⟨d, y₀, he⟩ := hA _ (chart_mem_atlas (EuclideanHalfSpace 1) y)
  have hmem := (extChartAt_self_mem_BCF he).1
  set p₀ := extChartAt (𝓡∂ 1) y y with hp₀
  set c := p₀ 0 with hc
  have hW : d.W ∈ 𝓝 c := d.isOpen_W.mem_nhds (d.V_subset hmem)
  have hπd : HasDerivAt d.π (deriv d.π c) c :=
    ((d.smooth.contDiffAt hW).differentiableAt (by simp)).hasDerivAt
  have hL : d.L (deriv d.π c) = 1 := by
    have h1 : HasDerivAt (fun t => d.L (d.π t) + d.κ) (d.L (deriv d.π c)) c :=
      (d.L.hasFDerivAt.comp_hasDerivAt c hπd).add_const d.κ
    have h2 : HasDerivAt (fun t => d.L (d.π t) + d.κ) 1 c :=
      (hasDerivAt_id c).congr_of_eventuallyEq (by filter_upwards [hW] with t ht using d.coord t ht)
    exact h1.unique h2
  have hg : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 1) => d.π (x 0))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv d.π c)).comp
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) p₀ :=
    hπd.hasFDerivAt.comp p₀
      ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt (x := p₀))
  have hmd : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, H) (Subtype.val : T → H) y :=
    ((contMDiff_val_BCF hA) y).mdifferentiableAt (by simp)
  have hw : writtenInExtChartAt (𝓡∂ 1) 𝓘(ℝ, H) y (Subtype.val : T → H) =ᶠ[𝓝[range (𝓡∂ 1)] p₀]
      fun x => d.π (x 0) := by
    unfold writtenInExtChartAt
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
    exact val_comp_extChartAt_symm_BCF he
  have hp₀r : p₀ ∈ range (𝓡∂ 1) := extChartAt_target_subset_range y (mem_extChartAt_target y)
  have hfd : mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (Subtype.val : T → H) y =
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv d.π c)).comp
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) := by
    rw [hmd.mfderiv_abuse, hw.fderivWithin_eq (hw.self_of_nhdsWithin hp₀r)]
    obtain ⟨q, hq⟩ := hp₀r
    exact hg.hasFDerivWithinAt.fderivWithin (hq ▸ (𝓡∂ 1).uniqueDiffWithinAt_image)
  have hD : ∀ u : EuclideanSpace ℝ (Fin 1),
      d.L (((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv d.π c)).comp
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) u) = u 0 := by
    intro u
    change d.L ((u 0) • deriv d.π c) = u 0
    rw [map_smul, hL, smul_eq_mul, mul_one]
  intro v w hvw
  rw [hfd] at hvw
  have h' := congrArg d.L hvw
  let v' : EuclideanSpace ℝ (Fin 1) := v
  let w' : EuclideanSpace ℝ (Fin 1) := w
  have e : v' 0 = w' 0 := (hD v').symm.trans (h'.trans (hD w'))
  exact (val_eq_single v').trans ((congrArg _ e).trans (val_eq_single w').symm)

end Atlas

end DifferentialGeometry.Topology
