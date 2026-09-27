import DifferentialGeometry.Geometry.Comparison.Soul.SliceTangent
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Filter Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {S : Set M} {d : ℕ}

private structure SliceChartData (p : S) where
  chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞
  plane : AffineSubspace ℝ E
  mem_source : p.1 ∈ chart.source
  finrank_direction : Module.finrank ℝ plane.direction = d
  isImage : chart.toPartialEquiv.IsImage S (plane : Set E)

private def sliceChartData (hS : IsEmbeddedSlice I d S) (p : S) :
    SliceChartData (I := I) (d := d) p := by
  have h : Nonempty (SliceChartData (I := I) (d := d) p) := by
    obtain ⟨c, A, -, hp, hdim, himage⟩ := hS p.1 p.2
    exact ⟨⟨c, A, hp, hdim, himage⟩⟩
  exact Classical.choice h

namespace SliceChartData

variable {p : S} (D : SliceChartData (I := I) (d := d) p)

private def proj : E →L[ℝ] D.plane.direction := by
  let K := D.plane.direction
  let K' := Classical.choose K.exists_isCompl
  have hK' : IsCompl K K' := Classical.choose_spec K.exists_isCompl
  exact ⟨K.projectionOnto K' hK', (K.projectionOnto K' hK').continuous_of_finiteDimensional⟩

private theorem proj_apply (v : E) (hv : v ∈ D.plane.direction) :
    D.proj v = ⟨v, hv⟩ :=
  Submodule.projectionOnto_apply_of_mem_left
    (Classical.choose_spec D.plane.direction.exists_isCompl) hv

private def equiv : D.plane.direction ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simpa using D.finrank_direction)

private def forward (x : M) : Fin d → ℝ :=
  D.equiv (D.proj (D.chart x - D.chart p.1))

private def lift (z : Fin d → ℝ) : E := (D.equiv.symm z : E) + D.chart p.1

private def inverse (z : Fin d → ℝ) : M := D.chart.symm (D.lift z)

private theorem lift_forward (q : S) (hq : q.1 ∈ D.chart.source) :
    D.lift (D.forward q.1) = D.chart q.1 := by
  have hqA : D.chart q.1 ∈ D.plane := (D.isImage.apply_mem_iff hq).2 q.2
  have hpA : D.chart p.1 ∈ D.plane := (D.isImage.apply_mem_iff D.mem_source).2 p.2
  have hmem : D.chart q.1 - D.chart p.1 ∈ D.plane.direction :=
    D.plane.vsub_mem_direction hqA hpA
  change (D.equiv.symm (D.equiv (D.proj _)) : E) + D.chart p.1 = D.chart q.1
  rw [D.equiv.symm_apply_apply, D.proj_apply _ hmem]
  exact sub_add_cancel _ _

private theorem inverse_mem (z : Fin d → ℝ) (hz : D.lift z ∈ D.chart.target) :
    D.inverse z ∈ S := by
  apply (D.isImage.apply_mem_iff (D.chart.map_target hz)).1
  change D.chart (D.chart.symm (D.lift z)) ∈ D.plane
  have hright : D.chart (D.chart.symm (D.lift z)) = D.lift z := D.chart.right_inv hz
  rw [hright]
  exact D.plane.vadd_mem_of_mem_direction (D.equiv.symm z).2
    ((D.isImage.apply_mem_iff D.mem_source).2 p.2)

private def subtypeInverse (z : Fin d → ℝ) : S := by
  classical
  exact if hz : D.lift z ∈ D.chart.target then ⟨D.inverse z, D.inverse_mem z hz⟩ else p

private theorem subtypeInverse_val (z : Fin d → ℝ) (hz : D.lift z ∈ D.chart.target) :
    (D.subtypeInverse z).1 = D.inverse z := by
  simp only [subtypeInverse, dif_pos hz]

private theorem lift_contMDiff : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) ∞ D.lift :=
  (D.plane.direction.subtypeL.contMDiff.comp D.equiv.symm.toContinuousLinearMap.contMDiff).add
    contMDiff_const

private theorem forward_contMDiffOn :
    ContMDiffOn I 𝓘(ℝ, Fin d → ℝ) ∞ D.forward D.chart.source :=
  (D.equiv.toContinuousLinearMap.contMDiff.comp D.proj.contMDiff).comp_contMDiffOn
    (D.chart.contMDiffOn_toFun.sub contMDiffOn_const)

private theorem inverse_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I ∞ D.inverse (D.lift ⁻¹' D.chart.target) :=
  D.chart.contMDiffOn_invFun.comp D.lift_contMDiff.contMDiffOn (fun _ hz => hz)

private def toChart : OpenPartialHomeomorph S (Fin d → ℝ) where
  toFun q := D.forward q.1
  invFun := D.subtypeInverse
  source := {q | q.1 ∈ D.chart.source}
  target := D.lift ⁻¹' D.chart.target
  map_source' q hq := by
    change D.lift (D.forward q.1) ∈ D.chart.target
    rw [D.lift_forward q hq]
    exact D.chart.map_source hq
  map_target' z hz := by
    change (D.subtypeInverse z).1 ∈ D.chart.source
    rw [D.subtypeInverse_val z hz]
    exact D.chart.map_target hz
  left_inv' q hq := by
    apply Subtype.ext
    have ht : D.lift (D.forward q.1) ∈ D.chart.target := by
      rw [D.lift_forward q hq]
      exact D.chart.map_source hq
    rw [D.subtypeInverse_val _ ht]
    change D.chart.symm (D.lift (D.forward q.1)) = q.1
    rw [D.lift_forward q hq]
    exact D.chart.left_inv hq
  right_inv' z hz := by
    rw [D.subtypeInverse_val z hz]
    change D.equiv (D.proj (D.chart (D.chart.symm (D.lift z)) - D.chart p.1)) = z
    have hright : D.chart (D.chart.symm (D.lift z)) = D.lift z := D.chart.right_inv hz
    rw [hright]
    change D.equiv (D.proj (((D.equiv.symm z : E) + D.chart p.1) - D.chart p.1)) = z
    rw [add_sub_cancel_right, D.proj_apply _ (D.equiv.symm z).2]
    exact D.equiv.apply_symm_apply z
  open_source := D.chart.open_source.preimage continuous_subtype_val
  open_target := D.chart.open_target.preimage D.lift_contMDiff.continuous
  continuousOn_toFun := D.forward_contMDiffOn.continuousOn.comp
    continuous_subtype_val.continuousOn (fun _ hq => hq)
  continuousOn_invFun := by
    apply _root_.Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact D.inverse_contMDiffOn.continuousOn.congr
      (fun z hz => D.subtypeInverse_val z hz)

private theorem inverse_eqOn :
    EqOn (fun z => (D.toChart.symm z).1) D.inverse D.toChart.target :=
  fun z hz => D.subtypeInverse_val z hz

private theorem inverse_val_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I ∞
      (fun z => (D.toChart.symm z).1) D.toChart.target :=
  D.inverse_contMDiffOn.congr D.inverse_eqOn

end SliceChartData

def embeddedSliceChart (hS : IsEmbeddedSlice I d S) (p : S) :
    OpenPartialHomeomorph S (Fin d → ℝ) :=
  (sliceChartData hS p).toChart


theorem mem_embeddedSliceChart_source (hS : IsEmbeddedSlice I d S) (p : S) :
    p ∈ (embeddedSliceChart hS p).source :=
  (sliceChartData hS p).mem_source

theorem embeddedSliceChart_transition_contDiffOn
    (hS : IsEmbeddedSlice I d S) (p q : S) :
    ContDiffOn ℝ ∞ ((embeddedSliceChart hS p).symm ≫ₕ embeddedSliceChart hS q)
      ((embeddedSliceChart hS p).symm ≫ₕ embeddedSliceChart hS q).source := by
  let D := sliceChartData hS p
  let D' := sliceChartData hS q
  intro z hz
  have hzt : z ∈ D.toChart.target := hz.1
  have hxs : (D.toChart.symm z).1 ∈ D'.chart.source := hz.2
  have hi := D.inverse_val_contMDiffOn.contMDiffAt (D.toChart.open_target.mem_nhds hzt)
  have hf := D'.forward_contMDiffOn.contMDiffAt (D'.chart.open_source.mem_nhds hxs)
  exact (contMDiffAt_iff_contDiffAt.mp (hf.comp z hi)).contDiffWithinAt

@[reducible] def embeddedSliceChartedSpace (hS : IsEmbeddedSlice I d S) :
    ChartedSpace (Fin d → ℝ) S where
  atlas := Set.range (embeddedSliceChart hS)
  chartAt := embeddedSliceChart hS
  mem_chart_source := mem_embeddedSliceChart_source hS
  chart_mem_atlas p := ⟨p, rfl⟩

theorem embeddedSlice_isManifold (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ S := by
  let _ := embeddedSliceChartedSpace hS
  refine { toHasGroupoid := ?_ }
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid ∞ 𝓘(ℝ, Fin d → ℝ)) ?_
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  change ContDiffOn ℝ ∞
    (𝓘(ℝ, Fin d → ℝ) ∘
      ((embeddedSliceChart hS p).symm ≫ₕ embeddedSliceChart hS q) ∘
      𝓘(ℝ, Fin d → ℝ).symm)
    (𝓘(ℝ, Fin d → ℝ).symm ⁻¹'
      ((embeddedSliceChart hS p).symm ≫ₕ embeddedSliceChart hS q).source ∩
      Set.range 𝓘(ℝ, Fin d → ℝ))
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id_eq, range_id, inter_univ]
  exact embeddedSliceChart_transition_contDiffOn hS p q

theorem embeddedSlice_inclusion_contMDiff (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    ContMDiff 𝓘(ℝ, Fin d → ℝ) I ∞ (Subtype.val : S → M) := by
  let _ := embeddedSliceChartedSpace hS
  change ContMDiff 𝓘(ℝ, Fin d → ℝ) I ∞ (Subtype.val : S → M)
  intro p
  let D := sliceChartData hS p
  have hp : p ∈ D.toChart.source := D.mem_source
  have hi := D.inverse_val_contMDiffOn.contMDiffAt
    (D.toChart.open_target.mem_nhds (D.toChart.map_source hp))
  rw [contMDiffAt_iff_source, modelWithCornersSelf_coe, range_id]
  exact hi.contMDiffWithinAt

theorem embeddedSlice_corestrict_contMDiff (hS : IsEmbeddedSlice I d S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → M) (hf : ContMDiff J I ∞ f) (hmem : ∀ x, f x ∈ S) :
    let _ := embeddedSliceChartedSpace hS
    ContMDiff J 𝓘(ℝ, Fin d → ℝ) ∞ (fun x => (⟨f x, hmem x⟩ : S)) := by
  let _ := embeddedSliceChartedSpace hS
  change ContMDiff J 𝓘(ℝ, Fin d → ℝ) ∞ (fun x => (⟨f x, hmem x⟩ : S))
  intro x
  let p : S := ⟨f x, hmem x⟩
  let D := sliceChartData hS p
  have hsm := D.forward_contMDiffOn.contMDiffAt (D.chart.open_source.mem_nhds D.mem_source)
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk hmem).continuousAt, ?_⟩
  exact hsm.comp x (hf x)

theorem embeddedSlice_inclusion_range_mfderiv (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range =
      sliceTangent I S p.1 := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  change (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range =
    sliceTangent I S p.1
  let D := sliceChartData hS p
  let L : (Fin d → ℝ) →L[ℝ] E :=
    D.plane.direction.subtypeL.comp D.equiv.symm.toContinuousLinearMap
  let Dc := mfderiv I 𝓘(ℝ, E) D.chart p.1
  let Di := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
  have hi : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p :=
    (embeddedSlice_inclusion_contMDiff hS p).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt I 𝓘(ℝ, E) D.chart p.1 :=
    D.chart.mdifferentiableAt (by simp) D.mem_source
  have hf : MDifferentiableAt I 𝓘(ℝ, Fin d → ℝ) D.forward p.1 :=
    (D.forward_contMDiffOn.contMDiffAt
      (D.chart.open_source.mem_nhds D.mem_source)).mdifferentiableAt (by simp)
  have hα : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
      (fun q : S => D.forward q.1) p = ContinuousLinearMap.id ℝ (Fin d → ℝ) := by
    change mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
      (extChartAt 𝓘(ℝ, Fin d → ℝ) p) p = _
    exact mfderiv_extChartAt_self
  have hl : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) D.lift (D.forward p.1) = L := by
    rw [mfderiv_eq_fderiv]
    exact (L.hasFDerivAt.add_const (D.chart p.1)).fderiv
  have heq : (fun q : S => D.chart q.1) =ᶠ[𝓝 p]
      (fun q : S => D.lift (D.forward q.1)) := by
    filter_upwards [D.toChart.open_source.mem_nhds D.mem_source] with q hq
    exact (D.lift_forward q hq).symm
  have hprod : Dc.comp Di = L := by
    have hco : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
        (fun q : S => D.chart q.1) p = Dc.comp Di := mfderiv_comp p hc hi
    have hcl : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
        (fun q : S => D.lift (D.forward q.1)) p =
        (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) D.lift (D.forward p.1)).comp
          (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
            (fun q : S => D.forward q.1) p) :=
      mfderiv_comp p (D.lift_contMDiff.mdifferentiable (by simp) _) (hf.comp p hi)
    have hderiv : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
        (fun q : S => D.chart q.1) p =
        mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
          (fun q : S => D.lift (D.forward q.1)) p := heq.mfderiv_eq
    rw [hco, hcl, hl, hα] at hderiv
    ext v
    exact congrArg (fun f : (Fin d → ℝ) →L[ℝ] E => f v) hderiv
  have hDc : Function.Injective Dc :=
    (D.chart.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ D.mem_source
      |>.mfderivToContinuousLinearEquiv (by simp)).injective
  rw [sliceTangent_eq_comap p.2 (show FiniteDimensional ℝ D.plane.direction from inferInstance)
    D.mem_source D.isImage]
  ext v
  change (∃ w, Di w = v) ↔ Dc v ∈ D.plane.direction
  constructor
  · rintro ⟨w, rfl⟩
    have heval := congrArg (fun f : (Fin d → ℝ) →L[ℝ] E => f w) hprod
    change Dc (Di w) = L w at heval
    rw [heval]
    exact (D.equiv.symm w).2
  · intro hv
    let w : Fin d → ℝ := D.equiv ⟨Dc v, hv⟩
    refine ⟨w, hDc ?_⟩
    have heval := congrArg (fun f : (Fin d → ℝ) →L[ℝ] E => f w) hprod
    change Dc (Di w) = L w at heval
    rw [heval]
    change (D.equiv.symm (D.equiv ⟨Dc v, hv⟩) : E) = Dc v
    rw [D.equiv.symm_apply_apply]

end DifferentialGeometry.Geometry.Topology
