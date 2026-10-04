import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderTangent
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The order-`k` manifold structure of a finite-order slice (W-SUB input adapter, lane CMS3-SLICE G1)

For `S` with `IsEmbeddedSliceOfOrder I k d S` (`E` finite-dimensional), the slice charts give the
subtype `S` a charted space modelled on `Fin d → ℝ` (`embeddedSliceChartedSpaceOfOrder`, chart at `p`:
`q ↦ e (π (c q - c p))` with `c` the chosen slice chart at `p`, `π` a projection onto the direction of
the affine subspace and `e` a linear equivalence onto `Fin d → ℝ`). It is a `C^k` manifold
(`embeddedSliceOfOrder_isManifold`), the inclusion is `C^k` (`contMDiff_val_ofOrder`), a map into `S`
is `C^m` (`m ≤ k`) as soon as its composite with the inclusion is
(`contMDiffAt_of_contMDiffAt_val_ofOrder`, `contMDiff_corestrict_ofOrder`), and for `k ≠ 0` the
differential of the inclusion has range `sliceTangent I S p` (`range_mfderiv_val_ofOrder`).

This is the input side of the W-SUB adapter: W-SUB's kernel takes an abstract compact `T2` type `S`
with `[ChartedSpace HS S]` (here `HS = Fin d → ℝ`, `IS = 𝓘(ℝ, Fin d → ℝ)`) and a tube; the tube itself
is built by lane CMS3-FLOW. Port of the smooth `Soul/EmbeddedSliceManifold.lean`.
-/

set_option autoImplicit false

noncomputable section

open Filter Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : WithTop ℕ∞} {S : Set M} {d : ℕ}

/-- The data of one chosen slice chart at a point of `S`. -/
private structure SliceChartDataOfOrder (k : WithTop ℕ∞) (d : ℕ) (p : S) where
  chart : PartialDiffeomorph I 𝓘(ℝ, E) M E k
  plane : AffineSubspace ℝ E
  mem_source : p.1 ∈ chart.source
  finrank_direction : Module.finrank ℝ plane.direction = d
  isImage : chart.toPartialEquiv.IsImage S (plane : Set E)

private def sliceChartDataOfOrder (hS : IsEmbeddedSliceOfOrder I k d S) (p : S) :
    SliceChartDataOfOrder (I := I) k d p := by
  have h : Nonempty (SliceChartDataOfOrder (I := I) k d p) := by
    obtain ⟨c, A, -, hp, hdim, himage⟩ := hS p.1 p.2
    exact ⟨⟨c, A, hp, hdim, himage⟩⟩
  exact Classical.choice h

namespace SliceChartDataOfOrder

variable {p : S} (D : SliceChartDataOfOrder (I := I) k d p)

private def proj : E →L[ℝ] D.plane.direction := by
  let K := D.plane.direction
  let K' := Classical.choose K.exists_isCompl
  have hK' : IsCompl K K' := Classical.choose_spec K.exists_isCompl
  exact ⟨K.projectionOnto K' hK', (K.projectionOnto K' hK').continuous_of_finiteDimensional⟩

private theorem proj_apply (v : E) (hv : v ∈ D.plane.direction) : D.proj v = ⟨v, hv⟩ :=
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
  simp only [subtypeInverse, dite_eq_left hz]

private theorem lift_contMDiff : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) k D.lift :=
  (D.plane.direction.subtypeL.contMDiff.comp D.equiv.symm.toContinuousLinearMap.contMDiff).add
    contMDiff_const

private theorem forward_contMDiffOn :
    ContMDiffOn I 𝓘(ℝ, Fin d → ℝ) k D.forward D.chart.source :=
  (D.equiv.toContinuousLinearMap.contMDiff.comp D.proj.contMDiff).comp_contMDiffOn
    (D.chart.contMDiffOn_toFun.sub contMDiffOn_const)

private theorem inverse_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I k D.inverse (D.lift ⁻¹' D.chart.target) :=
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
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I k (fun z => (D.toChart.symm z).1) D.toChart.target :=
  D.inverse_contMDiffOn.congr D.inverse_eqOn

end SliceChartDataOfOrder

/-- The chart of the order-`k` subtype structure at `p`. -/
def embeddedSliceChartOfOrder (hS : IsEmbeddedSliceOfOrder I k d S) (p : S) :
    OpenPartialHomeomorph S (Fin d → ℝ) :=
  (sliceChartDataOfOrder hS p).toChart

theorem mem_embeddedSliceChartOfOrder_source (hS : IsEmbeddedSliceOfOrder I k d S) (p : S) :
    p ∈ (embeddedSliceChartOfOrder hS p).source :=
  (sliceChartDataOfOrder hS p).mem_source

/-- Chart transitions of the subtype structure are `C^k`. -/
theorem embeddedSliceChartOfOrder_transition_contDiffOn (hS : IsEmbeddedSliceOfOrder I k d S)
    (p q : S) :
    ContDiffOn ℝ k ((embeddedSliceChartOfOrder hS p).symm ≫ₕ embeddedSliceChartOfOrder hS q)
      ((embeddedSliceChartOfOrder hS p).symm ≫ₕ embeddedSliceChartOfOrder hS q).source := by
  let D := sliceChartDataOfOrder hS p
  let D' := sliceChartDataOfOrder hS q
  intro z hz
  have hzt : z ∈ D.toChart.target := hz.1
  have hxs : (D.toChart.symm z).1 ∈ D'.chart.source := hz.2
  have hi := D.inverse_val_contMDiffOn.contMDiffAt (D.toChart.open_target.mem_nhds hzt)
  have hf := D'.forward_contMDiffOn.contMDiffAt (D'.chart.open_source.mem_nhds hxs)
  exact (contMDiffAt_iff_contDiffAt.mp (hf.comp z hi)).contDiffWithinAt

/-- **The order-`k` charted space on a finite-order slice**, modelled on `Fin d → ℝ`. -/
@[reducible] def embeddedSliceChartedSpaceOfOrder (hS : IsEmbeddedSliceOfOrder I k d S) :
    ChartedSpace (Fin d → ℝ) S where
  atlas := Set.range (embeddedSliceChartOfOrder hS)
  chartAt := embeddedSliceChartOfOrder hS
  mem_chart_source := mem_embeddedSliceChartOfOrder_source hS
  chart_mem_atlas p := ⟨p, rfl⟩

/-- **The subtype of a `C^k` slice is a `C^k` manifold.** -/
theorem embeddedSliceOfOrder_isManifold (hS : IsEmbeddedSliceOfOrder I k d S) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    IsManifold 𝓘(ℝ, Fin d → ℝ) k S := by
  let _ := embeddedSliceChartedSpaceOfOrder hS
  refine { toHasGroupoid := ?_ }
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid k 𝓘(ℝ, Fin d → ℝ)) ?_
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  change ContDiffOn ℝ k
    (𝓘(ℝ, Fin d → ℝ) ∘
      ((embeddedSliceChartOfOrder hS p).symm ≫ₕ embeddedSliceChartOfOrder hS q) ∘
      𝓘(ℝ, Fin d → ℝ).symm)
    (𝓘(ℝ, Fin d → ℝ).symm ⁻¹'
      ((embeddedSliceChartOfOrder hS p).symm ≫ₕ embeddedSliceChartOfOrder hS q).source ∩
      Set.range 𝓘(ℝ, Fin d → ℝ))
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id_eq, range_id, inter_univ]
  exact embeddedSliceChartOfOrder_transition_contDiffOn hS p q

/-- **The inclusion of a `C^k` slice is `C^k`.** -/
theorem contMDiff_val_ofOrder (hS : IsEmbeddedSliceOfOrder I k d S) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    ContMDiff 𝓘(ℝ, Fin d → ℝ) I k (Subtype.val : S → M) := by
  let _ := embeddedSliceChartedSpaceOfOrder hS
  change ContMDiff 𝓘(ℝ, Fin d → ℝ) I k (Subtype.val : S → M)
  intro p
  let D := sliceChartDataOfOrder hS p
  have hp : p ∈ D.toChart.source := D.mem_source
  have hi := D.inverse_val_contMDiffOn.contMDiffAt
    (D.toChart.open_target.mem_nhds (D.toChart.map_source hp))
  rw [contMDiffAt_iff_source, modelWithCornersSelf_coe, range_id]
  exact hi.contMDiffWithinAt

/-- **Maps into a `C^k` slice.** A map into the subtype is `C^m` at `x` (`m ≤ k`) as soon as its
composite with the inclusion is. -/
theorem contMDiffAt_of_contMDiffAt_val_ofOrder (hS : IsEmbeddedSliceOfOrder I k d S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {m : WithTop ℕ∞} (hm : m ≤ k)
    (f : X → S) {x : X} (hf : ContMDiffAt J I m (fun y => (f y : M)) x) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    ContMDiffAt J 𝓘(ℝ, Fin d → ℝ) m f x := by
  let _ := embeddedSliceChartedSpaceOfOrder hS
  change ContMDiffAt J 𝓘(ℝ, Fin d → ℝ) m f x
  let D := sliceChartDataOfOrder hS (f x)
  have hsm := (D.forward_contMDiffOn.contMDiffAt
    (D.chart.open_source.mem_nhds D.mem_source)).of_le hm
  rw [contMDiffAt_iff_target]
  refine ⟨_root_.Topology.IsInducing.subtypeVal.continuousAt_iff.2 hf.continuousAt, ?_⟩
  have h := ContMDiffAt.comp (f := fun y => (f y : M)) x hsm hf
  exact h

/-- A globally `C^m` map with values in a `C^k` slice (`m ≤ k`) corestricts to a `C^m` map. -/
theorem contMDiff_corestrict_ofOrder (hS : IsEmbeddedSliceOfOrder I k d S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {m : WithTop ℕ∞} (hm : m ≤ k)
    (f : X → M) (hf : ContMDiff J I m f) (hmem : ∀ x, f x ∈ S) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    ContMDiff J 𝓘(ℝ, Fin d → ℝ) m (fun x => (⟨f x, hmem x⟩ : S)) :=
  fun x => contMDiffAt_of_contMDiffAt_val_ofOrder hS hm (fun x => (⟨f x, hmem x⟩ : S)) (hf x)

/-- **The differential of the inclusion has range the tangent space of the slice** (`k ≠ 0`). -/
theorem range_mfderiv_val_ofOrder (hk : k ≠ 0) (hS : IsEmbeddedSliceOfOrder I k d S) (p : S) :
    let _ := embeddedSliceChartedSpaceOfOrder hS
    (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range = sliceTangent I S p.1 := by
  let _ := embeddedSliceChartedSpaceOfOrder hS
  let _ := embeddedSliceOfOrder_isManifold hS
  change (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range = sliceTangent I S p.1
  let D := sliceChartDataOfOrder hS p
  let L : (Fin d → ℝ) →L[ℝ] E :=
    D.plane.direction.subtypeL.comp D.equiv.symm.toContinuousLinearMap
  let Dc := mfderiv I 𝓘(ℝ, E) D.chart p.1
  let Di := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
  have hi : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p :=
    (contMDiff_val_ofOrder hS p).mdifferentiableAt hk
  have hc : MDifferentiableAt I 𝓘(ℝ, E) D.chart p.1 := D.chart.mdifferentiableAt hk D.mem_source
  have hf : MDifferentiableAt I 𝓘(ℝ, Fin d → ℝ) D.forward p.1 :=
    (D.forward_contMDiffOn.contMDiffAt
      (D.chart.open_source.mem_nhds D.mem_source)).mdifferentiableAt hk
  have hα : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
      (fun q : S => D.forward q.1) p = ContinuousLinearMap.id ℝ (Fin d → ℝ) := by
    change mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
      (extChartAt 𝓘(ℝ, Fin d → ℝ) p) p = _
    have : IsManifold 𝓘(ℝ, Fin d → ℝ) 1 S := IsManifold.of_le (n := k) (ENat.one_le_iff_ne_zero_withTop.2 hk)
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
      mfderiv_comp p (D.lift_contMDiff.mdifferentiable hk _) (hf.comp p hi)
    have hderiv : mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
        (fun q : S => D.chart q.1) p =
        mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E)
          (fun q : S => D.lift (D.forward q.1)) p := heq.mfderiv_eq
    rw [hco, hcl, hl, hα] at hderiv
    ext v
    exact congrArg (fun f : (Fin d → ℝ) →L[ℝ] E => f v) hderiv
  have hDc : Function.Injective Dc :=
    (D.chart.isLocalDiffeomorphAt I 𝓘(ℝ, E) k D.mem_source
      |>.mfderivToContinuousLinearEquiv hk).injective
  rw [sliceTangent_eq_comap_ofOrder hk p.2
    (show FiniteDimensional ℝ D.plane.direction from inferInstance) D.mem_source D.isImage]
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

end DifferentialGeometry.Geometry.FiniteSoul
