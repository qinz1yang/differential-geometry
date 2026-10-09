/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Measure

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology ContDiff

namespace DifferentialGeometry.BoundaryChartAction

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary BoundaryTopology
open MobiusBoundary Horospherical EuclideanBoundary GeodesicFlow BoundaryMeasure

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

def chartAction (g : IsometryGroup m) (x : Horizontal m) : Horizontal m :=
  coords (g • embed x)

def chartDomain (g : IsometryGroup m) : Set (Horizontal m) :=
  {x | g • embed x ≠ ptInfty}

theorem isOpen_chartDomain (g : IsometryGroup m) : IsOpen (chartDomain g) := by
  change IsOpen ((fun x : Horizontal m => g • embed x) ⁻¹' {ptInfty}ᶜ)
  exact isClosed_singleton.isOpen_compl.preimage
    ((continuous_const (y := g)).smul continuous_embed)

theorem embed_chartAction (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) : embed (chartAction g x) = g • embed x :=
  embed_coords hx

theorem chartAction_mul (g h : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain h) :
    chartAction g (chartAction h x) = chartAction (g * h) x := by
  simp only [chartAction, embed_coords hx, mul_smul]

theorem chartAction_one (x : Horizontal m) : chartAction (1 : IsometryGroup m) x = x := by
  simp [chartAction, coords_embed]

theorem chartAction_inv (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) : chartAction g⁻¹ (chartAction g x) = x := by
  rw [chartAction_mul _ _ hx, inv_mul_cancel, chartAction_one]

theorem chartAction_mem_inverseDomain (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) : chartAction g x ∈ chartDomain g⁻¹ := by
  change g⁻¹ • embed (chartAction g x) ≠ ptInfty
  rw [embed_chartAction g hx, inv_smul_smul]
  exact embed_ne_infty x

theorem measurable_coords : Measurable (coords : BoundaryH (m + 1) → Horizontal m) := by
  apply (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp
  apply Measurable.of_eval
  intro i
  exact (((continuous_apply _).comp isEmbedding_val.continuous).measurable).div
    (measurable_const.sub (((continuous_apply _).comp isEmbedding_val.continuous).measurable))

theorem measurable_chartAction (g : IsometryGroup m) : Measurable (chartAction g) :=
  measurable_coords.comp
    ((continuous_const (y := g)).smul continuous_embed).measurable

theorem measurePreserving_embed :
    MeasurePreserving (embed : Horizontal m → BoundaryH (m + 1)) volume (boundaryMeasure m) :=
  ⟨continuous_embed.measurable, rfl⟩

theorem measurePreserving_coords :
    MeasurePreserving (coords : BoundaryH (m + 1) → Horizontal m) (boundaryMeasure m) volume := by
  refine ⟨measurable_coords, ?_⟩
  rw [boundaryMeasure, Measure.map_map measurable_coords continuous_embed.measurable]
  have he : (coords : BoundaryH (m + 1) → Horizontal m) ∘ embed = id :=
    funext coords_embed
  rw [he, Measure.map_id]

def rawImage (A : LorGrp (m + 1)) (x : Horizontal m) : LorVec (m + 1) :=
  matOf A *ᵥ horoVec (fun i => x i)

def denominator (A : LorGrp (m + 1)) (x : Horizontal m) : ℝ :=
  vHeight (rawImage A x)

theorem rawImage_time_ne_zero (A : LorGrp (m + 1)) (x : Horizontal m) :
    tc (rawImage A x) ≠ 0 :=
  tc_matOf_mulVec_ne_zero_of_null A (lorB_horoVec_self _) (tc_horoVec_pos _).ne'

theorem action_mk_val (A : LorGrp (m + 1)) (x : Horizontal m) :
    ((QuotientGroup.mk' _ A : IsometryGroup m) • embed x).val = boundaryRep (rawImage A x) := by
  change boundaryRep (matOf A *ᵥ boundaryRep (horoVec (fun i => x i))) = _
  rw [show boundaryRep (horoVec (fun i => x i)) =
    (tc (horoVec (fun i => x i)))⁻¹ • horoVec (fun i => x i) from rfl, mulVec_smul]
  exact boundaryRep_smul _ (inv_ne_zero (tc_horoVec_pos _).ne')

theorem denominator_ne_zero_iff (A : LorGrp (m + 1)) (x : Horizontal m) :
    denominator A x ≠ 0 ↔ x ∈ chartDomain (QuotientGroup.mk' _ A) := by
  have hv : vHeight (((QuotientGroup.mk' _ A : IsometryGroup m) • embed x).val) =
      (tc (rawImage A x))⁻¹ * denominator A x := by
    rw [action_mk_val, boundaryRep, vHeight_smul]
    rfl
  have hi : ∀ v : BoundaryH (m + 1), vHeight v.val = 0 ↔ v = ptInfty := by
    intro v
    rw [vHeight, v.tc_eq, sub_eq_zero]
    constructor
    · intro h
      exact eq_ptInfty_of_axis_eq_one v h.symm
    · intro h
      rw [h, ptInfty_val_last]
  change denominator A x ≠ 0 ↔ (QuotientGroup.mk' _ A : IsometryGroup m) • embed x ≠ ptInfty
  have h := (hi ((QuotientGroup.mk' _ A : IsometryGroup m) • embed x)).not
  rw [hv, mul_eq_zero, or_iff_right (inv_ne_zero (rawImage_time_ne_zero A x))] at h
  exact h

theorem chartAction_mk_apply (A : LorGrp (m + 1)) (x : Horizontal m) (i : Fin m) :
    chartAction (QuotientGroup.mk' _ A) x i =
      rawImage A x (Sum.inl i.castSucc) / denominator A x := by
  change ((QuotientGroup.mk' _ A : IsometryGroup m) • embed x).val (Sum.inl i.castSucc) /
      (1 - ((QuotientGroup.mk' _ A : IsometryGroup m) • embed x).val (Sum.inl (Fin.last m))) = _
  rw [action_mk_val]
  simp only [boundaryRep, Pi.smul_apply, smul_eq_mul]
  have ht := rawImage_time_ne_zero A x
  have he : 1 - (tc (rawImage A x))⁻¹ * rawImage A x (Sum.inl (Fin.last m)) =
      (tc (rawImage A x))⁻¹ * denominator A x := by
    rw [denominator, vHeight]
    field_simp
  rw [he, mul_div_mul_left _ _ (inv_ne_zero ht)]

theorem contDiff_horoVec (k : ℕ∞ω) :
    ContDiff ℝ k (fun x : Horizontal m => horoVec (fun i => x i)) := by
  apply contDiff_pi.mpr
  intro i
  rcases i with j | j
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [horoVec_last, normSq]
      fun_prop
    · simp only [horoVec_castSucc]
      exact (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [horoVec_time, normSq]
    fun_prop

theorem contDiff_rawImage (A : LorGrp (m + 1)) (k : ℕ∞ω) :
    ContDiff ℝ k (rawImage A) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ k (fun x : Horizontal m => ∑ j, matOf A i j * horoVec (fun l => x l) j)
  exact ContDiff.sum fun j _ =>
    contDiff_const.mul ((contDiff_pi.mp (contDiff_horoVec k)) j)

theorem contDiff_denominator (A : LorGrp (m + 1)) (k : ℕ∞ω) :
    ContDiff ℝ k (denominator A) :=
  ((contDiff_pi.mp (contDiff_rawImage A k)) (Sum.inr 0)).sub
    ((contDiff_pi.mp (contDiff_rawImage A k)) (Sum.inl (Fin.last m)))

theorem contDiffAt_chartAction (g : IsometryGroup m) (k : ℕ∞ω) {x : Horizontal m}
    (hx : x ∈ chartDomain g) : ContDiffAt ℝ k (chartAction g) x := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hd := (denominator_ne_zero_iff A x).mpr hx
  have he : chartAction (QuotientGroup.mk' _ A) =
      fun y => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (fun i => rawImage A y (Sum.inl i.castSucc) / denominator A y) := by
    funext y
    ext i
    exact chartAction_mk_apply A y i
  rw [he]
  apply (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.contDiffAt.comp
  exact contDiffAt_pi.mpr fun i =>
    ((contDiff_pi.mp (contDiff_rawImage A k)) (Sum.inl i.castSucc)).contDiffAt.div
      (contDiff_denominator A k).contDiffAt hd

theorem differentiableAt_chartAction (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) : DifferentiableAt ℝ (chartAction g) x :=
  (contDiffAt_chartAction g 1 hx).differentiableAt one_ne_zero

variable [Nonempty (Fin m)]

theorem ae_mem_chartDomain (g : IsometryGroup m) :
    ∀ᵐ x ∂(volume : Measure (Horizontal m)), x ∈ chartDomain g := by
  have h := (chart_smul_null_iff g (measurableSet_singleton ptInfty)).mpr boundaryMeasure_infty
  simpa only [ae_iff, chartDomain, mem_ofPred_eq, mem_singleton_iff, not_not] using h

theorem quasiMeasurePreserving_chartAction (g : IsometryGroup m) :
    QuasiMeasurePreserving (chartAction g) volume volume :=
  measurePreserving_coords.quasiMeasurePreserving.comp
    ((quasiMeasurePreserving_smul g).comp measurePreserving_embed.quasiMeasurePreserving)

omit [Nonempty (Fin m)] in
theorem inverse_fderiv_chartAction (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) :
    (fderiv ℝ (chartAction g⁻¹) (chartAction g x)).comp (fderiv ℝ (chartAction g) x) =
      ContinuousLinearMap.id ℝ (Horizontal m) := by
  have hi := differentiableAt_chartAction g⁻¹ (chartAction_mem_inverseDomain g hx)
  have hf := differentiableAt_chartAction g hx
  have he : (fun y => chartAction g⁻¹ (chartAction g y)) =ᶠ[𝓝 x] id := by
    filter_upwards [(isOpen_chartDomain g).mem_nhds hx] with y hy
    exact chartAction_inv g hy
  exact (hi.hasFDerivAt.comp x hf.hasFDerivAt).unique
    ((hasFDerivAt_id x).congr_of_eventuallyEq he)

omit [Nonempty (Fin m)] in
theorem fderiv_inverse_chartAction (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) :
    (fderiv ℝ (chartAction g) x).comp (fderiv ℝ (chartAction g⁻¹) (chartAction g x)) =
      ContinuousLinearMap.id ℝ (Horizontal m) := by
  have h := inverse_fderiv_chartAction g⁻¹ (chartAction_mem_inverseDomain g hx)
  rwa [inv_inv, chartAction_inv g hx] at h

omit [Nonempty (Fin m)] in
theorem chart_conjugacy (g h : IsometryGroup m)
    (ψ : BoundaryH (m + 1) → BoundaryH (m + 1)) (F : Horizontal m → Horizontal m)
    (hF : ∀ x, embed (F x) = ψ (embed x))
    (heq : ∀ v, ψ (g • v) = h • ψ v)
    {x : Horizontal m} (hx : x ∈ chartDomain g) :
    F x ∈ chartDomain h ∧ F (chartAction g x) = chartAction h (F x) := by
  have hb : embed (F (chartAction g x)) = h • embed (F x) := by
    rw [hF, embed_chartAction g hx, heq, ← hF]
  refine ⟨fun hp => embed_ne_infty _ (hb.trans hp), ?_⟩
  have hc := congrArg coords hb
  rwa [coords_embed] at hc

theorem ae_fderiv_conjugacy (g h : IsometryGroup m)
    (ψ : BoundaryH (m + 1) → BoundaryH (m + 1)) (F : Horizontal m → Horizontal m)
    (hF : ∀ x, embed (F x) = ψ (embed x))
    (heq : ∀ v, ψ (g • v) = h • ψ v)
    (hdiff : ∀ᵐ x ∂(volume : Measure (Horizontal m)), DifferentiableAt ℝ F x) :
    ∀ᵐ x ∂(volume : Measure (Horizontal m)),
      x ∈ chartDomain g ∧ F x ∈ chartDomain h ∧
      (fderiv ℝ F (chartAction g x)).comp (fderiv ℝ (chartAction g) x) =
        (fderiv ℝ (chartAction h) (F x)).comp (fderiv ℝ F x) := by
  filter_upwards [ae_mem_chartDomain g, hdiff,
    (quasiMeasurePreserving_chartAction g).ae hdiff] with x hx hdx hdgx
  have hc := chart_conjugacy g h ψ F hF heq hx
  have he : (fun y => F (chartAction g y)) =ᶠ[𝓝 x] (fun y => chartAction h (F y)) := by
    filter_upwards [(isOpen_chartDomain g).mem_nhds hx] with y hy
    exact (chart_conjugacy g h ψ F hF heq hy).2
  refine ⟨hx, hc.1, ?_⟩
  exact (hdgx.hasFDerivAt.comp x (differentiableAt_chartAction g hx).hasFDerivAt).unique
    (((differentiableAt_chartAction h hc.1).hasFDerivAt.comp x hdx.hasFDerivAt).congr_of_eventuallyEq he)

end DifferentialGeometry.BoundaryChartAction
