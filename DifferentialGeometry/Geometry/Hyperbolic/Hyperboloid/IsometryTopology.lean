import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryClassification
import DifferentialGeometry.Geometry.Lorentz.Isometry
import DifferentialGeometry.Geometry.Metric.Isometry.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Units

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lorentzRepresentation : (Hyperboloid E ≃ᵢ Hyperboloid E) →*
    ((ℝ × E) →L[ℝ] (ℝ × E))ˣ where
  toFun f := (ContinuousLinearEquiv.unitsEquiv ℝ (ℝ × E)).symm
    (lorentzIsometryContinuousLinearEquiv (lorentzExtension f))
  map_one' := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro z
    change lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) z = z
    rw [lorentzExtension_refl]
    rfl
  map_mul' f g := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro z
    change lorentzExtension (g.trans f) z = lorentzExtension f (lorentzExtension g z)
    rw [lorentzExtension_trans]
    rfl

@[simp] theorem lorentzRepresentation_apply (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (z : ℝ × E) :
    (lorentzRepresentation f : (ℝ × E) →L[ℝ] (ℝ × E)) z = lorentzExtension f z := rfl

@[simp] theorem lorentzRepresentation_inv_apply (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (z : ℝ × E) :
    ((lorentzRepresentation f)⁻¹).val z =
      (lorentzExtension f).symm z := rfl

theorem lorentzRepresentation_trans (f g : Hyperboloid E ≃ᵢ Hyperboloid E) :
    lorentzRepresentation (f.trans g) = lorentzRepresentation g * lorentzRepresentation f :=
  (lorentzRepresentation (E := E)).map_mul g f

theorem lorentzRepresentation_symm (f : Hyperboloid E ≃ᵢ Hyperboloid E) :
    lorentzRepresentation f.symm = (lorentzRepresentation f)⁻¹ :=
  (lorentzRepresentation (E := E)).map_inv f

theorem lorentzRepresentation_injective : Function.Injective (lorentzRepresentation (E := E)) := by
  intro f g h
  apply IsometryEquiv.ext
  intro x
  apply Hyperboloid.ext
  have hx := congrArg
    (fun u : ((ℝ × E) →L[ℝ] (ℝ × E))ˣ => (u : (ℝ × E) →L[ℝ] (ℝ × E)) (x.time, x.space)) h
  rw [lorentzRepresentation_apply, lorentzRepresentation_apply,
    lorentzExtension_apply, lorentzExtension_apply] at hx
  exact congrArg Prod.snd hx

private theorem lorentzExtension_eval {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (z : ℝ × E) :
    lorentzExtension f z =
      (z.1 - (ofSpace z.2).time) • ((f origin).time, (f origin).space) +
        ((f (ofSpace z.2)).time, (f (ofSpace z.2)).space) := by
  have hz : z = (z.1 - (ofSpace z.2).time) • ((1 : ℝ), (0 : E)) +
      ((ofSpace z.2).time, z.2) := by
    rcases z with ⟨t, v⟩
    ext <;> simp
  have ho : lorentzExtension f (1, 0) = ((f origin).time, (f origin).space) := by
    simpa only [origin_time, origin_space] using lorentzExtension_apply f origin
  have hv : lorentzExtension f ((ofSpace z.2).time, z.2) =
      ((f (ofSpace z.2)).time, (f (ofSpace z.2)).space) := by
    simpa only [space_ofSpace] using lorentzExtension_apply f (ofSpace z.2)
  conv_lhs => rw [hz, map_add, map_smul]
  rw [ho, hv]

theorem continuous_lorentzExtension_apply {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × (ℝ × E) =>
      lorentzExtension p.1 p.2) := by
  have hz : Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × (ℝ × E) =>
      ofSpace p.2.2) := continuous_ofSpace.comp (continuous_snd.comp continuous_snd)
  have hc : Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × (ℝ × E) =>
      p.2.1 - (ofSpace p.2.2).time) :=
    (continuous_fst.comp continuous_snd).sub ((continuous_time (E := E)).comp hz)
  have ho : Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × (ℝ × E) =>
      p.1 origin) := (continuous_eval_const origin).comp continuous_fst
  have hv : Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × (ℝ × E) =>
      p.1 (ofSpace p.2.2)) := continuous_eval.comp (continuous_fst.prodMk hz)
  have ho' := ((continuous_time (E := F)).prodMk (continuous_space (E := F))).comp ho
  have hv' := ((continuous_time (E := F)).prodMk (continuous_space (E := F))).comp hv
  simp_rw [lorentzExtension_eval]
  exact (hc.smul ho').add hv'

theorem continuous_lorentzRepresentation [FiniteDimensional ℝ E] :
    Continuous (lorentzRepresentation (E := E)) := by
  apply Continuous.of_coeHom_comp
  change Continuous (fun f : Hyperboloid E ≃ᵢ Hyperboloid E =>
    (lorentzRepresentation f : (ℝ × E) →L[ℝ] (ℝ × E)))
  apply continuous_clm_apply.mpr
  intro z
  change Continuous (fun f : Hyperboloid E ≃ᵢ Hyperboloid E => lorentzExtension f z)
  exact (continuous_lorentzExtension_apply (E := E) (F := E)).comp
    (continuous_id.prodMk continuous_const)

private def spatialEvaluation (u : ((ℝ × E) →L[ℝ] (ℝ × E))ˣ) : Hyperboloid E → Hyperboloid E :=
  fun x => ofSpace ((u : (ℝ × E) →L[ℝ] (ℝ × E)) (x.time, x.space)).2

private theorem continuous_spatialEvaluation : Continuous (spatialEvaluation (E := E)) := by
  apply continuous_pi
  intro x
  exact continuous_ofSpace.comp (continuous_snd.comp
    ((ContinuousLinearMap.apply ℝ (ℝ × E) (x.time, x.space)).continuous.comp Units.continuous_val))

theorem isEmbedding_lorentzRepresentation [FiniteDimensional ℝ E] :
    Topology.IsEmbedding (lorentzRepresentation (E := E)) := by
  have h : (spatialEvaluation (E := E)) ∘ (lorentzRepresentation (E := E)) =
      ((⇑) : (Hyperboloid E ≃ᵢ Hyperboloid E) → Hyperboloid E → Hyperboloid E) := by
    funext f x
    change ofSpace ((lorentzRepresentation f : (ℝ × E) →L[ℝ] (ℝ × E))
      (x.time, x.space)).2 = f x
    rw [lorentzRepresentation_apply, lorentzExtension_apply, ofSpace_space]
  refine Topology.IsEmbedding.of_comp (continuous_lorentzRepresentation (E := E))
    (continuous_spatialEvaluation (E := E)) ?_
  rw [h]
  exact IsometryEquiv.isEmbedding_coe

end DifferentialGeometry.Hyperboloid
