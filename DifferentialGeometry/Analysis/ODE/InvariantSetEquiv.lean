import DifferentialGeometry.Analysis.ODE.InvariantSet
import Mathlib.Analysis.Calculus.Deriv.Comp

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def pushForwardVectorField (e : E ≃L[ℝ] F) (f : ℝ → E → E) : ℝ → F → F :=
  fun t y ↦ e (f t (e.symm y))

@[simp]
theorem pushForwardVectorField_apply (e : E ≃L[ℝ] F) (f : ℝ → E → E) (t : ℝ) (y : F) :
    pushForwardVectorField e f t y = e (f t (e.symm y)) :=
  rfl

@[simp]
theorem pushForwardVectorField_refl (f : ℝ → E → E) :
    pushForwardVectorField (ContinuousLinearEquiv.refl ℝ E) f = f := by
  ext t x
  simp [pushForwardVectorField]

@[simp]
theorem pushForwardVectorField_trans (e : E ≃L[ℝ] F) (e' : F ≃L[ℝ] G)
    (f : ℝ → E → E) :
    pushForwardVectorField (e.trans e') f =
      pushForwardVectorField e' (pushForwardVectorField e f) := by
  ext t x
  simp [pushForwardVectorField]

@[simp]
theorem pushForwardVectorField_symm (e : E ≃L[ℝ] F) (f : ℝ → E → E) :
    pushForwardVectorField e.symm (pushForwardVectorField e f) = f := by
  rw [← pushForwardVectorField_trans]
  simp

theorem ContinuousLinearEquiv.mapsTo_posTangentConeAt
    (e : E ≃L[ℝ] F) {C : Set E} {x : E} :
    MapsTo e (posTangentConeAt C x) (posTangentConeAt (e '' C) (e x)) := by
  intro v hv
  rcases exists_fun_of_mem_tangentConeAt hv with ⟨ι, l, hl, c, d, hd₀, hdC, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n ↦ e (d n)) ?_ ?_ ?_
  · simpa using e.continuous.continuousAt.tendsto.comp hd₀
  · filter_upwards [hdC] with n hn
    refine ⟨x + d n, hn, ?_⟩
    simp
  · apply Tendsto.congr' _ (e.continuous.continuousAt.tendsto.comp hcd)
    filter_upwards with n
    simp [NNReal.smul_def]

theorem ContinuousLinearEquiv.image_posTangentConeAt
    (e : E ≃L[ℝ] F) (C : Set E) (x : E) :
    e '' posTangentConeAt C x = posTangentConeAt (e '' C) (e x) := by
  apply Set.Subset.antisymm
  · exact (ContinuousLinearEquiv.mapsTo_posTangentConeAt e).image_subset
  intro v hv
  have hmap := ContinuousLinearEquiv.mapsTo_posTangentConeAt e.symm hv
  refine ⟨e.symm v, ?_, by simp⟩
  simpa using hmap

theorem VectorFieldTangentTo.pushForwardVectorField
    {f : ℝ → E → E} {C : Set E} (h : VectorFieldTangentTo f C) (e : E ≃L[ℝ] F) :
    VectorFieldTangentTo (pushForwardVectorField e f) (e '' C) := by
  intro t y hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using ContinuousLinearEquiv.mapsTo_posTangentConeAt e (h t x hx)

theorem IsIntegralCurveOn.pushForwardVectorField
    {f : ℝ → E → E} {s : Set ℝ} {gamma : ℝ → E}
    (h : IsIntegralCurveOn gamma f s) (e : E ≃L[ℝ] F) :
    IsIntegralCurveOn (fun t ↦ e (gamma t)) (pushForwardVectorField e f) s := by
  intro t ht
  simpa [Function.comp_def] using
    (e.toContinuousLinearMap.hasFDerivAt (x := gamma t)).comp_hasDerivWithinAt t (h t ht)

theorem IsIntegralCurve.pushForwardVectorField
    {f : ℝ → E → E} {gamma : ℝ → E}
    (h : IsIntegralCurve gamma f) (e : E ≃L[ℝ] F) :
    IsIntegralCurve (fun t ↦ e (gamma t)) (pushForwardVectorField e f) := by
  intro t
  simpa [Function.comp_def] using
    (e.toContinuousLinearMap.hasFDerivAt (x := gamma t)).comp_hasDerivAt t (h t)

theorem IsIntegralCurveAt.pushForwardVectorField
    {f : ℝ → E → E} {gamma : ℝ → E} {t₀ : ℝ}
    (h : IsIntegralCurveAt gamma f t₀) (e : E ≃L[ℝ] F) :
    IsIntegralCurveAt (fun t ↦ e (gamma t)) (pushForwardVectorField e f) t₀ := by
  filter_upwards [h] with t ht
  simpa [Function.comp_def] using
    (e.toContinuousLinearMap.hasFDerivAt (x := gamma t)).comp_hasDerivAt t ht

theorem isIntegralCurveOn_pushForwardVectorField_iff
    {f : ℝ → E → E} {s : Set ℝ} {gamma : ℝ → E} (e : E ≃L[ℝ] F) :
    IsIntegralCurveOn (fun t ↦ e (gamma t)) (pushForwardVectorField e f) s ↔
      IsIntegralCurveOn gamma f s := by
  constructor
  · intro h
    have hback := IsIntegralCurveOn.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsIntegralCurveOn.pushForwardVectorField h e

theorem isIntegralCurve_pushForwardVectorField_iff
    {f : ℝ → E → E} {gamma : ℝ → E} (e : E ≃L[ℝ] F) :
    IsIntegralCurve (fun t ↦ e (gamma t)) (pushForwardVectorField e f) ↔
      IsIntegralCurve gamma f := by
  constructor
  · intro h
    have hback := IsIntegralCurve.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsIntegralCurve.pushForwardVectorField h e

theorem isIntegralCurveAt_pushForwardVectorField_iff
    {f : ℝ → E → E} {gamma : ℝ → E} {t₀ : ℝ} (e : E ≃L[ℝ] F) :
    IsIntegralCurveAt (fun t ↦ e (gamma t)) (pushForwardVectorField e f) t₀ ↔
      IsIntegralCurveAt gamma f t₀ := by
  constructor
  · intro h
    have hback := IsIntegralCurveAt.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsIntegralCurveAt.pushForwardVectorField h e

theorem vectorFieldTangentTo_pushForwardVectorField_iff
    {f : ℝ → E → E} {C : Set E} (e : E ≃L[ℝ] F) :
    VectorFieldTangentTo (pushForwardVectorField e f) (e '' C) ↔
      VectorFieldTangentTo f C := by
  constructor
  · intro h
    have hback := VectorFieldTangentTo.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ VectorFieldTangentTo.pushForwardVectorField h e

theorem IsForwardInvariantForODE.pushForwardVectorField
    {f : ℝ → E → E} {C : Set E} (h : IsForwardInvariantForODE f C) (e : E ≃L[ℝ] F) :
    IsForwardInvariantForODE (pushForwardVectorField e f) (e '' C) := by
  intro a b hab gamma hgamma hgammaa
  have hback : IsIntegralCurveOn (fun t ↦ e.symm (gamma t)) f (Icc a b) := by
    simpa using IsIntegralCurveOn.pushForwardVectorField hgamma e.symm
  have ha : e.symm (gamma a) ∈ C := by
    obtain ⟨x, hx, hxeq⟩ := hgammaa
    simpa [← hxeq] using hx
  have hmap := h a b hab (fun t ↦ e.symm (gamma t)) hback ha
  intro t ht
  exact ⟨e.symm (gamma t), hmap ht, by simp⟩

theorem isForwardInvariantForODE_pushForwardVectorField_iff
    {f : ℝ → E → E} {C : Set E} (e : E ≃L[ℝ] F) :
    IsForwardInvariantForODE (pushForwardVectorField e f) (e '' C) ↔
      IsForwardInvariantForODE f C := by
  constructor
  · intro h
    have hback := IsForwardInvariantForODE.pushForwardVectorField h e.symm
    simpa using hback
  · exact fun h ↦ IsForwardInvariantForODE.pushForwardVectorField h e

end DifferentialGeometry.Analysis.ODE
