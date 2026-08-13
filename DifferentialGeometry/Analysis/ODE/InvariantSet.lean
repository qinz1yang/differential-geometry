import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.ODE.Basic

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def VectorFieldTangentTo (f : ℝ → E → E) (C : Set E) : Prop :=
  ∀ t x, x ∈ C → f t x ∈ posTangentConeAt C x

def IsForwardInvariantForODE (f : ℝ → E → E) (C : Set E) : Prop :=
  ∀ a b, a ≤ b → ∀ γ : ℝ → E,
    IsIntegralCurveOn γ f (Icc a b) → γ a ∈ C → MapsTo γ (Icc a b) C

theorem HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right
    {γ : ℝ → E} {t : ℝ} {v : E} {C : Set E}
    (hγ : HasDerivAt γ v t) (hC : ∀ᶠ h in 𝓝[>] (0 : ℝ), γ (t + h) ∈ C) :
    v ∈ posTangentConeAt C (γ t) := by
  let c : ℝ → ℝ≥0 := fun h ↦ ⟨max h⁻¹ 0, le_max_right _ _⟩
  let d : ℝ → E := fun h ↦ γ (t + h) - γ t
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) c d ?_ ?_ ?_
  · have htadd : Tendsto (fun h : ℝ ↦ t + h) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      simpa using
        (tendsto_const_nhds.add tendsto_id).mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa [d, Function.comp_def] using
      (hγ.continuousAt.tendsto.comp htadd).sub_const (γ t)
  · filter_upwards [hC] with h hh
    simpa [d] using hh
  · apply Tendsto.congr' _ hγ.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    simp [c, d, max_eq_left (inv_nonneg.mpr hpos.le), NNReal.smul_def]

theorem IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right
    {f : ℝ → E → E} {γ : ℝ → E} {t : ℝ} {C : Set E}
    (hγ : IsIntegralCurve γ f) (hC : MapsTo γ (Ici t) C) :
    f t (γ t) ∈ posTangentConeAt C (γ t) := by
  apply HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right (hγ t)
  filter_upwards [self_mem_nhdsWithin] with h hh
  apply hC
  change t ≤ t + h
  exact le_add_of_nonneg_right hh.le

theorem IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc
    {f : ℝ → E → E} {γ : ℝ → E} {a b : ℝ} {C : Set E}
    (hγ : IsIntegralCurve γ f) (hab : a < b) (hC : MapsTo γ (Icc a b) C) :
    f a (γ a) ∈ posTangentConeAt C (γ a) := by
  apply HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right (hγ a)
  have hb : Iio (b - a) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (sub_pos.mpr hab)
  have hb' : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Iio (b - a) :=
    Filter.Eventually.filter_mono inf_le_left hb
  filter_upwards [self_mem_nhdsWithin, hb'] with h hpos hlt
  apply hC
  constructor
  · exact le_add_of_nonneg_right hpos.le
  · have hlt' : h < b - a := hlt
    linarith

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve
    {f : ℝ → E → E} {C : Set E} (hC : IsForwardInvariantForODE f C)
    (hex : ∀ t x, ∃ γ : ℝ → E, IsIntegralCurve γ f ∧ γ t = x) :
    VectorFieldTangentTo f C := by
  intro t x hx
  obtain ⟨γ, hγ, hγt⟩ := hex t x
  have hmap : MapsTo γ (Icc t (t + 1)) C :=
    hC t (t + 1) (by linarith) γ (hγ.isIntegralCurveOn _) (hγt.symm ▸ hx)
  simpa [hγt] using
    IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc hγ
      (show t < t + 1 by linarith) hmap

theorem IsForwardInvariantForODE.inter
    {f : ℝ → E → E} {C D : Set E}
    (hC : IsForwardInvariantForODE f C) (hD : IsForwardInvariantForODE f D) :
    IsForwardInvariantForODE f (C ∩ D) := by
  intro a b hab γ hγ hγab
  exact (hC a b hab γ hγ hγab.1).inter (hD a b hab γ hγ hγab.2)

theorem isForwardInvariantForODE_univ (f : ℝ → E → E) :
    IsForwardInvariantForODE f univ := by
  intro a b hab γ hγ ha
  exact mapsTo_univ γ _

theorem Convex.vectorFieldTangentTo_of_sub_mem
    {f : ℝ → E → E} {C : Set E} (hC : Convex ℝ C)
    (hf : ∀ t x, x ∈ C → ∃ y ∈ C, f t x = y - x) :
    VectorFieldTangentTo f C := by
  intro t x hx
  obtain ⟨y, hy, hfy⟩ := hf t x hx
  rw [hfy]
  exact sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hx hy)

theorem ConvexCone.vectorFieldTangentTo_of_mapsTo
    (C : ConvexCone ℝ E) {f : ℝ → E → E}
    (hf : ∀ t, MapsTo (f t) C C) :
    VectorFieldTangentTo f C := by
  apply Convex.vectorFieldTangentTo_of_sub_mem C.convex
  intro t x hx
  refine ⟨x + f t x, C.add_mem hx (hf t hx), ?_⟩
  abel

theorem ProperCone.vectorFieldTangentTo_of_mapsTo
    (C : ProperCone ℝ E) {f : ℝ → E → E}
    (hf : ∀ t, MapsTo (f t) C C) :
    VectorFieldTangentTo f C := by
  apply Convex.vectorFieldTangentTo_of_sub_mem C.convex
  intro t x hx
  refine ⟨x + f t x, C.add_mem hx (hf t hx), ?_⟩
  abel

end DifferentialGeometry.Analysis.ODE
