import DifferentialGeometry.Topology.Manifold.RegularLevel.DescendingField
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
import DifferentialGeometry.Topology.Homotopy.EquivUnder
import DifferentialGeometry.Topology.Morse.Defs

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology.Homotopy
open DifferentialGeometry.Analysis.ODE

namespace Poincare.Morse

variable {m : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_sublevelHomotopyEquivUnder {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hK : IsCompact (f ⁻¹' Icc a b))
    (hr : ∀ x ∈ f ⁻¹' Icc a b, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {B : Type*} [TopologicalSpace B] (j : C(B, SublevelSpace f a)) :
    ∃ e : HomotopyEquivUnder ((sublevelInclusion f hab).comp j) j,
      e.invFun = sublevelInclusion f hab := by
  obtain ⟨V, hV, hsupp, hdf, hrate⟩ :=
    Poincare.Manifold.RegularLevel.exists_descendingField_on_compact I hf hK hr
  let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  let T : M → ℝ := fun x ↦ max (f x - a) 0
  have hT0 (x : M) (hx : f x ≤ a) : T x = 0 := max_eq_right (sub_nonpos.mpr hx)
  have hTnonneg (x : M) : 0 ≤ T x := le_max_right _ _
  have hrateFlow (x : M) {t : ℝ} (ht : 0 ≤ t) :
      f x - t ≤ f (curveAt V hc x t) ∧ f (curveAt V hc x t) ≤ f x := by
    simpa only [curveAt_zero] using
      f_rate_bounds_of_integralCurve f hf V hrate (hγ := curveAt_integralCurve V hc x) ht
  have hstop (x : SublevelSpace f b) : f (curveAt V hc x.1 (T x.1)) ≤ a := by
    by_cases hx : f x.1 ≤ a
    · rw [hT0 x.1 hx, curveAt_zero]
      exact hx
    · have hxlo : a ≤ f x.1 := (lt_of_not_ge hx).le
      have htime : T x.1 = f x.1 - a := max_eq_left (sub_nonneg.mpr hxlo)
      have hstay : ∀ t ∈ Icc 0 (T x.1), curveAt V hc x.1 t ∈ f ⁻¹' Icc a b := by
        intro t ht
        obtain ⟨hlo, hup⟩ := hrateFlow x.1 ht.1
        have htb : t ≤ f x.1 - a := htime ▸ ht.2
        exact ⟨by linarith, hup.trans x.2⟩
      have heq := f_eq_sub_of_integralCurve_on_strip f hf V hdf
        (hγ := curveAt_integralCurve V hc x.1) (hTnonneg x.1) hstay
      simp only [curveAt_zero] at heq
      rw [htime] at heq ⊢
      linarith
  have hTcont : Continuous T := (hf.continuous.sub continuous_const).max continuous_const
  have hflow : Continuous (fun q : ℝ × M ↦ curveAt V hc q.2 q.1) :=
    continuous_globalFlow_of_compactSupport V hV hsupp
  let r : C(SublevelSpace f b, SublevelSpace f a) := ⟨
    fun x ↦ ⟨curveAt V hc x.1 (T x.1), hstop x⟩,
    (hflow.comp ((hTcont.comp continuous_subtype_val).prodMk continuous_subtype_val)).subtype_mk
      (fun x ↦ hstop x)⟩
  let i := sublevelInclusion f hab
  have hri : r.comp i = ContinuousMap.id (SublevelSpace f a) := by
    ext x
    change curveAt V hc x.1 (T x.1) = x.1
    rw [hT0 x.1 x.2, curveAt_zero]
  have hmem (p : unitInterval × SublevelSpace f b) :
      f (curveAt V hc p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) ≤ b :=
    (hrateFlow p.2.1 (mul_nonneg (hTnonneg _) (sub_nonneg.mpr p.1.2.2))).2.trans p.2.2
  let F : C(unitInterval × SublevelSpace f b, SublevelSpace f b) := ⟨
    fun p ↦ ⟨curveAt V hc p.2.1 (T p.2.1 * (1 - (p.1 : ℝ))), hmem p⟩, by
      apply Continuous.subtype_mk
      exact hflow.comp (((hTcont.comp (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).prodMk
          (continuous_subtype_val.comp continuous_snd))⟩
  let hom : ContinuousMap.HomotopyRel (i.comp r) (ContinuousMap.id (SublevelSpace f b))
      (Set.range (i.comp j)) := {
    toHomotopy := {
      toContinuousMap := F
      map_zero_left := by
        intro x
        apply Subtype.ext
        change curveAt V hc x.1 (T x.1 * (1 - (0 : ℝ))) = curveAt V hc x.1 (T x.1)
        rw [sub_zero, mul_one]
      map_one_left := by intro x; apply Subtype.ext; change curveAt V hc x.1 _ = x.1; simp [curveAt_zero] }
    prop' := by
      rintro t _ ⟨x, rfl⟩
      apply Subtype.ext
      change curveAt V hc (j x).1 (T (j x).1 * (1 - (t : ℝ))) =
        curveAt V hc (j x).1 (T (j x).1)
      rw [hT0 (j x).1 (j x).2, zero_mul] }
  refine ⟨{
    toFun := r
    invFun := i
    map_toBase := by rw [← ContinuousMap.comp_assoc, hri, ContinuousMap.id_comp]
    map_fromBase := rfl
    leftInv := hom
    rightInv := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (SublevelSpace f a))
      (Set.range j)).cast hri.symm rfl }, rfl⟩

end Poincare.Morse
