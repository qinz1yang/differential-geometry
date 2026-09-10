import DifferentialGeometry.Topology.LocalDegree.SphereMapHomotopy
import DifferentialGeometry.Topology.LocalDegree.LinearizationHomotopy
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

set_option autoImplicit false
open Filter Metric Set
open scoped Manifold ContDiff Topology unitInterval
noncomputable section
namespace Poincare.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem operator_interpolation_ne_zero (A : F ≃L[ℝ] E) (B : F →L[ℝ] E)
    (hB : ‖B - A.toContinuousLinearMap‖ ≤ (2 * (‖A.symm.toContinuousLinearMap‖ + 1))⁻¹)
    {w : F} (hw : w ≠ 0) (t : I) :
    (1 - (t : ℝ)) • B w + (t : ℝ) • A w ≠ 0 := by
  let C : ℝ := ‖A.symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ‖w‖ ≤ C * ‖A w‖ := by
    have hh := A.symm.toContinuousLinearMap.le_opNorm (A w)
    simp only [ContinuousLinearEquiv.coe_coe, A.symm_apply_apply] at hh
    dsimp [C]
    nlinarith [norm_nonneg (A w)]
  have herr : ‖B w - A w‖ ≤ ‖A w‖ / 2 := by
    calc
      ‖B w - A w‖ = ‖(B - A.toContinuousLinearMap) w‖ := rfl
      _ ≤ ‖B - A.toContinuousLinearMap‖ * ‖w‖ := (B - A.toContinuousLinearMap).le_opNorm w
      _ ≤ (2 * C)⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
      _ ≤ (2 * C)⁻¹ * (C * ‖A w‖) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ‖A w‖ / 2 := by field_simp
  have hAw : 0 < ‖A w‖ := norm_pos_iff.mpr (by simpa using A.injective.ne hw)
  have hscale : ‖(1 - (t : ℝ)) • (B w - A w)‖ ≤ ‖A w‖ / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.property.2)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [t.property.1])).trans herr
  intro hz
  have heq : (1 - (t : ℝ)) • (B w - A w) = -A w := by
    calc
      (1 - (t : ℝ)) • (B w - A w) =
        ((1 - (t : ℝ)) • B w + (t : ℝ) • A w) - A w := by module
      _ = -A w := by rw [hz, zero_sub]
  rw [heq, norm_neg] at hscale
  linarith

private theorem inverse_fderiv_coordinate {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) :
    (fderiv ℝ φ x).inverse = fderiv ℝ φ.symm (φ x) := by
  simpa only [mfderiv_eq_fderiv] using!
    Poincare.VectorField.inverse_mfderiv_partialDiffeomorph φ
      (ne_of_gt (zero_lt_one.trans_le hn)) hx

private theorem continuousOn_inverse_coordinate_derivative {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n) :
    ContinuousOn (fun y ↦ fderiv ℝ φ.symm (φ y)) φ.source :=
  (φ.symm.contMDiffOn.contDiffOn.continuousOn_fderiv_of_isOpen φ.open_target hn).comp
    φ.contMDiffOn.continuousOn (fun _ hy ↦ φ.map_source hy)

private theorem exists_coordinate_derivative {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) :
    ∃ A : E ≃L[ℝ] F, A.toContinuousLinearMap = fderiv ℝ φ x := by
  have hi : (fderiv ℝ φ x).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using!
      Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph φ
        (ne_of_gt (zero_lt_one.trans_le hn)) hx
  exact hi

private theorem exists_coordinate_control {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) (A : E ≃L[ℝ] F)
    (hA : A.toContinuousLinearMap = fderiv ℝ φ x) {S : ℝ} (hS : 0 < S) :
    ∃ R > 0, ∀ y ∈ closedBall x R,
      y ∈ φ.source ∧ φ y ∈ closedBall (φ x) S ∧
      φ x + A (y - x) ∈ closedBall (φ x) S ∧
      ‖fderiv ℝ φ.symm (φ y) - A.symm.toContinuousLinearMap‖ ≤
        (2 * (‖A.toContinuousLinearMap‖ + 1))⁻¹ ∧
      ∀ t : I, y ≠ x →
        (1 - (t : ℝ)) • φ y + (t : ℝ) • (φ x + A (y - x)) ≠ φ x := by
  have hd : HasFDerivAt φ A.toContinuousLinearMap x := by
    rw [hA]
    exact ((φ.contMDiffOn.contDiffOn).contDiffAt
      (φ.open_source.mem_nhds hx)).differentiableAt
      (ne_of_gt (zero_lt_one.trans_le hn)) |>.hasFDerivAt
  obtain ⟨R₀, hR₀, hn₀⟩ := exists_pos_linearization_nonzero A
    (show (fun y ↦ φ y - φ x) x = 0 from sub_self _) (hd.sub_const (φ x))
  have hB : ContinuousAt (fun y ↦ fderiv ℝ φ.symm (φ y)) x :=
    (continuousOn_inverse_coordinate_derivative φ hn).continuousAt
      (φ.open_source.mem_nhds hx)
  have hBx : fderiv ℝ φ.symm (φ x) = A.symm.toContinuousLinearMap := by
    rw [← inverse_fderiv_coordinate φ hn hx, ← hA, ContinuousLinearMap.inverse_equiv]
  have hδ : 0 < (2 * (‖A.toContinuousLinearMap‖ + 1))⁻¹ := by positivity
  have hnorm : ∀ᶠ y in 𝓝 x,
      ‖fderiv ℝ φ.symm (φ y) - A.symm.toContinuousLinearMap‖ <
        (2 * (‖A.toContinuousLinearMap‖ + 1))⁻¹ :=
    (hB.sub_const A.symm.toContinuousLinearMap).norm.eventually
      (eventually_lt_nhds (by simpa only [hBx, sub_self, norm_zero] using hδ))
  have hφ : ∀ᶠ y in 𝓝 x, φ y ∈ closedBall (φ x) S :=
    (φ.toOpenPartialHomeomorph.continuousAt hx).preimage_mem_nhds (closedBall_mem_nhds _ hS)
  have hL : ∀ᶠ y in 𝓝 x, φ x + A (y - x) ∈ closedBall (φ x) S := by
    have hc : Continuous (fun y : E ↦ φ x + A (y - x)) :=
      continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))
    simpa only [sub_self, map_zero, add_zero] using!
      (hc.continuousAt (x := x)).preimage_mem_nhds (closedBall_mem_nhds _ hS)
  have hsource : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hx
  have hevent := hsource.and (hφ.and (hL.and hnorm))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min R₀ (ε / 2), lt_min hR₀ (by positivity), ?_⟩
  intro y hy
  have hh := hball (closedBall_subset_ball
    (lt_of_le_of_lt (min_le_right R₀ (ε / 2)) (by linarith)) hy)
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.le, ?_⟩
  intro t hyx hzero
  have hv : ‖y - x‖ ≤ R₀ :=
    (show ‖y - x‖ ≤ min R₀ (ε / 2) by simpa only [mem_closedBall, dist_eq_norm] using hy).trans
      (min_le_left _ _)
  apply hn₀ (y - x) hv (sub_ne_zero.mpr hyx) t
  have heq : (1 - (t : ℝ)) • (φ (x + (y - x)) - φ x) + (t : ℝ) • A (y - x) =
      ((1 - (t : ℝ)) • φ y + (t : ℝ) • (φ x + A (y - x))) - φ x := by
    rw [add_sub_cancel]
    module
  rw [heq, hzero, sub_self]

private theorem sphere_argument {x : E} {R : ℝ} (r : Ioc (0 : ℝ) R)
    (v : sphere (0 : E) 1) :
    x + (r : ℝ) • (v : E) ∈ closedBall x R ∧ x + (r : ℝ) • (v : E) ≠ x := by
  have hnorm : ‖(r : ℝ) • (v : E)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]
  constructor
  · simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm] using r.property.2
  · intro heq
    have hh : (r : ℝ) • (v : E) = 0 := (add_eq_left.mp heq)
    rw [hh, norm_zero] at hnorm
    exact r.property.1.ne' hnorm.symm

theorem exists_sphereMap_inverseDifferential_homotopy {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) {V : F → F} {S : ℝ} (hS : 0 < S)
    (hV : ContinuousOn V (closedBall (φ x) S))
    (hVzero : ∀ z ∈ closedBall (φ x) S, z ≠ φ x → V z ≠ 0) :
    let P : E → E := _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) φ V;
    ∃ A : E ≃L[ℝ] F, A.toContinuousLinearMap = fderiv ℝ φ x ∧
      ∃ R > 0,
        ∃ hP : ContinuousOn (P) (closedBall x R),
        ∃ hPzero : ∀ y ∈ closedBall x R, y ≠ x →
          P y ≠ 0,
        ∃ hQ : ContinuousOn (fun y ↦ A.symm (V (φ y))) (closedBall x R),
        ∃ hQzero : ∀ y ∈ closedBall x R, y ≠ x → A.symm (V (φ y)) ≠ 0,
        ∀ r : Ioc (0 : ℝ) R,
          ∃ H : (sphereMap (P)
              x R hP hPzero r).Homotopy
            (sphereMap (fun y ↦ A.symm (V (φ y))) x R hQ hQzero r),
            ∀ t : I, ∀ v : sphere (0 : E) 1,
              (H (t, v) : E) =
                ‖(1 - (t : ℝ)) • (P
                    (x + (r : ℝ) • (v : E)) : E) +
                  (t : ℝ) • A.symm (V (φ (x + (r : ℝ) • (v : E))))‖⁻¹ •
                ((1 - (t : ℝ)) • (P
                    (x + (r : ℝ) • (v : E)) : E) +
                  (t : ℝ) • A.symm (V (φ (x + (r : ℝ) • (v : E))))) := by
  obtain ⟨A, hA⟩ := exists_coordinate_derivative φ hn hx
  obtain ⟨R, hR, hcontrol⟩ := exists_coordinate_control φ hn hx A hA hS
  let P : E → E := _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) φ V
  let Q : E → E := fun y ↦ A.symm (V (φ y))
  have hPeq (y : E) (hy : y ∈ closedBall x R) :
      P y = (fderiv ℝ φ.symm (φ y)) (V (φ y)) := by
    have hh := congrArg (fun B : F →L[ℝ] E ↦ B (V (φ y)))
      (inverse_fderiv_coordinate φ hn (hcontrol y hy).1)
    simpa only [P, _root_.VectorField.mpullback, mfderiv_eq_fderiv] using! hh
  have hcomp : ContinuousOn (fun y ↦ V (φ y)) (closedBall x R) :=
    hV.comp (φ.contMDiffOn.continuousOn.mono (fun y hy ↦ (hcontrol y hy).1))
      (fun y hy ↦ (hcontrol y hy).2.1)
  have hP : ContinuousOn P (closedBall x R) :=
    (((continuousOn_inverse_coordinate_derivative φ hn).mono
      (fun y hy ↦ (hcontrol y hy).1)).clm_apply hcomp).congr hPeq
  have hQ : ContinuousOn Q (closedBall x R) := A.symm.continuous.comp_continuousOn hcomp
  have hnonzero (y : E) (hy : y ∈ closedBall x R) (hyx : y ≠ x) (t : I) :
      (1 - (t : ℝ)) • P y + (t : ℝ) • Q y ≠ 0 := by
    rw [hPeq y hy]
    exact operator_interpolation_ne_zero A.symm (fderiv ℝ φ.symm (φ y))
      (hcontrol y hy).2.2.2.1
      (hVzero _ (hcontrol y hy).2.1 (fun hh ↦ hyx (φ.injOn (hcontrol y hy).1 hx hh))) t
  have hPzero : ∀ y ∈ closedBall x R, y ≠ x → P y ≠ 0 := by
    intro y hy hyx
    simpa using hnonzero y hy hyx 0
  have hQzero : ∀ y ∈ closedBall x R, y ≠ x → Q y ≠ 0 := by
    intro y hy hyx
    simpa using hnonzero y hy hyx 1
  refine ⟨A, hA, R, hR, hP, hPzero, hQ, hQzero, ?_⟩
  intro r
  let H : I × sphere (0 : E) 1 → E := fun p ↦
    (1 - (p.1 : ℝ)) • P (x + (r : ℝ) • (p.2 : E)) +
      (p.1 : ℝ) • Q (x + (r : ℝ) • (p.2 : E))
  have harg : Continuous (fun p : I × sphere (0 : E) 1 ↦ x + (r : ℝ) • (p.2 : E)) :=
    continuous_const.add (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
  have ht : Continuous (fun p : I × sphere (0 : E) 1 ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hH : Continuous H :=
    ((continuous_const.sub ht).smul
      (hP.comp_continuous harg (fun p ↦ (sphere_argument r p.2).1))).add
      (ht.smul (hQ.comp_continuous harg (fun p ↦ (sphere_argument r p.2).1)))
  have hHz (p : I × sphere (0 : E) 1) : H p ≠ 0 :=
    hnonzero _ (sphere_argument r p.2).1 (sphere_argument r p.2).2 p.1
  refine ⟨sphereMapHomotopyOfFamily hP hQ hPzero hQzero r H hH hHz
    (fun _ ↦ by simp [H]) (fun _ ↦ by simp [H]), ?_⟩
  intro t v
  exact homeomorphUnitSphereProd_apply_fst_coe E _

theorem mpullback_affineCoordinate_eq (A : E ≃L[ℝ] F) (x y : E) (p : F) (V : F → F) :
    _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) (fun z ↦ p + A (z - x)) V y =
      A.symm (V (p + A (y - x))) := by
  have hd : HasFDerivAt (fun z ↦ p + A (z - x)) A.toContinuousLinearMap y := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using
      (A.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)).const_add p
  have hh : (fderiv ℝ (fun z ↦ p + A (z - x)) y).inverse (V (p + A (y - x))) =
      A.symm (V (p + A (y - x))) := by
    rw [hd.fderiv, ContinuousLinearMap.inverse_equiv]
    rfl
  simpa only [_root_.VectorField.mpullback, mfderiv_eq_fderiv] using! hh

theorem exists_sphereMap_coordinateStraightening_homotopy {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) (A : E ≃L[ℝ] F)
    (hA : A.toContinuousLinearMap = fderiv ℝ φ x)
    {V : F → F} {S : ℝ} (hS : 0 < S)
    (hV : ContinuousOn V (closedBall (φ x) S))
    (hVzero : ∀ z ∈ closedBall (φ x) S, z ≠ φ x → V z ≠ 0) :
    ∃ R > 0,
      ∃ hQ : ContinuousOn (fun y ↦ A.symm (V (φ y))) (closedBall x R),
      ∃ hQzero : ∀ y ∈ closedBall x R, y ≠ x → A.symm (V (φ y)) ≠ 0,
      ∃ hG : ContinuousOn (_root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F)
        (fun y ↦ φ x + A (y - x)) V) (closedBall x R),
      ∃ hGzero : ∀ y ∈ closedBall x R, y ≠ x →
        _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y ↦ φ x + A (y - x)) V y ≠ 0,
      ∀ r : Ioc (0 : ℝ) R,
        ∃ H : (sphereMap (fun y ↦ A.symm (V (φ y))) x R hQ hQzero r).Homotopy
          (sphereMap (_root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F)
            (fun y ↦ φ x + A (y - x)) V) x R hG hGzero r),
          ∀ t : I, ∀ v : sphere (0 : E) 1,
            (H (t, v) : E) =
              ‖A.symm (V ((1 - (t : ℝ)) • φ (x + (r : ℝ) • (v : E)) +
                (t : ℝ) • (φ x + A ((r : ℝ) • (v : E)))))‖⁻¹ •
              A.symm (V ((1 - (t : ℝ)) • φ (x + (r : ℝ) • (v : E)) +
                (t : ℝ) • (φ x + A ((r : ℝ) • (v : E))))) := by
  obtain ⟨R, hR, hcontrol⟩ := exists_coordinate_control φ hn hx A hA hS
  let Q : E → E := fun y ↦ A.symm (V (φ y))
  let G : E → E := _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F)
    (fun y ↦ φ x + A (y - x)) V
  have hGeq (y : E) : G y = A.symm (V (φ x + A (y - x))) :=
    mpullback_affineCoordinate_eq A x y (φ x) V
  have hφ : ContinuousOn φ (closedBall x R) :=
    φ.contMDiffOn.continuousOn.mono (fun y hy ↦ (hcontrol y hy).1)
  have hQ : ContinuousOn Q (closedBall x R) :=
    A.symm.continuous.comp_continuousOn (hV.comp hφ (fun y hy ↦ (hcontrol y hy).2.1))
  have hlinear : Continuous (fun y : E ↦ φ x + A (y - x)) :=
    continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))
  have hG : ContinuousOn G (closedBall x R) :=
    (A.symm.continuous.comp_continuousOn
      (hV.comp hlinear.continuousOn (fun y hy ↦ (hcontrol y hy).2.2.1))).congr
      (fun y _ ↦ hGeq y)
  have hmem (y : E) (hy : y ∈ closedBall x R) (t : I) :
      (1 - (t : ℝ)) • φ y + (t : ℝ) • (φ x + A (y - x)) ∈ closedBall (φ x) S :=
    (convex_closedBall (φ x) S) (hcontrol y hy).2.1 (hcontrol y hy).2.2.1
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  have hnonzero (y : E) (hy : y ∈ closedBall x R) (hyx : y ≠ x) (t : I) :
      A.symm (V ((1 - (t : ℝ)) • φ y + (t : ℝ) • (φ x + A (y - x)))) ≠ 0 :=
    mt A.symm.map_eq_zero_iff.mp
      (hVzero _ (hmem y hy t) ((hcontrol y hy).2.2.2.2 t hyx))
  have hQzero : ∀ y ∈ closedBall x R, y ≠ x → Q y ≠ 0 := by
    intro y hy hyx
    simpa [Q] using hnonzero y hy hyx 0
  have hGzero : ∀ y ∈ closedBall x R, y ≠ x → G y ≠ 0 := by
    intro y hy hyx
    rw [hGeq]
    simpa using hnonzero y hy hyx 1
  refine ⟨R, hR, hQ, hQzero, hG, hGzero, ?_⟩
  intro r
  let H : I × sphere (0 : E) 1 → E := fun p ↦
    A.symm (V ((1 - (p.1 : ℝ)) • φ (x + (r : ℝ) • (p.2 : E)) +
      (p.1 : ℝ) • (φ x + A ((r : ℝ) • (p.2 : E)))))
  have harg : Continuous (fun p : I × sphere (0 : E) 1 ↦ x + (r : ℝ) • (p.2 : E)) :=
    continuous_const.add (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
  have ht : Continuous (fun p : I × sphere (0 : E) 1 ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hφarg := hφ.comp_continuous harg (fun p ↦ (sphere_argument r p.2).1)
  have hAarg : Continuous (fun p : I × sphere (0 : E) 1 ↦
      φ x + A ((r : ℝ) • (p.2 : E))) :=
    continuous_const.add (A.continuous.comp
      (continuous_const.smul (continuous_subtype_val.comp continuous_snd)))
  have hH : Continuous H := A.symm.continuous.comp
    (hV.comp_continuous (((continuous_const.sub ht).smul hφarg).add (ht.smul hAarg))
      (fun p ↦ by
        have hh := hmem (x + (r : ℝ) • (p.2 : E)) (sphere_argument r p.2).1 p.1
        simpa only [add_sub_cancel_left] using! hh))
  have hHz (p : I × sphere (0 : E) 1) : H p ≠ 0 := by
    simpa only [H, add_sub_cancel_left] using
      hnonzero _ (sphere_argument r p.2).1 (sphere_argument r p.2).2 p.1
  refine ⟨sphereMapHomotopyOfFamily hQ hG hQzero hGzero r H hH hHz
    (fun _ ↦ by simp [H, Q]) (fun _ ↦ by simp [H, hGeq]), ?_⟩
  intro t v
  exact homeomorphUnitSphereProd_apply_fst_coe E _

private theorem sphereMap_same_radius {f : E → F} {x : E} {R S : ℝ}
    (hR : ContinuousOn f (closedBall x R)) (hS : ContinuousOn f (closedBall x S))
    (hzR : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (hzS : ∀ y ∈ closedBall x S, y ≠ x → f y ≠ 0)
    (r : Ioc (0 : ℝ) R) (s : Ioc (0 : ℝ) S) (hrs : (r : ℝ) = (s : ℝ)) :
    sphereMap f x R hR hzR r = sphereMap f x S hS hzS s := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply, hrs]

theorem exists_sphereMap_coordinateChange_homotopy {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F n) (hn : 1 ≤ n)
    {x : E} (hx : x ∈ φ.source) {V : F → F} {S : ℝ} (hS : 0 < S)
    (hV : ContinuousOn V (closedBall (φ x) S))
    (hVzero : ∀ z ∈ closedBall (φ x) S, z ≠ φ x → V z ≠ 0) :
    let P : E → E := _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) φ V;
    ∃ A : E ≃L[ℝ] F, A.toContinuousLinearMap = fderiv ℝ φ x ∧
      ∃ R > 0,
        ∃ hP : ContinuousOn P (closedBall x R),
        ∃ hPzero : ∀ y ∈ closedBall x R, y ≠ x → P y ≠ 0,
        ∃ hG : ContinuousOn (_root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F)
          (fun y ↦ φ x + A (y - x)) V) (closedBall x R),
        ∃ hGzero : ∀ y ∈ closedBall x R, y ≠ x →
          _root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y ↦ φ x + A (y - x)) V y ≠ 0,
        ∀ r : Ioc (0 : ℝ) R,
          Nonempty ((sphereMap P x R hP hPzero r).Homotopy
            (sphereMap (_root_.VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F)
              (fun y ↦ φ x + A (y - x)) V) x R hG hGzero r)) := by
  obtain ⟨A, hA, R₁, hR₁, hP₁, hzP₁, hQ₁, hzQ₁, h₁⟩ :=
    exists_sphereMap_inverseDifferential_homotopy φ hn hx hS hV hVzero
  obtain ⟨R₂, hR₂, hQ₂, hzQ₂, hG₂, hzG₂, h₂⟩ :=
    exists_sphereMap_coordinateStraightening_homotopy φ hn hx A hA hS hV hVzero
  let R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  have hsub₁ : closedBall x R ⊆ closedBall x R₁ := closedBall_subset_closedBall (min_le_left _ _)
  have hsub₂ : closedBall x R ⊆ closedBall x R₂ := closedBall_subset_closedBall (min_le_right _ _)
  let hP := hP₁.mono hsub₁
  let hzP := fun y (hy : y ∈ closedBall x R) ↦ hzP₁ y (hsub₁ hy)
  let hG := hG₂.mono hsub₂
  let hzG := fun y (hy : y ∈ closedBall x R) ↦ hzG₂ y (hsub₂ hy)
  refine ⟨A, hA, R, hR, hP, hzP, hG, hzG, ?_⟩
  intro r
  let r₁ : Ioc (0 : ℝ) R₁ := ⟨r, r.property.1, r.property.2.trans (min_le_left _ _)⟩
  let r₂ : Ioc (0 : ℝ) R₂ := ⟨r, r.property.1, r.property.2.trans (min_le_right _ _)⟩
  obtain ⟨H₁, _⟩ := h₁ r₁
  obtain ⟨H₂, _⟩ := h₂ r₂
  exact ⟨(H₁.cast (sphereMap_same_radius hP₁ hP hzP₁ hzP r₁ r rfl) rfl).trans
    (H₂.cast (sphereMap_same_radius hQ₂ hQ₁ hzQ₂ hzQ₁ r₂ r₁ rfl)
      (sphereMap_same_radius hG₂ hG hzG₂ hzG r₂ r rfl))⟩

end Poincare.LocalDegree
