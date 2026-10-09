import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates

/-!
A genuine full-circle polar rim chart and the corrected local ball-handle quadrant geometry.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

private theorem planeOfCircle_norm (t : Circle) : ‖planeOfCircle t‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

private theorem rimRadius_pos {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    0 < 1 + (1 / 16 : ℝ) * p.2.1 := by
  have h := (abs_lt.mp hp.1).1
  linarith

private theorem rimMap_norm {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    ‖(neckRim (1 / 16) p).1‖ = 1 + (1 / 16 : ℝ) * p.2.1 := by
  rw [neckRim, norm_smul, Real.norm_of_nonneg (rimRadius_pos hp).le,
    planeOfCircle_norm, mul_one]

private def rimInverse (q : EuclideanSpace ℝ (Fin 2) × ℝ) : Circle × (ℝ × ℝ) :=
  (unitOf (Complex.orthonormalBasisOneI.repr.symm q.1),
    ((‖q.1‖ - 1) / (1 / 16), q.2 / (1 / 16)))

def standardCycleRim : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
    (Circle × (ℝ × ℝ)) (EuclideanSpace ℝ (Fin 2) × ℝ) ∞ where
  toFun := neckRim (1 / 16)
  invFun := rimInverse
  source := univ ×ˢ rimBox 2
  target := {q | 7 / 8 < ‖q.1‖ ∧ ‖q.1‖ < 9 / 8 ∧ |q.2| < 1 / 8}
  map_source' := by
    intro p hp
    change 7 / 8 < ‖(neckRim (1 / 16) p).1‖ ∧
      ‖(neckRim (1 / 16) p).1‖ < 9 / 8 ∧ |(neckRim (1 / 16) p).2| < 1 / 8
    rw [rimMap_norm hp.2]
    have hx := abs_lt.mp hp.2.1
    have hy := abs_lt.mp hp.2.2
    change 7 / 8 < 1 + (1 / 16 : ℝ) * p.2.1 ∧
      1 + (1 / 16 : ℝ) * p.2.1 < 9 / 8 ∧ |(1 / 16 : ℝ) * p.2.2| < 1 / 8
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_lt]
    constructor <;> linarith
  map_target' := by
    intro q hq
    refine ⟨mem_univ _, ?_⟩
    change |(‖q.1‖ - 1) / (1 / 16 : ℝ)| < 2 ∧ |q.2 / (1 / 16 : ℝ)| < 2
    rw [abs_lt, abs_lt]
    have hy := abs_lt.mp hq.2.2
    have ha := hq.1
    have hb := hq.2.1
    constructor <;> constructor <;> norm_num [div_eq_mul_inv] <;> linarith
  left_inv' := by
    intro p hp
    apply Prod.ext
    · change unitOf (Complex.orthonormalBasisOneI.repr.symm
        ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1)) = p.1
      simp only [planeOfCircle, map_smul, LinearIsometryEquiv.symm_apply_apply]
      exact unitOf_smul (rimRadius_pos hp.2) p.1
    · apply Prod.ext
      · change (‖(neckRim (1 / 16) p).1‖ - 1) / (1 / 16 : ℝ) = p.2.1
        rw [rimMap_norm hp.2]
        ring
      · change ((1 / 16 : ℝ) * p.2.2) / (1 / 16 : ℝ) = p.2.2
        ring
  right_inv' := by
    intro q hq
    apply Prod.ext
    · change (1 + (1 / 16 : ℝ) * ((‖q.1‖ - 1) / (1 / 16 : ℝ))) •
        planeOfCircle (unitOf (Complex.orthonormalBasisOneI.repr.symm q.1)) = q.1
      rw [show 1 + (1 / 16 : ℝ) * ((‖q.1‖ - 1) / (1 / 16 : ℝ)) = ‖q.1‖ by ring]
      have h := congrArg Complex.orthonormalBasisOneI.repr
        (norm_smul_unitOf (Complex.orthonormalBasisOneI.repr.symm q.1))
      simpa only [planeOfCircle, map_smul, LinearIsometryEquiv.norm_map,
        LinearIsometryEquiv.apply_symm_apply] using h
    · change (1 / 16 : ℝ) * (q.2 / (1 / 16 : ℝ)) = q.2
      ring
  open_source := isOpen_univ.prod
    ((isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const))
  open_target :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).inter
      ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const))
  contMDiffOn_toFun := by
    have ht : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (fun p : Circle × (ℝ × ℝ) => planeOfCircle p.1) :=
      Complex.orthonormalBasisOneI.repr.contDiff.contMDiff.comp
        (contMDiff_circle_coe.comp contMDiff_fst)
    exact ((contMDiff_const.add (contMDiff_const.mul
      (contDiff_fst.contMDiff.comp contMDiff_snd))).smul ht).prodMk_space
        (contMDiff_const.mul (contDiff_snd.contMDiff.comp contMDiff_snd)) |>.contMDiffOn
  contMDiffOn_invFun := by
    have hn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ) ∞
        (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => ‖q.1‖)
        {q : EuclideanSpace ℝ (Fin 2) × ℝ |
          7 / 8 < ‖q.1‖ ∧ ‖q.1‖ < 9 / 8 ∧ |q.2| < 1 / 8} := by
      intro q hq
      have hz : q.1 ≠ 0 := norm_pos_iff.mp (by linarith [hq.1])
      exact ((contDiffAt_norm ℝ hz).contMDiffAt.comp q
        contDiff_fst.contMDiff.contMDiffAt).contMDiffWithinAt
    have hu : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 1) ∞
        (fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
          unitOf (Complex.orthonormalBasisOneI.repr.symm q.1))
        {q : EuclideanSpace ℝ (Fin 2) × ℝ |
          7 / 8 < ‖q.1‖ ∧ ‖q.1‖ < 9 / 8 ∧ |q.2| < 1 / 8} := contMDiffOn_unitOf.comp
      (Complex.orthonormalBasisOneI.repr.symm.contDiff.contMDiff.comp
        contDiff_fst.contMDiff).contMDiffOn (fun q hq => by
          change Complex.orthonormalBasisOneI.repr.symm q.1 ≠ 0
          intro hz
          have h := congrArg Complex.orthonormalBasisOneI.repr hz
          have hzero : q.1 = 0 := by
            simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using h
          have hlow := hq.1
          rw [hzero, norm_zero] at hlow
          norm_num at hlow)
    exact hu.prodMk ((hn.sub contMDiffOn_const).div_const (1 / 16) |>.prodMk_space
      (contDiff_snd.contMDiff.contMDiffOn.div_const (1 / 16)))

theorem standardCycleRim_source : standardCycleRim.source = univ ×ˢ rimBox 2 := rfl

theorem standardCycleRim_apply (p : Circle × (ℝ × ℝ)) :
    standardCycleRim p = neckRim (1 / 16) p := rfl

theorem standardCycleRim_target : standardCycleRim.target =
    {q | 7 / 8 < ‖q.1‖ ∧ ‖q.1‖ < 9 / 8 ∧ |q.2| < 1 / 8} := rfl

theorem standardCycleRim_ball {p : Circle × (ℝ × ℝ)} :
    (standardCycleRim p).2 ≤ 0 ↔ p.2.2 ≤ 0 := by
  change (1 / 16 : ℝ) * p.2.2 ≤ 0 ↔ p.2.2 ≤ 0
  constructor <;> intro h <;> linarith

theorem standardCycleRim_handle {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ standardCycleRim.source) :
    (0 ≤ (standardCycleRim p).2 ∧ ‖(standardCycleRim p).1‖ ≤ 1) ↔
      (0 ≤ p.2.2 ∧ p.2.1 ≤ 0) := by
  rw [standardCycleRim_apply, rimMap_norm hp.2]
  change (0 ≤ (1 / 16 : ℝ) * p.2.2 ∧ 1 + (1 / 16 : ℝ) * p.2.1 ≤ 1) ↔ _
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem standardCycleRim_quadrant {p : Circle × (ℝ × ℝ)}
    (hx : 0 < p.2.1) (hy : 0 < p.2.2) :
    ¬ ((standardCycleRim p).2 ≤ 0 ∨
      (0 ≤ (standardCycleRim p).2 ∧ ‖(standardCycleRim p).1‖ ≤ 1)) := by
  change ¬ ((1 / 16 : ℝ) * p.2.2 ≤ 0 ∨
    (0 ≤ (1 / 16 : ℝ) * p.2.2 ∧ ‖(1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1‖ ≤ 1))
  rw [norm_smul, Real.norm_of_nonneg (by linarith), planeOfCircle_norm, mul_one]
  rintro (h | ⟨h0, h1⟩) <;> linarith

theorem standardCycleRim_rounding {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ standardCycleRim.source) :
    neckRounding (1 / 16) (standardCycleRim p) = standardRimRounding p.2 := by
  rw [neckRounding, standardCycleRim_apply, rimMap_norm hp.2]
  congr 1
  apply Prod.ext
  · change (1 + (1 / 16 : ℝ) * p.2.1 - 1) / (1 / 16 : ℝ) = p.2.1
    ring
  · change ((1 / 16 : ℝ) * p.2.2) / (1 / 16 : ℝ) = p.2.2
    ring

end GC.GraphManifold.Assembly
