import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BasedTransport
import DifferentialGeometry.Topology.Homotopy.CubeInterior
import DifferentialGeometry.Topology.Homotopy.TransportComposition
import DifferentialGeometry.Topology.Homotopy.TransportContinuity
import DifferentialGeometry.Topology.LoopSpace.CircleCurry
import DifferentialGeometry.Topology.LoopSpace.FiberInclusion
import DifferentialGeometry.Topology.LoopSpace.HigherConnectivity
import DifferentialGeometry.Topology.LoopSpace.AdjunctionTransport

noncomputable section

open Set Bundle Manifold
open scoped Topology unitInterval Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

def sphereCubeVector (x : I^(Fin 2)) : ThreeSpace := by
  classical
  let u : ℝ := (2 * (x 0 : ℝ) - 1) / ((x 0 : ℝ) * (1 - (x 0 : ℝ)))
  let v : ℝ := (2 * (x 1 : ℝ) - 1) / ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
  exact if x ∈ Cube.boundary (Fin 2) then EuclideanSpace.single 2 1 else
    WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
      (u^2+v^2-1) / (1+u^2+v^2)]

theorem sphereCubeVector_norm (x : I^(Fin 2)) : ‖sphereCubeVector x‖ = 1 := by
  classical
  by_cases hb : x ∈ Cube.boundary (Fin 2)
  · simp [sphereCubeVector, hb, PiLp.norm_single]
  let u : ℝ := (2 * (x 0 : ℝ) - 1) / ((x 0 : ℝ) * (1 - (x 0 : ℝ)))
  let v : ℝ := (2 * (x 1 : ℝ) - 1) / ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
  have hd : 1 + u^2 + v^2 ≠ 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
  have hsq : ‖sphereCubeVector x‖^2 = 1 := by
    simp only [sphereCubeVector, if_neg hb]
    change ‖(WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
      (u^2+v^2-1) / (1+u^2+v^2)] : ThreeSpace)‖^2 = 1
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    field_simp [hd]
    ring
  nlinarith [norm_nonneg (sphereCubeVector x)]

private def openCubeCoordinate (t : ℝ) : ℝ := (2 * t - 1) / (t * (1 - t))

private def sphereCubeInteriorParam (p : ℝ × ℝ) : ThreeSpace :=
  WithLp.toLp 2 ![2 * p.1 / (1 + p.1 ^ 2 + p.2 ^ 2), -2 * p.2 / (1 + p.1 ^ 2 + p.2 ^ 2),
    (p.1 ^ 2 + p.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2 ^ 2)]

private lemma sphereCubeVector_eq_param (x : I^(Fin 2)) (hx : x ∉ Cube.boundary (Fin 2)) :
    sphereCubeVector x = sphereCubeInteriorParam
      (openCubeCoordinate ((x 0 : I) : ℝ), openCubeCoordinate ((x 1 : I) : ℝ)) := by
  classical
  simp only [sphereCubeVector, if_neg hx, sphereCubeInteriorParam, openCubeCoordinate]

private lemma vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := by
  rw [Matrix.cons_val_two]
  rfl

private lemma norm_sq_sphereCubeInteriorParam (p : ℝ × ℝ) :
    ‖sphereCubeInteriorParam p‖ ^ 2 = 1 := by
  have hd : 1 + p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by positivity
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [sphereCubeInteriorParam, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    vec3_two]
  field_simp
  ring

private lemma inner_sphereCubeInteriorParam_single (p : ℝ × ℝ) :
    inner ℝ (sphereCubeInteriorParam p) (EuclideanSpace.single 2 1) =
      (p.1 ^ 2 + p.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  rw [EuclideanSpace.inner_single_right]
  simp only [sphereCubeInteriorParam, PiLp.toLp_apply, vec3_two]
  simp

private lemma norm_single_two : ‖(EuclideanSpace.single 2 1 : ThreeSpace)‖ ^ 2 = 1 := by
  rw [PiLp.norm_single]
  norm_num

private lemma norm_sq_sphereCubeInteriorParam_sub_single (p : ℝ × ℝ) :
    ‖sphereCubeInteriorParam p - EuclideanSpace.single 2 1‖ ^ 2 =
      4 / (p.1 ^ 2 + p.2 ^ 2 + 1) := by
  have hd : 1 + p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by positivity
  rw [norm_sub_sq_real, norm_sq_sphereCubeInteriorParam, inner_sphereCubeInteriorParam_single,
    norm_single_two]
  field_simp
  ring

private lemma continuous_sphereCubeInteriorParam : Continuous sphereCubeInteriorParam := by
  have hD : Continuous fun p : ℝ × ℝ => 1 + p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  have hDne : ∀ p : ℝ × ℝ, 1 + p.1 ^ 2 + p.2 ^ 2 ≠ 0 := fun p => by positivity
  have hA : Continuous fun p : ℝ × ℝ => 2 * p.1 := by fun_prop
  have hB : Continuous fun p : ℝ × ℝ => 2 * p.2 := by fun_prop
  have hC : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 - 1 := by fun_prop
  unfold sphereCubeInteriorParam
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i <;>
    simp only [neg_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    first
      | exact hA.div₀ hD hDne
      | exact hB.neg.div₀ hD hDne
      | exact hC.div₀ hD hDne

private lemma openCubeCoordinate_eq_sub (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    openCubeCoordinate t = 1 / (1 - t) - 1 / t := by
  unfold openCubeCoordinate
  field_simp
  ring

private lemma continuousAt_openCubeCoordinate (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    ContinuousAt openCubeCoordinate t := by
  have hsub : ContinuousAt (fun s : ℝ => 1 / (1 - s) - 1 / s) t := by
    refine ContinuousAt.sub ?_ ?_
    · exact ContinuousAt.div continuousAt_const (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.mpr (Ne.symm h1))
    · exact ContinuousAt.div continuousAt_const continuousAt_id h0
  refine hsub.congr ?_
  filter_upwards [isOpen_ne.mem_nhds h1, isOpen_ne.mem_nhds h0] with s hs1 hs0
  exact (openCubeCoordinate_eq_sub s hs0 hs1).symm

private lemma continuousAt_cubeCoords_two (z : I^(Fin 2)) (hz : z ∉ Cube.boundary (Fin 2)) :
    ContinuousAt (fun z' : I^(Fin 2) =>
      (openCubeCoordinate ((z' 0 : I) : ℝ), openCubeCoordinate ((z' 1 : I) : ℝ))) z := by
  have hmem : ∀ i : Fin 2, ((z i : I) : ℝ) ≠ 0 ∧ ((z i : I) : ℝ) ≠ 1 := by
    intro i
    constructor
    · intro hc
      exact hz ⟨i, Or.inl (Subtype.ext hc)⟩
    · intro hc
      exact hz ⟨i, Or.inr (Subtype.ext hc)⟩
  have hc : ∀ i : Fin 2, ContinuousAt (fun z' : I^(Fin 2) =>
      openCubeCoordinate ((z' i : I) : ℝ)) z := by
    intro i
    have h1 : ContinuousAt (fun z' : I^(Fin 2) => ((z' i : I) : ℝ)) z :=
      ContinuousAt.comp continuous_subtype_val.continuousAt (continuous_apply i).continuousAt
    exact ContinuousAt.comp (f := fun z' : I^(Fin 2) => ((z' i : I) : ℝ))
      (continuousAt_openCubeCoordinate _ (hmem i).1 (hmem i).2) h1
  exact ContinuousAt.prodMk (hc 0) (hc 1)

private lemma one_div_two_mul_le_abs_openCubeCoordinate_left (t : ℝ) (h0 : 0 < t)
    (h1 : t ≤ 1 / 4) : 1 / (2 * t) ≤ |openCubeCoordinate t| := by
  unfold openCubeCoordinate
  have h2 : (0 : ℝ) < 1 - t := by linarith
  have hpos : 0 < t * (1 - t) := mul_pos h0 h2
  have hneg : 2 * t - 1 < 0 := by linarith
  have hval : |(2 * t - 1) / (t * (1 - t))| = (1 - 2 * t) / (t * (1 - t)) := by
    rw [abs_div, abs_of_pos hpos, abs_of_neg hneg]
    ring_nf
  rw [hval, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t) hpos]
  nlinarith

private lemma one_div_two_mul_le_abs_openCubeCoordinate_right (t : ℝ) (h0 : t < 1)
    (h1 : 3 / 4 ≤ t) : 1 / (2 * (1 - t)) ≤ |openCubeCoordinate t| := by
  unfold openCubeCoordinate
  have h2 : (0 : ℝ) < 1 - t := by linarith
  have ht0 : 0 < t := by linarith
  have hpos : 0 < t * (1 - t) := mul_pos ht0 h2
  have hpos' : 0 < 2 * t - 1 := by linarith
  have hval : |(2 * t - 1) / (t * (1 - t))| = (2 * t - 1) / (t * (1 - t)) := by
    rw [abs_div, abs_of_pos hpos, abs_of_pos hpos']
  rw [hval, div_le_div_iff₀ (by positivity) hpos]
  nlinarith

private lemma tendsto_sphereCubeVector_of_boundary (x : I^(Fin 2)) (i : Fin 2)
    (hi : ((x i : I) : ℝ) = 0 ∨ ((x i : I) : ℝ) = 1) :
    Filter.Tendsto sphereCubeVector (𝓝 x) (𝓝 (EuclideanSpace.single 2 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨δ, hδ1, hδε, hδpos⟩ : ∃ δ : ℝ, δ ≤ 1 / 4 ∧ δ ≤ ε / 8 ∧ 0 < δ :=
    ⟨min (1 / 4) (ε / 8), min_le_left _ _, min_le_right _ _, lt_min (by norm_num) hε8⟩
  have core : ∀ x' : I^(Fin 2), x' ∉ Cube.boundary (Fin 2) →
      1 / (2 * δ) ≤ |openCubeCoordinate ((x' i : I) : ℝ)| →
      dist (sphereCubeVector x') (EuclideanSpace.single 2 1) < ε := by
    intro x' hb' hbound
    have hval : sphereCubeVector x' =
        sphereCubeInteriorParam (openCubeCoordinate ((x' 0 : I) : ℝ),
          openCubeCoordinate ((x' 1 : I) : ℝ)) :=
      sphereCubeVector_eq_param x' hb'
    have hsum : (1 / (2 * δ)) ^ 2 ≤ (openCubeCoordinate ((x' 0 : I) : ℝ)) ^ 2 +
        (openCubeCoordinate ((x' 1 : I) : ℝ)) ^ 2 := by
      have hsq : (1 / (2 * δ)) ^ 2 ≤ (openCubeCoordinate ((x' i : I) : ℝ)) ^ 2 := by
        rw [← sq_abs (openCubeCoordinate ((x' i : I) : ℝ))]
        exact pow_le_pow_left₀ (by positivity) hbound 2
      have hle : (openCubeCoordinate ((x' i : I) : ℝ)) ^ 2 ≤
          ∑ j : Fin 2, (openCubeCoordinate ((x' j : I) : ℝ)) ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin 2 =>
          (openCubeCoordinate ((x' j : I) : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      rw [Fin.sum_univ_two] at hle
      exact le_trans hsq hle
    have hpos : 0 < (1 / (2 * δ)) ^ 2 := by positivity
    have h4 : 4 / ((openCubeCoordinate ((x' 0 : I) : ℝ)) ^ 2 +
        (openCubeCoordinate ((x' 1 : I) : ℝ)) ^ 2 + 1) < ε ^ 2 := by
      have hmono : 4 / ((openCubeCoordinate ((x' 0 : I) : ℝ)) ^ 2 +
          (openCubeCoordinate ((x' 1 : I) : ℝ)) ^ 2 + 1) ≤ 4 / (1 / (2 * δ)) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
      have h16 : 4 / (1 / (2 * δ)) ^ 2 = 16 * δ ^ 2 := by
        field_simp
        ring
      have hδ2 : 16 * δ ^ 2 ≤ ε ^ 2 / 4 := by nlinarith [hδε, hδpos, hε]
      have hfin : ε ^ 2 / 4 < ε ^ 2 := by nlinarith [hε]
      linarith [hmono, h16 ▸ hmono, hδ2, hfin]
    rw [hval, dist_eq_norm]
    have hsq : ‖sphereCubeInteriorParam (openCubeCoordinate ((x' 0 : I) : ℝ),
        openCubeCoordinate ((x' 1 : I) : ℝ)) - EuclideanSpace.single 2 1‖ ^ 2 < ε ^ 2 := by
      rw [norm_sq_sphereCubeInteriorParam_sub_single]
      exact h4
    nlinarith [norm_nonneg (sphereCubeInteriorParam
      (openCubeCoordinate ((x' 0 : I) : ℝ), openCubeCoordinate ((x' 1 : I) : ℝ)) -
        EuclideanSpace.single 2 1)]
  rcases hi with hi | hi
  · have hU : {x' : I^(Fin 2) | ((x' i : I) : ℝ) < δ} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds ?_ ?_
      · exact isOpen_lt (continuous_subtype_val.comp (continuous_apply i)) continuous_const
      · simp only [Set.mem_ofPred_eq]
        rw [hi]
        exact hδpos
    filter_upwards [hU] with x' hx'i
    by_cases hb' : x' ∈ Cube.boundary (Fin 2)
    · have hbval : sphereCubeVector x' = EuclideanSpace.single 2 1 := by
        simp only [sphereCubeVector, hb', if_true]
      rw [hbval, dist_self]
      exact hε
    · refine core x' hb' ?_
      have hne : ((x' i : I) : ℝ) ≠ 0 := fun hc => hb' ⟨i, Or.inl (Subtype.ext hc)⟩
      have hge : (0 : ℝ) ≤ ((x' i : I) : ℝ) := (x' i).2.1
      have hgt : 0 < ((x' i : I) : ℝ) := lt_of_le_of_ne hge (Ne.symm hne)
      have h1 : 1 / (2 * δ) ≤ 1 / (2 * ((x' i : I) : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact le_trans h1
        (one_div_two_mul_le_abs_openCubeCoordinate_left _ hgt (by linarith [hx'i, hδ1]))
  · have hU : {x' : I^(Fin 2) | 1 - δ < ((x' i : I) : ℝ)} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds ?_ ?_
      · exact isOpen_lt continuous_const (continuous_subtype_val.comp (continuous_apply i))
      · simp only [Set.mem_ofPred_eq]
        rw [hi]
        linarith
    filter_upwards [hU] with x' hx'i
    by_cases hb' : x' ∈ Cube.boundary (Fin 2)
    · have hbval : sphereCubeVector x' = EuclideanSpace.single 2 1 := by
        simp only [sphereCubeVector, hb', if_true]
      rw [hbval, dist_self]
      exact hε
    · refine core x' hb' ?_
      have hne : ((x' i : I) : ℝ) ≠ 1 := fun hc => hb' ⟨i, Or.inr (Subtype.ext hc)⟩
      have hle : ((x' i : I) : ℝ) ≤ 1 := (x' i).2.2
      have hlt : ((x' i : I) : ℝ) < 1 := lt_of_le_of_ne hle hne
      have h1m : 1 - ((x' i : I) : ℝ) < δ := by linarith
      have h1 : 1 / (2 * δ) ≤ 1 / (2 * (1 - ((x' i : I) : ℝ))) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact le_trans h1
        (one_div_two_mul_le_abs_openCubeCoordinate_right _ hlt (by linarith [h1m, hδ1]))

theorem sphereCubeVector_continuous : Continuous sphereCubeVector := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Cube.boundary (Fin 2)
  · have hxval : sphereCubeVector x = EuclideanSpace.single 2 1 := by
      simp only [sphereCubeVector, hx, if_true]
    rw [ContinuousAt, hxval]
    obtain ⟨i, hi | hi⟩ := hx
    · exact tendsto_sphereCubeVector_of_boundary x i (Or.inl (by rw [hi]; rfl))
    · exact tendsto_sphereCubeVector_of_boundary x i (Or.inr (by rw [hi]; rfl))
  · have hU : (Cube.boundary (Fin 2))ᶜ ∈ 𝓝 x := by
      refine IsOpen.mem_nhds ?_ hx
      rw [← DifferentialGeometry.Topology.cubeInterior_eq_compl_boundary]
      exact DifferentialGeometry.Topology.isOpen_cubeInterior (Fin 2)
    have heq : (fun x' : I^(Fin 2) => sphereCubeInteriorParam
          (openCubeCoordinate ((x' 0 : I) : ℝ), openCubeCoordinate ((x' 1 : I) : ℝ))) =ᶠ[𝓝 x]
        (fun x' : I^(Fin 2) => sphereCubeVector x') := by
      filter_upwards [hU] with x' hx'
      exact (sphereCubeVector_eq_param x' hx').symm
    refine ContinuousAt.congr ?_ heq
    exact ContinuousAt.comp (f := fun x' : I^(Fin 2) =>
        (openCubeCoordinate ((x' 0 : I) : ℝ), openCubeCoordinate ((x' 1 : I) : ℝ)))
      continuous_sphereCubeInteriorParam.continuousAt (continuousAt_cubeCoords_two x hx)


def sphereCubeParameter : C(I^(Fin 2), Sphere 2) :=
  ⟨fun x => ⟨sphereCubeVector x, by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereCubeVector_norm x⟩,
    sphereCubeVector_continuous.subtype_mk (fun x => by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereCubeVector_norm x)⟩

private def sfMap (t : ℝ) : ℝ := (2 * t - 1) / (t * (1 - t))

private def sfParam (p : ℝ × ℝ) : ThreeSpace :=
  WithLp.toLp 2 ![2 * p.1 / (1 + p.1 ^ 2 + p.2 ^ 2), -2 * p.2 / (1 + p.1 ^ 2 + p.2 ^ 2),
    (p.1 ^ 2 + p.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2 ^ 2)]

private lemma sf_single_eq : (EuclideanSpace.single 2 1 : ThreeSpace) = PiLp.single 2 2 1 := rfl

private lemma sf_coe (x : I^(Fin 2)) :
    ((sphereCubeParameter x : Sphere 2) : ThreeSpace) = sphereCubeVector x := rfl

private lemma sf_sphereCubeVector_eq_param (x : I^(Fin 2)) (hx : x ∉ Cube.boundary (Fin 2)) :
    sphereCubeVector x = sfParam (sfMap ((x 0 : I) : ℝ), sfMap ((x 1 : I) : ℝ)) := by
  classical
  simp only [sphereCubeVector, if_neg hx, sfParam, sfMap]

private lemma sf_sphereCubeVector_eq_north (x : I^(Fin 2)) (hx : x ∈ Cube.boundary (Fin 2)) :
    sphereCubeVector x = EuclideanSpace.single 2 1 := by
  classical
  simp only [sphereCubeVector, if_pos hx]

private lemma sf_north_zero : ((EuclideanSpace.single 2 1 : ThreeSpace)) 0 = 0 := by
  have h : ¬ ((0 : Fin 3) = 2) := by decide
  simp only [sf_single_eq, PiLp.single_apply, h, if_false]

private lemma sf_north_one : ((EuclideanSpace.single 2 1 : ThreeSpace)) 1 = 0 := by
  have h : ¬ ((1 : Fin 3) = 2) := by decide
  simp only [sf_single_eq, PiLp.single_apply, h, if_false]

private lemma sf_north_two : ((EuclideanSpace.single 2 1 : ThreeSpace)) 2 = 1 := by
  simp only [sf_single_eq, PiLp.single_apply]
  norm_num

private lemma sf_param_zero (p : ℝ × ℝ) :
    sfParam p 0 = 2 * p.1 / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  simp only [sfParam, PiLp.toLp_apply, Matrix.cons_val_zero]

private lemma sf_param_one (p : ℝ × ℝ) :
    sfParam p 1 = -2 * p.2 / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  simp only [sfParam, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]

private lemma sf_param_two (p : ℝ × ℝ) :
    sfParam p 2 = (p.1 ^ 2 + p.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  simp only [sfParam, PiLp.toLp_apply]
  rw [Matrix.cons_val_two]
  rfl

private lemma sf_denom_pos (p : ℝ × ℝ) : 0 < p.1 ^ 2 + p.2 ^ 2 + 1 := by positivity

private lemma sf_denom_ne (p : ℝ × ℝ) : p.1 ^ 2 + p.2 ^ 2 + 1 ≠ 0 :=
  ne_of_gt (sf_denom_pos p)

private lemma sf_norm_sq (p : ℝ × ℝ) : ‖sfParam p‖ ^ 2 = 1 := by
  have hd := sf_denom_ne p
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [sf_param_zero, sf_param_one, sf_param_two]
  field_simp
  ring

private lemma sf_norm_sq_sub (p : ℝ × ℝ) :
    ‖sfParam p - EuclideanSpace.single 2 1‖ ^ 2 = 4 / (p.1 ^ 2 + p.2 ^ 2 + 1) := by
  have hd := sf_denom_ne p
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [PiLp.sub_apply, sf_north_zero, sf_north_one, sf_north_two, sub_zero,
    sf_param_zero, sf_param_one, sf_param_two]
  field_simp
  ring

private lemma sf_recover_zero (p : ℝ × ℝ) :
    2 * (sfParam p 0) / ‖sfParam p - EuclideanSpace.single 2 1‖ ^ 2 = p.1 := by
  have hd := sf_denom_ne p
  rw [sf_param_zero, sf_norm_sq_sub]
  field_simp
  ring

private lemma sf_recover_one (p : ℝ × ℝ) :
    -2 * (sfParam p 1) / ‖sfParam p - EuclideanSpace.single 2 1‖ ^ 2 = p.2 := by
  have hd := sf_denom_ne p
  rw [sf_param_one, sf_norm_sq_sub]
  field_simp
  ring

private lemma sf_param_injective : Function.Injective sfParam := by
  intro p q hpq
  have h0 : p.1 = q.1 := by
    rw [← sf_recover_zero p, ← sf_recover_zero q, hpq]
  have h1 : p.2 = q.2 := by
    rw [← sf_recover_one p, ← sf_recover_one q, hpq]
  exact Prod.ext h0 h1

private lemma sf_param_ne_north (p : ℝ × ℝ) : sfParam p ≠ EuclideanSpace.single 2 1 := by
  intro h
  have h2 : ‖sfParam p - EuclideanSpace.single 2 1‖ ^ 2 = 0 := by
    rw [h, sub_self]
    simp
  rw [sf_norm_sq_sub] at h2
  have h3 : 0 < 4 / (p.1 ^ 2 + p.2 ^ 2 + 1) := by positivity
  linarith

private lemma sf_map_eq_sub (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    sfMap t = 1 / (1 - t) - 1 / t := by
  unfold sfMap
  field_simp
  ring

private lemma sf_map_injective {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t)
    (ht1 : t < 1) (h : sfMap s = sfMap t) : s = t := by
  have hs0' : s ≠ 0 := ne_of_gt hs0
  have hs1' : s ≠ 1 := ne_of_lt hs1
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have ht1' : t ≠ 1 := ne_of_lt ht1
  have hfac : 0 < 1 - s - t + 2 * s * t := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - s) (by linarith : (0 : ℝ) < 1 - t),
      mul_pos hs0 ht0]
  have h2 : (s - t) * (1 - s - t + 2 * s * t) = 0 := by
    simp only [sfMap] at h
    rw [div_eq_div_iff (mul_ne_zero hs0' (by linarith)) (mul_ne_zero ht0' (by linarith))] at h
    nlinarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 (ne_of_gt hfac)

private lemma sf_map_surjective (u : ℝ) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sfMap t = u := by
  set δ : ℝ := 1 / (3 + |u|) with hδ
  have h3u : 0 < 3 + |u| := by positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδlt : δ < 1 := by
    rw [hδ, div_lt_one h3u]
    linarith [abs_nonneg u]
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ h3u (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg u]
  have hone : 1 / δ = 3 + |u| := by
    rw [hδ, one_div_one_div]
  have hleft : sfMap δ < u := by
    have h0 : 1 / (1 - δ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      linarith
    rw [sf_map_eq_sub δ (ne_of_gt hδpos) (by linarith)]
    nlinarith [h0, hone, neg_le_abs u]
  have hright : u < sfMap (1 - δ) := by
    have h0 : 1 / (1 - (1 - δ)) = 1 / δ := by ring_nf
    have h1 : 1 / (1 - δ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      linarith
    rw [sf_map_eq_sub (1 - δ) (by linarith) (by linarith), h0]
    nlinarith [h1, hone, le_abs_self u]
  have hcont : ContinuousOn sfMap (Icc δ (1 - δ)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hδpos ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 (by linarith)
    exact mul_ne_zero (ne_of_gt ht0) (by linarith)
  have hmem : u ∈ Icc (sfMap δ) (sfMap (1 - δ)) := ⟨le_of_lt hleft, le_of_lt hright⟩
  obtain ⟨t, ht, htu⟩ := (intermediate_value_Icc (by linarith : δ ≤ 1 - δ) hcont) hmem
  exact ⟨t, lt_of_lt_of_le hδpos ht.1, lt_of_le_of_lt ht.2 (by linarith), htu⟩

private lemma sf_not_boundary_coords {y : I^(Fin 2)} (hy : y ∉ Cube.boundary (Fin 2))
    (i : Fin 2) : 0 < ((y i : I) : ℝ) ∧ ((y i : I) : ℝ) < 1 := by
  have h0 : ((y i : I) : ℝ) ≠ 0 := fun hc => hy ⟨i, Or.inl (Subtype.ext hc)⟩
  have h1 : ((y i : I) : ℝ) ≠ 1 := fun hc => hy ⟨i, Or.inr (Subtype.ext hc)⟩
  exact ⟨lt_of_le_of_ne (y i).2.1 (Ne.symm h0), lt_of_le_of_ne (y i).2.2 h1⟩

private lemma sf_sphereCubeVector_eq_iff (a b : I^(Fin 2)) :
    sphereCubeVector a = sphereCubeVector b ↔
      a = b ∨ (a ∈ Cube.boundary (Fin 2) ∧ b ∈ Cube.boundary (Fin 2)) := by
  classical
  constructor
  · intro h
    by_cases ha : a ∈ Cube.boundary (Fin 2)
    · by_cases hb : b ∈ Cube.boundary (Fin 2)
      · exact Or.inr ⟨ha, hb⟩
      · rw [sf_sphereCubeVector_eq_north a ha, sf_sphereCubeVector_eq_param b hb] at h
        exact absurd h.symm (sf_param_ne_north _)
    · by_cases hb : b ∈ Cube.boundary (Fin 2)
      · rw [sf_sphereCubeVector_eq_param a ha, sf_sphereCubeVector_eq_north b hb] at h
        exact absurd h (sf_param_ne_north _)
      · refine Or.inl (funext fun i => Subtype.ext ?_)
        have hp : sfParam (sfMap ((a 0 : I) : ℝ), sfMap ((a 1 : I) : ℝ)) =
            sfParam (sfMap ((b 0 : I) : ℝ), sfMap ((b 1 : I) : ℝ)) := by
          rw [← sf_sphereCubeVector_eq_param a ha, ← sf_sphereCubeVector_eq_param b hb]
          exact h
        have hpq := sf_param_injective hp
        have h0 := sf_not_boundary_coords ha 0
        have h1 := sf_not_boundary_coords hb 0
        have h2 := sf_not_boundary_coords ha 1
        have h3 := sf_not_boundary_coords hb 1
        fin_cases i
        · exact sf_map_injective h0.1 h0.2 h1.1 h1.2 (congrArg Prod.fst hpq)
        · exact sf_map_injective h2.1 h2.2 h3.1 h3.2 (congrArg Prod.snd hpq)
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [sf_sphereCubeVector_eq_north a ha, sf_sphereCubeVector_eq_north b hb]

private lemma sf_param_recover_aux (a b c S : ℝ) (hS : S ≠ 0)
    (hp : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hS2 : S = 2 - 2 * c) :
    sfParam (2 * a / S, -2 * b / S) = WithLp.toLp 2 ![a, b, c] := by
  have hD : 1 + (2 * a / S) ^ 2 + (-2 * b / S) ^ 2 = 4 / S := by
    field_simp
    nlinarith [hp, hS2]
  have hE : (2 * a / S) ^ 2 + (-2 * b / S) ^ 2 - 1 = 4 * c / S := by
    field_simp
    nlinarith [hp, hS2]
  apply PiLp.ext
  intro i
  fin_cases i
  · change sfParam (2 * a / S, -2 * b / S) 0 = a
    rw [sf_param_zero, hD]
    field_simp
    ring
  · change sfParam (2 * a / S, -2 * b / S) 1 = b
    rw [sf_param_one, hD]
    field_simp
    ring
  · change sfParam (2 * a / S, -2 * b / S) 2 = c
    rw [sf_param_two, hD, hE]
    field_simp

private lemma sf_param_recover (v : ThreeSpace) (hv : ‖v‖ = 1)
    (hne : v ≠ EuclideanSpace.single 2 1) :
    sfParam (2 * v 0 / ‖v - EuclideanSpace.single 2 1‖ ^ 2,
      -2 * v 1 / ‖v - EuclideanSpace.single 2 1‖ ^ 2) = v := by
  have hv2 : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    rw [Fin.sum_univ_three, hv] at h
    norm_num at h
    exact h.symm
  have hTne : ‖v - EuclideanSpace.single 2 1‖ ^ 2 ≠ 0 :=
    ne_of_gt (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2)
  have hT : ‖v - EuclideanSpace.single 2 1‖ ^ 2 = 2 - 2 * (v 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp only [PiLp.sub_apply, sf_north_zero, sf_north_one, sf_north_two, sub_zero]
    nlinarith [hv2]
  rw [sf_param_recover_aux (v 0) (v 1) (v 2) _ hTne hv2 hT]
  apply PiLp.ext
  intro i
  fin_cases i
  · change (WithLp.toLp 2 ![v 0, v 1, v 2] : ThreeSpace) 0 = v 0
    rw [PiLp.toLp_apply, Matrix.cons_val_zero]
  · change (WithLp.toLp 2 ![v 0, v 1, v 2] : ThreeSpace) 1 = v 1
    rw [PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
  · change (WithLp.toLp 2 ![v 0, v 1, v 2] : ThreeSpace) 2 = v 2
    rw [PiLp.toLp_apply, Matrix.cons_val_two]
    rfl

private lemma sf_sphereCubeParameter_surjective : Function.Surjective sphereCubeParameter := by
  intro z
  by_cases hz : (z : ThreeSpace) = EuclideanSpace.single 2 1
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [sf_coe, sf_sphereCubeVector_eq_north 0 ⟨0, Or.inl rfl⟩]
    exact hz.symm
  · obtain ⟨s, hs0, hs1, hsmap⟩ := sf_map_surjective
      (2 * (z : ThreeSpace) 0 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2)
    obtain ⟨r, hr0, hr1, hrmap⟩ := sf_map_surjective
      (-2 * (z : ThreeSpace) 1 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2)
    let x : I^(Fin 2) := ![⟨s, le_of_lt hs0, le_of_lt hs1⟩, ⟨r, le_of_lt hr0, le_of_lt hr1⟩]
    have hx0 : (x 0 : I) = ⟨s, le_of_lt hs0, le_of_lt hs1⟩ := by
      simp only [x, Matrix.cons_val_zero]
    have hx1 : (x 1 : I) = ⟨r, le_of_lt hr0, le_of_lt hr1⟩ := by
      simp only [x, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hxb : x ∉ Cube.boundary (Fin 2) := by
      rintro ⟨i, hi⟩
      fin_cases i
      · rcases hi with hi | hi
        · exact absurd (congrArg Subtype.val hi) (ne_of_gt hs0)
        · exact absurd (congrArg Subtype.val hi) (ne_of_lt hs1)
      · rcases hi with hi | hi
        · exact absurd (congrArg Subtype.val hi) (ne_of_gt hr0)
        · exact absurd (congrArg Subtype.val hi) (ne_of_lt hr1)
    refine ⟨x, ?_⟩
    have hscene : ‖(z : ThreeSpace)‖ = 1 := by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using z.2
    have hpair : (sfMap ((x 0 : I) : ℝ), sfMap ((x 1 : I) : ℝ)) =
        (2 * (z : ThreeSpace) 0 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2,
          -2 * (z : ThreeSpace) 1 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2) := by
      rw [hx0, hx1]
      refine Prod.ext ?_ ?_
      · simpa using hsmap
      · simpa using hrmap
    apply Subtype.ext
    rw [sf_coe, sf_sphereCubeVector_eq_param x hxb, hpair]
    exact sf_param_recover (z : ThreeSpace) hscene hz

variable {X : Type u} [TopologicalSpace X] {x : X}

private lemma sf_factorsThrough (c : GenLoop (Fin 2) X x) :
    Function.FactorsThrough c.val sphereCubeParameter := by
  intro a b hab
  have hv : sphereCubeVector a = sphereCubeVector b := by
    simpa only [sf_coe] using congrArg (fun y : Sphere 2 => (y : ThreeSpace)) hab
  rcases (sf_sphereCubeVector_eq_iff a b).mp hv with h | ⟨ha, hb⟩
  · rw [h]
  · rw [c.property a ha, c.property b hb]

theorem exists_unique_sphereFactor (c : GenLoop (Fin 2) X x) :
    ∃! f : C(Sphere 2, X), f.comp sphereCubeParameter = c.val := by
  have hq : Topology.IsQuotientMap sphereCubeParameter :=
    Topology.IsQuotientMap.of_surjective_continuous sf_sphereCubeParameter_surjective
      sphereCubeParameter.continuous
  refine ⟨hq.lift c.val (sf_factorsThrough c), hq.lift_comp c.val (sf_factorsThrough c), ?_⟩
  intro f hf
  have h1 : f.comp sphereCubeParameter = (hq.lift c.val (sf_factorsThrough c)).comp
      sphereCubeParameter := by
    rw [hf, hq.lift_comp]
  refine ContinuousMap.ext fun y => ?_
  obtain ⟨a, ha⟩ := sf_sphereCubeParameter_surjective y
  rw [← ha]
  exact congrFun (congrArg (fun g : C(I^(Fin 2), X) => (g : (I^(Fin 2)) → X)) h1) a

def sphereFactor (c : GenLoop (Fin 2) X x) : C(Sphere 2, X) :=
  Classical.choose (exists_unique_sphereFactor c)

theorem sphereFactor_eq (c : GenLoop (Fin 2) X x) :
    (sphereFactor c).comp sphereCubeParameter = c.val :=
  (Classical.choose_spec (exists_unique_sphereFactor c)).1

theorem sphereFactor_homotopic {c d : GenLoop (Fin 2) X x}
    (h : c.val.HomotopicRel d.val (Cube.boundary (Fin 2))) :
    ContinuousMap.Homotopic (sphereFactor c) (sphereFactor d) := by
  obtain ⟨H⟩ := h
  let Q : C(I × I^(Fin 2), I × Sphere 2) :=
    ⟨fun p => (p.1, sphereCubeParameter p.2),
      continuous_fst.prodMk (sphereCubeParameter.continuous.comp continuous_snd)⟩
  have hQsurj : Function.Surjective Q := by
    rintro ⟨t, y⟩
    obtain ⟨a, ha⟩ := sf_sphereCubeParameter_surjective y
    refine ⟨(t, a), ?_⟩
    exact Prod.ext rfl ha
  have hQ : Topology.IsQuotientMap Q :=
    Topology.IsQuotientMap.of_surjective_continuous hQsurj Q.continuous
  have hfac : Function.FactorsThrough H.toContinuousMap Q := by
    intro p q hpq
    have ht : p.1 = q.1 := (Prod.ext_iff.mp hpq).1
    have hq2 : sphereCubeParameter p.2 = sphereCubeParameter q.2 := (Prod.ext_iff.mp hpq).2
    have hv : sphereCubeVector p.2 = sphereCubeVector q.2 := by
      simpa only [sf_coe] using congrArg (fun y : Sphere 2 => (y : ThreeSpace)) hq2
    rcases (sf_sphereCubeVector_eq_iff p.2 q.2).mp hv with hpq2 | ⟨hp, hq'⟩
    · exact congrArg H.toContinuousMap (Prod.ext ht hpq2)
    · exact ((H.eq_fst p.1 hp).trans (c.property p.2 hp)).trans
        (((H.eq_fst q.1 hq').trans (c.property q.2 hq')).symm)
  let F : C(I × Sphere 2, X) := hQ.lift H.toContinuousMap hfac
  have hF : F.comp Q = H.toContinuousMap := hQ.lift_comp H.toContinuousMap hfac
  have hzero_fun (a : I^(Fin 2)) : F (0, sphereCubeParameter a) = c.val a := by
    have h := congrFun (congrArg (fun g : C(I × I^(Fin 2), X) =>
      (g : I × (I^(Fin 2)) → X)) hF) (0, a)
    exact h.trans (H.apply_zero a)
  have hone_fun (a : I^(Fin 2)) : F (1, sphereCubeParameter a) = d.val a := by
    have h := congrFun (congrArg (fun g : C(I × I^(Fin 2), X) =>
      (g : I × (I^(Fin 2)) → X)) hF) (1, a)
    exact h.trans (H.apply_one a)
  let K0 : C(Sphere 2, I × Sphere 2) :=
    ⟨fun y => (0, y), continuous_const.prodMk continuous_id⟩
  let K1 : C(Sphere 2, I × Sphere 2) :=
    ⟨fun y => (1, y), continuous_const.prodMk continuous_id⟩
  have hzero : (F.comp K0).comp sphereCubeParameter = c.val := by
    ext a
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, K0] using hzero_fun a
  have hone : (F.comp K1).comp sphereCubeParameter = d.val := by
    ext a
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, K1] using hone_fun a
  have hK0 : F.comp K0 = sphereFactor c :=
    (Classical.choose_spec (exists_unique_sphereFactor c)).2 (F.comp K0) hzero
  have hK1 : F.comp K1 = sphereFactor d :=
    (Classical.choose_spec (exists_unique_sphereFactor d)).2 (F.comp K1) hone
  refine ⟨{ toContinuousMap := F, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro y
    have h := congrFun (congrArg (fun g : C(Sphere 2, X) => (g : Sphere 2 → X)) hK0) y
    change F (0, y) = sphereFactor c y
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, K0] using h
  · intro y
    have h := congrFun (congrArg (fun g : C(Sphere 2, X) => (g : Sphere 2 → X)) hK1) y
    change F (1, y) = sphereFactor d y
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, K1] using h


private theorem sphereCubeParameter_eq_of_mem_boundary {v : I^(Fin 2)}
    (hv : v ∈ Cube.boundary (Fin 2)) :
    sphereCubeParameter v = sphereCubeParameter 0 := by
  apply Subtype.ext
  change sphereCubeVector v = sphereCubeVector 0
  rw [sf_sphereCubeVector_eq_north v hv,
    sf_sphereCubeVector_eq_north 0 ⟨0, Or.inl rfl⟩]

private def sphereCubeFamilyQuotient (K : Type v) [TopologicalSpace K] :
    C(K × I^(Fin 2), K × Sphere 2) :=
  ContinuousMap.prodMap (ContinuousMap.id K) sphereCubeParameter

private theorem isQuotientMap_sphereCubeFamilyQuotient (K : Type v) [TopologicalSpace K] :
    Topology.IsQuotientMap (sphereCubeFamilyQuotient K) := by
  have hp : IsProperMap (sphereCubeFamilyQuotient K) :=
    isProperMap_id.prodMap sphereCubeParameter.continuous.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((Function.surjective_id : Function.Surjective (id : K → K)).prodMap
      sf_sphereCubeParameter_surjective)

private theorem sphereCubeFamily_factors {K : Type v} [TopologicalSpace K]
    (F : C(K × I^(Fin 2), X)) (b : C(K, X))
    (hb : ∀ k v, v ∈ Cube.boundary (Fin 2) → F (k, v) = b k) :
    ∀ k v v', sphereCubeParameter v = sphereCubeParameter v' → F (k, v) = F (k, v') := by
  intro k v v' hv
  have hvv : sphereCubeVector v = sphereCubeVector v' := by
    change ((sphereCubeParameter v : Sphere 2) : ThreeSpace) =
      ((sphereCubeParameter v' : Sphere 2) : ThreeSpace)
    exact congrArg (fun y : Sphere 2 => (y : ThreeSpace)) hv
  rcases (sf_sphereCubeVector_eq_iff v v').mp hvv with h | ⟨h1, h2⟩
  · rw [h]
  · rw [hb k v h1, hb k v' h2]

private def sphereCubeFamilyDescendValue {K : Type v} [TopologicalSpace K]
    (F : C(K × I^(Fin 2), X))
    (hfac : ∀ k v v', sphereCubeParameter v = sphereCubeParameter v' → F (k, v) = F (k, v')) :
    C(K × Sphere 2, X) :=
  ⟨fun z => F (z.1, Classical.choose (sf_sphereCubeParameter_surjective z.2)), by
    refine (isQuotientMap_sphereCubeFamilyQuotient K).continuous_iff.mpr ?_
    refine F.continuous.congr ?_
    intro z
    exact (hfac z.1 _ _ (Classical.choose_spec
      (sf_sphereCubeParameter_surjective (sphereCubeParameter z.2)))).symm⟩

private theorem sphereCubeFamilyDescendValue_projection {K : Type v} [TopologicalSpace K]
    (F : C(K × I^(Fin 2), X))
    (hfac : ∀ k v v', sphereCubeParameter v = sphereCubeParameter v' → F (k, v) = F (k, v'))
    (k : K) (v : I^(Fin 2)) :
    sphereCubeFamilyDescendValue F hfac (k, sphereCubeParameter v) = F (k, v) :=
  hfac k _ _ (Classical.choose_spec (sf_sphereCubeParameter_surjective (sphereCubeParameter v)))

theorem genLoop_homotopic_of_sphereFactor_homotopic [SimplyConnectedSpace X]
    (c d : GenLoop (Fin 2) X x) (h : (sphereFactor c).Homotopic (sphereFactor d)) :
    GenLoop.Homotopic c d := by
  obtain ⟨H⟩ := h
  have hbase : (0 : I^(Fin 2)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let p : Path x x :=
    { toFun := fun t => H (t, sphereCubeParameter 0)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := ((H.apply_zero (sphereCubeParameter 0)).trans
        (by simpa only [ContinuousMap.comp_apply] using
          DFunLike.congr_fun (sphereFactor_eq c) (0 : I^(Fin 2)))).trans (c.property 0 hbase)
      target' := ((H.apply_one (sphereCubeParameter 0)).trans
        (by simpa only [ContinuousMap.comp_apply] using
          DFunLike.congr_fun (sphereFactor_eq d) (0 : I^(Fin 2)))).trans (d.property 0 hbase) }
  let F : C(unitInterval × I^(Fin 2), X) :=
    ⟨fun z => H (z.1, sphereCubeParameter z.2),
      H.continuous.comp (continuous_fst.prodMk
        (sphereCubeParameter.continuous.comp continuous_snd))⟩
  have h0 : ∀ v, F (0, v) = c.val v := fun v => (H.apply_zero (sphereCubeParameter v)).trans
    (by simpa only [ContinuousMap.comp_apply] using DFunLike.congr_fun (sphereFactor_eq c) v)
  have h1 : ∀ v, F (1, v) = d.val v := fun v => (H.apply_one (sphereCubeParameter v)).trans
    (by simpa only [ContinuousMap.comp_apply] using DFunLike.congr_fun (sphereFactor_eq d) v)
  have hb : ∀ t v, v ∈ Cube.boundary (Fin 2) → F (t, v) = p t := fun t v hv => by
    change H (t, sphereCubeParameter v) = H (t, sphereCubeParameter 0)
    rw [sphereCubeParameter_eq_of_mem_boundary hv]
  have htr := DifferentialGeometry.Topology.genLoopTransport_extension_unique 1 p c d F h0 h1 hb
  have hp := DifferentialGeometry.Topology.genLoopTransport_path_homotopic 1
    (SimplyConnectedSpace.paths_homotopic p (Path.refl x)) c
  have hr := DifferentialGeometry.Topology.genLoopTransport_refl_homotopic 1 c
  exact hr.symm.trans (hp.symm.trans htr.symm)

theorem exists_sphereFactor_homotopic [PathConnectedSpace X] (x : X) (f : C(Sphere 2, X)) :
    ∃ c : GenLoop (Fin 2) X x, f.Homotopic (sphereFactor c) := by
  classical
  let c₀ : GenLoop (Fin 2) X (f (sphereCubeParameter 0)) :=
    ⟨f.comp sphereCubeParameter, fun v hv => by
      change f (sphereCubeParameter v) = f (sphereCubeParameter 0)
      rw [sphereCubeParameter_eq_of_mem_boundary hv]⟩
  let p : Path (f (sphereCubeParameter 0)) x :=
    PathConnectedSpace.somePath (f (sphereCubeParameter 0)) x
  let Γ : GenLoop (Fin 2) X x := DifferentialGeometry.Topology.genLoopTransport 1 p c₀
  let F : C(unitInterval × I^(Fin 2), X) :=
    (DifferentialGeometry.Topology.cubePathHomotopy 1 p c₀).toContinuousMap
  have hb : ∀ t v, v ∈ Cube.boundary (Fin 2) → F (t, v) = p t :=
    DifferentialGeometry.Topology.cubePathHomotopy_boundary 1 p c₀
  let hfac := sphereCubeFamily_factors F p.toContinuousMap hb
  let K : C(unitInterval × Sphere 2, X) := sphereCubeFamilyDescendValue F hfac
  have hK (t : unitInterval) (v : I^(Fin 2)) : K (t, sphereCubeParameter v) = F (t, v) :=
    sphereCubeFamilyDescendValue_projection F hfac t v
  refine ⟨Γ, ⟨⟨K, ?_, ?_⟩⟩⟩
  · intro z
    obtain ⟨v, rfl⟩ := sf_sphereCubeParameter_surjective z
    exact (hK 0 v).trans ((DifferentialGeometry.Topology.cubePathHomotopy 1 p c₀).apply_zero v)
  · intro z
    obtain ⟨v, rfl⟩ := sf_sphereCubeParameter_surjective z
    refine (hK 1 v).trans ?_
    refine ((DifferentialGeometry.Topology.cubePathHomotopy 1 p c₀).apply_one v).trans ?_
    exact (by simpa only [ContinuousMap.comp_apply] using
      (DFunLike.congr_fun (sphereFactor_eq Γ) v).symm)

def forgetBasedSphere (x : X) : HomotopyGroup (Fin 2) X x → FreeHomotopyClass (Sphere 2) X :=
  Quotient.lift (fun c => FreeHomotopyClass.mk (sphereFactor c))
    (fun _ _ h => (FreeHomotopyClass.mk_eq_mk_iff _ _).2 (sphereFactor_homotopic h))

def contractibleLoopInclusion : C(ContractibleContinuousLoop X, ContinuousFreeLoop X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem forgetBasedSphere_one (x : X) : forgetBasedSphere x 1 =
    FreeHomotopyClass.mk (ContinuousMap.const (Sphere 2) x) := by
  rw [HomotopyGroup.one_def]
  change FreeHomotopyClass.mk (sphereFactor (GenLoop.const : GenLoop (Fin 2) X x)) = _
  apply congrArg FreeHomotopyClass.mk
  exact ((Classical.choose_spec (exists_unique_sphereFactor
    (GenLoop.const : GenLoop (Fin 2) X x))).2 (ContinuousMap.const (Sphere 2) x) rfl).symm

theorem forgetBasedSphere_bijective [PathConnectedSpace X] [SimplyConnectedSpace X] (x : X) :
    Function.Bijective (forgetBasedSphere x) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h c =>
      induction b using Quotient.inductionOn with
      | h d =>
        change FreeHomotopyClass.mk (sphereFactor c) = FreeHomotopyClass.mk (sphereFactor d) at hab
        exact Quotient.sound (genLoop_homotopic_of_sphereFactor_homotopic c d
          ((FreeHomotopyClass.mk_eq_mk_iff _ _).mp hab))
  · intro ξ
    induction ξ using Quotient.inductionOn with
    | h f =>
      obtain ⟨c, hc⟩ := exists_sphereFactor_homotopic x f
      exact ⟨Quotient.mk _ c, by
        change FreeHomotopyClass.mk (sphereFactor c) = FreeHomotopyClass.mk f
        exact (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hc.symm⟩

theorem sphereFactor_natural {P Q : Type u} [TopologicalSpace P] [TopologicalSpace Q]
    (g : C(P, Q)) {x : ContinuousFreeLoop P}
    (c : GenLoop (Fin 2) (ContinuousFreeLoop P) x) :
    (loopPostcompose g).comp (sphereFactor c) =
      sphereFactor (genLoopPostcompose (loopPostcompose g) c) := by
  refine (Classical.choose_spec (exists_unique_sphereFactor
    (genLoopPostcompose (loopPostcompose g) c))).2 _ ?_
  dsimp only
  rw [ContinuousMap.comp_assoc, sphereFactor_eq c]
  rfl

theorem forgetBasedSphere_natural {P Q : Type u} [TopologicalSpace P] [TopologicalSpace Q]
    (g : C(P, Q)) (x : ContinuousFreeLoop P)
    (a : HomotopyGroup (Fin 2) (ContinuousFreeLoop P) x) :
    FreeHomotopyClass.map (loopPostcompose g) (forgetBasedSphere x a) =
      forgetBasedSphere (loopPostcompose g x) (basedHomotopyMap (loopPostcompose g) x a) := by
  induction a using Quotient.inductionOn with
  | h c =>
    change FreeHomotopyClass.mk ((loopPostcompose g).comp (sphereFactor c)) =
      FreeHomotopyClass.mk (sphereFactor (genLoopPostcompose (loopPostcompose g) c))
    rw [sphereFactor_natural g c]

private theorem pathTransportClass_eq_mk_genLoopTransport {x y : X} (n : ℕ) (p : Path x y)
    (c : GenLoop (Fin (n + 1)) X x) :
    pathTransportClass p c = Quotient.mk _
      (DifferentialGeometry.Topology.genLoopTransport n p c) :=
  ((Classical.choose_spec (exists_unique_pathTransportClass p c)).2 _
    ⟨DifferentialGeometry.Topology.genLoopTransport n p c, rfl,
      ⟨⟨DifferentialGeometry.Topology.cubePathHomotopy n p c,
        DifferentialGeometry.Topology.cubePathHomotopy_boundary n p c⟩⟩⟩).symm

private theorem pathTransport_eq_homotopyGroupTransport {x y : X} (n : ℕ) (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    pathTransport (k := n + 1) p a = DifferentialGeometry.Topology.homotopyGroupTransport n p a := by
  induction a using Quotient.inductionOn with
  | h c =>
    rw [pathTransport_pathTransportClass, pathTransportClass_eq_mk_genLoopTransport n p c]
    rfl

theorem sphereFactor_genLoopTransport_homotopic {x y : X} (γ : Path x y)
    (c : GenLoop (Fin 2) X x) :
    (sphereFactor c).Homotopic
      (sphereFactor (DifferentialGeometry.Topology.genLoopTransport 1 γ c)) := by
  let F : C(unitInterval × I^(Fin 2), X) :=
    (DifferentialGeometry.Topology.cubePathHomotopy 1 γ c).toContinuousMap
  have hb : ∀ t v, v ∈ Cube.boundary (Fin 2) → F (t, v) = γ t :=
    DifferentialGeometry.Topology.cubePathHomotopy_boundary 1 γ c
  let hfac := sphereCubeFamily_factors F γ.toContinuousMap hb
  let K : C(unitInterval × Sphere 2, X) := sphereCubeFamilyDescendValue F hfac
  have hK (t : unitInterval) (v : I^(Fin 2)) : K (t, sphereCubeParameter v) = F (t, v) :=
    sphereCubeFamilyDescendValue_projection F hfac t v
  refine ⟨⟨K, ?_, ?_⟩⟩
  · intro z
    obtain ⟨v, rfl⟩ := sf_sphereCubeParameter_surjective z
    exact (hK 0 v).trans (((DifferentialGeometry.Topology.cubePathHomotopy 1 γ c).apply_zero v).trans
      (by simpa only [ContinuousMap.comp_apply] using
        (DFunLike.congr_fun (sphereFactor_eq c) v).symm))
  · intro z
    obtain ⟨v, rfl⟩ := sf_sphereCubeParameter_surjective z
    exact (hK 1 v).trans (((DifferentialGeometry.Topology.cubePathHomotopy 1 γ c).apply_one v).trans
      (by simpa only [ContinuousMap.comp_apply] using
        (DFunLike.congr_fun (sphereFactor_eq
          (DifferentialGeometry.Topology.genLoopTransport 1 γ c)) v).symm))

theorem forgetBasedSphere_homotopyGroupTransport {x y : X} (γ : Path x y)
    (a : HomotopyGroup (Fin 2) X x) :
    forgetBasedSphere y (DifferentialGeometry.Topology.homotopyGroupTransport 1 γ a) =
      forgetBasedSphere x a := by
  induction a using Quotient.inductionOn with
  | h c =>
    change FreeHomotopyClass.mk
        (sphereFactor (DifferentialGeometry.Topology.genLoopTransport 1 γ c)) =
      FreeHomotopyClass.mk (sphereFactor c)
    exact (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr
      (sphereFactor_genLoopTransport_homotopic γ c).symm

theorem sphereFamily_homotopic_const_of_pi2_subsingleton
    (h : ∀ q : X, Subsingleton (HomotopyGroup (Fin 2) X q))
    (f : C(Sphere 2, X)) :
    ∃ q : X, ContinuousMap.Homotopic f (ContinuousMap.const (Sphere 2) q) := by
  classical
  have hz : (0 : I^(Fin 2)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let q : X := f (sphereCubeParameter 0)
  let c : GenLoop (Fin 2) X q := ⟨f.comp sphereCubeParameter, by
    intro y hy
    change f (sphereCubeParameter y) = f (sphereCubeParameter 0)
    apply congrArg f
    apply Subtype.ext
    change sphereCubeVector y = sphereCubeVector 0
    simp [sphereCubeVector, hy, hz]⟩
  have hf : sphereFactor c = f :=
    ((Classical.choose_spec (exists_unique_sphereFactor c)).2 f rfl).symm
  have hc : (⟦c⟧ : HomotopyGroup (Fin 2) X q) =
      (1 : HomotopyGroup (Fin 2) X q) := (h q).elim _ _
  refine ⟨q, (FreeHomotopyClass.mk_eq_mk_iff _ _).mp ?_⟩
  have he : forgetBasedSphere q (⟦c⟧ : HomotopyGroup (Fin 2) X q) =
      forgetBasedSphere q (1 : HomotopyGroup (Fin 2) X q) :=
    congrArg (forgetBasedSphere q) hc
  rw [forgetBasedSphere_one] at he
  change FreeHomotopyClass.mk (sphereFactor c) = _ at he
  rwa [hf] at he

private def zeroPt : Icc (0 : ℝ) (0 + 1) := ⟨0, by constructor <;> norm_num⟩

private def onePt : Icc (0 : ℝ) (0 + 1) := ⟨0 + 1, by constructor <;> norm_num⟩

private def circleQuotLift {Y : Type v} [TopologicalSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) :
    Y × Quot (AddCircle.EndpointIdent (1 : ℝ) 0) → X :=
  fun q => Quot.lift (r := AddCircle.EndpointIdent (1 : ℝ) 0) (fun t => φ (q.1, t))
    (fun a b hab => by cases hab; exact hφ q.1) q.2

private theorem continuous_circleQuotLift {Y : Type v} [TopologicalSpace Y]
    [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) :
    Continuous (circleQuotLift φ hφ) := by
  refine (isQuotientMap_quot_mk (r := AddCircle.EndpointIdent (1 : ℝ) 0)
    (X := Icc (0 : ℝ) (0 + 1))).continuous_lift_prod_right ?_
  have h : (fun p : Y × Icc (0 : ℝ) (0 + 1) =>
      circleQuotLift φ hφ (p.1, Quot.mk _ p.2)) = φ := by
    funext p
    simp [circleQuotLift]
  rw [h]
  exact φ.continuous

private def circleLift {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) :
    C(Y × Circle, X) where
  toFun q := circleQuotLift φ hφ (q.1, AddCircle.homeoIccQuot (1 : ℝ) 0 q.2)
  continuous_toFun :=
    (continuous_circleQuotLift φ hφ).comp
      (continuous_fst.prodMk
        ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp continuous_snd))

private theorem homeoIccQuot_coe {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (0 + 1)) :
    AddCircle.homeoIccQuot (1 : ℝ) 0 (t : Circle) =
      Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) ⟨t, Ico_subset_Icc_self ht⟩ := by
  have h := congr_fun (AddCircle.equivIccQuot_comp_mk_eq_toIcoMod (1 : ℝ) 0) t
  simp only [Function.comp_apply] at h
  have hmod : toIcoMod (by norm_num : (0 : ℝ) < 1) 0 t = t :=
    (toIcoMod_eq_iff (by norm_num : (0 : ℝ) < 1)).2 ⟨ht, 0, by simp⟩
  simp only [hmod] at h
  exact h

private theorem circleLift_apply {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) (q : Y × Circle) :
    circleLift φ hφ q =
      circleQuotLift φ hφ (q.1, AddCircle.homeoIccQuot (1 : ℝ) 0 q.2) := rfl

private theorem circleLift_coe {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt))
    (y : Y) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (0 + 1)) :
    circleLift φ hφ (y, (t : Circle)) = φ (y, ⟨t, Ico_subset_Icc_self ht⟩) := by
  rw [circleLift_apply, homeoIccQuot_coe ht]
  simp only [circleQuotLift]

private theorem subinterval_mem_I {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    t ∈ Icc (0 : ℝ) 1 :=
  ⟨ht.1, ht.2.le⟩

private theorem subinterval_coe_mem_I (t : Icc (0 : ℝ) (0 + 1)) : (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
  ⟨t.2.1, by simpa using t.2.2⟩

private theorem onePt_val : (onePt : ℝ) = 1 := zero_add 1

private theorem zeroPt_I : (⟨(zeroPt : ℝ), subinterval_coe_mem_I zeroPt⟩ : I) = 0 := rfl

private theorem onePt_I : (⟨(onePt : ℝ), subinterval_coe_mem_I onePt⟩ : I) = 1 :=
  Subtype.ext onePt_val

private def cubeParamHom : C((I^(Fin 2)) × Icc (0 : ℝ) (0 + 1), I^(Fin 3)) where
  toFun q := ![q.1 0, q.1 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply (0 : Fin 2)).comp continuous_fst
    · exact (continuous_apply (1 : Fin 2)).comp continuous_fst
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _

private theorem cubeParamHom_apply (q : (I^(Fin 2)) × Icc (0 : ℝ) (0 + 1)) :
    cubeParamHom q = ![q.1 0, q.1 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩] := rfl

private theorem cubeParamHom_zero (p : I^(Fin 2)) :
    cubeParamHom (p, zeroPt) = ![p 0, p 1, (0 : I)] := by
  rw [cubeParamHom_apply]
  rfl

private theorem cubeParamHom_one (p : I^(Fin 2)) :
    cubeParamHom (p, onePt) = ![p 0, p 1, (1 : I)] := by
  rw [cubeParamHom_apply]
  rw [onePt_I]

private def cubeLoopParam (c : GenLoop (Fin 3) X x) :
    C((I^(Fin 2)) × Icc (0 : ℝ) (0 + 1), X) :=
  c.val.comp cubeParamHom

private theorem cubeLoopParam_zero (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    cubeLoopParam c (p, zeroPt) = x := by
  rw [cubeLoopParam, ContinuousMap.comp_apply, cubeParamHom_zero p]
  exact c.property _ ⟨2, Or.inl rfl⟩

private theorem cubeLoopParam_one (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    cubeLoopParam c (p, onePt) = x := by
  rw [cubeLoopParam, ContinuousMap.comp_apply, cubeParamHom_one p]
  exact c.property _ ⟨2, Or.inr rfl⟩

private def cubeLoopFamily (c : GenLoop (Fin 3) X x) : C((I^(Fin 2)) × Circle, X) :=
  circleLift (X := X) (Y := I^(Fin 2)) (cubeLoopParam c)
    (fun p => (cubeLoopParam_zero c p).trans (cubeLoopParam_one c p).symm)

private theorem cubeLoopFamily_coe (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    cubeLoopFamily c (p, (t : Circle)) = c ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [cubeLoopFamily, circleLift_coe _ _ _ (by simpa using ht)]
  rw [cubeLoopParam, ContinuousMap.comp_apply, cubeParamHom_apply]
  rfl

private theorem cubeLoopFamily_zero (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    cubeLoopFamily c (p, ((0 : ℝ) : Circle)) = x := by
  rw [cubeLoopFamily_coe c p (t := 0) (by constructor <;> norm_num)]
  exact c.property _ ⟨2, Or.inl rfl⟩

private theorem cubeLoopFamily_base (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    ((cubeLoopFamily c).curry p) 0 = x := by
  rw [ContinuousMap.curry_apply, ← AddCircle.coe_zero (1 : ℝ)]
  exact cubeLoopFamily_zero c p

private def cubeAdjunctVal (c : GenLoop (Fin 3) X x) : C(I^(Fin 2), BasedContinuousLoop x) where
  toFun p := ⟨(cubeLoopFamily c).curry p, cubeLoopFamily_base c p⟩
  continuous_toFun :=
    ((cubeLoopFamily c).curry).continuous.subtype_mk (cubeLoopFamily_base c)

private theorem cubeAdjunctVal_coe (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (cubeAdjunctVal c p : C(Circle, X)) (t : Circle) =
      c ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [cubeAdjunctVal]
  exact cubeLoopFamily_coe c p ht

private theorem mem_boundary_three_of_mem_boundary_two (p : I^(Fin 2))
    (hp : p ∈ Cube.boundary (Fin 2)) (t : I) :
    ![p 0, p 1, t] ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hp
  fin_cases i
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

private theorem cubeAdjunctVal_boundary (c : GenLoop (Fin 3) X x) {p : I^(Fin 2)}
    (hp : p ∈ Cube.boundary (Fin 2)) :
    cubeAdjunctVal c p = basedConstantLoop x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  rw [cubeAdjunctVal_coe c p ht]
  exact c.property _
    (mem_boundary_three_of_mem_boundary_two p hp ⟨t, subinterval_mem_I ht⟩)

private def cubeAdjunctGenLoop (c : GenLoop (Fin 3) X x) :
    GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  ⟨cubeAdjunctVal c, by intro p hp; exact cubeAdjunctVal_boundary c hp⟩

private theorem cubeAdjunctGenLoop_coe (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (cubeAdjunctGenLoop c p : C(Circle, X)) (t : Circle) =
      c ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] :=
  cubeAdjunctVal_coe c p ht

private theorem cubeAdjunctGenLoop_apply (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) (t : I) :
    (cubeAdjunctGenLoop c p : C(Circle, X)) ((t : ℝ) : Circle) = c ![p 0, p 1, t] := by
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · rw [cubeAdjunctGenLoop_coe c p ⟨t.2.1, ht⟩]
  · have hz : ((t : ℝ) : Circle) = 0 := by rw [ht, AddCircle.coe_period (1 : ℝ)]
    have h1 : (cubeAdjunctGenLoop c p : C(Circle, X)) ((t : ℝ) : Circle) = x := by
      rw [hz]
      exact (cubeAdjunctGenLoop c p).2
    have h2 : c ![p 0, p 1, t] = x := c.property _ ⟨2, Or.inr (Subtype.ext ht)⟩
    rw [h1, h2]

private theorem cubeAdjunctGenLoop_unique (c : GenLoop (Fin 3) X x)
    (A : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (hA : ∀ p : I^(Fin 2), ∀ t : I,
      (A p : C(Circle, X)) ((t : ℝ) : Circle) = c ![p 0, p 1, t]) :
    A = cubeAdjunctGenLoop c := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (hA p ⟨t, subinterval_mem_I ht⟩).trans (cubeAdjunctGenLoop_coe c p ht).symm

theorem exists_unique_cubeAdjunct (c : GenLoop (Fin 3) X x) :
    ∃! A : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x),
      ∀ p : I^(Fin 2), ∀ t : I,
        (A p).1 ((t : ℝ) : Circle) = c ![p 0, p 1, t] :=
  ⟨cubeAdjunctGenLoop c, cubeAdjunctGenLoop_apply c, fun A hA =>
    cubeAdjunctGenLoop_unique c A hA⟩

def cubeAdjunct (c : GenLoop (Fin 3) X x) :
    GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  Classical.choose (exists_unique_cubeAdjunct c)

theorem cubeAdjunct_apply (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) (t : I) :
    (cubeAdjunct c p).1 ((t : ℝ) : Circle) = c ![p 0, p 1, t] :=
  (Classical.choose_spec (exists_unique_cubeAdjunct c)).1 p t

private def cubeHomotopyParamHom :
    C((I × I^(Fin 2)) × Icc (0 : ℝ) (0 + 1), I × I^(Fin 3)) where
  toFun q := (q.1.1, ![q.1.2 0, q.1.2 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩])
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_fst
    · apply continuous_pi
      intro i
      fin_cases i
      · exact (continuous_apply (0 : Fin 2)).comp continuous_fst.snd
      · exact (continuous_apply (1 : Fin 2)).comp continuous_fst.snd
      · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _

private theorem cubeHomotopyParamHom_apply (q : (I × I^(Fin 2)) × Icc (0 : ℝ) (0 + 1)) :
    cubeHomotopyParamHom q =
      (q.1.1, ![q.1.2 0, q.1.2 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩]) := rfl

private theorem cubeHomotopyParamHom_zero (q : I × I^(Fin 2)) :
    cubeHomotopyParamHom (q, zeroPt) = (q.1, ![q.2 0, q.2 1, (0 : I)]) := by
  rw [cubeHomotopyParamHom_apply]
  rfl

private theorem cubeHomotopyParamHom_one (q : I × I^(Fin 2)) :
    cubeHomotopyParamHom (q, onePt) = (q.1, ![q.2 0, q.2 1, (1 : I)]) := by
  rw [cubeHomotopyParamHom_apply, onePt_I]

private theorem cubeHomotopyParamHom_endpoints {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) :
    H.toContinuousMap (cubeHomotopyParamHom (q, zeroPt)) =
      H.toContinuousMap (cubeHomotopyParamHom (q, onePt)) := by
  rw [cubeHomotopyParamHom_zero q, cubeHomotopyParamHom_one q]
  exact ((H.eq_fst q.1 ⟨2, Or.inl rfl⟩).trans (c.property _ ⟨2, Or.inl rfl⟩)).trans
    (((c.property _ ⟨2, Or.inr rfl⟩).symm).trans (H.eq_fst q.1 ⟨2, Or.inr rfl⟩).symm)

private def cubeHomotopyLoopFamily {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3))) :
    C(I × I^(Fin 2), C(Circle, X)) :=
  (circleLift (X := X) (Y := I × I^(Fin 2))
    (H.toContinuousMap.comp cubeHomotopyParamHom)
    (fun q => cubeHomotopyParamHom_endpoints H q)).curry

private theorem cubeHomotopyLoopFamily_coe {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    cubeHomotopyLoopFamily H q (t : Circle) =
      H (q.1, ![q.2 0, q.2 1, ⟨t, subinterval_mem_I ht⟩]) := by
  rw [cubeHomotopyLoopFamily, ContinuousMap.curry_apply,
    circleLift_coe _ _ _ (by simpa using ht)]
  rw [ContinuousMap.comp_apply, cubeHomotopyParamHom_apply]
  rfl

private theorem cubeHomotopyLoopFamily_base {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) :
    cubeHomotopyLoopFamily H q 0 = x := by
  rw [cubeHomotopyLoopFamily, ContinuousMap.curry_apply, ← AddCircle.coe_zero (1 : ℝ),
    circleLift_coe _ _ _ (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1))]
  rw [ContinuousMap.comp_apply, cubeHomotopyParamHom_apply]
  exact (H.eq_fst q.1 ⟨2, Or.inl rfl⟩).trans (c.property _ ⟨2, Or.inl rfl⟩)

private def cubeAdjunctHomotopy {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3))) :
    C(I × I^(Fin 2), BasedContinuousLoop x) where
  toFun q := ⟨cubeHomotopyLoopFamily H q, cubeHomotopyLoopFamily_base H q⟩
  continuous_toFun :=
    (cubeHomotopyLoopFamily H).continuous.subtype_mk (cubeHomotopyLoopFamily_base H)

private theorem cubeAdjunctHomotopy_coe {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (cubeAdjunctHomotopy H q : C(Circle, X)) (t : Circle) =
      H (q.1, ![q.2 0, q.2 1, ⟨t, subinterval_mem_I ht⟩]) :=
  cubeHomotopyLoopFamily_coe H q ht

private theorem cubeAdjunctHomotopy_zero {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (p : I^(Fin 2)) :
    cubeAdjunctHomotopy H (0, p) = (cubeAdjunct c).val p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (cubeAdjunctHomotopy_coe H (0, p) ht).trans
    ((H.apply_zero _).trans (cubeAdjunct_apply c p ⟨t, subinterval_mem_I ht⟩).symm)

private theorem cubeAdjunctHomotopy_one {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (p : I^(Fin 2)) :
    cubeAdjunctHomotopy H (1, p) = (cubeAdjunct d).val p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (cubeAdjunctHomotopy_coe H (1, p) ht).trans
    ((H.apply_one _).trans (cubeAdjunct_apply d p ⟨t, subinterval_mem_I ht⟩).symm)

private theorem cubeAdjunctHomotopy_eq_const {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (s : I) {p : I^(Fin 2)} (hp : p ∈ Cube.boundary (Fin 2)) :
    cubeAdjunctHomotopy H (s, p) = basedConstantLoop x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (cubeAdjunctHomotopy_coe H (s, p) ht).trans
    ((H.eq_fst s (mem_boundary_three_of_mem_boundary_two p hp ⟨t, subinterval_mem_I ht⟩)).trans
      (c.property _ (mem_boundary_three_of_mem_boundary_two p hp ⟨t, subinterval_mem_I ht⟩)))

theorem cubeAdjunct_homotopic {c d : GenLoop (Fin 3) X x}
    (h : c.val.HomotopicRel d.val (Cube.boundary (Fin 3))) :
    (cubeAdjunct c).val.HomotopicRel (cubeAdjunct d).val (Cube.boundary (Fin 2)) := by
  obtain ⟨H⟩ := h
  exact ⟨{ toContinuousMap := cubeAdjunctHomotopy H
           map_zero_left := fun p => cubeAdjunctHomotopy_zero H p
           map_one_left := fun p => cubeAdjunctHomotopy_one H p
           prop' := fun s p hp =>
             (cubeAdjunctHomotopy_eq_const H s hp).trans
               ((cubeAdjunct c).property p hp).symm }⟩


def basedLoopAdjunction (x : X) : HomotopyGroup (Fin 3) X x →
    HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  Quotient.map cubeAdjunct (fun _ _ h => cubeAdjunct_homotopic h)

private theorem cubeAdjunct_const (x : X) :
    cubeAdjunct (GenLoop.const : GenLoop (Fin 3) X x) = GenLoop.const :=
  ((Classical.choose_spec
      (exists_unique_cubeAdjunct (GenLoop.const : GenLoop (Fin 3) X x))).2
    GenLoop.const (fun _ _ => rfl)).symm

private theorem basedLoopAdjunction_mk (x : X) (c : GenLoop (Fin 3) X x) :
    basedLoopAdjunction x (Quotient.mk _ c) = Quotient.mk _ (cubeAdjunct c) :=
  Quotient.map_mk cubeAdjunct (fun _ _ h => cubeAdjunct_homotopic h) c

private theorem update_fin_two (p : I^(Fin 2)) (u : I) :
    Function.update p 0 u = ![u, p 1] := by
  funext i
  fin_cases i <;> simp

private theorem update_fin_three (p : I^(Fin 2)) (u t : I) :
    Function.update ![p 0, p 1, t] (0 : Fin 3) u = ![u, p 1, t] := by
  funext i
  fin_cases i <;> simp

private theorem vecThree_zero (p : I^(Fin 2)) (t : I) :
    (![p 0, p 1, t] : I^(Fin 3)) 0 = p 0 := rfl

private theorem cubeAdjunct_transAt_left (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hP : (p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 2) (cubeAdjunct d) (cubeAdjunct c) p).1
        ((t : ℝ) : Circle) =
      d ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ)), p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, if_pos hP,
    cubeAdjunct_apply d (Function.update p 0 (Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ))))
      ⟨t, subinterval_mem_I ht⟩, update_fin_two]
  rfl

private theorem cubeAdjunct_transAt_right (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hP : ¬(p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 2) (cubeAdjunct d) (cubeAdjunct c) p).1
        ((t : ℝ) : Circle) =
      c ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ) - 1), p 1,
        ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, if_neg hP,
    cubeAdjunct_apply c
      (Function.update p 0 (Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ) - 1)))
      ⟨t, subinterval_mem_I ht⟩, update_fin_two]
  rfl

private theorem cubeTransAt_left (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hP : (p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 3) d c) ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] =
      d ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ)), p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, vecThree_zero p ⟨t, subinterval_mem_I ht⟩, if_pos hP,
    update_fin_three]

private theorem cubeTransAt_right (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hP : ¬(p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 3) d c) ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] =
      c ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ) - 1), p 1,
        ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, vecThree_zero p ⟨t, subinterval_mem_I ht⟩, if_neg hP,
    update_fin_three]

private theorem cubeAdjunct_transAt (c d : GenLoop (Fin 3) X x) :
    cubeAdjunct (GenLoop.transAt (0 : Fin 3) d c) =
      GenLoop.transAt (0 : Fin 2) (cubeAdjunct d) (cubeAdjunct c) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  refine (cubeAdjunct_apply (GenLoop.transAt (0 : Fin 3) d c) p
    ⟨t, subinterval_mem_I ht⟩).trans ?_
  by_cases hP : (p 0 : ℝ) ≤ 1 / 2
  · exact (cubeTransAt_left c d p ht hP).trans (cubeAdjunct_transAt_left c d p ht hP).symm
  · exact (cubeTransAt_right c d p ht hP).trans (cubeAdjunct_transAt_right c d p ht hP).symm

private def twoCubeCurried (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x)) :
    C(I^(Fin 2), C(Circle, X)) where
  toFun p := (a p : C(Circle, X))
  continuous_toFun := continuous_subtype_val.comp a.val.continuous

private theorem twoCubeCurried_apply
    (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x)) (p : I^(Fin 2)) :
    twoCubeCurried a p = (a p : C(Circle, X)) := rfl

private theorem uncurriedTwoCubeCurried_apply
    (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (p : I^(Fin 2)) (w : Circle) :
    ContinuousMap.uncurry (twoCubeCurried a) (p, w) = (a p : C(Circle, X)) w := by
  rw [ContinuousMap.uncurry_apply]
  rfl

private theorem circleCoe_zero_of_eq_zero {t : I} (h : t = 0) :
    ((t : ℝ) : Circle) = 0 := by
  rw [h]
  rfl

private theorem circleCoe_zero_of_eq_one {t : I} (h : t = 1) :
    ((t : ℝ) : Circle) = 0 := by
  have h' : (t : ℝ) = 1 := by simpa using congrArg (fun s : I => (s : ℝ)) h
  rw [h']
  exact AddCircle.coe_period (1 : ℝ)

private theorem vecThree_eta (z : I^(Fin 3)) :
    ![(![z 0, z 1] : I^(Fin 2)) 0, (![z 0, z 1] : I^(Fin 2)) 1, z 2] = z := by
  funext i
  fin_cases i <;> rfl

private theorem vecTwo_eta_sub (p : I^(Fin 2)) (t : I) :
    ![(![p 0, p 1, t] : I^(Fin 3)) 0, (![p 0, p 1, t] : I^(Fin 3)) 1] = p := by
  funext i
  fin_cases i <;> rfl

private def threeCubeParamHom : C(I^(Fin 3), (I^(Fin 2)) × Circle) where
  toFun z := (![z 0, z 1], ((z 2 : ℝ) : Circle))
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_apply 0
      · exact continuous_apply 1
    · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
        (continuous_subtype_val.comp (continuous_apply 2))

private theorem threeCubeParamHom_apply (z : I^(Fin 3)) :
    threeCubeParamHom z = (![z 0, z 1], ((z 2 : ℝ) : Circle)) := rfl

private theorem twoCube_boundary_of_zero {z : I^(Fin 3)} (h : z 0 = 0 ∨ z 0 = 1) :
    (![z 0, z 1] : I^(Fin 2)) ∈ Cube.boundary (Fin 2) :=
  ⟨0, by simpa using h⟩

private theorem twoCube_boundary_of_one {z : I^(Fin 3)} (h : z 1 = 0 ∨ z 1 = 1) :
    (![z 0, z 1] : I^(Fin 2)) ∈ Cube.boundary (Fin 2) :=
  ⟨1, by simpa using h⟩

private def twoCubeAdjunctFun (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) : C(I^(Fin 3), X) :=
  (ContinuousMap.uncurry (twoCubeCurried a)).comp threeCubeParamHom

private theorem twoCubeAdjunctFun_apply (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) (z : I^(Fin 3)) :
    twoCubeAdjunctFun a z = (a ![z 0, z 1] : C(Circle, X)) ((z 2 : ℝ) : Circle) := by
  rw [twoCubeAdjunctFun, ContinuousMap.comp_apply, threeCubeParamHom_apply,
    uncurriedTwoCubeCurried_apply]

private def twoCubeAdjunct (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x)) :
    GenLoop (Fin 3) X x :=
  ⟨twoCubeAdjunctFun a, by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    fin_cases i
    · exact (congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X))
          ((z 2 : ℝ) : Circle))
        (a.property ![z 0, z 1] (twoCube_boundary_of_zero hi))).trans rfl
    · exact (congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X))
          ((z 2 : ℝ) : Circle))
        (a.property ![z 0, z 1] (twoCube_boundary_of_one hi))).trans rfl
    · have hz2 : ((z 2 : ℝ) : Circle) = 0 := by
        rcases hi with h | h
        · exact circleCoe_zero_of_eq_zero h
        · exact circleCoe_zero_of_eq_one h
      exact (congrArg (fun w : Circle => (a ![z 0, z 1] : C(Circle, X)) w) hz2).trans
        (a ![z 0, z 1]).2⟩

private theorem twoCubeAdjunct_apply (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) (z : I^(Fin 3)) :
    twoCubeAdjunct a z = (a ![z 0, z 1] : C(Circle, X)) ((z 2 : ℝ) : Circle) := by
  exact twoCubeAdjunctFun_apply a z

private theorem twoCubeAdjunct_adjunct (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) :
    cubeAdjunct (twoCubeAdjunct a) = a :=
  ((Classical.choose_spec (exists_unique_cubeAdjunct (twoCubeAdjunct a))).2 a (fun p t => by
    rw [twoCubeAdjunct_apply]
    exact congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((t : ℝ) : Circle))
      (congrArg a (vecTwo_eta_sub p t)).symm)).symm

private def twoCubeHomotopyParamHom : C(I × I^(Fin 3), (I × I^(Fin 2)) × Circle) where
  toFun q := ((q.1, ![q.2 0, q.2 1]), ((q.2 2 : ℝ) : Circle))
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.prodMk
      · exact continuous_fst
      · apply continuous_pi
        intro i
        fin_cases i <;> fun_prop
    · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
        (continuous_subtype_val.comp ((continuous_apply 2).comp continuous_snd))

private theorem twoCubeHomotopyParamHom_apply (q : I × I^(Fin 3)) :
    twoCubeHomotopyParamHom q = ((q.1, ![q.2 0, q.2 1]), ((q.2 2 : ℝ) : Circle)) := rfl

private def twoCubeHomotopyCurried {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2))) :
    C(I × I^(Fin 2), C(Circle, X)) where
  toFun q := (A q : C(Circle, X))
  continuous_toFun := continuous_subtype_val.comp A.toContinuousMap.continuous

private theorem uncurriedTwoCubeHomotopyCurried_apply {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (q : I × I^(Fin 2)) (w : Circle) :
    ContinuousMap.uncurry (twoCubeHomotopyCurried A) (q, w) = (A q : C(Circle, X)) w := by
  rw [ContinuousMap.uncurry_apply]
  rfl

private def twoCubeHomotopyUncurried {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2))) : C(I × I^(Fin 3), X) :=
  (ContinuousMap.uncurry (twoCubeHomotopyCurried A)).comp twoCubeHomotopyParamHom

private theorem twoCubeHomotopyUncurried_apply {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (s : I) (z : I^(Fin 3)) :
    twoCubeHomotopyUncurried A (s, z) =
      (A (s, ![z 0, z 1]) : C(Circle, X)) ((z 2 : ℝ) : Circle) := by
  rw [twoCubeHomotopyUncurried, ContinuousMap.comp_apply, twoCubeHomotopyParamHom_apply,
    uncurriedTwoCubeHomotopyCurried_apply]

private theorem twoCubeHomotopy_const_of_boundary {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (s : I) {z : I^(Fin 3)} (hb : ![z 0, z 1] ∈ Cube.boundary (Fin 2)) :
    (A (s, ![z 0, z 1]) : C(Circle, X)) ((z 2 : ℝ) : Circle) = x :=
  (congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
    (A.prop s ![z 0, z 1] hb)).trans
  ((congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
    ((cubeAdjunct c).property ![z 0, z 1] hb)).trans rfl)

private theorem twoCubeHomotopy_const_of_circle_eq {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (s : I) {z : I^(Fin 3)} (h : ((z 2 : ℝ) : Circle) = 0) :
    (A (s, ![z 0, z 1]) : C(Circle, X)) ((z 2 : ℝ) : Circle) = x :=
  (congrArg (fun w : Circle => (A (s, ![z 0, z 1]) : C(Circle, X)) w) h).trans
    (A (s, ![z 0, z 1])).2

private def cubeHomotopyOfAdjunctHomotopy {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2))) :
    ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)) where
  toContinuousMap := twoCubeHomotopyUncurried A
  map_zero_left := fun z =>
    (twoCubeHomotopyUncurried_apply A 0 z).trans
      ((congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
        (A.apply_zero ![z 0, z 1])).trans
      ((cubeAdjunct_apply c ![z 0, z 1] (z 2)).trans (congrArg c (vecThree_eta z))))
  map_one_left := fun z =>
    (twoCubeHomotopyUncurried_apply A 1 z).trans
      ((congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
        (A.apply_one ![z 0, z 1])).trans
      ((cubeAdjunct_apply d ![z 0, z 1] (z 2)).trans (congrArg d (vecThree_eta z))))
  prop' := fun s z hz => by
    have h := twoCubeHomotopyUncurried_apply A s z
    obtain ⟨i, hi⟩ := hz
    fin_cases i
    · exact h.trans ((twoCubeHomotopy_const_of_boundary A s (twoCube_boundary_of_zero hi)).trans
        (c.property z ⟨0, hi⟩).symm)
    · exact h.trans ((twoCubeHomotopy_const_of_boundary A s (twoCube_boundary_of_one hi)).trans
        (c.property z ⟨1, hi⟩).symm)
    · have hz2 : ((z 2 : ℝ) : Circle) = 0 := by
        rcases hi with hh | hh
        · exact circleCoe_zero_of_eq_zero hh
        · exact circleCoe_zero_of_eq_one hh
      exact h.trans ((twoCubeHomotopy_const_of_circle_eq A s hz2).trans
        (c.property z ⟨2, hi⟩).symm)

theorem basedLoopAdjunction_bijective (x : X) : Function.Bijective (basedLoopAdjunction x) := by
  constructor
  · rintro a b hab
    induction a using Quotient.inductionOn with
    | h c =>
      induction b using Quotient.inductionOn with
      | h d =>
        rw [basedLoopAdjunction_mk, basedLoopAdjunction_mk] at hab
        obtain ⟨A⟩ := Quotient.exact hab
        exact Quotient.sound ⟨cubeHomotopyOfAdjunctHomotopy A⟩
  · intro b
    induction b using Quotient.inductionOn with
    | h a =>
      exact ⟨Quotient.mk _ (twoCubeAdjunct a), by
        rw [basedLoopAdjunction_mk]
        exact congrArg (Quotient.mk _) (twoCubeAdjunct_adjunct a)⟩

theorem basedLoopAdjunction_one (x : X) : basedLoopAdjunction x 1 = 1 := by
  rw [HomotopyGroup.one_def, basedLoopAdjunction_mk, cubeAdjunct_const x]
  exact HomotopyGroup.one_def.symm

theorem basedLoopAdjunction_mul (a b : HomotopyGroup (Fin 3) X x) :
    basedLoopAdjunction x (a * b) = basedLoopAdjunction x a * basedLoopAdjunction x b := by
  induction a using Quotient.inductionOn with
  | h c =>
    induction b using Quotient.inductionOn with
    | h d =>
      have hm : ((· * ·) : HomotopyGroup (Fin 3) X x → HomotopyGroup (Fin 3) X x →
          HomotopyGroup (Fin 3) X x) ⟦c⟧ ⟦d⟧ =
          (⟦GenLoop.transAt (0 : Fin 3) d c⟧ : HomotopyGroup (Fin 3) X x) :=
        HomotopyGroup.mul_spec (i := (0 : Fin 3)) (p := c) (q := d)
      have h3 : basedLoopAdjunction x
            (((· * ·) : HomotopyGroup (Fin 3) X x → HomotopyGroup (Fin 3) X x →
              HomotopyGroup (Fin 3) X x) ⟦c⟧ ⟦d⟧) =
          (((· * ·) : HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) →
              HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) →
              HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
            (basedLoopAdjunction x ⟦c⟧) (basedLoopAdjunction x ⟦d⟧)) := by
        rw [hm, basedLoopAdjunction_mk, basedLoopAdjunction_mk, basedLoopAdjunction_mk]
        exact (congrArg (Quotient.mk _) (cubeAdjunct_transAt c d)).trans
          (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := cubeAdjunct c)
            (q := cubeAdjunct d)).symm
      exact h3

def basedLoopAdjunctionEquiv (x : X) : HomotopyGroup (Fin 3) X x ≃*
    HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  MulEquiv.ofBijective
    ({ toFun := basedLoopAdjunction x
       map_one' := basedLoopAdjunction_one x
       map_mul' := basedLoopAdjunction_mul } : HomotopyGroup (Fin 3) X x →*
      HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (basedLoopAdjunction_bijective x)


def freeLoopAdjunction (x : X) : HomotopyGroup (Fin 3) X x →
    HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  basedHomotopyMap (basedLoopInclusion x) (basedConstantLoop x) ∘ basedLoopAdjunction x

def freeLoopAdjunctionHom (x : X) : HomotopyGroup (Fin 3) X x →*
    HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  (basedHomotopyHom (basedLoopInclusion x) (basedConstantLoop x)).comp
    (basedLoopAdjunctionEquiv x).toMonoidHom

@[simp] theorem freeLoopAdjunctionHom_apply (x : X) (a : HomotopyGroup (Fin 3) X x) :
    freeLoopAdjunctionHom x a = freeLoopAdjunction x a := rfl

theorem freeLoopAdjunction_eq_piThreeFreeLoopPiTwoMulEquiv (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] (a : HomotopyGroup (Fin 3) X x) :
    freeLoopAdjunction x a = DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv x a := by
  induction a using Quotient.inductionOn with
  | h c =>
    have htrans : DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv x (Quotient.mk _ c) =
        (DifferentialGeometry.Topology.basedCircleInclusionMulEquiv x
          ((DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv x).symm
            (Quotient.mk _ c)) :
          HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x)) := rfl
    have hfree : freeLoopAdjunction x (Quotient.mk _ c) =
        (Quotient.mk _ (genLoopPostcompose (basedLoopInclusion x) (cubeAdjunct c)) :
          HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x)) := rfl
    have hincl : (DifferentialGeometry.Topology.basedCircleInclusionMulEquiv x
          (Quotient.mk _ (DifferentialGeometry.Topology.genLoopCircleCurry 1 x c)) :
          HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x)) =
        (Quotient.mk _ (DifferentialGeometry.Topology.genLoopBasedMap
            (DifferentialGeometry.Topology.basedCircleInclusion x)
            (DifferentialGeometry.Topology.basedCircleConstant x)
            (DifferentialGeometry.Topology.FreeLoop.constants x) rfl
            (DifferentialGeometry.Topology.genLoopCircleCurry 1 x c)) :
          HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x)) := rfl
    rw [hfree, htrans, DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv_symm_mk, hincl]
    refine congrArg (Quotient.mk _) (Subtype.ext (ContinuousMap.ext (fun p =>
      ContinuousMap.ext (fun z => ?_))))
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    change (cubeAdjunct c p).1 ((t : ℝ) : Circle) =
      (DifferentialGeometry.Topology.genLoopCircleCurry 1 x c p).val ((t : ℝ) : Circle)
    rw [cubeAdjunct_apply c p ⟨t, ht.1, le_of_lt ht.2⟩,
      DifferentialGeometry.Topology.genLoopCircleCurry_coe 1 x c p ⟨t, ht.1, le_of_lt ht.2⟩]
    exact congrArg c (by
      funext i
      fin_cases i <;> rfl)

theorem freeLoopAdjunction_bijective (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    Function.Bijective (freeLoopAdjunction x) := by
  have h : freeLoopAdjunction x =
      ⇑(DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv x) :=
    funext fun a => freeLoopAdjunction_eq_piThreeFreeLoopPiTwoMulEquiv x a
  rw [h]
  exact (DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv x).bijective

def freeLoopAdjunctionEquiv (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    HomotopyGroup (Fin 3) X x ≃*
      HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  MulEquiv.ofBijective (freeLoopAdjunctionHom x) (freeLoopAdjunction_bijective x)

theorem freeLoopAdjunction_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (a : HomotopyGroup (Fin 3) X x) :
    basedHomotopyMap (loopPostcompose f) (constantLoops x) (freeLoopAdjunction x a) =
      freeLoopAdjunction (f x) (basedHomotopyMap f x a) := by
  induction a using Quotient.inductionOn with
  | h c =>
    change Quotient.mk _
        (genLoopPostcompose (loopPostcompose f)
          (genLoopPostcompose (basedLoopInclusion x) (cubeAdjunct c))) =
      Quotient.mk _
        (genLoopPostcompose (basedLoopInclusion (f x)) (cubeAdjunct (genLoopPostcompose f c)))
    refine congrArg (Quotient.mk _) (Subtype.ext (ContinuousMap.ext (fun p =>
      ContinuousMap.ext (fun z => ?_))))
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    change f (((cubeAdjunct c) p).1 ((t : ℝ) : Circle)) =
      ((cubeAdjunct (genLoopPostcompose f c)) p).1 ((t : ℝ) : Circle)
    rw [cubeAdjunct_apply c p ⟨t, subinterval_mem_I ht⟩,
      cubeAdjunct_apply (genLoopPostcompose f c) p ⟨t, subinterval_mem_I ht⟩]
    rfl

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hConnected : ConnectedSpace M] [hSimplyConnected : SimplyConnectedSpace M]

include hT2 hCompact hConnected hSimplyConnected

omit hConnected in
theorem rfs_free_loop_class (q : M) :
    PathConnectedSpace (ContinuousFreeLoop M) ∧ SimplyConnectedSpace (ContinuousFreeLoop M) ∧
    Function.Bijective (freeLoopAdjunction q) ∧
    Function.Bijective (forgetBasedSphere (constantLoops q)) := by
  have htwo : Subsingleton (HomotopyGroup (Fin 2) M q) := (rfs_homotopy_groups q).1
  have hpc : PathConnectedSpace (ContinuousFreeLoop M) :=
    DifferentialGeometry.Topology.freeLoop_pathConnected_of_simplyConnected
  have hsc : SimplyConnectedSpace (ContinuousFreeLoop M) :=
    DifferentialGeometry.Topology.freeLoop_simplyConnected_of_piTwo q
  exact ⟨hpc, hsc, freeLoopAdjunction_bijective q, forgetBasedSphere_bijective (constantLoops q)⟩

def positiveBasedLoopClass (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 2) (ContinuousFreeLoop M) (constantLoops q) :=
  freeLoopAdjunction q (positiveHomotopyClass o q)

def positiveFreeLoopClass (o : TangentOrientationSection M) : FreeSphereClass M :=
  let q : M := Classical.choice inferInstance
  forgetBasedSphere (constantLoops q) (positiveBasedLoopClass o q)

theorem positiveFreeLoopClass_eq (o : TangentOrientationSection M) (q : M) :
    positiveFreeLoopClass o = forgetBasedSphere (constantLoops q) (positiveBasedLoopClass o q) := by
  have hpc : PathConnectedSpace M := inferInstance
  let q₀ : M := Classical.choice (inferInstance : Nonempty M)
  let p : Path q₀ q := PathConnectedSpace.somePath q₀ q
  have h2q : Subsingleton (HomotopyGroup (Fin 2) M q) := (rfs_homotopy_groups q).1
  have h2q₀ : Subsingleton (HomotopyGroup (Fin 2) M q₀) := (rfs_homotopy_groups q₀).1
  have hbase : positiveFreeLoopClass o =
      forgetBasedSphere (constantLoops q₀) (positiveBasedLoopClass o q₀) := rfl
  rw [hbase]
  have htransport : DifferentialGeometry.Topology.homotopyGroupTransport 2 p
      (positiveHomotopyClass o q₀) = positiveHomotopyClass o q := by
    rw [← pathTransport_eq_homotopyGroupTransport 2 p (positiveHomotopyClass o q₀)]
    exact positiveHomotopyClass_pathTransport o p
  have hmain : positiveBasedLoopClass o q =
      DifferentialGeometry.Topology.homotopyGroupTransport 1 (p.map constantLoops.continuous)
        (positiveBasedLoopClass o q₀) := by
    rw [positiveBasedLoopClass, positiveBasedLoopClass,
      freeLoopAdjunction_eq_piThreeFreeLoopPiTwoMulEquiv q,
      freeLoopAdjunction_eq_piThreeFreeLoopPiTwoMulEquiv q₀, ← htransport]
    exact DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv_transport p
      (positiveHomotopyClass o q₀)
  rw [hmain]
  exact (forgetBasedSphere_homotopyGroupTransport (p.map constantLoops.continuous)
    (positiveBasedLoopClass o q₀)).symm

theorem positiveFreeLoopClass_nontrivial (o : TangentOrientationSection M) (q : M) :
    positiveFreeLoopClass o ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2) (constantLoops q)) := by
  intro h
  rw [positiveFreeLoopClass_eq o q, ← forgetBasedSphere_one (constantLoops q)] at h
  have hb := (rfs_free_loop_class q).2.2.2.injective h
  have ha : positiveHomotopyClass o q = 1 := by
    apply (rfs_free_loop_class q).2.2.1.injective
    exact hb.trans (freeLoopAdjunctionHom q).map_one.symm
  have h10 : (1 : ℤ) = 0 := (positiveHomotopyClass_infiniteOrder o q)
    (by simpa only [zpow_one, zpow_zero] using ha)
  norm_num at h10

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] hT2 hCompact hConnected in
theorem every_continuousLoop_contractible (γ : ContinuousFreeLoop M) : IsContractibleLoop γ := by
  let pγ : Path (γ 0) (γ 0) :=
    { toFun := fun u : I => γ ((u : ℝ) : Circle)
      continuous_toFun :=
        γ.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)
      source' := rfl
      target' := congrArg γ (AddCircle.coe_period (1 : ℝ)) }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic pγ (Path.refl (γ 0))
  let φ : C(I × Icc (0 : ℝ) (0 + 1), M) :=
    ⟨fun q => F.toContinuousMap (q.1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩), by
      apply Continuous.comp F.toContinuousMap.continuous
      apply Continuous.prodMk continuous_fst
      exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _⟩
  have hφ : ∀ s : I, φ (s, zeroPt) = φ (s, onePt) := fun s =>
    ((congrArg (fun u : I => F.toContinuousMap (s, u)) zeroPt_I).trans
      ((F.eq_fst s (by simp)).trans pγ.source')).trans
    (((congrArg (fun u : I => F.toContinuousMap (s, u)) onePt_I).trans
      ((F.eq_fst s (by simp)).trans pγ.target')).symm)
  refine ⟨γ 0, ⟨circleLift (X := M) (Y := I) φ hφ, ?_, ?_⟩⟩
  · intro z
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    exact (circleLift_coe φ hφ 0 (by simpa using ht)).trans ((F.apply_zero _).trans rfl)
  · intro z
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    exact (circleLift_coe φ hφ 1 (by simpa using ht)).trans ((F.apply_one _).trans rfl)

def toContractibleLoops : C(ContinuousFreeLoop M, ContractibleContinuousLoop M) :=
  ⟨fun γ => ⟨γ, every_continuousLoop_contractible γ⟩, continuous_id.subtype_mk _⟩

def positiveFreeContractibleClass (o : TangentOrientationSection M) : FreeContractibleSphereClass M :=
  FreeHomotopyClass.map toContractibleLoops (positiveFreeLoopClass o)

theorem positiveFreeContractibleClass_inclusion (o : TangentOrientationSection M) :
    FreeHomotopyClass.map contractibleLoopInclusion (positiveFreeContractibleClass o) =
      positiveFreeLoopClass o := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  exact FreeHomotopyClass.map_id _

theorem positiveFreeContractibleClass_nontrivial (o : TangentOrientationSection M) (q : M) :
    positiveFreeContractibleClass o ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2) (⟨constantLoops q, isContractibleLoop_constant q⟩ :
        ContractibleContinuousLoop M)) := by
  intro h
  apply positiveFreeLoopClass_nontrivial o q
  have hh := congrArg (FreeHomotopyClass.map contractibleLoopInclusion) h
  rw [positiveFreeContractibleClass_inclusion, FreeHomotopyClass.map_mk] at hh
  exact hh

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]

theorem positiveFreeLoopClass_natural (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1) :
    FreeHomotopyClass.map (loopPostcompose f) (positiveFreeLoopClass oM) =
      positiveFreeLoopClass oN := by
  let q₀ : M := Classical.choice (inferInstance : Nonempty M)
  have hstep : basedHomotopyMap (loopPostcompose f) (constantLoops q₀)
      (positiveBasedLoopClass oM q₀) = positiveBasedLoopClass oN (f q₀) := by
    unfold positiveBasedLoopClass
    rw [freeLoopAdjunction_natural f (positiveHomotopyClass oM q₀),
      rfs_degree_class_transport oM oN f q₀, hf, zpow_one]
  rw [positiveFreeLoopClass_eq oM q₀, positiveFreeLoopClass_eq oN (f q₀),
    forgetBasedSphere_natural f (constantLoops q₀)
      (positiveBasedLoopClass oM q₀), hstep]
  simp only [loopPostcompose_constantLoops]

theorem positiveFreeContractibleClass_natural (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1) :
    FreeHomotopyClass.map (contractibleLoopPostcompose f) (positiveFreeContractibleClass oM) =
      positiveFreeContractibleClass oN := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  have hcomp : (contractibleLoopPostcompose f).comp (toContractibleLoops (M := M)) =
      (toContractibleLoops (M := N)).comp (loopPostcompose f) := rfl
  rw [hcomp, FreeHomotopyClass.map_comp, positiveFreeLoopClass_natural oM oN f hf]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
