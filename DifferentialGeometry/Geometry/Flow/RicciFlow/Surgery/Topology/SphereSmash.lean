import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass
import DifferentialGeometry.Topology.Homotopy.CubeInterior
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation

noncomputable section
open Set Filter
open scoped Topology unitInterval Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private def smashSphereNorth : Sphere 2 :=
  ⟨EuclideanSpace.single 2 1, by
    simp [Sphere, PiLp.norm_single]⟩


def sphereCircleWedge : Set (Sphere 2 × Circle) :=
  {p | p.1 = smashSphereNorth ∨ p.2 = 0}

def sphereCircleSmashSetoid : Setoid (Sphere 2 × Circle) where
  r a b := a = b ∨ (a ∈ sphereCircleWedge ∧ b ∈ sphereCircleWedge)
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr ⟨hab.1, hbc.2⟩


abbrev SphereCircleSmash := Quotient sphereCircleSmashSetoid

def sphereCircleSmashQuotient : C(Sphere 2 × Circle, SphereCircleSmash) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

def sphereCircleSmashBase : SphereCircleSmash :=
  sphereCircleSmashQuotient (smashSphereNorth, 0)


def cubeSphereCircleParameter : C(I^(Fin 3), Sphere 2 × Circle) where
  toFun z := (sphereCubeParameter ![z 0, z 1], ((z 2 : ℝ) : Circle))
  continuous_toFun := by
    apply Continuous.prodMk
    · exact sphereCubeParameter.continuous.comp (by fun_prop)
    · fun_prop

def smashCubeParameter : C(I^(Fin 3), SphereCircleSmash) :=
  sphereCircleSmashQuotient.comp cubeSphereCircleParameter

private def openCubeCoordinate (t : ℝ) : ℝ := (2 * t - 1) / (t * (1 - t))


def orientedSphereTwoInterior (x : EuclideanSpace ℝ (Fin 2)) : ThreeSpace :=
  let u := openCubeCoordinate (x 0)
  let v := openCubeCoordinate (x 1)
  WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
    (u^2+v^2-1) / (1+u^2+v^2)]

def orientedSphereThreeInterior (x : ThreeSpace) : EuclideanSpace ℝ (Fin 4) :=
  let u := openCubeCoordinate (x 0)
  let v := openCubeCoordinate (x 1)
  let w := openCubeCoordinate (x 2)
  WithLp.toLp 2 ![2*u / (1+u^2+v^2+w^2), 2*v / (1+u^2+v^2+w^2),
    2*w / (1+u^2+v^2+w^2), (u^2+v^2+w^2-1) / (1+u^2+v^2+w^2)]

def sphereThreeCubeVector (z : I^(Fin 3)) : EuclideanSpace ℝ (Fin 4) := by
  classical
  exact if z ∈ Cube.boundary (Fin 3) then EuclideanSpace.single 3 1 else
    orientedSphereThreeInterior (WithLp.toLp 2 (fun i => (z i : ℝ)))

theorem sphereThreeCubeVector_norm (z : I^(Fin 3)) : ‖sphereThreeCubeVector z‖ = 1 := by
  classical
  by_cases hb : z ∈ Cube.boundary (Fin 3)
  · simp [sphereThreeCubeVector, hb, PiLp.norm_single]
  let u : ℝ := (2 * (z 0 : ℝ) - 1) / ((z 0 : ℝ) * (1 - (z 0 : ℝ)))
  let v : ℝ := (2 * (z 1 : ℝ) - 1) / ((z 1 : ℝ) * (1 - (z 1 : ℝ)))
  let w : ℝ := (2 * (z 2 : ℝ) - 1) / ((z 2 : ℝ) * (1 - (z 2 : ℝ)))
  have hd : 1 + u^2 + v^2 + w^2 ≠ 0 := by
    nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg w]
  have hsq : ‖sphereThreeCubeVector z‖^2 = 1 := by
    simp only [sphereThreeCubeVector, if_neg hb]
    change ‖(WithLp.toLp 2 ![2*u / (1+u^2+v^2+w^2), 2*v / (1+u^2+v^2+w^2),
      2*w / (1+u^2+v^2+w^2),
      (u^2+v^2+w^2-1) / (1+u^2+v^2+w^2)] : EuclideanSpace ℝ (Fin 4))‖^2 = 1
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    field_simp [hd]
    ring
  nlinarith [norm_nonneg (sphereThreeCubeVector z)]


private def sphereTwoInteriorParam (p : ℝ × ℝ) : ThreeSpace :=
  WithLp.toLp 2 ![2 * p.1 / (1 + p.1 ^ 2 + p.2 ^ 2), -2 * p.2 / (1 + p.1 ^ 2 + p.2 ^ 2),
    (p.1 ^ 2 + p.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2 ^ 2)]

private def sphereThreeInteriorParam (p : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![2 * p.1 / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2),
    2 * p.2.1 / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2),
    2 * p.2.2 / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2),
    (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)]

private lemma orientedSphereTwoInterior_eq_param (x : EuclideanSpace ℝ (Fin 2)) :
    orientedSphereTwoInterior x =
      sphereTwoInteriorParam (openCubeCoordinate (x 0), openCubeCoordinate (x 1)) := by
  simp only [orientedSphereTwoInterior, sphereTwoInteriorParam]

private lemma orientedSphereThreeInterior_eq_param (x : ThreeSpace) :
    orientedSphereThreeInterior x =
      sphereThreeInteriorParam
        (openCubeCoordinate (x 0), openCubeCoordinate (x 1), openCubeCoordinate (x 2)) := by
  simp only [orientedSphereThreeInterior, sphereThreeInteriorParam]

private lemma hasDerivAt_openCubeCoordinate (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    HasDerivAt (fun s : ℝ => (2 * s - 1) / (s * (1 - s)))
      ((2 * t ^ 2 - 2 * t + 1) / (t * (1 - t)) ^ 2) t := by
  have hden : t * (1 - t) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  have hnum : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).sub_const (1 : ℝ)
  have hq : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
    HasDerivAt.const_sub (x := t) (1 : ℝ) (hasDerivAt_id t)
  have hd : HasDerivAt (fun s : ℝ => s * (1 - s)) (1 - 2 * t) t := by
    have h := (hasDerivAt_id t).mul hq
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  refine (hnum.div hd hden).congr_deriv ?_
  field_simp [hden]
  ring

private lemma vec4_two (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 2 = c := by
  rw [Matrix.cons_val_two]
  rfl

private lemma vec4_three (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 3 = d := by
  rw [Matrix.cons_val_three]
  rfl

private lemma norm_sq_sphereThreeInteriorParam (p : ℝ × ℝ × ℝ) :
    ‖sphereThreeInteriorParam p‖ ^ 2 = 1 := by
  have hd : 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≠ 0 := by positivity
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    vec4_two, vec4_three]
  field_simp
  ring

private lemma inner_sphereThreeInteriorParam_single (p : ℝ × ℝ × ℝ) :
    inner ℝ (sphereThreeInteriorParam p) (EuclideanSpace.single 3 1) =
      (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  rw [EuclideanSpace.inner_single_right]
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply, vec4_three]
  simp

private lemma norm_single_three : ‖(EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 1 := by
  rw [PiLp.norm_single]
  norm_num

private lemma norm_sq_sphereThreeInteriorParam_sub_single (p : ℝ × ℝ × ℝ) :
    ‖sphereThreeInteriorParam p - EuclideanSpace.single 3 1‖ ^ 2 =
      4 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) := by
  have hd : 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≠ 0 := by positivity
  rw [norm_sub_sq_real, norm_sq_sphereThreeInteriorParam, inner_sphereThreeInteriorParam_single,
    norm_single_three]
  field_simp
  ring

private lemma continuous_sphereTwoInteriorParam : Continuous sphereTwoInteriorParam := by
  have hD : Continuous fun p : ℝ × ℝ => 1 + p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  have hDne : ∀ p : ℝ × ℝ, 1 + p.1 ^ 2 + p.2 ^ 2 ≠ 0 := fun p => by positivity
  have hA : Continuous fun p : ℝ × ℝ => 2 * p.1 := by fun_prop
  have hB : Continuous fun p : ℝ × ℝ => 2 * p.2 := by fun_prop
  have hC : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 - 1 := by fun_prop
  unfold sphereTwoInteriorParam
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i <;>
    simp only [neg_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    first
      | exact hA.div₀ hD hDne
      | exact hB.neg.div₀ hD hDne
      | exact hC.div₀ hD hDne

private lemma continuous_sphereThreeInteriorParam : Continuous sphereThreeInteriorParam := by
  have hD : Continuous fun p : ℝ × ℝ × ℝ => 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by fun_prop
  have hDne : ∀ p : ℝ × ℝ × ℝ, 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≠ 0 := fun p => by positivity
  have hA : Continuous fun p : ℝ × ℝ × ℝ => 2 * p.1 := by fun_prop
  have hB : Continuous fun p : ℝ × ℝ × ℝ => 2 * p.2.1 := by fun_prop
  have hC : Continuous fun p : ℝ × ℝ × ℝ => 2 * p.2.2 := by fun_prop
  have hE : Continuous fun p : ℝ × ℝ × ℝ => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1 := by fun_prop
  unfold sphereThreeInteriorParam
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    first
      | exact hA.div₀ hD hDne
      | exact hB.div₀ hD hDne
      | exact hC.div₀ hD hDne
      | exact hE.div₀ hD hDne

private lemma one_div_two_mul_le_abs_openCubeCoordinate_left (t : ℝ) (h0 : 0 < t)
    (h1 : t ≤ 1 / 4) : 1 / (2 * t) ≤ |(2 * t - 1) / (t * (1 - t))| := by
  have h2 : (0 : ℝ) < 1 - t := by linarith
  have hpos : 0 < t * (1 - t) := mul_pos h0 h2
  have hneg : 2 * t - 1 < 0 := by linarith
  have hval : |(2 * t - 1) / (t * (1 - t))| = (1 - 2 * t) / (t * (1 - t)) := by
    rw [abs_div, abs_of_pos hpos, abs_of_neg hneg]
    ring_nf
  rw [hval, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t) hpos]
  nlinarith

private lemma one_div_two_mul_le_abs_openCubeCoordinate_right (t : ℝ) (h0 : t < 1)
    (h1 : 3 / 4 ≤ t) : 1 / (2 * (1 - t)) ≤ |(2 * t - 1) / (t * (1 - t))| := by
  have h2 : (0 : ℝ) < 1 - t := by linarith
  have ht0 : 0 < t := by linarith
  have hpos : 0 < t * (1 - t) := mul_pos ht0 h2
  have hpos' : 0 < 2 * t - 1 := by linarith
  have hval : |(2 * t - 1) / (t * (1 - t))| = (2 * t - 1) / (t * (1 - t)) := by
    rw [abs_div, abs_of_pos hpos, abs_of_pos hpos']
  rw [hval, div_le_div_iff₀ (by positivity) hpos]
  nlinarith

private lemma continuousAt_cubeCoords_three (z : I^(Fin 3)) (hz : z ∉ Cube.boundary (Fin 3)) :
    ContinuousAt (fun z' : I^(Fin 3) =>
      (openCubeCoordinate ((z' 0 : I) : ℝ), openCubeCoordinate ((z' 1 : I) : ℝ),
        openCubeCoordinate ((z' 2 : I) : ℝ))) z := by
  have hmem : ∀ i : Fin 3, ((z i : I) : ℝ) ≠ 0 ∧ ((z i : I) : ℝ) ≠ 1 := by
    intro i
    constructor
    · intro hc
      exact hz ⟨i, Or.inl (Subtype.ext hc)⟩
    · intro hc
      exact hz ⟨i, Or.inr (Subtype.ext hc)⟩
  have hc : ∀ i : Fin 3, ContinuousAt (fun z' : I^(Fin 3) =>
      openCubeCoordinate ((z' i : I) : ℝ)) z := by
    intro i
    have h1 : ContinuousAt (fun z' : I^(Fin 3) => ((z' i : I) : ℝ)) z :=
      ContinuousAt.comp continuous_subtype_val.continuousAt (continuous_apply i).continuousAt
    exact ContinuousAt.comp (f := fun z' : I^(Fin 3) => ((z' i : I) : ℝ))
      ((hasDerivAt_openCubeCoordinate _ (hmem i).1 (hmem i).2).continuousAt) h1
  exact ContinuousAt.prodMk (hc 0) (ContinuousAt.prodMk (hc 1) (hc 2))

private lemma tendsto_sphereThreeCubeVector_of_boundary (z : I^(Fin 3)) (i : Fin 3)
    (hi : ((z i : I) : ℝ) = 0 ∨ ((z i : I) : ℝ) = 1) :
    Tendsto sphereThreeCubeVector (𝓝 z) (𝓝 (EuclideanSpace.single 3 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨δ, hδ1, hδε, hδpos⟩ : ∃ δ : ℝ, δ ≤ 1 / 4 ∧ δ ≤ ε / 8 ∧ 0 < δ :=
    ⟨min (1 / 4) (ε / 8), min_le_left _ _, min_le_right _ _, lt_min (by norm_num) hε8⟩
  have core : ∀ z' : I^(Fin 3), z' ∉ Cube.boundary (Fin 3) →
      1 / (2 * δ) ≤ |openCubeCoordinate ((z' i : I) : ℝ)| →
      dist (sphereThreeCubeVector z') (EuclideanSpace.single 3 1) < ε := by
    intro z' hb' hbound
    have hval : sphereThreeCubeVector z' =
        sphereThreeInteriorParam (openCubeCoordinate ((z' 0 : I) : ℝ),
          openCubeCoordinate ((z' 1 : I) : ℝ), openCubeCoordinate ((z' 2 : I) : ℝ)) := by
      simp only [sphereThreeCubeVector, hb', if_false]
      exact orientedSphereThreeInterior_eq_param _
    have hsum : (1 / (2 * δ)) ^ 2 ≤ (openCubeCoordinate ((z' 0 : I) : ℝ)) ^ 2 +
        (openCubeCoordinate ((z' 1 : I) : ℝ)) ^ 2 +
        (openCubeCoordinate ((z' 2 : I) : ℝ)) ^ 2 := by
      have hsq : (1 / (2 * δ)) ^ 2 ≤ (openCubeCoordinate ((z' i : I) : ℝ)) ^ 2 := by
        rw [← sq_abs (openCubeCoordinate ((z' i : I) : ℝ))]
        exact pow_le_pow_left₀ (by positivity) hbound 2
      have hle : (openCubeCoordinate ((z' i : I) : ℝ)) ^ 2 ≤
          ∑ j : Fin 3, (openCubeCoordinate ((z' j : I) : ℝ)) ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin 3 =>
          (openCubeCoordinate ((z' j : I) : ℝ)) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [Fin.sum_univ_three] at hle
      exact le_trans hsq hle
    have hpos : 0 < (1 / (2 * δ)) ^ 2 := by positivity
    have h4 : 4 / ((openCubeCoordinate ((z' 0 : I) : ℝ)) ^ 2 +
        (openCubeCoordinate ((z' 1 : I) : ℝ)) ^ 2 +
        (openCubeCoordinate ((z' 2 : I) : ℝ)) ^ 2 + 1) < ε ^ 2 := by
      have hmono : 4 / ((openCubeCoordinate ((z' 0 : I) : ℝ)) ^ 2 +
          (openCubeCoordinate ((z' 1 : I) : ℝ)) ^ 2 +
          (openCubeCoordinate ((z' 2 : I) : ℝ)) ^ 2 + 1) ≤ 4 / (1 / (2 * δ)) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
      have h16 : 4 / (1 / (2 * δ)) ^ 2 = 16 * δ ^ 2 := by
        field_simp
        ring
      have hδ2 : 16 * δ ^ 2 ≤ ε ^ 2 / 4 := by nlinarith [hδε, hδpos, hε]
      have hfin : ε ^ 2 / 4 < ε ^ 2 := by nlinarith [hε]
      linarith [hmono, h16 ▸ hmono, hδ2, hfin]
    rw [hval, dist_eq_norm]
    have hsq : ‖sphereThreeInteriorParam (openCubeCoordinate ((z' 0 : I) : ℝ),
        openCubeCoordinate ((z' 1 : I) : ℝ),
        openCubeCoordinate ((z' 2 : I) : ℝ)) -
        EuclideanSpace.single 3 1‖ ^ 2 < ε ^ 2 := by
      rw [norm_sq_sphereThreeInteriorParam_sub_single]
      exact h4
    nlinarith [norm_nonneg (sphereThreeInteriorParam
      (openCubeCoordinate ((z' 0 : I) : ℝ), openCubeCoordinate ((z' 1 : I) : ℝ),
        openCubeCoordinate ((z' 2 : I) : ℝ)) - EuclideanSpace.single 3 1)]
  rcases hi with hi | hi
  · have hU : {z' : I^(Fin 3) | ((z' i : I) : ℝ) < δ} ∈ 𝓝 z := by
      refine IsOpen.mem_nhds ?_ ?_
      · exact isOpen_lt (continuous_subtype_val.comp (continuous_apply i)) continuous_const
      · simp only [Set.mem_ofPred_eq]
        rw [hi]
        exact hδpos
    filter_upwards [hU] with z' hz'i
    by_cases hb' : z' ∈ Cube.boundary (Fin 3)
    · have hbval : sphereThreeCubeVector z' = EuclideanSpace.single 3 1 := by
        simp only [sphereThreeCubeVector, hb', if_true]
      rw [hbval, dist_self]
      exact hε
    · refine core z' hb' ?_
      have hne : ((z' i : I) : ℝ) ≠ 0 := fun hc => hb' ⟨i, Or.inl (Subtype.ext hc)⟩
      have hge : (0 : ℝ) ≤ ((z' i : I) : ℝ) := (z' i).2.1
      have hgt : 0 < ((z' i : I) : ℝ) := lt_of_le_of_ne hge (Ne.symm hne)
      have h1 : 1 / (2 * δ) ≤ 1 / (2 * ((z' i : I) : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact le_trans h1
        (one_div_two_mul_le_abs_openCubeCoordinate_left _ hgt (by linarith [hz'i, hδ1]))
  · have hU : {z' : I^(Fin 3) | 1 - δ < ((z' i : I) : ℝ)} ∈ 𝓝 z := by
      refine IsOpen.mem_nhds ?_ ?_
      · exact isOpen_lt continuous_const (continuous_subtype_val.comp (continuous_apply i))
      · simp only [Set.mem_ofPred_eq]
        rw [hi]
        linarith
    filter_upwards [hU] with z' hz'i
    by_cases hb' : z' ∈ Cube.boundary (Fin 3)
    · have hbval : sphereThreeCubeVector z' = EuclideanSpace.single 3 1 := by
        simp only [sphereThreeCubeVector, hb', if_true]
      rw [hbval, dist_self]
      exact hε
    · refine core z' hb' ?_
      have hne : ((z' i : I) : ℝ) ≠ 1 := fun hc => hb' ⟨i, Or.inr (Subtype.ext hc)⟩
      have hle : ((z' i : I) : ℝ) ≤ 1 := (z' i).2.2
      have hlt : ((z' i : I) : ℝ) < 1 := lt_of_le_of_ne hle hne
      have h1m : 1 - ((z' i : I) : ℝ) < δ := by linarith
      have h1 : 1 / (2 * δ) ≤ 1 / (2 * (1 - ((z' i : I) : ℝ))) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact le_trans h1
        (one_div_two_mul_le_abs_openCubeCoordinate_right _ hlt (by linarith [h1m, hδ1]))

theorem sphereThreeCubeVector_continuous : Continuous sphereThreeCubeVector := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ Cube.boundary (Fin 3)
  · have hzval : sphereThreeCubeVector z = EuclideanSpace.single 3 1 := by
      simp only [sphereThreeCubeVector, hz, if_true]
    rw [ContinuousAt, hzval]
    obtain ⟨i, hi | hi⟩ := hz
    · exact tendsto_sphereThreeCubeVector_of_boundary z i (Or.inl (by rw [hi]; rfl))
    · exact tendsto_sphereThreeCubeVector_of_boundary z i (Or.inr (by rw [hi]; rfl))
  · have hU : (Cube.boundary (Fin 3))ᶜ ∈ 𝓝 z := by
      refine IsOpen.mem_nhds ?_ hz
      rw [← DifferentialGeometry.Topology.cubeInterior_eq_compl_boundary]
      exact DifferentialGeometry.Topology.isOpen_cubeInterior (Fin 3)
    have heq : (fun z' : I^(Fin 3) => sphereThreeInteriorParam
          (openCubeCoordinate ((z' 0 : I) : ℝ), openCubeCoordinate ((z' 1 : I) : ℝ),
            openCubeCoordinate ((z' 2 : I) : ℝ))) =ᶠ[𝓝 z]
        (fun z' : I^(Fin 3) => sphereThreeCubeVector z') := by
      filter_upwards [hU] with z' hz'
      have hz'' : z' ∉ Cube.boundary (Fin 3) := hz'
      simp only [sphereThreeCubeVector, hz'', if_false]
      simpa only [PiLp.toLp_apply] using (orientedSphereThreeInterior_eq_param
        (WithLp.toLp 2 fun i : Fin 3 => ((z' i : I) : ℝ))).symm
    refine ContinuousAt.congr ?_ heq
    exact ContinuousAt.comp (f := fun z' : I^(Fin 3) =>
        (openCubeCoordinate ((z' 0 : I) : ℝ), openCubeCoordinate ((z' 1 : I) : ℝ),
          openCubeCoordinate ((z' 2 : I) : ℝ)))
      continuous_sphereThreeInteriorParam.continuousAt (continuousAt_cubeCoords_three z hz)

def sphereThreeCubeParameter : C(I^(Fin 3), Sphere 3) :=
  ⟨fun z => ⟨sphereThreeCubeVector z, by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereThreeCubeVector_norm z⟩,
    sphereThreeCubeVector_continuous.subtype_mk (fun z => by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using
        sphereThreeCubeVector_norm z)⟩

theorem exists_unique_standardSmashHomeomorph :
    ∃! e : SphereCircleSmash ≃ₜ Sphere 3,
      (⟨e, e.continuous⟩ : C(SphereCircleSmash, Sphere 3)).comp smashCubeParameter =
        sphereThreeCubeParameter := by
  sorry

def standardSmashHomeomorph : SphereCircleSmash ≃ₜ Sphere 3 :=
  Classical.choose exists_unique_standardSmashHomeomorph

theorem standardSmashHomeomorph_cube :
    (⟨standardSmashHomeomorph, standardSmashHomeomorph.continuous⟩ :
      C(SphereCircleSmash, Sphere 3)).comp smashCubeParameter = sphereThreeCubeParameter :=
  (Classical.choose_spec exists_unique_standardSmashHomeomorph).1


theorem sphereCubeParameter_interior (z : I^(Fin 2)) (hz : z ∉ Cube.boundary (Fin 2)) :
    (sphereCubeParameter z : ThreeSpace) =
      orientedSphereTwoInterior (WithLp.toLp 2 (fun i => (z i : ℝ))) := by
  classical
  simp [sphereCubeParameter, sphereCubeVector, hz, orientedSphereTwoInterior,
    openCubeCoordinate]


theorem sphereTwo_parameter_positive (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereTwoInterior x ∧
      (0 : ℝ) < Matrix.det (fun i j : Fin 3 =>
        Fin.cases (orientedSphereTwoInterior x i)
          (fun k => (fderiv ℝ orientedSphereTwoInterior x
            (EuclideanSpace.single k 1)) i) j) := by
  sorry

theorem standardSmash_parameter_positive (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereThreeInterior x ∧
      (0 : ℝ) < Matrix.det (fun i j : Fin 4 =>
        Fin.cases (orientedSphereThreeInterior x i)
          (fun k => (fderiv ℝ orientedSphereThreeInterior x
            (EuclideanSpace.single k 1)) i) j) := by
  sorry


theorem standardSmashHomeomorph_interior (z : I^(Fin 3))
    (hz : z ∉ Cube.boundary (Fin 3)) :
    (standardSmashHomeomorph (smashCubeParameter z) : EuclideanSpace ℝ (Fin 4)) =
      orientedSphereThreeInterior (WithLp.toLp 2 (fun i => (z i : ℝ))) := by
  have h := congrArg (fun f : C(I^(Fin 3), Sphere 3) => (f z : EuclideanSpace ℝ (Fin 4)))
    standardSmashHomeomorph_cube
  dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, sphereThreeCubeParameter] at h
  simpa [sphereThreeCubeVector, hz] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
