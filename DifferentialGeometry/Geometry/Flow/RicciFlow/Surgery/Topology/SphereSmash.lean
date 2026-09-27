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

private lemma sp_oc_eq_sub (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    openCubeCoordinate t = 1 / (1 - t) - 1 / t := by
  unfold openCubeCoordinate
  field_simp
  ring

private lemma sp_oc_inj {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : openCubeCoordinate s = openCubeCoordinate t) : s = t := by
  have hs0' : s ≠ 0 := ne_of_gt hs0
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hfac : 0 < 1 - s - t + 2 * s * t := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - s) (by linarith : (0 : ℝ) < 1 - t),
      mul_pos hs0 ht0]
  have h2 : (s - t) * (1 - s - t + 2 * s * t) = 0 := by
    simp only [openCubeCoordinate] at h
    rw [div_eq_div_iff (mul_ne_zero hs0' (by linarith)) (mul_ne_zero ht0' (by linarith))] at h
    nlinarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 (ne_of_gt hfac)

private lemma sp_oc_surj (u : ℝ) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ openCubeCoordinate t = u := by
  set δ : ℝ := 1 / (3 + |u|) with hδ
  have h3u : 0 < 3 + |u| := by positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδlt : δ < 1 := by
    rw [hδ, div_lt_one h3u]
    linarith [abs_nonneg u]
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ h3u (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg u]
  have hone : 1 / δ = 3 + |u| := by rw [hδ, one_div_one_div]
  have hleft : openCubeCoordinate δ < u := by
    have h0 : 1 / (1 - δ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      linarith
    rw [sp_oc_eq_sub δ (ne_of_gt hδpos) (by linarith)]
    nlinarith [h0, hone, neg_le_abs u]
  have hright : u < openCubeCoordinate (1 - δ) := by
    have h0 : 1 / (1 - (1 - δ)) = 1 / δ := by ring_nf
    have h1 : 1 / (1 - δ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      linarith
    rw [sp_oc_eq_sub (1 - δ) (by linarith) (by linarith), h0]
    nlinarith [h1, hone, le_abs_self u]
  have hcont : ContinuousOn openCubeCoordinate (Icc δ (1 - δ)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hδpos ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 (by linarith)
    exact mul_ne_zero (ne_of_gt ht0) (by linarith)
  have hmem : u ∈ Icc (openCubeCoordinate δ) (openCubeCoordinate (1 - δ)) :=
    ⟨le_of_lt hleft, le_of_lt hright⟩
  obtain ⟨t, ht, htu⟩ := (intermediate_value_Icc (by linarith : δ ≤ 1 - δ) hcont) hmem
  exact ⟨t, lt_of_lt_of_le hδpos ht.1, lt_of_le_of_lt ht.2 (by linarith), htu⟩

private lemma sp_vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := by
  rw [Matrix.cons_val_two]
  rfl

private lemma sp_sphereCubeVector_eq_param (x : I^(Fin 2)) (hx : x ∉ Cube.boundary (Fin 2)) :
    sphereCubeVector x = sphereTwoInteriorParam (openCubeCoordinate ((x 0 : I) : ℝ),
      openCubeCoordinate ((x 1 : I) : ℝ)) := by
  classical
  simp only [sphereCubeVector, if_neg hx, sphereTwoInteriorParam, openCubeCoordinate]

private lemma sp_sphereCubeVector_eq_north (x : I^(Fin 2)) (hx : x ∈ Cube.boundary (Fin 2)) :
    sphereCubeVector x = EuclideanSpace.single 2 1 := by
  classical
  simp only [sphereCubeVector, if_pos hx]

private lemma sp_single_two : (EuclideanSpace.single 2 1 : ThreeSpace) = PiLp.single 2 2 1 := rfl

private lemma sp_single_two_zero : ((EuclideanSpace.single 2 1 : ThreeSpace)) 0 = 0 := by
  have h : ¬ ((0 : Fin 3) = 2) := by decide
  simp only [sp_single_two, PiLp.single_apply, h, if_false]

private lemma sp_single_two_one : ((EuclideanSpace.single 2 1 : ThreeSpace)) 1 = 0 := by
  have h : ¬ ((1 : Fin 3) = 2) := by decide
  simp only [sp_single_two, PiLp.single_apply, h, if_false]

private lemma sp_single_two_two : ((EuclideanSpace.single 2 1 : ThreeSpace)) 2 = 1 := by
  simp only [sp_single_two, PiLp.single_apply]
  norm_num

private lemma sp_two_denom_ne (p : ℝ × ℝ) : p.1 ^ 2 + p.2 ^ 2 + 1 ≠ 0 := by positivity

private lemma sp_two_norm_sq_sub (p : ℝ × ℝ) :
    ‖sphereTwoInteriorParam p - EuclideanSpace.single 2 1‖ ^ 2 =
      4 / (p.1 ^ 2 + p.2 ^ 2 + 1) := by
  have hd := sp_two_denom_ne p
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [PiLp.sub_apply, sp_single_two_zero, sp_single_two_one, sp_single_two_two, sub_zero,
    sphereTwoInteriorParam, Matrix.cons_val_zero, Matrix.cons_val_one, sp_vec3_two]
  field_simp
  ring

private lemma sp_two_param_zero (p : ℝ × ℝ) :
    sphereTwoInteriorParam p 0 = 2 * p.1 / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  simp only [sphereTwoInteriorParam, PiLp.toLp_apply, Matrix.cons_val_zero]

private lemma sp_two_param_one (p : ℝ × ℝ) :
    sphereTwoInteriorParam p 1 = -2 * p.2 / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  simp only [sphereTwoInteriorParam, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]

private lemma sp_two_recover_zero (p : ℝ × ℝ) :
    2 * (sphereTwoInteriorParam p 0) /
      ‖sphereTwoInteriorParam p - EuclideanSpace.single 2 1‖ ^ 2 = p.1 := by
  have hd := sp_two_denom_ne p
  rw [sp_two_param_zero p, sp_two_norm_sq_sub]
  field_simp
  ring

private lemma sp_two_recover_one (p : ℝ × ℝ) :
    -2 * (sphereTwoInteriorParam p 1) /
      ‖sphereTwoInteriorParam p - EuclideanSpace.single 2 1‖ ^ 2 = p.2 := by
  have hd := sp_two_denom_ne p
  rw [sp_two_param_one p, sp_two_norm_sq_sub]
  field_simp
  ring

private lemma sp_two_injective : Function.Injective sphereTwoInteriorParam := by
  intro p q hpq
  have h0 : p.1 = q.1 := by
    rw [← sp_two_recover_zero p, ← sp_two_recover_zero q, hpq]
  have h1 : p.2 = q.2 := by
    rw [← sp_two_recover_one p, ← sp_two_recover_one q, hpq]
  exact Prod.ext h0 h1

private lemma sp_two_ne_north (p : ℝ × ℝ) :
    sphereTwoInteriorParam p ≠ EuclideanSpace.single 2 1 := by
  intro h
  have h2 : ‖sphereTwoInteriorParam p - EuclideanSpace.single 2 1‖ ^ 2 = 0 := by
    rw [h, sub_self]
    simp
  rw [sp_two_norm_sq_sub] at h2
  have h3 : 0 < 4 / (p.1 ^ 2 + p.2 ^ 2 + 1) := by positivity
  linarith

private lemma sp_not_boundary_coords {N : Type*} {y : I^N} (hy : y ∉ Cube.boundary N)
    (i : N) : 0 < ((y i : I) : ℝ) ∧ ((y i : I) : ℝ) < 1 := by
  have h0 : ((y i : I) : ℝ) ≠ 0 := fun hc => hy ⟨i, Or.inl (Subtype.ext hc)⟩
  have h1 : ((y i : I) : ℝ) ≠ 1 := fun hc => hy ⟨i, Or.inr (Subtype.ext hc)⟩
  exact ⟨lt_of_le_of_ne (y i).2.1 (Ne.symm h0), lt_of_le_of_ne (y i).2.2 h1⟩

private lemma sp_two_fiber (a b : I^(Fin 2)) :
    sphereCubeVector a = sphereCubeVector b ↔
      a = b ∨ (a ∈ Cube.boundary (Fin 2) ∧ b ∈ Cube.boundary (Fin 2)) := by
  classical
  constructor
  · intro h
    by_cases ha : a ∈ Cube.boundary (Fin 2)
    · by_cases hb : b ∈ Cube.boundary (Fin 2)
      · exact Or.inr ⟨ha, hb⟩
      · rw [sp_sphereCubeVector_eq_north a ha, sp_sphereCubeVector_eq_param b hb] at h
        exact absurd h.symm (sp_two_ne_north _)
    · by_cases hb : b ∈ Cube.boundary (Fin 2)
      · rw [sp_sphereCubeVector_eq_param a ha, sp_sphereCubeVector_eq_north b hb] at h
        exact absurd h (sp_two_ne_north _)
      · refine Or.inl (funext fun i => Subtype.ext ?_)
        have hp : sphereTwoInteriorParam (openCubeCoordinate ((a 0 : I) : ℝ),
            openCubeCoordinate ((a 1 : I) : ℝ)) =
            sphereTwoInteriorParam (openCubeCoordinate ((b 0 : I) : ℝ),
              openCubeCoordinate ((b 1 : I) : ℝ)) := by
          rw [← sp_sphereCubeVector_eq_param a ha, ← sp_sphereCubeVector_eq_param b hb]
          exact h
        have hpq := sp_two_injective hp
        have h0 := sp_not_boundary_coords ha 0
        have h1 := sp_not_boundary_coords hb 0
        have h2 := sp_not_boundary_coords ha 1
        have h3 := sp_not_boundary_coords hb 1
        fin_cases i
        · exact sp_oc_inj h0.1 h0.2 h1.1 h1.2 (congrArg Prod.fst hpq)
        · exact sp_oc_inj h2.1 h2.2 h3.1 h3.2 (congrArg Prod.snd hpq)
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [sp_sphereCubeVector_eq_north a ha, sp_sphereCubeVector_eq_north b hb]

private lemma sp_two_eq_north_iff (z : I^(Fin 2)) :
    sphereCubeVector z = EuclideanSpace.single 2 1 ↔ z ∈ Cube.boundary (Fin 2) := by
  constructor
  · intro h
    by_contra hz
    rw [sp_sphereCubeVector_eq_param z hz] at h
    exact sp_two_ne_north _ h
  · exact sp_sphereCubeVector_eq_north z

private lemma sp_two_cubeParam_eq_north_iff (z : I^(Fin 2)) :
    sphereCubeParameter z = smashSphereNorth ↔ z ∈ Cube.boundary (Fin 2) := by
  constructor
  · intro h
    have hv : sphereCubeVector z = EuclideanSpace.single 2 1 := by
      have h1 := congrArg (fun y : Sphere 2 => (y : ThreeSpace)) h
      have h2 : ((sphereCubeParameter z : Sphere 2) : ThreeSpace) = sphereCubeVector z := rfl
      have h3 : ((smashSphereNorth : Sphere 2) : ThreeSpace) = EuclideanSpace.single 2 1 := rfl
      rw [h2, h3] at h1
      exact h1
    exact (sp_two_eq_north_iff z).mp hv
  · intro hz
    apply Subtype.ext
    have h2 : ((sphereCubeParameter z : Sphere 2) : ThreeSpace) = sphereCubeVector z := rfl
    have h3 : ((smashSphereNorth : Sphere 2) : ThreeSpace) = EuclideanSpace.single 2 1 := rfl
    rw [h2, h3]
    exact sp_sphereCubeVector_eq_north z hz
private lemma sp_two_param_two (p : ℝ × ℝ) :
    sphereTwoInteriorParam p 2 = (p.1 ^ 2 + p.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  simp only [sphereTwoInteriorParam, PiLp.toLp_apply]
  rw [Matrix.cons_val_two]
  rfl

private lemma sp_two_recover_aux (a b c S : ℝ) (hS : S ≠ 0)
    (hp : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hS2 : S = 2 - 2 * c) :
    sphereTwoInteriorParam (2 * a / S, -2 * b / S) = WithLp.toLp 2 ![a, b, c] := by
  have hD : 1 + (2 * a / S) ^ 2 + (-2 * b / S) ^ 2 = 4 / S := by
    field_simp
    nlinarith [hp, hS2]
  have hE : (2 * a / S) ^ 2 + (-2 * b / S) ^ 2 - 1 = 4 * c / S := by
    field_simp
    nlinarith [hp, hS2]
  apply PiLp.ext
  intro i
  fin_cases i
  · change sphereTwoInteriorParam (2 * a / S, -2 * b / S) 0 = a
    rw [sp_two_param_zero, hD]
    field_simp
    ring
  · change sphereTwoInteriorParam (2 * a / S, -2 * b / S) 1 = b
    rw [sp_two_param_one, hD]
    field_simp
    ring
  · change sphereTwoInteriorParam (2 * a / S, -2 * b / S) 2 = c
    rw [sp_two_param_two, hD, hE]
    field_simp

private lemma sp_two_recover (v : ThreeSpace) (hv : ‖v‖ = 1)
    (hne : v ≠ EuclideanSpace.single 2 1) :
    sphereTwoInteriorParam (2 * v 0 / ‖v - EuclideanSpace.single 2 1‖ ^ 2,
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
    simp only [PiLp.sub_apply, sp_single_two_zero, sp_single_two_one, sp_single_two_two, sub_zero]
    nlinarith [hv2]
  rw [sp_two_recover_aux (v 0) (v 1) (v 2) _ hTne hv2 hT]
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

private lemma sp_sphereCubeParameter_surjective : Function.Surjective sphereCubeParameter := by
  intro z
  by_cases hz : (z : ThreeSpace) = EuclideanSpace.single 2 1
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    have h2 : ((sphereCubeParameter 0 : Sphere 2) : ThreeSpace) = sphereCubeVector 0 := rfl
    rw [h2, sp_sphereCubeVector_eq_north 0 ⟨0, Or.inl rfl⟩]
    exact hz.symm
  · obtain ⟨s, hs0, hs1, hsmap⟩ := sp_oc_surj
      (2 * (z : ThreeSpace) 0 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2)
    obtain ⟨r, hr0, hr1, hrmap⟩ := sp_oc_surj
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
    have hpair : (openCubeCoordinate ((x 0 : I) : ℝ), openCubeCoordinate ((x 1 : I) : ℝ)) =
        (2 * (z : ThreeSpace) 0 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2,
          -2 * (z : ThreeSpace) 1 / ‖(z : ThreeSpace) - EuclideanSpace.single 2 1‖ ^ 2) := by
      rw [hx0, hx1]
      refine Prod.ext ?_ ?_
      · simpa using hsmap
      · simpa using hrmap
    apply Subtype.ext
    have h2 : ((sphereCubeParameter x : Sphere 2) : ThreeSpace) = sphereCubeVector x := rfl
    rw [h2, sp_sphereCubeVector_eq_param x hxb, hpair]
    exact sp_two_recover (z : ThreeSpace) hscene hz

private lemma sp_three_denom_ne (p : ℝ × ℝ × ℝ) :
    p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 ≠ 0 := by positivity

private lemma sp_three_param_zero (p : ℝ × ℝ × ℝ) :
    sphereThreeInteriorParam p 0 =
      2 * p.1 / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply, Matrix.cons_val_zero]

private lemma sp_three_param_one (p : ℝ × ℝ × ℝ) :
    sphereThreeInteriorParam p 1 =
      2 * p.2.1 / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]

private lemma sp_three_param_two (p : ℝ × ℝ × ℝ) :
    sphereThreeInteriorParam p 2 =
      2 * p.2.2 / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply, vec4_two]

private lemma sp_three_param_three (p : ℝ × ℝ × ℝ) :
    sphereThreeInteriorParam p 3 =
      (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply, vec4_three]

private lemma sp_three_recover_zero (p : ℝ × ℝ × ℝ) :
    2 * (sphereThreeInteriorParam p 0) /
      ‖sphereThreeInteriorParam p - EuclideanSpace.single 3 1‖ ^ 2 = p.1 := by
  have hd := sp_three_denom_ne p
  rw [sp_three_param_zero p, norm_sq_sphereThreeInteriorParam_sub_single]
  field_simp
  ring

private lemma sp_three_recover_one (p : ℝ × ℝ × ℝ) :
    2 * (sphereThreeInteriorParam p 1) /
      ‖sphereThreeInteriorParam p - EuclideanSpace.single 3 1‖ ^ 2 = p.2.1 := by
  have hd := sp_three_denom_ne p
  rw [sp_three_param_one p, norm_sq_sphereThreeInteriorParam_sub_single]
  field_simp
  ring

private lemma sp_three_recover_two (p : ℝ × ℝ × ℝ) :
    2 * (sphereThreeInteriorParam p 2) /
      ‖sphereThreeInteriorParam p - EuclideanSpace.single 3 1‖ ^ 2 = p.2.2 := by
  have hd := sp_three_denom_ne p
  rw [sp_three_param_two p, norm_sq_sphereThreeInteriorParam_sub_single]
  field_simp
  ring

private lemma sp_three_injective : Function.Injective sphereThreeInteriorParam := by
  intro p q hpq
  have h0 : p.1 = q.1 := by
    rw [← sp_three_recover_zero p, ← sp_three_recover_zero q, hpq]
  have h1 : p.2.1 = q.2.1 := by
    rw [← sp_three_recover_one p, ← sp_three_recover_one q, hpq]
  have h2 : p.2.2 = q.2.2 := by
    rw [← sp_three_recover_two p, ← sp_three_recover_two q, hpq]
  exact Prod.ext h0 (Prod.ext h1 h2)

private lemma sp_three_ne_north (p : ℝ × ℝ × ℝ) :
    sphereThreeInteriorParam p ≠ EuclideanSpace.single 3 1 := by
  intro h
  have h2 : ‖sphereThreeInteriorParam p - EuclideanSpace.single 3 1‖ ^ 2 = 0 := by
    rw [h, sub_self]
    simp
  rw [norm_sq_sphereThreeInteriorParam_sub_single] at h2
  have h3 : 0 < 4 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) := by positivity
  linarith

private lemma sp_single_three :
    (EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4)) = PiLp.single 2 3 1 := rfl

private lemma sp_single_three_zero :
    ((EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))) 0 = 0 := by
  have h : ¬ ((0 : Fin 4) = 3) := by decide
  simp only [sp_single_three, PiLp.single_apply, h, if_false]

private lemma sp_single_three_one :
    ((EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))) 1 = 0 := by
  have h : ¬ ((1 : Fin 4) = 3) := by decide
  simp only [sp_single_three, PiLp.single_apply, h, if_false]

private lemma sp_single_three_two :
    ((EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))) 2 = 0 := by
  have h : ¬ ((2 : Fin 4) = 3) := by decide
  simp only [sp_single_three, PiLp.single_apply, h, if_false]

private lemma sp_single_three_three :
    ((EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))) 3 = 1 := by
  simp only [sp_single_three, PiLp.single_apply]
  norm_num

private lemma sp_threeCubeVector_eq_param (z : I^(Fin 3))
    (hz : z ∉ Cube.boundary (Fin 3)) :
    sphereThreeCubeVector z = sphereThreeInteriorParam (openCubeCoordinate ((z 0 : I) : ℝ),
      openCubeCoordinate ((z 1 : I) : ℝ), openCubeCoordinate ((z 2 : I) : ℝ)) := by
  classical
  simp only [sphereThreeCubeVector, if_neg hz, orientedSphereThreeInterior_eq_param]

private lemma sp_threeCubeVector_eq_north (z : I^(Fin 3))
    (hz : z ∈ Cube.boundary (Fin 3)) :
    sphereThreeCubeVector z = EuclideanSpace.single 3 1 := by
  classical
  simp only [sphereThreeCubeVector, if_pos hz]

private lemma sp_three_fiber (a b : I^(Fin 3)) :
    sphereThreeCubeVector a = sphereThreeCubeVector b ↔
      a = b ∨ (a ∈ Cube.boundary (Fin 3) ∧ b ∈ Cube.boundary (Fin 3)) := by
  classical
  constructor
  · intro h
    by_cases ha : a ∈ Cube.boundary (Fin 3)
    · by_cases hb : b ∈ Cube.boundary (Fin 3)
      · exact Or.inr ⟨ha, hb⟩
      · rw [sp_threeCubeVector_eq_north a ha, sp_threeCubeVector_eq_param b hb] at h
        exact absurd h.symm (sp_three_ne_north _)
    · by_cases hb : b ∈ Cube.boundary (Fin 3)
      · rw [sp_threeCubeVector_eq_param a ha, sp_threeCubeVector_eq_north b hb] at h
        exact absurd h (sp_three_ne_north _)
      · refine Or.inl (funext fun i => Subtype.ext ?_)
        have hp : sphereThreeInteriorParam (openCubeCoordinate ((a 0 : I) : ℝ),
            openCubeCoordinate ((a 1 : I) : ℝ), openCubeCoordinate ((a 2 : I) : ℝ)) =
            sphereThreeInteriorParam (openCubeCoordinate ((b 0 : I) : ℝ),
              openCubeCoordinate ((b 1 : I) : ℝ), openCubeCoordinate ((b 2 : I) : ℝ)) := by
          rw [← sp_threeCubeVector_eq_param a ha, ← sp_threeCubeVector_eq_param b hb]
          exact h
        have hpq := sp_three_injective hp
        have h0 := sp_not_boundary_coords ha 0
        have h1 := sp_not_boundary_coords hb 0
        have h2 := sp_not_boundary_coords ha 1
        have h3 := sp_not_boundary_coords hb 1
        have h4 := sp_not_boundary_coords ha 2
        have h5 := sp_not_boundary_coords hb 2
        fin_cases i
        · exact sp_oc_inj h0.1 h0.2 h1.1 h1.2 (congrArg (fun p : ℝ × ℝ × ℝ => p.1) hpq)
        · exact sp_oc_inj h2.1 h2.2 h3.1 h3.2 (congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hpq)
        · exact sp_oc_inj h4.1 h4.2 h5.1 h5.2 (congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hpq)
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [sp_threeCubeVector_eq_north a ha, sp_threeCubeVector_eq_north b hb]

private lemma sp_three_recover_aux (v0 v1 v2 v3 T : ℝ) (hT : T ≠ 0)
    (hv : v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = 1) (hTv : T = 2 - 2 * v3) :
    sphereThreeInteriorParam (2 * v0 / T, 2 * v1 / T, 2 * v2 / T) =
      WithLp.toLp 2 ![v0, v1, v2, v3] := by
  have hD : 1 + (2 * v0 / T) ^ 2 + (2 * v1 / T) ^ 2 + (2 * v2 / T) ^ 2 = 4 / T := by
    field_simp
    nlinarith [hv, hTv]
  have hE : (2 * v0 / T) ^ 2 + (2 * v1 / T) ^ 2 + (2 * v2 / T) ^ 2 - 1 = 4 * v3 / T := by
    field_simp
    nlinarith [hv, hTv]
  apply PiLp.ext
  intro i
  fin_cases i
  · change sphereThreeInteriorParam (2 * v0 / T, 2 * v1 / T, 2 * v2 / T) 0 = v0
    rw [sp_three_param_zero, hD]
    field_simp
    ring
  · change sphereThreeInteriorParam (2 * v0 / T, 2 * v1 / T, 2 * v2 / T) 1 = v1
    rw [sp_three_param_one, hD]
    field_simp
    ring
  · change sphereThreeInteriorParam (2 * v0 / T, 2 * v1 / T, 2 * v2 / T) 2 = v2
    rw [sp_three_param_two, hD]
    field_simp
    ring
  · change sphereThreeInteriorParam (2 * v0 / T, 2 * v1 / T, 2 * v2 / T) 3 = v3
    rw [sp_three_param_three, hD, hE]
    field_simp

private lemma sp_three_recover (v : EuclideanSpace ℝ (Fin 4)) (hv : ‖v‖ = 1)
    (hne : v ≠ EuclideanSpace.single 3 1) :
    sphereThreeInteriorParam (2 * v 0 / ‖v - EuclideanSpace.single 3 1‖ ^ 2,
      2 * v 1 / ‖v - EuclideanSpace.single 3 1‖ ^ 2,
      2 * v 2 / ‖v - EuclideanSpace.single 3 1‖ ^ 2) = v := by
  have hv2 : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    rw [Fin.sum_univ_four, hv] at h
    norm_num at h
    exact h.symm
  have hTne : ‖v - EuclideanSpace.single 3 1‖ ^ 2 ≠ 0 :=
    ne_of_gt (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2)
  have hT : ‖v - EuclideanSpace.single 3 1‖ ^ 2 = 2 - 2 * (v 3) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp only [PiLp.sub_apply, sp_single_three_zero, sp_single_three_one, sp_single_three_two,
      sp_single_three_three, sub_zero]
    nlinarith [hv2]
  rw [sp_three_recover_aux (v 0) (v 1) (v 2) (v 3) _ hTne hv2 hT]
  apply PiLp.ext
  intro i
  fin_cases i
  · change (WithLp.toLp 2 ![v 0, v 1, v 2, v 3] : EuclideanSpace ℝ (Fin 4)) 0 = v 0
    rw [PiLp.toLp_apply, Matrix.cons_val_zero]
  · change (WithLp.toLp 2 ![v 0, v 1, v 2, v 3] : EuclideanSpace ℝ (Fin 4)) 1 = v 1
    rw [PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
  · change (WithLp.toLp 2 ![v 0, v 1, v 2, v 3] : EuclideanSpace ℝ (Fin 4)) 2 = v 2
    rw [PiLp.toLp_apply, vec4_two]
  · change (WithLp.toLp 2 ![v 0, v 1, v 2, v 3] : EuclideanSpace ℝ (Fin 4)) 3 = v 3
    rw [PiLp.toLp_apply, vec4_three]

private lemma sp_sphereThreeCubeParameter_surjective :
    Function.Surjective sphereThreeCubeParameter := by
  intro z
  by_cases hz : (z : EuclideanSpace ℝ (Fin 4)) = EuclideanSpace.single 3 1
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    have h2 : ((sphereThreeCubeParameter 0 : Sphere 3) : EuclideanSpace ℝ (Fin 4)) =
        sphereThreeCubeVector 0 := rfl
    rw [h2, sp_threeCubeVector_eq_north 0 ⟨0, Or.inl rfl⟩]
    exact hz.symm
  · obtain ⟨a, ha0, ha1, hamap⟩ := sp_oc_surj
      (2 * (z : EuclideanSpace ℝ (Fin 4)) 0 /
        ‖(z : EuclideanSpace ℝ (Fin 4)) - EuclideanSpace.single 3 1‖ ^ 2)
    obtain ⟨b, hb0, hb1, hbmap⟩ := sp_oc_surj
      (2 * (z : EuclideanSpace ℝ (Fin 4)) 1 /
        ‖(z : EuclideanSpace ℝ (Fin 4)) - EuclideanSpace.single 3 1‖ ^ 2)
    obtain ⟨c, hc0, hc1, hcmap⟩ := sp_oc_surj
      (2 * (z : EuclideanSpace ℝ (Fin 4)) 2 /
        ‖(z : EuclideanSpace ℝ (Fin 4)) - EuclideanSpace.single 3 1‖ ^ 2)
    let x : I^(Fin 3) := ![⟨a, le_of_lt ha0, le_of_lt ha1⟩, ⟨b, le_of_lt hb0, le_of_lt hb1⟩,
      ⟨c, le_of_lt hc0, le_of_lt hc1⟩]
    have hx0 : (x 0 : I) = ⟨a, le_of_lt ha0, le_of_lt ha1⟩ := by
      simp only [x, Matrix.cons_val_zero]
    have hx1 : (x 1 : I) = ⟨b, le_of_lt hb0, le_of_lt hb1⟩ := by
      simp only [x, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hx2 : (x 2 : I) = ⟨c, le_of_lt hc0, le_of_lt hc1⟩ := by
      simp only [x]
      rw [Matrix.cons_val_two]
      rfl
    have hxb : x ∉ Cube.boundary (Fin 3) := by
      rintro ⟨i, hi⟩
      fin_cases i
      · rcases hi with hi | hi
        · exact absurd (congrArg Subtype.val hi) (ne_of_gt ha0)
        · exact absurd (congrArg Subtype.val hi) (ne_of_lt ha1)
      · rcases hi with hi | hi
        · exact absurd (congrArg Subtype.val hi) (ne_of_gt hb0)
        · exact absurd (congrArg Subtype.val hi) (ne_of_lt hb1)
      · rcases hi with hi | hi
        · exact absurd (congrArg Subtype.val hi) (ne_of_gt hc0)
        · exact absurd (congrArg Subtype.val hi) (ne_of_lt hc1)
    refine ⟨x, ?_⟩
    have hscene : ‖(z : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using z.2
    have hpair : (openCubeCoordinate ((x 0 : I) : ℝ), openCubeCoordinate ((x 1 : I) : ℝ),
        openCubeCoordinate ((x 2 : I) : ℝ)) =
        (2 * (z : EuclideanSpace ℝ (Fin 4)) 0 /
            ‖(z : EuclideanSpace ℝ (Fin 4)) - EuclideanSpace.single 3 1‖ ^ 2,
          2 * (z : EuclideanSpace ℝ (Fin 4)) 1 /
            ‖(z : EuclideanSpace ℝ (Fin 4)) - EuclideanSpace.single 3 1‖ ^ 2,
          2 * (z : EuclideanSpace ℝ (Fin 4)) 2 /
            ‖(z : EuclideanSpace ℝ (Fin 4)) - EuclideanSpace.single 3 1‖ ^ 2) := by
      rw [hx0, hx1, hx2]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simpa using hamap
      · simpa using hbmap
      · simpa using hcmap
    apply Subtype.ext
    have h2 : ((sphereThreeCubeParameter x : Sphere 3) : EuclideanSpace ℝ (Fin 4)) =
        sphereThreeCubeVector x := rfl
    rw [h2, sp_threeCubeVector_eq_param x hxb, hpair]
    exact sp_three_recover (z : EuclideanSpace ℝ (Fin 4)) hscene hz

private lemma sp_two_eq_north_of_param_eq (z : I^(Fin 2)) (hw : sphereCubeParameter z = smashSphereNorth) :
    sphereCubeVector z = EuclideanSpace.single 2 1 := by
  have h1 := congrArg (fun y : Sphere 2 => (y : ThreeSpace)) hw
  have h2 : ((sphereCubeParameter z : Sphere 2) : ThreeSpace) = sphereCubeVector z := rfl
  have h3 : ((smashSphereNorth : Sphere 2) : ThreeSpace) = EuclideanSpace.single 2 1 := rfl
  rw [h2, h3] at h1
  exact h1

private lemma sp_twoBoundary_to_three {z : I^(Fin 3)} (h : ![z 0, z 1] ∈ Cube.boundary (Fin 2)) :
    z ∈ Cube.boundary (Fin 3) := by
  rcases h with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

private lemma sp_threeBoundary_cases_aux {z : I^(Fin 3)} (hz : z ∈ Cube.boundary (Fin 3)) :
    ![z 0, z 1] ∈ Cube.boundary (Fin 2) ∨ z 2 = (0 : I) ∨ z 2 = (1 : I) := by
  rcases hz with ⟨i, hi⟩
  fin_cases i
  · exact Or.inl ⟨0, by simpa using hi⟩
  · exact Or.inl ⟨1, by simpa using hi⟩
  · rcases hi with hi | hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)

private lemma sp_norm_single_three :
    ‖(EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
  have h := norm_single_three
  nlinarith [norm_nonneg (EuclideanSpace.single 3 1 : EuclideanSpace ℝ (Fin 4))]

private def spNorthThree : Sphere 3 :=
  ⟨EuclideanSpace.single 3 1, by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sp_norm_single_three⟩

private lemma sp_threeCubeParameter_eq_north (z : I^(Fin 3))
    (hz : z ∈ Cube.boundary (Fin 3)) : sphereThreeCubeParameter z = spNorthThree := by
  apply Subtype.ext
  have h2 : ((sphereThreeCubeParameter z : Sphere 3) : EuclideanSpace ℝ (Fin 4)) =
      sphereThreeCubeVector z := rfl
  have h3 : ((spNorthThree : Sphere 3) : EuclideanSpace ℝ (Fin 4)) =
      EuclideanSpace.single 3 1 := rfl
  rw [h2, h3]
  exact sp_threeCubeVector_eq_north z hz

private lemma sp_threeParameter_fiber (a b : I^(Fin 3)) :
    sphereThreeCubeParameter a = sphereThreeCubeParameter b ↔
      a = b ∨ (a ∈ Cube.boundary (Fin 3) ∧ b ∈ Cube.boundary (Fin 3)) := by
  constructor
  · intro h
    have hv : sphereThreeCubeVector a = sphereThreeCubeVector b := by
      have hh := congrArg (fun y : Sphere 3 => (y : EuclideanSpace ℝ (Fin 4))) h
      have h2 : ((sphereThreeCubeParameter a : Sphere 3) : EuclideanSpace ℝ (Fin 4)) =
          sphereThreeCubeVector a := rfl
      have h3 : ((sphereThreeCubeParameter b : Sphere 3) : EuclideanSpace ℝ (Fin 4)) =
          sphereThreeCubeVector b := rfl
      rw [h2, h3] at hh
      exact hh
    exact (sp_three_fiber a b).mp hv
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [sp_threeCubeParameter_eq_north a ha, sp_threeCubeParameter_eq_north b hb]

private lemma sp_mem_wedge_iff (p : Sphere 2 × Circle) :
    p ∈ sphereCircleWedge ↔ p.1 = smashSphereNorth ∨ p.2 = 0 := by
  simp only [sphereCircleWedge, Set.mem_ofPred_eq]

private lemma sp_circle_coe_eq_zero_iff {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (t : Circle) = 0 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    by_cases ht : t = 1
    · exact Or.inr ht
    · refine Or.inl ?_
      have hmem : t ∈ Ico (0 : ℝ) 1 := ⟨h0, lt_of_le_of_ne h1 ht⟩
      exact (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) hmem).mp h
  · rintro (rfl | rfl)
    · exact (AddCircle.coe_zero (p := (1 : ℝ)) : ((0 : ℝ) : Circle) = 0)
    · exact (AddCircle.coe_period (p := (1 : ℝ)) : ((1 : ℝ) : Circle) = 0)

private lemma sp_circle_coe_inj {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1)
    (h : (t : Circle) = (s : Circle)) :
    t = s ∨ (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) := by
  by_cases ht1 : t = 1
  · subst ht1
    have hper : ((1 : ℝ) : Circle) = 0 := AddCircle.coe_period (p := (1 : ℝ))
    rw [hper] at h
    rcases (sp_circle_coe_eq_zero_iff hs.1 hs.2).mp h.symm with h' | h'
    · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · exact Or.inl h'.symm
  · by_cases hs1 : s = 1
    · subst hs1
      have hper : ((1 : ℝ) : Circle) = 0 := AddCircle.coe_period (p := (1 : ℝ))
      rw [hper] at h
      rcases (sp_circle_coe_eq_zero_iff ht.1 ht.2).mp h with h' | h'
      · exact Or.inr (Or.inl ⟨h', rfl⟩)
      · exact Or.inl h'
    · refine Or.inl ?_
      have ht' : t ∈ Ico (0 : ℝ) (0 + 1) := ⟨ht.1, by simpa using lt_of_le_of_ne ht.2 ht1⟩
      have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := ⟨hs.1, by simpa using lt_of_le_of_ne hs.2 hs1⟩
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico ht' hs').mp h

private lemma sp_smash_boundary_wedge (z : I^(Fin 3)) (hz : z ∈ Cube.boundary (Fin 3)) :
    cubeSphereCircleParameter z ∈ sphereCircleWedge := by
  rw [sp_mem_wedge_iff]
  rcases sp_threeBoundary_cases_aux hz with h | h | h
  · left
    change sphereCubeParameter ![z 0, z 1] = smashSphereNorth
    apply Subtype.ext
    have h2 : ((sphereCubeParameter ![z 0, z 1] : Sphere 2) : ThreeSpace) =
        sphereCubeVector ![z 0, z 1] := rfl
    have h3 : ((smashSphereNorth : Sphere 2) : ThreeSpace) = EuclideanSpace.single 2 1 := rfl
    rw [h2, h3]
    exact sp_sphereCubeVector_eq_north _ h
  · right
    change ((z 2 : ℝ) : Circle) = 0
    rw [h]
    exact (AddCircle.coe_zero (p := (1 : ℝ)) : ((0 : ℝ) : Circle) = 0)
  · right
    change ((z 2 : ℝ) : Circle) = 0
    rw [h]
    exact (AddCircle.coe_period (p := (1 : ℝ)) : ((1 : ℝ) : Circle) = 0)

private lemma sp_smash_boundary_eq (z w : I^(Fin 3)) (hz : z ∈ Cube.boundary (Fin 3))
    (hw : w ∈ Cube.boundary (Fin 3)) : smashCubeParameter z = smashCubeParameter w := by
  have h1 : (cubeSphereCircleParameter z : Sphere 2 × Circle) ∈ sphereCircleWedge :=
    sp_smash_boundary_wedge z hz
  have h2 : (cubeSphereCircleParameter w : Sphere 2 × Circle) ∈ sphereCircleWedge :=
    sp_smash_boundary_wedge w hw
  have h3 : Quotient.mk sphereCircleSmashSetoid (cubeSphereCircleParameter z) =
      Quotient.mk sphereCircleSmashSetoid (cubeSphereCircleParameter w) :=
    Quotient.sound (Or.inr ⟨h1, h2⟩)
  exact h3

private lemma sp_smash_fiber (a b : I^(Fin 3)) :
    smashCubeParameter a = smashCubeParameter b ↔
      a = b ∨ (a ∈ Cube.boundary (Fin 3) ∧ b ∈ Cube.boundary (Fin 3)) := by
  constructor
  · intro h
    have h' : Quotient.mk sphereCircleSmashSetoid (cubeSphereCircleParameter a) =
        Quotient.mk sphereCircleSmashSetoid (cubeSphereCircleParameter b) := h
    rw [Quotient.eq] at h'
    change cubeSphereCircleParameter a = cubeSphereCircleParameter b ∨
      (cubeSphereCircleParameter a ∈ sphereCircleWedge ∧
        cubeSphereCircleParameter b ∈ sphereCircleWedge) at h'
    rcases h' with heq | ⟨hwa, hwb⟩
    · have h1 : sphereCubeParameter ![a 0, a 1] = sphereCubeParameter ![b 0, b 1] :=
        congrArg Prod.fst heq
      have h2 : ((a 2 : ℝ) : Circle) = ((b 2 : ℝ) : Circle) := congrArg Prod.snd heq
      have hv : sphereCubeVector ![a 0, a 1] = sphereCubeVector ![b 0, b 1] := by
        have hh := congrArg (fun y : Sphere 2 => (y : ThreeSpace)) h1
        have h4 : ((sphereCubeParameter ![a 0, a 1] : Sphere 2) : ThreeSpace) =
            sphereCubeVector ![a 0, a 1] := rfl
        have h5 : ((sphereCubeParameter ![b 0, b 1] : Sphere 2) : ThreeSpace) =
            sphereCubeVector ![b 0, b 1] := rfl
        rw [h4, h5] at hh
        exact hh
      rcases (sp_two_fiber ![a 0, a 1] ![b 0, b 1]).mp hv with hpair | ⟨hp2a, hp2b⟩
      · have ha0 : a 0 = b 0 := by
          have hh := congrArg (fun z : I^(Fin 2) => z 0) hpair
          simpa using hh
        have ha1 : a 1 = b 1 := by
          have hh := congrArg (fun z : I^(Fin 2) => z 1) hpair
          simpa using hh
        rcases sp_circle_coe_inj (a 2).2 (b 2).2 h2 with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · refine Or.inl (funext fun i => ?_)
          apply Subtype.ext
          fin_cases i
          · exact congrArg Subtype.val ha0
          · exact congrArg Subtype.val ha1
          · exact h3
        · exact Or.inr ⟨⟨2, Or.inl (Subtype.ext h3)⟩, ⟨2, Or.inr (Subtype.ext h4)⟩⟩
        · exact Or.inr ⟨⟨2, Or.inr (Subtype.ext h3)⟩, ⟨2, Or.inl (Subtype.ext h4)⟩⟩
      · exact Or.inr ⟨sp_twoBoundary_to_three hp2a, sp_twoBoundary_to_three hp2b⟩
    · have hwa' := (sp_mem_wedge_iff _).mp hwa
      have hwb' := (sp_mem_wedge_iff _).mp hwb
      have ha : a ∈ Cube.boundary (Fin 3) := by
        rcases hwa' with hw | hw
        · exact sp_twoBoundary_to_three
            ((sp_two_eq_north_iff _).mp (sp_two_eq_north_of_param_eq _ hw))
        · rcases (sp_circle_coe_eq_zero_iff (a 2).2.1 (a 2).2.2).mp hw with h' | h'
          · exact ⟨2, Or.inl (Subtype.ext h')⟩
          · exact ⟨2, Or.inr (Subtype.ext h')⟩
      have hb : b ∈ Cube.boundary (Fin 3) := by
        rcases hwb' with hw | hw
        · exact sp_twoBoundary_to_three
            ((sp_two_eq_north_iff _).mp (sp_two_eq_north_of_param_eq _ hw))
        · rcases (sp_circle_coe_eq_zero_iff (b 2).2.1 (b 2).2.2).mp hw with h' | h'
          · exact ⟨2, Or.inl (Subtype.ext h')⟩
          · exact ⟨2, Or.inr (Subtype.ext h')⟩
      exact Or.inr ⟨ha, hb⟩
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · exact sp_smash_boundary_eq a b ha hb

private lemma sp_smash_rep (y : SphereCircleSmash) :
    ∃ z : I^(Fin 3), smashCubeParameter z = y := by
  induction y using Quotient.inductionOn with
  | h x =>
    obtain ⟨z, hz⟩ := sp_sphereCubeParameter_surjective x.1
    obtain ⟨t, ⟨ht0, ht1⟩, htc⟩ := AddCircle.eq_coe_Ico x.2
    have hmem : t ∈ I := ⟨ht0, ht1.le⟩
    let tt : I := ⟨t, hmem⟩
    have htt : ((tt : I) : ℝ) = t := rfl
    have hpair : ![z 0, z 1] = z := by
      funext i
      fin_cases i <;> rfl
    refine ⟨![z 0, z 1, tt], ?_⟩
    have hx : cubeSphereCircleParameter ![z 0, z 1, tt] = x := by
      refine Prod.ext ?_ ?_
      · change sphereCubeParameter ![z 0, z 1] = x.1
        rw [hpair, hz]
      · change ((tt : I) : Circle) = x.2
        rw [htt]
        exact htc
    rw [← hx]
    rfl

private lemma sp_sphereThreeCubeParameter_surjective' :
    Function.Surjective sphereThreeCubeParameter := sp_sphereThreeCubeParameter_surjective

private lemma sp_quotient_maps (a b : I^(Fin 3))
    (hker : ∀ a b : I^(Fin 3), smashCubeParameter a = smashCubeParameter b ↔
      sphereThreeCubeParameter a = sphereThreeCubeParameter b) :
    smashCubeParameter a = smashCubeParameter b ↔
      sphereThreeCubeParameter a = sphereThreeCubeParameter b := hker a b
theorem exists_unique_standardSmashHomeomorph :
    ∃! e : SphereCircleSmash ≃ₜ Sphere 3,
      (⟨e, e.continuous⟩ : C(SphereCircleSmash, Sphere 3)).comp smashCubeParameter =
        sphereThreeCubeParameter := by
  have hsq : Topology.IsQuotientMap sphereCircleSmashQuotient :=
    isQuotientMap_quotient_mk' (s := sphereCircleSmashSetoid)
  have hg : Topology.IsQuotientMap cubeSphereCircleParameter := by
    refine Topology.IsQuotientMap.of_surjective_continuous ?_ cubeSphereCircleParameter.continuous
    rintro ⟨p, c⟩
    obtain ⟨z, hz⟩ := sp_sphereCubeParameter_surjective p
    obtain ⟨t, ⟨ht0, ht1⟩, htc⟩ := AddCircle.eq_coe_Ico c
    have hmem : t ∈ I := ⟨ht0, ht1.le⟩
    let tt : I := ⟨t, hmem⟩
    have htt : ((tt : I) : ℝ) = t := rfl
    have hpair : ![z 0, z 1] = z := by
      funext i
      fin_cases i <;> rfl
    refine ⟨![z 0, z 1, tt], ?_⟩
    refine Prod.ext ?_ ?_
    · change sphereCubeParameter ![z 0, z 1] = p
      rw [hpair, hz]
    · change ((tt : I) : Circle) = c
      rw [htt]
      exact htc
  have h₁ : Topology.IsQuotientMap smashCubeParameter := by
    change Topology.IsQuotientMap (⇑sphereCircleSmashQuotient ∘ ⇑cubeSphereCircleParameter)
    exact Topology.IsQuotientMap.comp hsq hg
  have h₂ : Topology.IsQuotientMap sphereThreeCubeParameter :=
    Topology.IsQuotientMap.of_surjective_continuous sp_sphereThreeCubeParameter_surjective
      sphereThreeCubeParameter.continuous
  have hker : ∀ a b : I^(Fin 3), smashCubeParameter a = smashCubeParameter b ↔
      sphereThreeCubeParameter a = sphereThreeCubeParameter b := by
    intro a b
    rw [sp_smash_fiber a b, sp_threeParameter_fiber a b]
  have hfac₁ : Function.FactorsThrough sphereThreeCubeParameter
      (smashCubeParameter : (I^(Fin 3)) → SphereCircleSmash) :=
    fun a b hab => (hker a b).mp hab
  have hfac₂ : Function.FactorsThrough smashCubeParameter
      (sphereThreeCubeParameter : (I^(Fin 3)) → Sphere 3) :=
    fun a b hab => (hker a b).mpr hab
  let φ : C(SphereCircleSmash, Sphere 3) := h₁.lift sphereThreeCubeParameter hfac₁
  let ψ : C(Sphere 3, SphereCircleSmash) := h₂.lift smashCubeParameter hfac₂
  have hφ : φ.comp smashCubeParameter = sphereThreeCubeParameter :=
    h₁.lift_comp sphereThreeCubeParameter hfac₁
  have hψ : ψ.comp sphereThreeCubeParameter = smashCubeParameter :=
    h₂.lift_comp smashCubeParameter hfac₂
  have hφ_apply : ∀ x : I^(Fin 3), φ (smashCubeParameter x) = sphereThreeCubeParameter x :=
    fun x => congrFun (congrArg (fun g : C(I^(Fin 3), Sphere 3) =>
      (g : (I^(Fin 3)) → Sphere 3)) hφ) x
  have hψ_apply : ∀ x : I^(Fin 3), ψ (sphereThreeCubeParameter x) = smashCubeParameter x :=
    fun x => congrFun (congrArg (fun g : C(I^(Fin 3), SphereCircleSmash) =>
      (g : (I^(Fin 3)) → SphereCircleSmash)) hψ) x
  let e : SphereCircleSmash ≃ₜ Sphere 3 :=
    { toFun := φ
      invFun := ψ
      left_inv := fun y => by
        obtain ⟨a, rfl⟩ := sp_smash_rep y
        rw [hφ_apply a, hψ_apply a]
      right_inv := fun y => by
        obtain ⟨a, rfl⟩ := sp_sphereThreeCubeParameter_surjective y
        rw [hψ_apply a, hφ_apply a]
      continuous_toFun := φ.continuous
      continuous_invFun := ψ.continuous }
  refine ⟨e, ?_, ?_⟩
  · change (⟨e, e.continuous⟩ : C(SphereCircleSmash, Sphere 3)).comp smashCubeParameter =
      sphereThreeCubeParameter
    have hcoe : (⟨e, e.continuous⟩ : C(SphereCircleSmash, Sphere 3)) = φ := rfl
    rw [hcoe]
    exact hφ
  · intro e' he'
    refine Homeomorph.ext fun y => ?_
    obtain ⟨a, rfl⟩ := sp_smash_rep y
    have h1 : e' (smashCubeParameter a) = sphereThreeCubeParameter a := by
      have hh := congrFun (congrArg (fun g : C(I^(Fin 3), Sphere 3) =>
        (g : (I^(Fin 3)) → Sphere 3)) he') a
      simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] using hh
    exact h1.trans (hφ_apply a).symm

def standardSmashHomeomorph : SphereCircleSmash ≃ₜ Sphere 3 :=
  Classical.choose exists_unique_standardSmashHomeomorph

private lemma fderiv_single_eq_deriv {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin 2)) (h : DifferentiableAt ℝ f x) (k : Fin 2) (i : Fin m) :
    (fderiv ℝ f x (EuclideanSpace.single k 1)) i =
      deriv (fun t : ℝ => (f (x + t • EuclideanSpace.single k 1)) i) 0 := by
  have hg : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single k 1)
      (EuclideanSpace.single k 1) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 2)))
        (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 2)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 2))
    simpa using h1.const_add x
  have hcomp : HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single k 1))
      (fderiv ℝ f x (EuclideanSpace.single k 1)) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x)
        (x + (0 : ℝ) • (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 2))) := by
      simpa using h.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hg
  have hproj := (PiLp.proj (𝕜 := ℝ) (β := fun _ : Fin m => ℝ) (p := 2) (i := i)).hasFDerivAt.comp_hasDerivAt 0 hcomp
  exact hproj.deriv.symm

private lemma deriv_oc_shift (a : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    deriv (fun t : ℝ => openCubeCoordinate (a + t)) 0 =
      (2 * a ^ 2 - 2 * a + 1) / (a * (1 - a)) ^ 2 := by
  have hc : HasDerivAt openCubeCoordinate ((2 * a ^ 2 - 2 * a + 1) / (a * (1 - a)) ^ 2) a :=
    hasDerivAt_openCubeCoordinate a ha0 ha1
  have hd : deriv openCubeCoordinate a = (2 * a ^ 2 - 2 * a + 1) / (a * (1 - a)) ^ 2 := hc.deriv
  have hshift : deriv (fun t : ℝ => a + t) 0 = 1 := by
    exact deriv_const_add_id a (x := (0 : ℝ))
  have h : deriv (openCubeCoordinate ∘ (fun t : ℝ => a + t)) 0 =
      deriv openCubeCoordinate (a + 0) * deriv (fun t : ℝ => a + t) 0 :=
    deriv_comp 0 (by simpa using hc.differentiableAt) (by fun_prop)
  simpa only [Function.comp_def, add_zero, hd, hshift, mul_one] using h

private lemma deriv_c0_left (v s : ℝ) :
    deriv (fun s : ℝ => 2 * s / (1 + s ^ 2 + v ^ 2)) s =
      2 * (1 + v ^ 2 - s ^ 2) / (1 + s ^ 2 + v ^ 2) ^ 2 := by
  have hD : (1 + s ^ 2 + v ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun s : ℝ => 2 * s) (d := fun s : ℝ => 1 + s ^ 2 + v ^ 2)
    (by fun_prop) (by fun_prop) hD]
  rw [deriv_const_mul_id (2 : ℝ)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2) (g := fun _ : ℝ => v ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma deriv_c1_left (v s : ℝ) :
    deriv (fun s : ℝ => -2 * v / (1 + s ^ 2 + v ^ 2)) s =
      4 * s * v / (1 + s ^ 2 + v ^ 2) ^ 2 := by
  have hD : (1 + s ^ 2 + v ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun _ : ℝ => -2 * v) (d := fun s : ℝ => 1 + s ^ 2 + v ^ 2)
    (by fun_prop) (by fun_prop) hD]
  rw [deriv_const]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2) (g := fun _ : ℝ => v ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma deriv_c2_left (v s : ℝ) :
    deriv (fun s : ℝ => (s ^ 2 + v ^ 2 - 1) / (1 + s ^ 2 + v ^ 2)) s =
      4 * s / (1 + s ^ 2 + v ^ 2) ^ 2 := by
  have hD : (1 + s ^ 2 + v ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun s : ℝ => s ^ 2 + v ^ 2 - 1)
    (d := fun s : ℝ => 1 + s ^ 2 + v ^ 2) (by fun_prop) (by fun_prop) hD]
  rw [deriv_fun_sub (f := fun s : ℝ => s ^ 2 + v ^ 2) (g := fun _ : ℝ => (1 : ℝ))
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => s ^ 2) (g := fun _ : ℝ => v ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2) (g := fun _ : ℝ => v ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma deriv_c0_right (u s : ℝ) :
    deriv (fun s : ℝ => 2 * u / (1 + u ^ 2 + s ^ 2)) s =
      -4 * u * s / (1 + u ^ 2 + s ^ 2) ^ 2 := by
  have hD : (1 + u ^ 2 + s ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun _ : ℝ => 2 * u) (d := fun s : ℝ => 1 + u ^ 2 + s ^ 2)
    (by fun_prop) (by fun_prop) hD]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + u ^ 2) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma deriv_c1_right (u s : ℝ) :
    deriv (fun s : ℝ => -2 * s / (1 + u ^ 2 + s ^ 2)) s =
      2 * (s ^ 2 - u ^ 2 - 1) / (1 + u ^ 2 + s ^ 2) ^ 2 := by
  have hD : (1 + u ^ 2 + s ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun s : ℝ => -2 * s) (d := fun s : ℝ => 1 + u ^ 2 + s ^ 2)
    (by fun_prop) (by fun_prop) hD]
  rw [deriv_const_mul_id (-2 : ℝ)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + u ^ 2) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma deriv_c2_right (u s : ℝ) :
    deriv (fun s : ℝ => (u ^ 2 + s ^ 2 - 1) / (1 + u ^ 2 + s ^ 2)) s =
      4 * s / (1 + u ^ 2 + s ^ 2) ^ 2 := by
  have hD : (1 + u ^ 2 + s ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun s : ℝ => u ^ 2 + s ^ 2 - 1)
    (d := fun s : ℝ => 1 + u ^ 2 + s ^ 2) (by fun_prop) (by fun_prop) hD]
  rw [deriv_fun_sub (f := fun s : ℝ => u ^ 2 + s ^ 2) (g := fun _ : ℝ => (1 : ℝ))
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => u ^ 2) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + u ^ 2) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

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

private lemma differentiableAt_sphereTwoInteriorParam (p : ℝ × ℝ) :
    DifferentiableAt ℝ sphereTwoInteriorParam p := by
  rw [differentiableAt_piLp]
  intro i
  simp only [sphereTwoInteriorParam, PiLp.toLp_apply]
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, div_eq_mul_inv] <;>
    first
      | exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => 2 * p.1) p).mul
          ((by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => 1 + p.1 ^ 2 + p.2 ^ 2) p).inv
            (by positivity))
      | exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => -2 * p.2) p).mul
          ((by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => 1 + p.1 ^ 2 + p.2 ^ 2) p).inv
            (by positivity))
      | exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 - 1) p).mul
          ((by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => 1 + p.1 ^ 2 + p.2 ^ 2) p).inv
            (by positivity))

private lemma differentiableAt_cubeCoordinate (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) (i : Fin 2) :
    DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 2) => openCubeCoordinate (x i)) x := by
  have hz : (x i : ℝ) ≠ 0 := ne_of_gt (hx i).1
  have ho : (x i : ℝ) ≠ 1 := ne_of_lt (hx i).2
  have hc := (hasDerivAt_openCubeCoordinate (x i) hz ho).differentiableAt
  have hp : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 2) => x i) x :=
    (PiLp.proj (𝕜 := ℝ) (β := fun _ : Fin 2 => ℝ) (p := 2) (i := i)).differentiableAt
  exact hc.comp x hp

private lemma differentiableAt_orientedSphereTwoInterior (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereTwoInterior x := by
  have hpair : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 2) =>
      (openCubeCoordinate (x 0), openCubeCoordinate (x 1))) x :=
    DifferentiableAt.prodMk (differentiableAt_cubeCoordinate x hx 0)
      (differentiableAt_cubeCoordinate x hx 1)
  have hpar := differentiableAt_sphereTwoInteriorParam
    (openCubeCoordinate (x 0), openCubeCoordinate (x 1))
  have hcomp := hpar.comp x hpair
  have hfun : orientedSphereTwoInterior = sphereTwoInteriorParam ∘
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (openCubeCoordinate (x 0), openCubeCoordinate (x 1))) := by
    funext y
    rw [Function.comp_apply, orientedSphereTwoInterior_eq_param]
  exact hfun ▸ hcomp

private lemma differentiableAt_oc_shift (a : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (a + t)) 0 := by
  have hnum : DifferentiableAt ℝ (fun t : ℝ => 2 * (a + t) - 1) 0 := by fun_prop
  have hden : DifferentiableAt ℝ (fun t : ℝ => (a + t) * (1 - (a + t))) 0 := by fun_prop
  have hne : (a + 0) * (1 - (a + 0)) ≠ 0 := by
    simp only [add_zero]
    exact mul_ne_zero ha0 (sub_ne_zero.mpr (Ne.symm ha1))
  exact hnum.div hden hne

private lemma deriv_oriented_two_zero_zero (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 0 1)) 0) 0 =
      (2 * (1 + openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 0) ^ 2) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hz0 : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have ho0 : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 0 1)) 0) =
      fun t : ℝ => 2 * openCubeCoordinate (x 0 + t) /
        (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2) := by
    funext t
    rw [orientedSphereTwoInterior_eq_param]
    simp [sphereTwoInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2)) ∘
      (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (2 * (1 + openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 0) ^ 2) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2))
        (openCubeCoordinate (x 0 + 0)) := by fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 0 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 0) hz0 ho0
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp]
    rw [add_zero, deriv_c0_left, deriv_oc_shift (x 0) hz0 ho0]
  simpa only [Function.comp_def] using hmain

private lemma deriv_oriented_two_one_zero (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 1 1)) 0) 0 =
      (-4 * openCubeCoordinate (x 0) * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hz1 : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have ho1 : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 1 1)) 0) =
      fun t : ℝ => 2 * openCubeCoordinate (x 0) /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2) := by
    funext t
    rw [orientedSphereTwoInterior_eq_param]
    simp [sphereTwoInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 0) /
      (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2)) ∘
      (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (-4 * openCubeCoordinate (x 0) * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 0) /
        (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2)) (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg := differentiableAt_oc_shift (x 1) hz1 ho1
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp]
    rw [add_zero, deriv_c0_right, deriv_oc_shift (x 1) hz1 ho1]
  simpa only [Function.comp_def] using hmain

private lemma deriv_oriented_two_one_one (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 1 1)) 1) 0 =
      (2 * (openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 0) ^ 2 - 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hz1 : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have ho1 : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 1 1)) 1) =
      fun t : ℝ => -2 * openCubeCoordinate (x 1 + t) /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2) := by
    funext t
    rw [orientedSphereTwoInterior_eq_param]
    simp [sphereTwoInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => -2 * s /
      (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2)) ∘
      (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (2 * (openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 0) ^ 2 - 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => -2 * s /
        (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2)) (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg := differentiableAt_oc_shift (x 1) hz1 ho1
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp]
    rw [add_zero, deriv_c1_right, deriv_oc_shift (x 1) hz1 ho1]
  simpa only [Function.comp_def] using hmain

private lemma deriv_oriented_two_one_two (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 1 1)) 2) 0 =
      (4 * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hz1 : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have ho1 : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 1 1)) 2) =
      fun t : ℝ => (openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2 - 1) /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2) := by
    funext t
    rw [orientedSphereTwoInterior_eq_param]
    simp [sphereTwoInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => (openCubeCoordinate (x 0) ^ 2 + s ^ 2 - 1) /
      (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2)) ∘
      (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (4 * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => (openCubeCoordinate (x 0) ^ 2 + s ^ 2 - 1) /
        (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2)) (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg := differentiableAt_oc_shift (x 1) hz1 ho1
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp]
    rw [add_zero, deriv_c2_right, deriv_oc_shift (x 1) hz1 ho1]
  simpa only [Function.comp_def] using hmain

private lemma deriv_oriented_two_zero_one (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 0 1)) 1) 0 =
      (4 * openCubeCoordinate (x 0) * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hz0 : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have ho0 : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 0 1)) 1) =
      fun t : ℝ => -2 * openCubeCoordinate (x 1) /
        (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2) := by
    funext t
    rw [orientedSphereTwoInterior_eq_param]
    simp [sphereTwoInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => -2 * openCubeCoordinate (x 1) /
      (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2)) ∘
      (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (4 * openCubeCoordinate (x 0) * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => -2 * openCubeCoordinate (x 1) /
        (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2)) (openCubeCoordinate (x 0 + 0)) := by
      fun_prop (disch := positivity)
    have hg := differentiableAt_oc_shift (x 0) hz0 ho0
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp]
    rw [add_zero, deriv_c1_left, deriv_oc_shift (x 0) hz0 ho0]
  simpa only [Function.comp_def] using hmain

private lemma deriv_oriented_two_zero_two (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 0 1)) 2) 0 =
      (4 * openCubeCoordinate (x 0) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hz0 : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have ho0 : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereTwoInterior (x + t • EuclideanSpace.single 0 1)) 2) =
      fun t : ℝ => (openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2 - 1) /
        (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2) := by
    funext t
    rw [orientedSphereTwoInterior_eq_param]
    simp [sphereTwoInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 1) ^ 2 - 1) /
      (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2)) ∘
      (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (4 * openCubeCoordinate (x 0) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 1) ^ 2 - 1) /
        (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2)) (openCubeCoordinate (x 0 + 0)) := by
      fun_prop (disch := positivity)
    have hg := differentiableAt_oc_shift (x 0) hz0 ho0
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp]
    rw [add_zero, deriv_c2_left, deriv_oc_shift (x 0) hz0 ho0]
  simpa only [Function.comp_def] using hmain

private lemma fderiv_two_zero_zero (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single 0 1)) 0 =
      (2 * (1 + openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 0) ^ 2) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [fderiv_single_eq_deriv orientedSphereTwoInterior x
      (differentiableAt_orientedSphereTwoInterior x hx) 0 0,
    deriv_oriented_two_zero_zero x hx]

private lemma fderiv_two_zero_one (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single 0 1)) 1 =
      (4 * openCubeCoordinate (x 0) * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [fderiv_single_eq_deriv orientedSphereTwoInterior x
      (differentiableAt_orientedSphereTwoInterior x hx) 0 1,
    deriv_oriented_two_zero_one x hx]

private lemma fderiv_two_zero_two (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single 0 1)) 2 =
      (4 * openCubeCoordinate (x 0) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [fderiv_single_eq_deriv orientedSphereTwoInterior x
      (differentiableAt_orientedSphereTwoInterior x hx) 0 2,
    deriv_oriented_two_zero_two x hx]

private lemma fderiv_two_one_zero (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single 1 1)) 0 =
      (-4 * openCubeCoordinate (x 0) * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [fderiv_single_eq_deriv orientedSphereTwoInterior x
      (differentiableAt_orientedSphereTwoInterior x hx) 1 0,
    deriv_oriented_two_one_zero x hx]

private lemma fderiv_two_one_one (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single 1 1)) 1 =
      (2 * (openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 0) ^ 2 - 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [fderiv_single_eq_deriv orientedSphereTwoInterior x
      (differentiableAt_orientedSphereTwoInterior x hx) 1 1,
    deriv_oriented_two_one_one x hx]

private lemma fderiv_two_one_two (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single 1 1)) 2 =
      (4 * openCubeCoordinate (x 1) /
          (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [fderiv_single_eq_deriv orientedSphereTwoInterior x
      (differentiableAt_orientedSphereTwoInterior x hx) 1 2,
    deriv_oriented_two_one_two x hx]

private lemma fin_cases_one {α : Sort*} (A : α) (F : Fin 2 → α) :
    Fin.cases A F (1 : Fin 3) = F 0 := rfl

private lemma fin_cases_two {α : Sort*} (A : α) (F : Fin 2 → α) :
    Fin.cases A F (2 : Fin 3) = F 1 := rfl

theorem sphereTwo_parameter_positive (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereTwoInterior x ∧
      (0 : ℝ) < Matrix.det (fun i j : Fin 3 =>
        Fin.cases (orientedSphereTwoInterior x i)
          (fun k => (fderiv ℝ orientedSphereTwoInterior x
            (EuclideanSpace.single k 1)) i) j) := by
  refine ⟨differentiableAt_orientedSphereTwoInterior x hx, ?_⟩
  change (0 : ℝ) < Matrix.det (Matrix.of (α := ℝ) (fun i j : Fin 3 =>
    Fin.cases (orientedSphereTwoInterior x i)
      (fun k => (fderiv ℝ orientedSphereTwoInterior x (EuclideanSpace.single k 1)) i) j))
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, fin_cases_one, fin_cases_two, Fin.isValue, Fin.cases_zero]
  simp only [fderiv_two_zero_zero x hx, fderiv_two_zero_one x hx, fderiv_two_zero_two x hx,
    fderiv_two_one_zero x hx, fderiv_two_one_one x hx, fderiv_two_one_two x hx,
    orientedSphereTwoInterior_eq_param, sphereTwoInteriorParam, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hdu : 0 < (2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2 := by
    apply div_pos
    · nlinarith [sq_nonneg ((x 0) - 1 / 2)]
    · exact pow_pos (mul_pos (hx 0).1 (by linarith [(hx 0).2])) 2
  have hdv : 0 < (2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2 := by
    apply div_pos
    · nlinarith [sq_nonneg ((x 1) - 1 / 2)]
    · exact pow_pos (mul_pos (hx 1).1 (by linarith [(hx 1).2])) 2
  have hDpos : 0 < 1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 := by
    positivity
  have hpos : 0 < (2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2 *
      ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) *
      (4 / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) :=
    mul_pos (mul_pos hdu hdv) (div_pos (by norm_num) (pow_pos hDpos 2))
  convert hpos using 1
  field_simp
  ring


private lemma sp_fderiv_single_eq_deriv {m : ℕ}
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin 3)) (h : DifferentiableAt ℝ f x) (k : Fin 3) (i : Fin m) :
    (fderiv ℝ f x (EuclideanSpace.single k 1)) i =
      deriv (fun t : ℝ => (f (x + t • EuclideanSpace.single k 1)) i) 0 := by
  have hg : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single k 1)
      (EuclideanSpace.single k 1) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 3)))
        (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 3)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 3))
    simpa using h1.const_add x
  have hcomp : HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single k 1))
      (fderiv ℝ f x (EuclideanSpace.single k 1)) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x)
        (x + (0 : ℝ) • (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin 3))) := by
      simpa using h.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hg
  have hproj := (PiLp.proj (𝕜 := ℝ) (β := fun _ : Fin m => ℝ) (p := 2) (i := i)).hasFDerivAt.comp_hasDerivAt 0 hcomp
  exact hproj.deriv.symm

private lemma sp_deriv_const_div (c b c2 s : ℝ) :
    deriv (fun s : ℝ => c / (1 + s ^ 2 + b ^ 2 + c2 ^ 2)) s =
      -2 * c * s / (1 + s ^ 2 + b ^ 2 + c2 ^ 2) ^ 2 := by
  have hD : (1 + s ^ 2 + b ^ 2 + c2 ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun _ : ℝ => c) (d := fun s : ℝ => 1 + s ^ 2 + b ^ 2 + c2 ^ 2)
    (by fun_prop) (by fun_prop) hD]
  rw [deriv_const]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2 + b ^ 2) (g := fun _ : ℝ => c2 ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2) (g := fun _ : ℝ => b ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma sp_deriv_lin_div (b c2 s : ℝ) :
    deriv (fun s : ℝ => 2 * s / (1 + s ^ 2 + b ^ 2 + c2 ^ 2)) s =
      2 * (1 + b ^ 2 + c2 ^ 2 - s ^ 2) / (1 + s ^ 2 + b ^ 2 + c2 ^ 2) ^ 2 := by
  have hD : (1 + s ^ 2 + b ^ 2 + c2 ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun s : ℝ => 2 * s) (d := fun s : ℝ => 1 + s ^ 2 + b ^ 2 + c2 ^ 2)
    (by fun_prop) (by fun_prop) hD]
  rw [deriv_const_mul_id (2 : ℝ)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2 + b ^ 2) (g := fun _ : ℝ => c2 ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2) (g := fun _ : ℝ => b ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring

private lemma sp_deriv_quad_div (b c2 s : ℝ) :
    deriv (fun s : ℝ => (s ^ 2 + b ^ 2 + c2 ^ 2 - 1) / (1 + s ^ 2 + b ^ 2 + c2 ^ 2)) s =
      4 * s / (1 + s ^ 2 + b ^ 2 + c2 ^ 2) ^ 2 := by
  have hD : (1 + s ^ 2 + b ^ 2 + c2 ^ 2) ≠ 0 := by positivity
  rw [deriv_fun_div (c := fun s : ℝ => s ^ 2 + b ^ 2 + c2 ^ 2 - 1)
    (d := fun s : ℝ => 1 + s ^ 2 + b ^ 2 + c2 ^ 2) (by fun_prop) (by fun_prop) hD]
  rw [deriv_fun_sub (f := fun s : ℝ => s ^ 2 + b ^ 2 + c2 ^ 2) (g := fun _ : ℝ => (1 : ℝ))
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => s ^ 2 + b ^ 2) (g := fun _ : ℝ => c2 ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => s ^ 2) (g := fun _ : ℝ => b ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2 + b ^ 2) (g := fun _ : ℝ => c2 ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun s : ℝ => 1 + s ^ 2) (g := fun _ : ℝ => b ^ 2)
    (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => s ^ 2)
    (by fun_prop) (by fun_prop)]
  simp only [deriv_const, deriv_fun_pow (f := fun s : ℝ => s) differentiableAt_id 2, deriv_id'']
  field_simp
  ring





private lemma sp_deriv_three_00 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 0) 0 =
      (2 * (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2 - openCubeCoordinate (x 0) ^ 2) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hzk : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have hok : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 0) =
      fun t : ℝ => 2 * openCubeCoordinate (x 0 + t) / (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (2 * (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2 - openCubeCoordinate (x 0) ^ 2) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 0 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 0 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 0) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp, add_zero]
    rw [sp_deriv_lin_div (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 0)), deriv_oc_shift (x 0) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_01 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 1) 0 =
      (-2 * (2 * openCubeCoordinate (x 1)) * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hzk : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have hok : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 1) =
      fun t : ℝ => 2 * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 1) / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (-2 * (2 * openCubeCoordinate (x 1)) * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 1) / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 0 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 0 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 0) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp, add_zero]
    rw [sp_deriv_const_div (2 * openCubeCoordinate (x 1)) (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 0)), deriv_oc_shift (x 0) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_02 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 2) 0 =
      (-2 * (2 * openCubeCoordinate (x 2)) * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hzk : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have hok : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 2) =
      fun t : ℝ => 2 * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 2) / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (-2 * (2 * openCubeCoordinate (x 2)) * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 2) / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 0 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 0 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 0) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp, add_zero]
    rw [sp_deriv_const_div (2 * openCubeCoordinate (x 2)) (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 0)), deriv_oc_shift (x 0) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_03 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 3) 0 =
      (4 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  have hzk : (x 0 : ℝ) ≠ 0 := ne_of_gt (hx 0).1
  have hok : (x 0 : ℝ) ≠ 1 := ne_of_lt (hx 0).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 0 1)) 3) =
      fun t : ℝ => (openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + openCubeCoordinate (x 0 + t) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 0 + t))) 0 =
      (4 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
    have hc : DifferentiableAt ℝ (fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + s ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 0 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 0 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 0) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcomp, add_zero]
    rw [sp_deriv_quad_div (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 0)), deriv_oc_shift (x 0) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_10 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 0) 0 =
      (-2 * (2 * openCubeCoordinate (x 0)) * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hzk : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have hok : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 0) =
      fun t : ℝ => 2 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (-2 * (2 * openCubeCoordinate (x 0)) * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hcom : (fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) = (fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 1 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 1) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_const_div (2 * openCubeCoordinate (x 0)) (openCubeCoordinate (x 0)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 1)), deriv_oc_shift (x 1) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_11 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 1) 0 =
      (2 * (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2 - openCubeCoordinate (x 1) ^ 2) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hzk : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have hok : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 1) =
      fun t : ℝ => 2 * openCubeCoordinate (x 1 + t) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * s / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (2 * (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2 - openCubeCoordinate (x 1) ^ 2) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hcom : (fun s : ℝ => 2 * s / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) = (fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 1 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 1) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_lin_div (openCubeCoordinate (x 0)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 1)), deriv_oc_shift (x 1) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_12 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 2) 0 =
      (-2 * (2 * openCubeCoordinate (x 2)) * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hzk : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have hok : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 2) =
      fun t : ℝ => 2 * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (-2 * (2 * openCubeCoordinate (x 2)) * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hcom : (fun s : ℝ => 2 * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) = (fun s : ℝ => 2 * openCubeCoordinate (x 2) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 2) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 1 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 1) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_const_div (2 * openCubeCoordinate (x 2)) (openCubeCoordinate (x 0)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 1)), deriv_oc_shift (x 1) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_13 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 3) 0 =
      (4 * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  have hzk : (x 1 : ℝ) ≠ 0 := ne_of_gt (hx 1).1
  have hok : (x 1 : ℝ) ≠ 1 := ne_of_lt (hx 1).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 1 1)) 3) =
      fun t : ℝ => (openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1 + t) ^ 2 + openCubeCoordinate (x 2) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => (openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 1 + t))) 0 =
      (4 * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2) ^ 2) * ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
    have hcom : (fun s : ℝ => (openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + openCubeCoordinate (x 0) ^ 2 + s ^ 2 + openCubeCoordinate (x 2) ^ 2)) = (fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2 - 1) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 2) ^ 2))
        (openCubeCoordinate (x 1 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 1 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 1) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_quad_div (openCubeCoordinate (x 0)) (openCubeCoordinate (x 2)) (openCubeCoordinate (x 1)), deriv_oc_shift (x 1) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_20 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 0) 0 =
      (-2 * (2 * openCubeCoordinate (x 0)) * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  have hzk : (x 2 : ℝ) ≠ 0 := ne_of_gt (hx 2).1
  have hok : (x 2 : ℝ) ≠ 1 := ne_of_lt (hx 2).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 0) =
      fun t : ℝ => 2 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2 + t) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 2 + t))) 0 =
      (-2 * (2 * openCubeCoordinate (x 0)) * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
    have hcom : (fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) = (fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 0) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2))
        (openCubeCoordinate (x 2 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 2 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 2) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_const_div (2 * openCubeCoordinate (x 0)) (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)), deriv_oc_shift (x 2) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_21 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 1) 0 =
      (-2 * (2 * openCubeCoordinate (x 1)) * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  have hzk : (x 2 : ℝ) ≠ 0 := ne_of_gt (hx 2).1
  have hok : (x 2 : ℝ) ≠ 1 := ne_of_lt (hx 2).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 1) =
      fun t : ℝ => 2 * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2 + t) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 2 + t))) 0 =
      (-2 * (2 * openCubeCoordinate (x 1)) * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
    have hcom : (fun s : ℝ => 2 * openCubeCoordinate (x 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) = (fun s : ℝ => 2 * openCubeCoordinate (x 1) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * openCubeCoordinate (x 1) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2))
        (openCubeCoordinate (x 2 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 2 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 2) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_const_div (2 * openCubeCoordinate (x 1)) (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)), deriv_oc_shift (x 2) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_22 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 2) 0 =
      (2 * (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 2) ^ 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  have hzk : (x 2 : ℝ) ≠ 0 := ne_of_gt (hx 2).1
  have hok : (x 2 : ℝ) ≠ 1 := ne_of_lt (hx 2).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 2) =
      fun t : ℝ => 2 * openCubeCoordinate (x 2 + t) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2 + t) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => 2 * s / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 2 + t))) 0 =
      (2 * (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 - openCubeCoordinate (x 2) ^ 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
    have hcom : (fun s : ℝ => 2 * s / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) = (fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => 2 * s / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2))
        (openCubeCoordinate (x 2 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 2 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 2) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_lin_div (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)), deriv_oc_shift (x 2) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain

private lemma sp_deriv_three_23 (x : ThreeSpace) (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 3) 0 =
      (4 * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  have hzk : (x 2 : ℝ) ≠ 0 := ne_of_gt (hx 2).1
  have hok : (x 2 : ℝ) ≠ 1 := ne_of_lt (hx 2).2
  have hfun : (fun t : ℝ => (orientedSphereThreeInterior (x + t • EuclideanSpace.single 2 1)) 3) =
      fun t : ℝ => (openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2 + t) ^ 2 - 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + openCubeCoordinate (x 2 + t) ^ 2) := by
    funext t
    rw [orientedSphereThreeInterior_eq_param]
    simp [sphereThreeInteriorParam]
  rw [hfun]
  have hmain : deriv ((fun s : ℝ => (openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2 - 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) ∘ (fun t : ℝ => openCubeCoordinate (x 2 + t))) 0 =
      (4 * openCubeCoordinate (x 2) / (1 + openCubeCoordinate (x 2) ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2) ^ 2) * ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
    have hcom : (fun s : ℝ => (openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2 - 1) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 + s ^ 2)) = (fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 - 1) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2)) := by
      funext s
      ring
    have hc : DifferentiableAt ℝ (fun s : ℝ => (s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 - 1) / (1 + s ^ 2 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2))
        (openCubeCoordinate (x 2 + 0)) := by
      fun_prop (disch := positivity)
    have hg : DifferentiableAt ℝ (fun t : ℝ => openCubeCoordinate (x 2 + t)) 0 := by
      simpa only [add_zero] using differentiableAt_oc_shift (x 2) hzk hok
    have hcomp := deriv_comp 0 hc hg
    rw [hcom]
    rw [hcomp, add_zero]
    rw [sp_deriv_quad_div (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1)) (openCubeCoordinate (x 2)), deriv_oc_shift (x 2) hzk hok]
    try ring
  simpa only [Function.comp_def] using hmain


private lemma fin_succ_two_eq_three : (Fin.succ 2 : Fin 4) = 3 := rfl

private lemma fin4_succAbove_one_zero : (1 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
private lemma fin4_succAbove_one_one : (1 : Fin 4).succAbove (1 : Fin 3) = 2 := by decide
private lemma fin4_succAbove_one_two : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
private lemma fin4_succAbove_two_zero : (2 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
private lemma fin4_succAbove_two_one : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
private lemma fin4_succAbove_two_two : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
private lemma fin4_succAbove_three_zero : (3 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
private lemma fin4_succAbove_three_one : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
private lemma fin4_succAbove_three_two : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide

private lemma det_four_general (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2 -
        A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1 +
        A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1 -
        A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2 +
        A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0 -
        A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0 +
        A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1 -
        A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0 +
        A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0 -
        A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1 +
        A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0 -
        A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  rw [Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, fin_succ_two_eq_three, fin4_succAbove_one_zero, fin4_succAbove_one_one,
    fin4_succAbove_one_two, fin4_succAbove_two_zero, fin4_succAbove_two_one,
    fin4_succAbove_two_two, fin4_succAbove_three_zero, fin4_succAbove_three_one,
    fin4_succAbove_three_two, Fin.isValue]
  norm_num
  ring

private def spGeoA (u v w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 * u, 2 * (1 + v ^ 2 + w ^ 2 - u ^ 2), -2 * (2 * u) * v, -2 * (2 * u) * w;
    2 * v, -2 * (2 * v) * u, 2 * (1 + u ^ 2 + w ^ 2 - v ^ 2), -2 * (2 * v) * w;
    2 * w, -2 * (2 * w) * u, -2 * (2 * w) * v, 2 * (1 + u ^ 2 + v ^ 2 - w ^ 2);
    u ^ 2 + v ^ 2 + w ^ 2 - 1, 4 * u, 4 * v, 4 * w]

private lemma sp_geoA_det (u v w : ℝ) :
    Matrix.det (spGeoA u v w) = 8 * (1 + u ^ 2 + v ^ 2 + w ^ 2) ^ 4 := by
  rw [det_four_general]
  simp only [spGeoA, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring


private lemma spGeoA_apply_00 (u v w : ℝ) :
    spGeoA u v w 0 0 = 2 * u := by
  simp [spGeoA]

private lemma spGeoA_apply_01 (u v w : ℝ) :
    spGeoA u v w 0 1 = 2 * (1 + v ^ 2 + w ^ 2 - u ^ 2) := by
  simp [spGeoA]

private lemma spGeoA_apply_02 (u v w : ℝ) :
    spGeoA u v w 0 2 = -2 * (2 * u) * v := by
  simp [spGeoA]

private lemma spGeoA_apply_03 (u v w : ℝ) :
    spGeoA u v w 0 3 = -2 * (2 * u) * w := by
  simp [spGeoA]

private lemma spGeoA_apply_10 (u v w : ℝ) :
    spGeoA u v w 1 0 = 2 * v := by
  simp [spGeoA]

private lemma spGeoA_apply_11 (u v w : ℝ) :
    spGeoA u v w 1 1 = -2 * (2 * v) * u := by
  simp [spGeoA]

private lemma spGeoA_apply_12 (u v w : ℝ) :
    spGeoA u v w 1 2 = 2 * (1 + u ^ 2 + w ^ 2 - v ^ 2) := by
  simp [spGeoA]

private lemma spGeoA_apply_13 (u v w : ℝ) :
    spGeoA u v w 1 3 = -2 * (2 * v) * w := by
  simp [spGeoA]

private lemma spGeoA_apply_20 (u v w : ℝ) :
    spGeoA u v w 2 0 = 2 * w := by
  simp [spGeoA]

private lemma spGeoA_apply_21 (u v w : ℝ) :
    spGeoA u v w 2 1 = -2 * (2 * w) * u := by
  simp [spGeoA]

private lemma spGeoA_apply_22 (u v w : ℝ) :
    spGeoA u v w 2 2 = -2 * (2 * w) * v := by
  simp [spGeoA]

private lemma spGeoA_apply_23 (u v w : ℝ) :
    spGeoA u v w 2 3 = 2 * (1 + u ^ 2 + v ^ 2 - w ^ 2) := by
  simp [spGeoA]

private lemma spGeoA_apply_30 (u v w : ℝ) :
    spGeoA u v w 3 0 = u ^ 2 + v ^ 2 + w ^ 2 - 1 := by
  simp [spGeoA]

private lemma spGeoA_apply_31 (u v w : ℝ) :
    spGeoA u v w 3 1 = 4 * u := by
  simp [spGeoA]

private lemma spGeoA_apply_32 (u v w : ℝ) :
    spGeoA u v w 3 2 = 4 * v := by
  simp [spGeoA]

private lemma spGeoA_apply_33 (u v w : ℝ) :
    spGeoA u v w 3 3 = 4 * w := by
  simp [spGeoA]

private lemma differentiableAt_sphereThreeInteriorParam (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ sphereThreeInteriorParam p := by
  rw [differentiableAt_piLp]
  intro i
  simp only [sphereThreeInteriorParam, PiLp.toLp_apply]
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv] <;>
    first
      | exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => 2 * p.1) p).mul
          ((by fun_prop : DifferentiableAt ℝ
            (fun p : ℝ × ℝ × ℝ => 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) p).inv
            (by positivity))
      | exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => 2 * p.2.1) p).mul
          ((by fun_prop : DifferentiableAt ℝ
            (fun p : ℝ × ℝ × ℝ => 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) p).inv
            (by positivity))
      | exact (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => 2 * p.2.2) p).mul
          ((by fun_prop : DifferentiableAt ℝ
            (fun p : ℝ × ℝ × ℝ => 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) p).inv
            (by positivity))
      | exact (by fun_prop : DifferentiableAt ℝ
            (fun p : ℝ × ℝ × ℝ => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) p).mul
          ((by fun_prop : DifferentiableAt ℝ
            (fun p : ℝ × ℝ × ℝ => 1 + p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) p).inv
            (by positivity))

private lemma differentiableAt_cubeCoordinate_three (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun x : ThreeSpace => openCubeCoordinate (x i)) x := by
  have hz : (x i : ℝ) ≠ 0 := ne_of_gt (hx i).1
  have ho : (x i : ℝ) ≠ 1 := ne_of_lt (hx i).2
  have hc := (hasDerivAt_openCubeCoordinate (x i) hz ho).differentiableAt
  have hp : DifferentiableAt ℝ (fun x : ThreeSpace => x i) x :=
    (PiLp.proj (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) (p := 2) (i := i)).differentiableAt
  exact hc.comp x hp

private lemma differentiableAt_orientedSphereThreeInterior (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereThreeInterior x := by
  have htriple : DifferentiableAt ℝ (fun x : ThreeSpace =>
      (openCubeCoordinate (x 0), openCubeCoordinate (x 1), openCubeCoordinate (x 2))) x :=
    (differentiableAt_cubeCoordinate_three x hx 0).prodMk
      ((differentiableAt_cubeCoordinate_three x hx 1).prodMk
        (differentiableAt_cubeCoordinate_three x hx 2))
  have hpar := differentiableAt_sphereThreeInteriorParam
    (openCubeCoordinate (x 0), openCubeCoordinate (x 1), openCubeCoordinate (x 2))
  have hcomp := hpar.comp x htriple
  have hfun : orientedSphereThreeInterior = sphereThreeInteriorParam ∘
      (fun x : ThreeSpace =>
        (openCubeCoordinate (x 0), openCubeCoordinate (x 1), openCubeCoordinate (x 2))) := by
    funext y
    rw [Function.comp_apply, orientedSphereThreeInterior_eq_param]
  exact hfun ▸ hcomp

private lemma sp_point_three (x : ThreeSpace) (i : Fin 4) :
    orientedSphereThreeInterior x i =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) i 0 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) := by
  rw [orientedSphereThreeInterior_eq_param]
  fin_cases i <;>
    simp [sphereThreeInteriorParam, spGeoA, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

private lemma sp_fderiv_three_00 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 0 1)) 0 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 0 1 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 0 0,
    sp_deriv_three_00 x hx, spGeoA_apply_01]

private lemma sp_fderiv_three_01 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 0 1)) 1 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 1 1 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 0 1,
    sp_deriv_three_01 x hx, spGeoA_apply_11]

private lemma sp_fderiv_three_02 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 0 1)) 2 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 2 1 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 0 2,
    sp_deriv_three_02 x hx, spGeoA_apply_21]

private lemma sp_fderiv_three_03 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 0 1)) 3 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 3 1 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 0 3,
    sp_deriv_three_03 x hx, spGeoA_apply_31]

private lemma sp_fderiv_three_10 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 1 1)) 0 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 0 2 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 1 0,
    sp_deriv_three_10 x hx, spGeoA_apply_02]
  ring_nf

private lemma sp_fderiv_three_11 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 1 1)) 1 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 1 2 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 1 1,
    sp_deriv_three_11 x hx, spGeoA_apply_12]
  ring_nf

private lemma sp_fderiv_three_12 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 1 1)) 2 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 2 2 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 1 2,
    sp_deriv_three_12 x hx, spGeoA_apply_22]
  ring_nf

private lemma sp_fderiv_three_13 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 1 1)) 3 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 3 2 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 1 3,
    sp_deriv_three_13 x hx, spGeoA_apply_32]
  ring_nf

private lemma sp_fderiv_three_20 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 2 1)) 0 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 0 3 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 2 0,
    sp_deriv_three_20 x hx, spGeoA_apply_03]
  ring_nf

private lemma sp_fderiv_three_21 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 2 1)) 1 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 1 3 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 2 1,
    sp_deriv_three_21 x hx, spGeoA_apply_13]
  ring_nf

private lemma sp_fderiv_three_22 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 2 1)) 2 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 2 3 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 2 2,
    sp_deriv_three_22 x hx, spGeoA_apply_23]
  ring_nf

private lemma sp_fderiv_three_23 (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ orientedSphereThreeInterior x (EuclideanSpace.single 2 1)) 3 =
      spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) 3 3 /
        (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
          openCubeCoordinate (x 2) ^ 2) ^ 2 *
        ((2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2) := by
  rw [sp_fderiv_single_eq_deriv orientedSphereThreeInterior x
      (differentiableAt_orientedSphereThreeInterior x hx) 2 3,
    sp_deriv_three_23 x hx, spGeoA_apply_33]
  ring_nf

private lemma mul_diagonal_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (d : Fin 4 → ℝ)
    (i j : Fin 4) : (A * Matrix.diagonal d) i j = A i j * d j := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases j <;> simp [Matrix.diagonal]

private lemma fin4_mk_zero (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl

private lemma fin4_mk_one (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl

private lemma fin4_mk_two (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl

private lemma fin4_mk_three (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl

private lemma fin_cases_four_one {α : Sort*} (A : α) (F : Fin 3 → α) :
    Fin.cases A F (1 : Fin 4) = F 0 := rfl

private lemma fin_cases_four_two {α : Sort*} (A : α) (F : Fin 3 → α) :
    Fin.cases A F (2 : Fin 4) = F 1 := rfl

private lemma fin_cases_four_three {α : Sort*} (A : α) (F : Fin 3 → α) :
    Fin.cases A F (3 : Fin 4) = F 2 := rfl

private def smashScale (x : ThreeSpace) : Fin 4 → ℝ :=
  ![(1 : ℝ) / (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
        openCubeCoordinate (x 2) ^ 2),
    (2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2 /
      (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
        openCubeCoordinate (x 2) ^ 2) ^ 2,
    (2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2 /
      (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
        openCubeCoordinate (x 2) ^ 2) ^ 2,
    (2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2 /
      (1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
        openCubeCoordinate (x 2) ^ 2) ^ 2]

private lemma det_colScale (A : Matrix (Fin 4) (Fin 4) ℝ) (d : Fin 4 → ℝ) :
    Matrix.det (fun i j => A i j * d j) = Matrix.det A * (d 0 * d 1 * d 2 * d 3) := by
  have hfun : (fun i j : Fin 4 => A i j * d j) =
      (A * Matrix.diagonal d : Matrix (Fin 4) (Fin 4) ℝ) := by
    funext i j
    rw [mul_diagonal_apply]
  rw [hfun, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four]

theorem standardSmash_parameter_positive (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereThreeInterior x ∧
      (0 : ℝ) < Matrix.det (fun i j : Fin 4 =>
        Fin.cases (orientedSphereThreeInterior x i)
          (fun k => (fderiv ℝ orientedSphereThreeInterior x
            (EuclideanSpace.single k 1)) i) j) := by
  refine ⟨differentiableAt_orientedSphereThreeInterior x hx, ?_⟩
  have hframe : (fun i j : Fin 4 =>
        Fin.cases (orientedSphereThreeInterior x i)
          (fun k => (fderiv ℝ orientedSphereThreeInterior x
            (EuclideanSpace.single k 1)) i) j) =
      fun i j : Fin 4 =>
        spGeoA (openCubeCoordinate (x 0)) (openCubeCoordinate (x 1))
          (openCubeCoordinate (x 2)) i j * smashScale x j := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp only [fin4_mk_zero, fin4_mk_one, fin4_mk_two, fin4_mk_three, Fin.cases_zero,
        fin_cases_four_one, fin_cases_four_two, fin_cases_four_three, sp_point_three,
        sp_fderiv_three_00 x hx, sp_fderiv_three_01 x hx, sp_fderiv_three_02 x hx,
        sp_fderiv_three_03 x hx, sp_fderiv_three_10 x hx, sp_fderiv_three_11 x hx,
        sp_fderiv_three_12 x hx, sp_fderiv_three_13 x hx, sp_fderiv_three_20 x hx,
        sp_fderiv_three_21 x hx, sp_fderiv_three_22 x hx, sp_fderiv_three_23 x hx,
        spGeoA_apply_00, spGeoA_apply_01, spGeoA_apply_02, spGeoA_apply_03, spGeoA_apply_10,
        spGeoA_apply_11, spGeoA_apply_12, spGeoA_apply_13, spGeoA_apply_20, spGeoA_apply_21,
        spGeoA_apply_22, spGeoA_apply_23, spGeoA_apply_30, spGeoA_apply_31, spGeoA_apply_32,
        spGeoA_apply_33, smashScale, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;>
      ring_nf
  rw [hframe, det_colScale, sp_geoA_det]
  simp only [smashScale, vec4_two, vec4_three, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd0 : 0 < (2 * (x 0) ^ 2 - 2 * (x 0) + 1) / ((x 0) * (1 - (x 0))) ^ 2 := by
    apply div_pos
    · nlinarith [sq_nonneg ((x 0) - 1 / 2)]
    · exact pow_pos (mul_pos (hx 0).1 (by linarith [(hx 0).2])) 2
  have hd1 : 0 < (2 * (x 1) ^ 2 - 2 * (x 1) + 1) / ((x 1) * (1 - (x 1))) ^ 2 := by
    apply div_pos
    · nlinarith [sq_nonneg ((x 1) - 1 / 2)]
    · exact pow_pos (mul_pos (hx 1).1 (by linarith [(hx 1).2])) 2
  have hd2 : 0 < (2 * (x 2) ^ 2 - 2 * (x 2) + 1) / ((x 2) * (1 - (x 2))) ^ 2 := by
    apply div_pos
    · nlinarith [sq_nonneg ((x 2) - 1 / 2)]
    · exact pow_pos (mul_pos (hx 2).1 (by linarith [(hx 2).2])) 2
  have hDpos : 0 < 1 + openCubeCoordinate (x 0) ^ 2 + openCubeCoordinate (x 1) ^ 2 +
      openCubeCoordinate (x 2) ^ 2 := by positivity
  positivity



theorem standardSmashHomeomorph_interior (z : I^(Fin 3))
    (hz : z ∉ Cube.boundary (Fin 3)) :
    (standardSmashHomeomorph (smashCubeParameter z) : EuclideanSpace ℝ (Fin 4)) =
      orientedSphereThreeInterior (WithLp.toLp 2 (fun i => (z i : ℝ))) := by
  have h := congrArg (fun f : C(I^(Fin 3), Sphere 3) => (f z : EuclideanSpace ℝ (Fin 4)))
    standardSmashHomeomorph_cube
  dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, sphereThreeCubeParameter] at h
  simpa [sphereThreeCubeVector, hz] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
