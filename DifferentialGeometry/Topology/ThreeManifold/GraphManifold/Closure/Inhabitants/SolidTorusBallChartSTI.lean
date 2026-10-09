import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusInterior
import DifferentialGeometry.Topology.Manifold.ClosedCellChart

/-!
# S-SOLIDTORUS (suffix `_STI`), part 1: the graph chart of the cap ball

The ball zero core of the solid torus instance is the S³ cap `{Re z₂ ≥ κ}`, `κ = 4/5`. Its graph
chart `v = (z₁, Im z₂) ∈ ℝ³ ↦ (z₁, √(1 - ‖v‖²) + i v₂)` is a partial diffeomorphism from the open
unit ball of `ℝ³` onto the open hemisphere `{Re z₂ > 0}` of `S³`. The cap is the image of the closed
ball of radius `3/5`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI

/-- The point of `ℝ³` with the given coordinates. -/
def ofCoords_STI (a b c : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  a • EuclideanSpace.single 0 (1 : ℝ) + b • EuclideanSpace.single 1 (1 : ℝ) +
    c • EuclideanSpace.single 2 (1 : ℝ)

@[simp] theorem ofCoords_zero_STI (a b c : ℝ) : ofCoords_STI a b c 0 = a := by
  simp [ofCoords_STI]

@[simp] theorem ofCoords_one_STI (a b c : ℝ) : ofCoords_STI a b c 1 = b := by
  simp [ofCoords_STI]

@[simp] theorem ofCoords_two_STI (a b c : ℝ) : ofCoords_STI a b c 2 = c := by
  simp [ofCoords_STI]

theorem norm_sq_fin_three_STI (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The first coordinate `z₁ = v₀ + i v₁` of the graph chart. -/
def graphFirst_STI (v : EuclideanSpace ℝ (Fin 3)) : ℂ := ⟨v 0, v 1⟩

/-- The second coordinate `z₂ = √(1 - ‖v‖²) + i v₂` of the graph chart. -/
def graphSecond_STI (v : EuclideanSpace ℝ (Fin 3)) : ℂ := ⟨√(1 - ‖v‖ ^ 2), v 2⟩

theorem graph_norm_STI {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ^ 2 ≤ 1) :
    ‖graphFirst_STI v‖ ^ 2 + ‖graphSecond_STI v‖ ^ 2 = 1 := by
  have h1 : ‖graphFirst_STI v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [graphFirst_STI, sq]
  have h2 : ‖graphSecond_STI v‖ ^ 2 = (1 - ‖v‖ ^ 2) + v 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [graphSecond_STI]
    have := Real.sq_sqrt (sub_nonneg.mpr hv)
    nlinarith
  rw [h1, h2, norm_sq_fin_three_STI v]
  ring


theorem graphFirst_re_STI (v : EuclideanSpace ℝ (Fin 3)) : (graphFirst_STI v).re = v 0 := rfl

theorem graphFirst_im_STI (v : EuclideanSpace ℝ (Fin 3)) : (graphFirst_STI v).im = v 1 := rfl

theorem graphSecond_re_STI (v : EuclideanSpace ℝ (Fin 3)) :
    (graphSecond_STI v).re = √(1 - ‖v‖ ^ 2) := rfl

theorem graphSecond_im_STI (v : EuclideanSpace ℝ (Fin 3)) : (graphSecond_STI v).im = v 2 := rfl

/-- A default point of `S³` (the point `(0, 1)`), used off the source of the chart. -/
def graphDefault_STI : SphereCarrier.{0} := sphereOfPair 0 1 (by simp)

/-- The graph chart map `v ↦ (z₁, z₂)` of the hemisphere `{Re z₂ > 0}`. -/
def graphMap_STI (v : EuclideanSpace ℝ (Fin 3)) : SphereCarrier.{0} :=
  if h : ‖v‖ ^ 2 ≤ 1 then sphereOfPair (graphFirst_STI v) (graphSecond_STI v) (graph_norm_STI h)
  else graphDefault_STI

theorem graphMap_of_le_STI {v : EuclideanSpace ℝ (Fin 3)} (h : ‖v‖ ^ 2 ≤ 1) :
    graphMap_STI v = sphereOfPair (graphFirst_STI v) (graphSecond_STI v) (graph_norm_STI h) := by
  rw [graphMap_STI]
  split_ifs
  rfl

theorem sphereFirst_graphMap_STI {v : EuclideanSpace ℝ (Fin 3)} (h : ‖v‖ ^ 2 ≤ 1) :
    sphereFirst (graphMap_STI v) = graphFirst_STI v := by
  rw [graphMap_of_le_STI h, sphereFirst_sphereOfPair]

theorem sphereSecond_graphMap_STI {v : EuclideanSpace ℝ (Fin 3)} (h : ‖v‖ ^ 2 ≤ 1) :
    sphereSecond (graphMap_STI v) = graphSecond_STI v := by
  rw [graphMap_of_le_STI h, sphereSecond_sphereOfPair]

/-- The inverse of the graph chart: the coordinates `(Re z₁, Im z₁, Im z₂)`. -/
def graphInv_STI (p : SphereCarrier.{0}) : EuclideanSpace ℝ (Fin 3) :=
  ofCoords_STI (sphereFirst p).re (sphereFirst p).im (sphereSecond p).im

theorem norm_sq_graphInv_STI (p : SphereCarrier.{0}) :
    ‖graphInv_STI p‖ ^ 2 = 1 - (sphereSecond p).re ^ 2 := by
  rw [norm_sq_fin_three_STI]
  have h := norm_sphereFirst_sq_add p
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply] at h
  simp only [graphInv_STI, ofCoords_zero_STI, ofCoords_one_STI, ofCoords_two_STI]
  nlinarith

theorem contDiff_ofCoords_STI :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ => ofCoords_STI x.1 x.2.1 x.2.2) := by
  unfold ofCoords_STI
  fun_prop

theorem contMDiff_graphInv_STI :
    ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ graphInv_STI := by
  have hre : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p : SphereCarrier.{0} => (sphereFirst p).re) :=
    Complex.reCLM.contDiff.contMDiff.comp contMDiff_sphereFirst
  have him : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p : SphereCarrier.{0} => (sphereFirst p).im) :=
    Complex.imCLM.contDiff.contMDiff.comp contMDiff_sphereFirst
  have him2 : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p : SphereCarrier.{0} => (sphereSecond p).im) :=
    Complex.imCLM.contDiff.contMDiff.comp contMDiff_sphereSecond
  exact contDiff_ofCoords_STI.contMDiff.comp (hre.prodMk_space (him.prodMk_space him2))


theorem graphFirst_contDiff_STI :
    ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => graphFirst_STI v) := by
  have h : (fun v : EuclideanSpace ℝ (Fin 3) => graphFirst_STI v) =
      fun v => (v 0 : ℝ) • (1 : ℂ) + (v 1 : ℝ) • Complex.I := by
    funext v
    apply Complex.ext <;> simp [graphFirst_STI]
  rw [h]
  have h0 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff
  exact (h0.smul contDiff_const).add (h1.smul contDiff_const)

theorem graphSecond_contDiffOn_STI :
    ContDiffOn ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => graphSecond_STI v) (Metric.ball 0 1) := by
  have h : (fun v : EuclideanSpace ℝ (Fin 3) => graphSecond_STI v) =
      fun v => (√(1 - ‖v‖ ^ 2) : ℝ) • (1 : ℂ) + (v 2 : ℝ) • Complex.I := by
    funext v
    apply Complex.ext <;> simp [graphSecond_STI]
  rw [h]
  have h2 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff
  have hs : ContDiffOn ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => √(1 - ‖v‖ ^ 2))
      (Metric.ball 0 1) := by
    intro v hv
    have hpos : 0 < 1 - ‖v‖ ^ 2 := by
      have : ‖v‖ < 1 := by simpa using hv
      nlinarith [norm_nonneg v]
    have hin : ContDiffAt ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => 1 - ‖v‖ ^ 2) v :=
      (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt
    exact ((Real.contDiffAt_sqrt hpos.ne').comp v hin).contDiffWithinAt
  exact (hs.smul contDiffOn_const).add (h2.contDiffOn.smul contDiffOn_const)

/-- **The graph chart of the hemisphere `{Re z₂ > 0}`** as a partial diffeomorphism from the open
unit ball of `ℝ³`. -/
def graphChart_STI :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) SphereCarrier.{0} ∞ where
  toFun := graphMap_STI
  invFun := graphInv_STI
  source := Metric.ball 0 1
  target := {p | 0 < (sphereSecond p).re}
  map_source' := by
    intro v hv
    have hv1 : ‖v‖ < 1 := by simpa using hv
    have hle : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    change 0 < (sphereSecond (graphMap_STI v)).re
    rw [sphereSecond_graphMap_STI hle, graphSecond_re_STI]
    exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg v])
  map_target' := by
    intro p hp
    change 0 < (sphereSecond p).re at hp
    have h := norm_sq_graphInv_STI p
    have : ‖graphInv_STI p‖ < 1 := by
      by_contra hcon
      replace hcon := not_lt.mp hcon
      nlinarith [norm_nonneg (graphInv_STI p)]
    simpa using this
  left_inv' := by
    intro v hv
    have hv1 : ‖v‖ < 1 := by simpa using hv
    have hle : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    change graphInv_STI (graphMap_STI v) = v
    ext i
    fin_cases i
    · simp [graphInv_STI, sphereFirst_graphMap_STI hle]
      rfl
    · simp [graphInv_STI, sphereFirst_graphMap_STI hle]
      rfl
    · simp [graphInv_STI, sphereSecond_graphMap_STI hle]
      rfl
  right_inv' := by
    intro p hp
    change 0 < (sphereSecond p).re at hp
    have hsq := norm_sq_graphInv_STI p
    have hle : ‖graphInv_STI p‖ ^ 2 ≤ 1 := by nlinarith
    change graphMap_STI (graphInv_STI p) = p
    apply sphere_ext
    · rw [sphereFirst_graphMap_STI hle]
      apply Complex.ext <;> simp [graphFirst_STI, graphInv_STI]
    · rw [sphereSecond_graphMap_STI hle]
      apply Complex.ext
      · simp only [graphSecond_re_STI, hsq]
        rw [show 1 - (1 - (sphereSecond p).re ^ 2) = (sphereSecond p).re ^ 2 by ring]
        exact Real.sqrt_sq hp.le
      · simp [graphSecond_STI, graphInv_STI]
  open_source := Metric.isOpen_ball
  open_target := isOpen_lt continuous_const
    (Complex.continuous_re.comp contMDiff_sphereSecond.continuous)
  contMDiffOn_toFun := by
    refine contMDiffOn_of_sphereFirst_sphereSecond Metric.isOpen_ball ?_ ?_
    · refine (graphFirst_contDiff_STI.contMDiff.contMDiffOn).congr ?_
      intro v hv
      have hv1 : ‖v‖ < 1 := by simpa using hv
      exact sphereFirst_graphMap_STI (by nlinarith [norm_nonneg v])
    · refine (graphSecond_contDiffOn_STI.contMDiffOn).congr ?_
      intro v hv
      have hv1 : ‖v‖ < 1 := by simpa using hv
      exact sphereSecond_graphMap_STI (by nlinarith [norm_nonneg v])
  contMDiffOn_invFun := contMDiff_graphInv_STI.contMDiffOn

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI
