import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopOrbit

/-!
A genuine deep complementary solid torus for the one-ball, one-handle loop in S³.
Its whole compact image has Clifford height at least 3/4 and leaves a nonempty orbit shell.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance complementSphereSecond : SecondCountableTopology SphereCarrier.{0} :=
  secondCountableTopology_sphereCarrier

private def complementBaseScale : (EuclideanSpace ℝ (Fin 2) × Circle)
    ≃ₘ⟮(𝓡 2).prod (𝓡 1), (𝓡 2).prod (𝓡 1)⟯ (EuclideanSpace ℝ (Fin 2) × Circle) :=
  Diffeomorph.prodCongr
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin 2)) (1 / 2)
      (by norm_num)).toContinuousLinearEquiv.toDiffeomorph
    (Diffeomorph.refl (𝓡 1) Circle ∞)

private theorem complementBaseScale_apply (p : EuclideanSpace ℝ (Fin 2) × Circle) :
    complementBaseScale p = ((1 / 2 : ℝ) • p.1, p.2) := rfl

private def complementChart : PartialDiffeomorph (𝓡 3) (𝓡 3)
    SphereCarrier.{0} SphereCarrier.{0} ∞ :=
  sphereSwap.toPartialDiffeomorph.trans
    (loopCircleCoordinates.symm.trans
      (complementBaseScale.toPartialDiffeomorph.trans loopCircleCoordinates))

private theorem complementChart_source (p : solidTorusSet.{0}) :
    p.val ∈ complementChart.source := by
  have hne : sphereFirst (sphereSwap p.val) ≠ 0 := by
    rw [sphereFirst_sphereSwap]
    exact sphereSecond_ne_zero_of_mem p.2
  have hn : ‖(loopCircleCoordinates.symm (sphereSwap p.val)).1‖ < 1 :=
    loopCircleCoordinates.symm.map_source hne
  refine ⟨trivial, hne, trivial, ?_⟩
  change ‖(1 / 2 : ℝ) • (loopCircleCoordinates.symm (sphereSwap p.val)).1‖ < 1
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith [norm_nonneg (loopCircleCoordinates.symm (sphereSwap p.val)).1]

private theorem complementChart_second (p : solidTorusSet.{0}) :
    sphereSecond (complementChart p.val) = (1 / 2 : ℝ) • sphereFirst p.val := by
  have hp := complementChart_source p
  change sphereSecond (loopCircleCoordinates
    (complementBaseScale (loopCircleCoordinates.symm (sphereSwap p.val)))) = _
  have hh : ‖(complementBaseScale
      (loopCircleCoordinates.symm (sphereSwap p.val))).1‖ < 1 := hp.2.2.2
  rw [loopCircleCoordinates_second hh, complementBaseScale_apply,
    loopCircleCoordinates_inverse, sphereSecond_sphereSwap, map_smul,
    LinearIsometryEquiv.apply_symm_apply]

private theorem complementMap_smooth : ContMDiff (𝓡∂ 3) (𝓡 3) ∞
    (fun p : solidTorusSet.{0} => complementChart p.val) := by
  intro p
  exact (complementChart.contMDiffOn_toFun.contMDiffAt
    (complementChart.open_source.mem_nhds (complementChart_source p))).comp p
    (contMDiff_solidTorus_val p)

private theorem complementMap_bijective (p : solidTorusSet.{0}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (fun p : solidTorusSet.{0} => complementChart p.val) p) := by
  change Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
    ((complementChart : SphereCarrier.{0} → SphereCarrier.{0}) ∘
      (Subtype.val : solidTorusSet.{0} → SphereCarrier.{0})) p)
  rw [mfderiv_comp p (complementChart.mdifferentiableAt (by simp) (complementChart_source p))
    (contMDiff_solidTorus_val.mdifferentiable (by simp) p)]
  have hloc := complementChart.isLocalDiffeomorphAt _ _ _ (complementChart_source p)
  exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective.comp
    (solidTorusAtlas.mfderiv_subtypeVal_bijective p)

def loopComplementVertex : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}) where
  Piece := solidTorusSet.{0}
  map := fun p => complementChart p.val
  smooth := complementMap_smooth
  mfderiv_bijective := complementMap_bijective
  injective := by
    intro p q h
    apply Subtype.ext
    exact complementChart.injOn (complementChart_source p) (complementChart_source q) h

private theorem complementMap_height (p : solidTorusSet.{0}) :
    3 / 4 ≤ cliffordHeight (loopComplementVertex.map p) := by
  have hh := norm_sphereSecond_sq_eq (loopComplementVertex.map p)
  have hs := complementChart_second p
  change sphereSecond (loopComplementVertex.map p) = (1 / 2 : ℝ) • sphereFirst p.val at hs
  rw [hs, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow] at hh
  have hfirst := norm_sphereFirst_sq_eq p.val
  have hp : cliffordHeight p.val ≤ 0 := p.2
  nlinarith

theorem loopComplementVertex_range : Set.range loopComplementVertex.map =
    {p | 3 / 4 ≤ cliffordHeight p} := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, rfl⟩
    exact complementMap_height p
  · intro q hq
    have hsec : ‖sphereSecond q‖ ^ 2 ≤ 1 / 8 := by
      have hh := norm_sphereSecond_sq_eq q
      change 3 / 4 ≤ cliffordHeight q at hq
      linarith
    have hne : sphereFirst q ≠ 0 := by
      intro he
      have hh := norm_sphereFirst_sq_add q
      rw [he, norm_zero, zero_pow (by decide), zero_add] at hh
      linarith
    let z : EuclideanSpace ℝ (Fin 2) := modelPlaneComplex.symm (sphereSecond q)
    have hz : ‖z‖ ^ 2 ≤ 1 / 8 := by
      simpa only [z, LinearIsometryEquiv.norm_map] using hsec
    have hsource : ‖(2 : ℝ) • z‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [norm_nonneg z]
    let w : SphereCarrier.{0} := loopCircleCoordinates ((2 : ℝ) • z, unitOf (sphereFirst q))
    have hwsec : sphereSecond w = modelPlaneComplex ((2 : ℝ) • z) :=
      loopCircleCoordinates_second hsource
    have hwheight : 0 ≤ cliffordHeight w := by
      have hh := norm_sphereSecond_sq_eq w
      rw [hwsec, modelPlaneComplex.norm_map, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_pow] at hh
      nlinarith
    have hwmem : sphereSwap w ∈ solidTorusSet.{0} := by
      change cliffordHeight (sphereSwap w) ≤ 0
      rw [cliffordHeight_sphereSwap]
      linarith
    refine ⟨⟨sphereSwap w, hwmem⟩, ?_⟩
    change loopCircleCoordinates
      (complementBaseScale (loopCircleCoordinates.symm (sphereSwap (sphereSwap w)))) = q
    rw [sphereSwap_sphereSwap]
    have hwcoord : loopCircleCoordinates.symm w = ((2 : ℝ) • z, unitOf (sphereFirst q)) :=
      loopCircleCoordinates.left_inv hsource
    rw [hwcoord, complementBaseScale_apply]
    have hscale : (1 / 2 : ℝ) • (2 : ℝ) • z = z := by
      rw [smul_smul]
      norm_num
    change loopCircleCoordinates
      ((1 / 2 : ℝ) • (2 : ℝ) • z, unitOf (sphereFirst q)) = q
    rw [hscale]
    change loopCircleCoordinates (loopCircleCoordinates.symm q) = q
    exact loopCircleCoordinates.right_inv hne

theorem loopComplementVertex_disjoint :
    Disjoint (Set.range loopComplementVertex.map) solidTorusSet.{0} := by
  rw [loopComplementVertex_range]
  apply Set.disjoint_left.mpr
  intro p hp hs
  change 3 / 4 ≤ cliffordHeight p at hp
  change cliffordHeight p ≤ 0 at hs
  linarith

end GC.GraphManifold.Assembly
