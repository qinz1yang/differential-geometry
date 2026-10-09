import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeBundleData

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_RankX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_RankX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialNegativeSeam : TopologicalSpace.Opens (Torus × ℝ) :=
  ⟨{q | -1 < q.2 ∧ q.2 < 0},
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)⟩

def negativeSeamToSphere (q : radialNegativeSeam) : radialSphereInterior :=
  ⟨cliffordSeamMap q.val, by
    change cliffordHeight (cliffordSeamMap q.val) < 0
    rw [cliffordHeight_cliffordSeamMap,
      seamClamp_of_mem q.property.1.le (q.property.2.trans_le (by norm_num)).le]
    exact q.property.2⟩

theorem negativeSeamToSphere_smooth :
    ContMDiff signedCollarModel (𝓡 3) ∞ negativeSeamToSphere := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialSphereInterior negativeSeamToSphere).mp
  intro q
  have hq : q.val ∈ cliffordSeam.{0}.source :=
    ⟨q.property.1, q.property.2.trans (by norm_num)⟩
  exact (cliffordSeam.{0}.contMDiffOn_toFun.contMDiffAt
    (cliffordSeam.{0}.open_source.mem_nhds hq)).comp q contMDiff_subtype_val.contMDiffAt

def negativeSeamToCarrier (q : radialNegativeSeam) : carrier.Carrier :=
  sphereInteriorToCarrier (negativeSeamToSphere q)

theorem negativeSeamToCarrier_smooth :
    ContMDiff signedCollarModel (𝓡∂ 3) ∞ negativeSeamToCarrier :=
  sphereInteriorToCarrier_smooth.comp negativeSeamToSphere_smooth

theorem height_negativeSeam (q : radialNegativeSeam) :
    height (negativeSeamToCarrier q) = q.val.2 := by
  change cliffordHeight (cliffordSeamMap q.val) = q.val.2
  rw [cliffordHeight_cliffordSeamMap,
    seamClamp_of_mem q.property.1.le (q.property.2.trans_le (by norm_num)).le]

theorem edgeLongitude_negativeSeam (q : radialNegativeSeam) :
    edgeLongitude (negativeSeamToCarrier q) = q.val.1.2 := by
  change unitOf (sphereSecond (cliffordSeamMap q.val)) = q.val.1.2
  rw [sphereSecond_cliffordSeamMap]
  exact unitOf_smul (seamSecond_pos (q.property.2.trans (by norm_num))) _

def edgeCircleHeight (p : carrier.Carrier) : Circle × ℝ := (edgeLongitude p, height p)

theorem edgeCircleHeight_smooth :
    ContMDiff (𝓡∂ 3) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ edgeCircleHeight :=
  edgeLongitude_smooth.prodMk height_smooth

def negativeSeamPair (q : radialNegativeSeam) : Circle × ℝ := (q.val.1.2, q.val.2)

theorem negativeSeamPair_onto (q : radialNegativeSeam) :
    Surjective (mfderiv signedCollarModel ((𝓡 1).prod 𝓘(ℝ, ℝ)) negativeSeamPair q) := by
  change Surjective (mfderiv signedCollarModel ((𝓡 1).prod 𝓘(ℝ, ℝ))
    (fun y : radialNegativeSeam => (y.val.1.2, y.val.2)) q)
  rw [DifferentialGeometry.mfderiv_restrict_open
    (fun y : Torus × ℝ => (y.1.2, y.2)) radialNegativeSeam q]
  have h₁ : MDifferentiableAt signedCollarModel (𝓡 1)
      (fun y : Torus × ℝ => y.1.2) q.val :=
    mdifferentiableAt_snd.comp q.val mdifferentiableAt_fst
  have hc : mfderiv signedCollarModel (𝓡 1) (fun y : Torus × ℝ => y.1.2) q.val =
      (mfderiv ((𝓡 1).prod (𝓡 1)) (𝓡 1) (fun t : Torus => t.2) q.val.1).comp
        (mfderiv signedCollarModel ((𝓡 1).prod (𝓡 1))
          (fun y : Torus × ℝ => y.1) q.val) :=
    mfderiv_comp q.val mdifferentiableAt_snd mdifferentiableAt_fst
  have hd := mfderiv_prodMk h₁ (mdifferentiableAt_snd
    (I := ((𝓡 1).prod (𝓡 1))) (I' := 𝓘(ℝ, ℝ)) (x := q.val))
  intro v
  refine ⟨((0, v.1), v.2), ?_⟩
  rw [hd]
  apply Prod.ext
  · change mfderiv signedCollarModel (𝓡 1)
      (fun y : Torus × ℝ => y.1.2) q.val ((0, v.1), v.2) = v.1
    rw [hc, mfderiv_snd, mfderiv_fst]
    rfl
  · change mfderiv signedCollarModel 𝓘(ℝ, ℝ)
      (fun y : Torus × ℝ => y.2) q.val ((0, v.1), v.2) = v.2
    rw [mfderiv_snd]
    rfl

theorem edgeCircleHeight_negativeSeam_onto (q : radialNegativeSeam) :
    Surjective (mfderiv (𝓡∂ 3) ((𝓡 1).prod 𝓘(ℝ, ℝ)) edgeCircleHeight
      (negativeSeamToCarrier q)) := by
  have heq : edgeCircleHeight ∘ negativeSeamToCarrier = negativeSeamPair := by
    funext y
    exact Prod.ext (edgeLongitude_negativeSeam y) (height_negativeSeam y)
  have hc := mfderiv_comp q (edgeCircleHeight_smooth.mdifferentiableAt (by simp))
    (negativeSeamToCarrier_smooth.mdifferentiableAt (by simp))
  rw [heq] at hc
  intro v
  obtain ⟨w, hw⟩ := negativeSeamPair_onto q v
  refine ⟨mfderiv signedCollarModel (𝓡∂ 3) negativeSeamToCarrier q w, ?_⟩
  exact (congrArg (fun A => A w) hc).symm.trans hw

theorem exists_negativeSeam_at (p : carrier.Carrier)
    (hp : -1 < height p) (hn : height p < 0) :
    ∃ q : radialNegativeSeam, negativeSeamToCarrier q = p := by
  have ht : p.val ∈ cliffordSeam.{0}.target := by
    constructor
    · intro hz
      have hh := norm_sphereFirst_sq_eq p.val
      rw [hz, norm_zero, zero_pow (by decide)] at hh
      change -1 < cliffordHeight p.val at hp
      linarith
    · intro hz
      have hh := norm_sphereSecond_sq_eq p.val
      rw [hz, norm_zero, zero_pow (by decide)] at hh
      change cliffordHeight p.val < 0 at hn
      linarith
  let q : radialNegativeSeam := ⟨cliffordSeamInv p.val, ⟨hp, hn⟩⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact cliffordSeam.{0}.right_inv ht

theorem edgeCircleHeight_onto (p : carrier.Carrier)
    (hp : -1 < height p) (hn : height p < 0) :
    Surjective (mfderiv (𝓡∂ 3) ((𝓡 1).prod 𝓘(ℝ, ℝ)) edgeCircleHeight p) := by
  obtain ⟨q, rfl⟩ := exists_negativeSeam_at p hp hn
  exact edgeCircleHeight_negativeSeam_onto q

theorem edgeBundle_rank_two (p : radialCarrierInterior)
    (hp : edgeBundleHeight p = -(3 / 4 : ℝ)) :
    Surjective fun v : TangentSpace (𝓡∂ 3) p.val =>
      (mfderiv (𝓡∂ 3) (𝓡 1) edgeBundleProjection p v,
        mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) edgeBundleHeight p v) := by
  have hlo : -1 < height p.val := by
    change height p.val = -(3 / 4 : ℝ) at hp
    rw [hp]
    norm_num
  have ho := edgeCircleHeight_onto p.val hlo p.property
  have hc := mfderiv_prodMk (edgeLongitude_smooth.mdifferentiableAt (by simp)
    (x := p.val)) (height_smooth.mdifferentiableAt (by simp) (x := p.val))
  intro v
  obtain ⟨w, hw⟩ := ho v
  have he : mfderiv (𝓡∂ 3) (𝓡 1) edgeBundleProjection p =
      mfderiv (𝓡∂ 3) (𝓡 1) edgeLongitude p.val :=
    DifferentialGeometry.mfderiv_restrict_open edgeLongitude radialCarrierInterior p
  have hh : mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) edgeBundleHeight p =
      mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) height p.val :=
    DifferentialGeometry.mfderiv_restrict_open height radialCarrierInterior p
  refine ⟨w, ?_⟩
  rw [he, hh]
  exact (congrArg (fun A => A w) hc).symm.trans hw

def radialEdgeBundle : EdgeBundle carrier where
  Base := Circle
  source := radialCarrierInterior
  source_interior := fun p hp => sphereInteriorToCarrier_interior
    (openCarrierToSphere ⟨p, hp⟩)
  proj := edgeBundleProjection
  proj_smooth := edgeBundleProjection_smooth
  proj_submersion := edgeBundleProjection_onto
  height := edgeBundleHeight
  height_smooth := edgeBundleHeight_smooth
  level := -(3 / 4 : ℝ)
  rank_two := edgeBundle_rank_two
  proper := edgeBundle_proper
  fibre_disk := edgeBundle_fibre_disk
  cbase := univ
  cbase_compact := isCompact_univ
  cbase_domain := by simp

end GC.GraphManifold.Assembly.FC39P0.X135Radial
