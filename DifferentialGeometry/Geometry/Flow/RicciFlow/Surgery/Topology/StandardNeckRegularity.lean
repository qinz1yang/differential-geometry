import DifferentialGeometry.Geometry.Boundary.ProductHalfSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCap
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private abbrev NeckE3 := EuclideanSpace ℝ (Fin 3)
private abbrev NeckE4 := EuclideanSpace ℝ (Fin 4)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private theorem contMDiff_neckHeight :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun z : TubeDomain => Real.sqrt (1 - ((z.2 : ℝ) / 4) ^ 2)) := by
  have hg : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => Real.sqrt (1 - (t / 4) ^ 2)) (Icc (-2 : ℝ) 2) := by
    apply ContDiffOn.contMDiffOn
    refine ContDiffOn.sqrt ?_ ?_
    · apply ContDiffOn.sub contDiffOn_const
      apply ContDiffOn.pow
      exact contDiffOn_id.div_const 4
    · intro t ht
      have h1 : |t| ≤ 2 := abs_le.mpr ⟨ht.1, ht.2⟩
      have h2 : t ^ 2 ≤ 4 := by
        have h3 : |t| ^ 2 ≤ 2 ^ 2 := by nlinarith [abs_nonneg t, h1]
        norm_num at h3
        exact h3
      have h4 : (t / 4) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (t / 4)]
  exact hg.comp_contMDiff ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)).comp
    contMDiff_snd) (fun z => z.2.2)

private theorem snocR_three (f : Fin 3 → ℝ) (a : ℝ) : snocR f a (3 : Fin 4) = a := by
  rw [show (3 : Fin 4) = Fin.last 3 from rfl, snocR_last]

private theorem contMDiff_neckCoord_last :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun z : TubeDomain => (z.2 : ℝ) / 4) :=
  ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)).comp contMDiff_snd).div_const 4

private theorem contMDiff_sphereCoord (j : Fin 3) :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun z : TubeDomain => ((z.1 : NeckE3) j)) :=
  ((EuclideanSpace.proj j).contMDiff).comp <|
    (contMDiff_coe_sphere (n := 2) (E := NeckE3)).comp contMDiff_fst

private def neckCoordFun (z : TubeDomain) : Fin 4 → ℝ :=
  snocR (fun j : Fin 3 => Real.sqrt (1 - ((z.2 : ℝ) / 4) ^ 2) * ((z.1 : NeckE3) j))
    ((z.2 : ℝ) / 4)

private theorem contMDiff_neckCoordFun :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, (Fin 4 → ℝ)) ∞ neckCoordFun := by
  rw [contMDiff_pi_space]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [neckCoordFun, snocR_last]
    exact contMDiff_neckCoord_last
  · intro j
    simp only [neckCoordFun, snocR_castSucc]
    exact contMDiff_neckHeight.mul (contMDiff_sphereCoord j)

private theorem contMDiff_neckPoint :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, NeckE4) ∞
      (fun z : TubeDomain => (neckPoint z.1 z.2.1 : NeckE4)) := by
  have hE : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, NeckE4) ∞
      (fun z : TubeDomain => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm
        (neckCoordFun z)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm :
      (Fin 4 → ℝ) →L[ℝ] NeckE4).contMDiff.comp contMDiff_neckCoordFun
  refine hE.congr ?_
  intro z
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, neckCoordFun, neckPoint,
    snocR]

theorem contMDiff_standardNeckTubeFun :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTubeFun := by
  have h := contMDiff_neckPoint.codRestrict_sphere (n := 3)
    (fun z : TubeDomain => neckPoint_mem_sphere z.1 z.2)
  rwa [show (codRestrict (fun z : TubeDomain => (neckPoint z.1 z.2.1 : NeckE4))
      (Metric.sphere 0 1) _) = standardNeckTubeFun from rfl] at h

theorem standardNeckTube_isImmersion_of_isSmoothEmbedding
    (h : standardNeckTubeIsSmoothEmbedding) :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTube :=
  h.isImmersion

theorem standardNeckTubeIsSmoothEmbedding_of_isImmersion
    (h : letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
      IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTube) :
    standardNeckTubeIsSmoothEmbedding :=
  ⟨h, isEmbedding_standardNeckTubeFun⟩

theorem standardNeckTube_isImmersion_of_cylinder_immersion (g : Sphere 2 × ℝ → Sphere 3)
    (hg : IsImmersion ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g)
    (hsub : ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z) :
    IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTubeFun := by
  have hf : IsImmersion ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (Prod.map (id : Sphere 2 → Sphere 2) (Subtype.val : Icc (-2 : ℝ) 2 → ℝ)) :=
    IsImmersion.prodMap IsImmersion.id
      (isImmersionOfComplement_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)).isImmersion
  exact (IsImmersion.comp_of_smoothBoundary hf hg).congr (funext hsub)

theorem standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding
    (g : Sphere 2 × ℝ → Sphere 3)
    (hg : IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g)
    (hsub : ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z) :
    standardNeckTubeIsSmoothEmbedding :=
  ⟨standardNeckTube_isImmersion_of_cylinder_immersion g hg.isImmersion hsub,
    isEmbedding_standardNeckTubeFun⟩

theorem TubeSystem.coreBoundarySphere_disjoint {M : Type u} [TopologicalSpace M]
    (T : TubeSystem M) {b b' : T.Boundary} (h : b ≠ b') :
    Disjoint (Set.range (T.coreBoundarySphere b)) (Set.range (T.coreBoundarySphere b')) := by
  rcases b with ⟨a, s⟩
  rcases b' with ⟨a', s'⟩
  rw [Set.disjoint_left]
  rintro p ⟨y, rfl⟩ ⟨y', hy'⟩
  have h' : T.boundarySphere (a', s') y' = T.boundarySphere (a, s) y :=
    congrArg (fun q : T.core => (q : M)) hy'
  by_cases ha : a = a'
  · subst ha
    have hcoord : TubeSystem.boundaryLevel s' = TubeSystem.boundaryLevel s := by
      have hinj := (T.embedding a).injective h'
      exact congrArg (fun z : TubeDomain => z.2) hinj
    cases s <;> cases s'
    · exact absurd rfl h
    · norm_num [TubeSystem.boundaryLevel] at hcoord
    · norm_num [TubeSystem.boundaryLevel] at hcoord
    · exact absurd rfl h
  · refine Set.disjoint_left.mp (T.disjoint ha)
      (Set.mem_range_self (f := T.tube a) ⟨y, TubeSystem.boundaryLevel s⟩) ?_
    exact ⟨⟨y', TubeSystem.boundaryLevel s'⟩, h'⟩

theorem TubeSystem.coreBoundarySphere_mem_boundary {M : Type u} [TopologicalSpace M]
    (T : TubeSystem M) [ChartedSpace (EuclideanHalfSpace 3) T.core]
    [IsManifold (𝓡∂ 3) ∞ T.core]
    (hcore : (𝓡∂ 3).boundary T.core = ⋃ b, Set.range (T.coreBoundarySphere b))
    (b : T.Boundary) (y : Sphere 2) :
    T.coreBoundarySphere b y ∈ (𝓡∂ 3).boundary T.core := by
  rw [hcore]
  exact Set.mem_iUnion.mpr ⟨b, Set.mem_range_self y⟩

theorem CutCapTransitionData.coreBoundarySphere_mem_boundary {P Q D N : OrientedThreeStage.{u}}
    (X : CutCapTransitionData P Q D N) (b : X.trace.tubes.Boundary) (y : Sphere 2) :
    letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
    letI : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
    X.trace.tubes.coreBoundarySphere b y ∈ (𝓡∂ 3).boundary X.trace.tubes.core :=
  @TubeSystem.coreBoundarySphere_mem_boundary _ _ X.trace.tubes X.coreCharts X.coreSmooth
    X.core_boundary b y

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
