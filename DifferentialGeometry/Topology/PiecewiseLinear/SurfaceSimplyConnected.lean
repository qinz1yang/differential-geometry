/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FieldPathCones
import DifferentialGeometry.Topology.PiecewiseLinear.BettiPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryHomology
import DifferentialGeometry.Topology.PiecewiseLinear.OrderedChainCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSphereRecognition
import Mathlib.Algebra.Field.ZMod

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem finrank_ker_eq_homology_add_range
    {k : Type} [Field k] (S : CategoryTheory.ShortComplex (ModuleCat k))
    [FiniteDimensional k S.X₂] :
    Module.finrank k (LinearMap.ker S.g.hom) = Module.finrank k S.homology +
      Module.finrank k (LinearMap.range S.f.hom) := by
  have h := DifferentialGeometry.ShortComplex.finrank_eq_homology_add_range S
  have hr := S.g.hom.finrank_range_add_finrank_ker
  omega

private noncomputable def surfaceModTwoFundamentalChain
    (K : Geometry.SimplicialComplex ℝ E) :
    {s : Finset E // s ∈ K.faces ∧ s.card = 3} → ZMod 2 :=
  fun _ => 1

open Classical in
theorem IsCombinatorialManifold.orderedNormalizedBoundary_surfaceModTwoFundamentalChain
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) :
    let _ := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
    SimplicialComplex.orderedNormalizedBoundary (k := ZMod 2)
      K.toPreAbstractSimplicialComplex 1 (surfaceModTwoFundamentalChain K) = 0 := by
  dsimp
  let r := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let _ := r
  ext t
  change SimplicialComplex.orderedNormalizedBoundary (k := ZMod 2)
    K.toPreAbstractSimplicialComplex 1 (fun _ => 1) t = 0
  rw [orderedNormalizedBoundary_apply_eq_sum_faceCofaces r K 1
    (fun _ : Finset E => (1 : ZMod 2)) t]
  have htwo := hK.card_faceCofaces_eq_two K t.2.1 t.2.2
  calc
    _ = ∑ _s ∈ faceCofaces K t.1 3, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro s hs
      obtain ⟨hsK, hscard, hts⟩ := (mem_faceCofaces K).mp hs
      rcases simplexBoundaryCoefficient_eq_one_or_neg_one r hts (by omega) with h | h
      · simp [h]
      · simp [h]
    _ = 0 := by simpa [htwo] using ZMod.natCast_self 2

open Classical in
private theorem surfaceModTwoFundamentalChain_ne_zero
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space) :
    surfaceModTwoFundamentalChain K ≠ 0 := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htcard⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs
  intro hzero
  have hz := congrFun hzero ⟨t, ht, htcard⟩
  simp [surfaceModTwoFundamentalChain] at hz

open Classical in
theorem IsCombinatorialManifold.bettiNumber_two_pos_mod_two
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space) :
    0 < Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 2 := by
  let r := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let _ := r
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let R := ModuleCat.of (ZMod 2) (ZMod 2)
  let C := X.normalizedChainComplex R
  let e₁ := SimplicialComplex.orderedNormalizedChainEquiv (k := ZMod 2)
    K.toPreAbstractSimplicialComplex 1
  let e₂ := SimplicialComplex.orderedNormalizedChainEquiv (k := ZMod 2)
    K.toPreAbstractSimplicialComplex 2
  let z := e₂.symm (surfaceModTwoFundamentalChain K)
  let _ : FiniteDimensional (ZMod 2) (C.X 2) :=
    DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X X R 2
  let _ : FiniteDimensional (ZMod 2) (C.sc' 3 2 1).X₂ := by
    change FiniteDimensional (ZMod 2) (C.X 2)
    infer_instance
  have hzcycle : C.d 2 1 z = 0 := by
    apply e₁.injective
    simpa [SimplicialComplex.orderedNormalizedBoundary, X, C, e₁, e₂, z] using
      hK.orderedNormalizedBoundary_surfaceModTwoFundamentalChain K
  have hzne : z ≠ 0 := by
    intro hz
    apply surfaceModTwoFundamentalChain_ne_zero K hK hconn
    have he := congrArg e₂ hz
    simpa [z] using he
  let zker : LinearMap.ker (C.d 2 1).hom := ⟨z, hzcycle⟩
  have hzneKer : zker ≠ 0 := by
    intro hz
    apply hzne
    exact congrArg Subtype.val hz
  have hkerPos : 0 < Module.finrank (ZMod 2) (LinearMap.ker (C.d 2 1).hom) :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr ⟨zker, hzneKer⟩
  let _ : X.HasDimensionLT 3 :=
    SimplicialComplex.orderedSimplicialSet_hasDimensionLT
      K.toPreAbstractSimplicialComplex 3 (fun s hs => hK.card_le K hs)
  let _ : Subsingleton (C.X 3) := ModuleCat.subsingleton_of_isZero
    (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R 3 3)
  have hd₃ : (C.d 3 2).hom = 0 := by
    ext x
    rw [show x = 0 from Subsingleton.elim _ _, map_zero]
    rfl
  have hker := finrank_ker_eq_homology_add_range (C.sc' 3 2 1)
  have hhomPos : 0 < Module.finrank (ZMod 2) (C.homology 2) := by
    change Module.finrank (ZMod 2) (LinearMap.ker (C.d 2 1).hom) =
      Module.finrank (ZMod 2) (C.sc' 3 2 1).homology +
        Module.finrank (ZMod 2) (LinearMap.range (C.d 3 2).hom) at hker
    have hsc := (CategoryTheory.ShortComplex.homologyMapIso
      (C.isoSc' 3 2 1 (by simp) (by simp))).toLinearEquiv.finrank_eq
    change Module.finrank (ZMod 2) (C.homology 2) =
      Module.finrank (ZMod 2) (C.sc' 3 2 1).homology at hsc
    rw [hd₃, LinearMap.range_zero, finrank_bot, add_zero, ← hsc] at hker
    omega
  have hnorm := (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) 2).toLinearEquiv.finrank_eq
  change Module.finrank (ZMod 2) ((X.chainComplex R).homology 2) =
    Module.finrank (ZMod 2) (C.homology 2) at hnorm
  have hreal := (DifferentialGeometry.SSet.realizationHomologyIso R X 2).toLinearEquiv.finrank_eq
  let F := (singularHomologyFunctor (ModuleCat (ZMod 2)) 2).obj R
  let e : _root_.SSet.toTop.obj X ≅ TopCat.of K.space :=
    TopCat.isoOfHomeo (by simpa [X] using
      SimplicialComplex.geometricRealizationHomeomorphism K)
  have hhomeo := (F.mapIso e).toLinearEquiv.finrank_eq
  change 0 < Module.finrank (ZMod 2)
    (((singularHomologyFunctor (ModuleCat (ZMod 2)) 2).obj R).obj (TopCat.of K.space))
  calc
    0 < Module.finrank (ZMod 2) (C.homology 2) := hhomPos
    _ = Module.finrank (ZMod 2) ((X.chainComplex R).homology 2) := hnorm.symm
    _ = Module.finrank (ZMod 2)
        (((singularHomologyFunctor (ModuleCat (ZMod 2)) 2).obj R).obj
          (_root_.SSet.toTop.obj X)) := hreal
    _ = Module.finrank (ZMod 2)
        (((singularHomologyFunctor (ModuleCat (ZMod 2)) 2).obj R).obj
          (TopCat.of K.space)) := by simpa [F, X] using hhomeo

open Classical in
theorem IsCombinatorialManifold.isPLSphere_two_of_simplyConnectedSpace
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) [SimplyConnectedSpace K.space] :
    IsPLSphere 2 K.space := by
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have hb₀ := bettiNumber_zero_of_isConnected K (ZMod 2) hconn
  let _ : Subsingleton (((singularHomologyFunctor (ModuleCat (ZMod 2)) 1).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj (TopCat.of K.space)) :=
    fieldSingularHomology_one_subsingleton (k := ZMod 2) (X := K.space)
  have hb₁ : Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 1 = 0 :=
    Module.finrank_zero_of_subsingleton
  have hb₂ := hK.bettiNumber_two_pos_mod_two K hconn
  have hEuler := eulerChar_eq_sum_bettiNumber K (ZMod 2) 2
    (fun s hs => hK.card_le K hs)
  have hEulerFormula : eulerChar K = 1 +
      (Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 2 : ℤ) := by
    rw [hEuler]
    norm_num [Finset.sum_range_succ, hb₀, hb₁]
  have hle := hK.faceEulerChar_le_two K hconn
  have hEulerEq : SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex = 2 := by
    change eulerChar K ≤ 2 at hle
    change eulerChar K = 2
    rw [hEulerFormula]
    have hb₂cast : (1 : ℤ) ≤
        (Homology.bettiNumber (ZMod 2) (TopCat.of K.space) 2 : ℤ) := by
      exact_mod_cast hb₂
    omega
  exact hK.isPLSphere_two_of_faceEulerChar_eq_two K hconn hEulerEq

end DifferentialGeometry.Topology.PiecewiseLinear
