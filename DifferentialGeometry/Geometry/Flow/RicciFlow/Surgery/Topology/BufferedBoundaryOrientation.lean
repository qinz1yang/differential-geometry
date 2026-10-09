import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingCollarDifferential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedCappingOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingCollarOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCappingSmooth
import DifferentialGeometry.Topology.Manifold.Interval.TangentLift
import DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarDifferential
import DifferentialGeometry.Topology.Manifold.OrientationFrameDictionary

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] {ι : Type} [Finite ι] {δ : ι → ℝ}
  (hδ : ∀ i, 0 < δ i)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph IC (𝓡 3) ∞ (f i))

theorem cuttingCollar_orientation_ratio {L : ℝ} (hL : 0 < L)
    (b : ι × Bool) (o : SmoothOrientation (𝓡 3) M)
    (oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    ∀ (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (δ b.1))),
      (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q =
        (cuttingCollarSmoothOrientation (𝓡 3) (by simp) hδ f hf hdisj hs b o).val q →
      ∃ K : (E2 × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] E3,
        (K : (E2 × EuclideanSpace ℝ (Fin 1)) →L[ℝ] E3) =
          mfderiv IR (𝓡 3) (f b.1 ∘ cuttingCollarCylinderMap (hδ b.1) b.2) q ∧
        Orientation.map (Fin 3)
          ((differentialEquivOfBijective IR (𝓡 3)
            (radialCollarOrientationMap L (cuttingCollarWidth (δ b.1)))
            (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos (hδ b.1))) q).symm.toLinearEquiv.trans K.toLinearEquiv)
          (Orientation.reindex ℝ E3 (finCongr (by simp)) oE) =
            (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation o).orientation
              (f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 q)) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace (𝓡 3) (by simp) hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold (𝓡 3) (by simp) hδ f hf hdisj hs
  intro q hm
  let R := differentialEquivOfBijective IR (𝓡 3)
    (radialCollarOrientationMap L (cuttingCollarWidth (δ b.1)))
    (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos (hδ b.1))) q
  let C := differentialEquivOfBijective IR IR
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_mfderiv_bijective (𝓡 3) (by simp) hδ f hf hdisj hs b) q
  let J := differentialEquivOfBijective IR (𝓡 3) (Subtype.val : cutCore f → M)
    (cutCore_ambientInclusion_mfderiv_bijective (𝓡 3) (by simp) hδ f hf hdisj hs)
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)
  let K := C.trans J
  refine ⟨K, ?_, ?_⟩
  · exact (mfderiv_comp q
      ((cutCore_ambientInclusion_isSmoothEmbedding (𝓡 3) (by simp) hδ f hf hdisj hs).contMDiff.mdifferentiableAt (by simp))
      ((cuttingCollarMap_isLocalDiffeomorph (𝓡 3) (by simp) hδ f hf hdisj hs b).contMDiff.mdifferentiableAt (by simp))).symm
  · let oc := (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q
    have hR : tangentOrientationEquiv R.toLinearEquiv oc = oE :=
      tangentOrientationEquiv_symm R.symm.toLinearEquiv oE
    have hK : tangentOrientationEquiv K.toLinearEquiv oc =
        o.val (f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 q)) := by
      change tangentOrientationEquiv (C.toLinearEquiv.trans J.toLinearEquiv) oc = _
      rw [tangentOrientationEquiv_trans]
      have hC : tangentOrientationEquiv C.toLinearEquiv oc =
          (cutCoreSmoothOrientation (𝓡 3) (by simp) hδ f hf hdisj hs o).val
            (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
        dsimp only [oc]
        rw [hm, cuttingCollarSmoothOrientation_apply]
        exact tangentOrientationEquiv_symm C.symm.toLinearEquiv _
      rw [hC]
      exact cutCoreSmoothOrientation_pushforward (𝓡 3) (by simp) hδ f hf hdisj hs o _
    rw [DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofSmoothOrientation_apply]
    exact DifferentialGeometry.orientation_map_inverse_trans_of_tangentOrientationEquiv
      (by simp) R.toLinearEquiv K.toLinearEquiv oc hR hK

end DifferentialGeometry.Topology.ThreeManifold.Surgery

end

end

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] {ι : Type} [Fintype ι] {δ : ι → ℝ}
  (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph IC (𝓡 3) ∞ (f i))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj

omit [T2Space M] [IsManifold (𝓡 3) ∞ M] in
include hs in
theorem mfderiv_buffered_boundarySphere_comp
    (b : ι × Bool) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (z : S2) (v : E2) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    mfderiv (𝓡 2) (𝓡 3) ((T).boundarySphere b ∘ a) z v =
      mfderiv IR (𝓡 3) (f b.1 ∘ cuttingCollarCylinderMap (hδ b.1) b.2)
        (a z, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
        (mfderiv (𝓡 2) (𝓡 2) a z v, (0 : E1)) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let c := f b.1 ∘ cuttingCollarCylinderMap (hδ b.1) b.2
  let j : S2 → S2 × Ico (0 : ℝ) (cuttingCollarWidth (δ b.1)) :=
    fun y => (a y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
  have heq : (T).boundarySphere b ∘ a = c ∘ j := by
    funext y
    change f b.1 _ = f b.1 _
    congr 1
    apply Subtype.ext
    change (a y, (TubeSystem.boundaryLevel b.2).val) =
      (a y, cuttingSign b.2 + cuttingSign b.2 * 0)
    congr 1
    cases b.2 <;> norm_num [TubeSystem.boundaryLevel, cuttingSign]
  have hc : ContMDiff IR (𝓡 3) ∞ c :=
    (hs b.1).contMDiff.comp (cuttingCollarCylinderMap_contMDiff (hδ b.1) b.2)
  have hj : ContMDiff (𝓡 2) IR ∞ j := a.contMDiff.prodMk contMDiff_const
  erw [heq]
  erw [mfderiv_comp_apply z (hc.mdifferentiableAt (by simp)) (hj.mdifferentiableAt (by simp))]
  congr 1
  change mfderiv (𝓡 2) IR (fun y => (a y, (⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩ : Ico (0 : ℝ) (cuttingCollarWidth (δ b.1))))) z v = _
  erw [mfderiv_prodMk (a.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const]
  rfl


omit [T2Space M] [IsManifold (𝓡 3) ∞ M] [Fintype ι] in
include hs in
theorem mfderiv_buffered_outward_eq_neg_collar
    (b : ι × Bool) (y : S2) (ν : E1) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (δ b.1)) :=
      (y, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
    mvfderiv (I := (𝓡∂ 1)) (Subtype.val : Ico (0 : ℝ) (cuttingCollarWidth (δ b.1)) → ℝ) q.2 ν = 1 →
    mfderiv IR (𝓡 3) (originalTubularMap (hδ b.1) (hδ1 b.1) (f b.1))
      (y, TubeSystem.boundaryLevel b.2)
      (0, (if b.2 then (-1 : ℝ) else 1) • EuclideanSpace.single 0 (1 : ℝ)) =
      -mfderiv IR (𝓡 3) (f b.1 ∘ cuttingCollarCylinderMap (hδ b.1) b.2) q (0, ν) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  intro q hν
  let p := cuttingCollarCylinderMap (hδ b.1) b.2 q
  have hp : p.val = (y, (TubeSystem.boundaryLevel b.2).val) := by
    change (y, cuttingSign b.2 + cuttingSign b.2 * 0) = _
    congr 1
    cases b.2 <;> norm_num [TubeSystem.boundaryLevel, cuttingSign]
  erw [mfderiv_originalTubularMap (𝓡 3) (hδ b.1) (hδ1 b.1) (f b.1)
    (hs b.1).contMDiff (y, TubeSystem.boundaryLevel b.2) p hp]
  have hc := (cuttingCollarCylinderMap_contMDiff (hδ b.1) b.2).mdifferentiableAt (x := q) (by simp)
  erw [mfderiv_comp_apply q ((hs b.1).contMDiff.mdifferentiableAt (by simp)) hc,
    mfderiv_cuttingCollarCylinderMap (hδ b.1) b.2 q 0 ν, hν, mul_one]
  have ht : (TubeSystem.boundaryLevel b.2).val < 2 := by
    cases b.2 <;> norm_num [TubeSystem.boundaryLevel]
  have hsingle := DifferentialGeometry.Manifold.Interval.mfderiv_subtypeVal_Icc_single_of_lt
    (TubeSystem.boundaryLevel b.2) ht 1
  erw [map_smul, hsingle]
  change mfderiv IC (𝓡 3) (f b.1) p
    (0, (if b.2 then (-1 : ℝ) else 1) * 1) =
      -mfderiv IC (𝓡 3) (f b.1) p (0, cuttingSign b.2)
  rw [mul_one]
  have heq : ((0 : E2), (if b.2 then (-1 : ℝ) else 1)) =
      -((0 : E2), cuttingSign b.2) := by
    cases b.2 <;> simp [cuttingSign]
  rw [heq]
  exact map_neg (mfderiv IC (𝓡 3) (f b.1) p) (0, cuttingSign b.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] {ι : Type} [Fintype ι] {δ : ι → ℝ}
  (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph IC (𝓡 3) ∞ (f i))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj

include hs in
theorem buffered_boundary_orientation_signed {L : ℝ} (hL : 0 < L)
    (b : ι × Bool) (o : SmoothOrientation (𝓡 3) M)
    (oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)))
    (A : E3 ≃ₗᵢ[ℝ] E3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (ha : ∀ z, (a z : E3) = A z)
    (hA : Orientation.map (Fin 3) A.toLinearEquiv (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
      (if b.2 then (1 : ℝˣ) else -1) • Orientation.reindex ℝ E3 (finCongr (by simp)) oE) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    (∀ q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (δ b.1)),
      (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q =
        (cuttingCollarSmoothOrientation (𝓡 3) (by simp) hδ f hf hdisj hs b o).val q) →
    ∀ (z : S2) (v w : E2),
      let β := (T).boundarySphere b ∘ a
      let oo := (TangentOrientationSection.ofSmoothOrientation o).orientation (β z)
      0 < (oo.someBasis (by change Fintype.card (Fin 3) = Module.finrank ℝ E3; simp)).det
        ![mfderiv IR (𝓡 3) (originalTubularMap (hδ b.1) (hδ1 b.1) (f b.1))
            (a z, TubeSystem.boundaryLevel b.2)
            (0, (if b.2 then (-1 : ℝ) else 1) • EuclideanSpace.single 0 (1 : ℝ)),
          mfderiv (𝓡 2) (𝓡 3) β z v, mfderiv (𝓡 2) (𝓡 3) β z w] ↔
        (if b.2 then (1 : ℝ) else -1) * (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
          ![z.val, mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v,
            mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z w] < 0 := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  intro hm z v w β oo
  let q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (δ b.1)) :=
    (a z, ⟨0, le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩)
  obtain ⟨K, hK, hratio⟩ := cuttingCollar_orientation_ratio hδ f hf hdisj hs hL b o oE q (hm q)
  let R := differentialEquivOfBijective IR (𝓡 3)
    (radialCollarOrientationMap L (cuttingCollarWidth (δ b.1)))
    (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos (hδ b.1))) q
  have hsurj := (bijective_mfderiv_of_isImmersionAt (𝓡∂ 1) 𝓘(ℝ)
    (Subtype.val : Ico (0 : ℝ) (cuttingCollarWidth (δ b.1)) → ℝ) q.2
    ((isSmoothEmbedding_halfClosedInterval_inclusion (cuttingCollarWidth_pos (hδ b.1))).isImmersion.isImmersionAt q.2)
    (by simp)).surjective
  obtain ⟨ν, hν⟩ := hsurj 1
  have hn : R (0, ν) = A z.val := by
    exact (radialCollar_mfderiv_normal (L := L) (cuttingCollarWidth_pos (hδ b.1)) (a z) ν hν).trans (ha z)
  have hv : R (mfderiv (𝓡 2) (𝓡 2) a z v, (0 : E1)) =
      L • A (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v) :=
    radialCollar_mfderiv_tangent (L := L) (cuttingCollarWidth_pos (hδ b.1)) A a ha z v
  have hw : R (mfderiv (𝓡 2) (𝓡 2) a z w, (0 : E1)) =
      L • A (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z w) :=
    radialCollar_mfderiv_tangent (L := L) (cuttingCollarWidth_pos (hδ b.1)) A a ha z w
  have hh := basisDet_boundary_pos_iff_signed_of_radial_frame A.toLinearEquiv R.toLinearEquiv K.toLinearEquiv
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (Orientation.reindex ℝ E3 (finCongr (by simp)) oE)
    ((TangentOrientationSection.ofSmoothOrientation o).orientation
      (f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 q))) (by simp)
    (if b.2 then (1 : ℝˣ) else -1) hL.ne' hratio hA z.val
    (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v)
    (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z w)
    (0, ν) (mfderiv (𝓡 2) (𝓡 2) a z v, (0 : E1))
    (mfderiv (𝓡 2) (𝓡 2) a z w, (0 : E1)) hn hv hw
  have hout := mfderiv_buffered_outward_eq_neg_collar hδ hδ1 f hs b (a z) ν hν
  have htv := mfderiv_buffered_boundarySphere_comp hδ hδ1 f hf hdisj hs b a z v
  have htw := mfderiv_buffered_boundarySphere_comp hδ hδ1 f hf hdisj hs b a z w
  have hp : β z = f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 q) := by
    change f b.1 _ = f b.1 _
    congr 1
    apply Subtype.ext
    change (a z, (TubeSystem.boundaryLevel b.2).val) =
      (a z, cuttingSign b.2 + cuttingSign b.2 * 0)
    congr 1
    cases b.2 <;> norm_num [TubeSystem.boundaryLevel, cuttingSign]
  change 0 < (((TangentOrientationSection.ofSmoothOrientation o).orientation (β z)).someBasis _).det _ ↔ _
  rw [hp]
  erw [hout, htv, htw]
  have hKa (x : E2 × E1) : K.toLinearEquiv x = mfderiv IR (𝓡 3)
      (f b.1 ∘ cuttingCollarCylinderMap (hδ b.1) b.2) q x :=
    congrArg (fun D : E2 × E1 →L[ℝ] E3 => D x) hK
  simp only [hKa] at hh
  convert hh using 1
  · rfl
  · cases b.2 <;> simp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end
