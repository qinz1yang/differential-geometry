import DifferentialGeometry.Topology.Homology.SimplexDegreeNaturality
import DifferentialGeometry.Topology.ThreeManifold.LocalOrientation
import DifferentialGeometry.Topology.Homology.PositiveAffineNormalization

noncomputable section

open CategoryTheory CategoryTheory.Limits Set ContinuousMap
open DifferentialGeometry.Topology
open Convexity.StdSimplex (coordinateSet coordinateHomeomorph coordinateEquiv)
open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}

def OrientedChartSimplex.localHomologyNormalizationIso
    (S : OrientedChartSimplex o x) :
    integralLocalHomology 3 x ≅ integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) := by
  let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let e := S.chart.trans
    (Homeomorph.ulift (X := ThreeSpace) : liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.toOpenPartialHomeomorph
  have hx : x ∈ e.source := ⟨S.center_mem, Set.mem_univ _⟩
  let N : liftedSphereSpace.{u} 1 ≃ₜ liftedSphereSpace.{u} 1 :=
    (Homeomorph.addRight (-(e x))).trans
      (Homeomorph.smulOfNeZero S.radius⁻¹ (inv_ne_zero (ne_of_gt S.radius_pos)))
  have hN : N (e x) = 0 := by
    change S.radius⁻¹ • (e x - e x) = 0
    rw [sub_self, smul_zero]
  exact integralLocalHomologyOpenPartialHomeomorphIso 3 e x hx ≪≫
    integralRelativeHomologyHomeomorphIso 3 N ({e x}ᶜ : Set (liftedSphereSpace.{u} 1))
      ({0}ᶜ : Set (liftedSphereSpace.{u} 1))
      (fun _ hy heq => hy (N.injective (heq.trans hN.symm)))
      (fun y hy heq => hy ((N.apply_symm_apply y).symm.trans ((congrArg N heq).trans hN)))

theorem OrientedChartSimplex.localHomologyNormalizationIso_localOrientationClass
    (S : OrientedChartSimplex o x) :
    S.localHomologyNormalizationIso.hom.hom (localOrientationClass o x) =
      euclideanStandardSimplexClass.{u} := by
  let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let e := S.chart.trans
    (Homeomorph.ulift (X := ThreeSpace) : liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.toOpenPartialHomeomorph
  have hx : x ∈ e.source := ⟨S.center_mem, Set.mem_univ _⟩
  let σ := S.simplex.comp
    ⟨(coordinateHomeomorph ℝ _).symm, (coordinateHomeomorph ℝ _).symm.continuous⟩
  have hσsource : ∀ q : coordinateSet ℝ (Fin 4), σ q ∈ e.source :=
    fun q => ⟨S.chart.map_target (S.simplex_inside _), Set.mem_univ _⟩
  have hσ : ∀ (i : Fin 4) (q : coordinateSet ℝ (Fin 3)),
      σ (SimplexDegree.orientedSimplexFace i q) ≠ x := by
    intro i q heq
    let t := (coordinateHomeomorph ℝ _).symm (SimplexDegree.orientedSimplexFace i q)
    have h := congrArg S.chart heq
    change S.chart (S.chart.symm (S.chart x + S.radius • positiveTetrahedron t)) =
      S.chart x at h
    rw [S.chart.right_inv (S.simplex_inside t)] at h
    have hs : S.radius • positiveTetrahedron t = 0 :=
      add_left_cancel (h.trans (add_zero _).symm)
    apply SimplexDegree.standardTetrahedronSimplex_face_ne_zero.{u} i q
    exact congrArg ULift.up ((smul_eq_zero.mp hs).resolve_left (ne_of_gt S.radius_pos))
  have hσround :
      σ.comp ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩ = S.simplex := by
    ext q
    rfl
  have hclass : localOrientationClass o x = SimplexDegree.simplexLocalClass x σ hσ := by
    rw [← localOrientationClass_spec o x S]
    unfold SimplexDegree.simplexLocalClass SimplexDegree.integralSimplexChain
    simp only [hσround]
    rfl
  let σE : C(coordinateSet ℝ (Fin 4), liftedSphereSpace.{u} 1) :=
    ⟨fun q => e (σ q), e.continuousOn.comp_continuous σ.continuous hσsource⟩
  have hσE : ∀ (i : Fin 4) (q : coordinateSet ℝ (Fin 3)),
      σE (SimplexDegree.orientedSimplexFace i q) ≠ e x :=
    fun i q h => hσ i q (e.injOn (hσsource _) hx h)
  let N : liftedSphereSpace.{u} 1 ≃ₜ liftedSphereSpace.{u} 1 :=
    (Homeomorph.addRight (-(e x))).trans
      (Homeomorph.smulOfNeZero S.radius⁻¹ (inv_ne_zero (ne_of_gt S.radius_pos)))
  have hN : N (e x) = 0 := by
    change S.radius⁻¹ • (e x - e x) = 0
    rw [sub_self, smul_zero]
  have hNmap : MapsTo N ({e x}ᶜ : Set (liftedSphereSpace.{u} 1))
      ({0}ᶜ : Set (liftedSphereSpace.{u} 1)) :=
    fun _ hy heq => hy (N.injective (heq.trans hN.symm))
  have hNinv : MapsTo N.symm ({0}ᶜ : Set (liftedSphereSpace.{u} 1))
      ({e x}ᶜ : Set (liftedSphereSpace.{u} 1)) :=
    fun y hy heq => hy ((N.apply_symm_apply y).symm.trans ((congrArg N heq).trans hN))
  change (integralRelativeHomologyHomeomorphIso 3 N _ _ hNmap hNinv).hom.hom
    ((integralLocalHomologyOpenPartialHomeomorphIso 3 e x hx).hom.hom
      (localOrientationClass o x)) = _
  rw [hclass,
    SimplexDegree.integralLocalHomologyOpenPartialHomeomorphIso_simplexLocalClass
      e x hx σ hσsource hσ]
  change (integralRelativeHomologyHomeomorphIso 3 N _ _ hNmap hNinv).hom.hom
    (SimplexDegree.simplexLocalClass (e x) σE hσE) = _
  change integralRelativeHomologyMap 3 (⟨N, N.continuous⟩ : C(liftedSphereSpace.{u} 1, liftedSphereSpace.{u} 1)) hNmap
    (SimplexDegree.simplexLocalClass (e x) σE hσE) = _
  rw [SimplexDegree.integralRelativeHomologyMap_simplexLocalClass]
  have hσN : (⟨N, N.continuous⟩ : C(liftedSphereSpace.{u} 1, liftedSphereSpace.{u} 1)).comp σE =
      SimplexDegree.standardTetrahedronSimplex := by
    apply ContinuousMap.ext
    intro q
    let t := (coordinateHomeomorph ℝ _).symm q
    change (ULift.up (S.radius⁻¹ •
      (S.chart (S.chart.symm (S.chart x + S.radius • positiveTetrahedron t)) - S.chart x)) :
      liftedSphereSpace.{u} 1) = ULift.up (positiveTetrahedron t)
    rw [S.chart.right_inv (S.simplex_inside t), add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (ne_of_gt S.radius_pos), one_smul]
  simp only [hσN]
  unfold SimplexDegree.simplexLocalClass SimplexDegree.integralSimplexChain
    euclideanStandardSimplexClass simplexLocalClass
  congr 1


theorem OrientedChartSimplex.localOrientationClass_chart_normalization
    (S : OrientedChartSimplex o x) :
    let e := S.chart.trans
      (Homeomorph.ulift (X := ThreeSpace) : liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.toOpenPartialHomeomorph
    let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
    integralRelativeHomologyMap 3 (toContinuousMap (Homeomorph.addRight (-(e x))))
      (show MapsTo (Homeomorph.addRight (-(e x))) ({e x}ᶜ : Set (liftedSphereSpace.{u} 1))
        ({0}ᶜ : Set (liftedSphereSpace.{u} 1)) from fun _ hz => sub_ne_zero.mpr hz)
      ((integralLocalHomologyOpenPartialHomeomorphIso 3 e x
        (show x ∈ e.source from ⟨S.center_mem, Set.mem_univ _⟩)).hom.hom
        (localOrientationClass o x)) = euclideanStandardSimplexClass.{u} := by
  let _ : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let e := S.chart.trans
    (Homeomorph.ulift (X := ThreeSpace) : liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.toOpenPartialHomeomorph
  have h := S.localHomologyNormalizationIso_localOrientationClass
  change integralRelativeHomologyMap 3
    (toContinuousMap ((Homeomorph.addRight (-(e x))).trans
      (Homeomorph.smulOfNeZero S.radius⁻¹ (inv_ne_zero (ne_of_gt S.radius_pos)))))
    (show MapsTo (fun y : liftedSphereSpace.{u} 1 => S.radius⁻¹ • (y - e x))
      ({e x}ᶜ : Set (liftedSphereSpace.{u} 1)) ({0}ᶜ : Set (liftedSphereSpace.{u} 1)) from
      fun _ hy hz => hy (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left
        (inv_ne_zero (ne_of_gt S.radius_pos)))))
    ((integralLocalHomologyOpenPartialHomeomorphIso 3 e x
      (show x ∈ e.source from ⟨S.center_mem, Set.mem_univ _⟩)).hom.hom
      (localOrientationClass o x)) = _ at h
  rw [integralRelativeHomologyMap_smul_sub_eq_sub 3 (e x) (inv_pos.mpr S.radius_pos)] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
